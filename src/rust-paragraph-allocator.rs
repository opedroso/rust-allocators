#![allow(dead_code)]

use crate::definitions::*;
use crossbeam::atomic::*;
use log::*;
use std::alloc::Layout;
use std::cell::UnsafeCell;
use std::cmp::max;
use std::default::Default;
use std::mem::{align_of, offset_of, size_of, size_of_val};
use std::ops::*;
use std::ops::{BitAnd, BitOr};
use std::pin::Pin;
use std::ptr::NonNull;

/// MemoryArena manages allocations within its static memory array
/// It is meant to be written once by possibly multi-threaded user block producers
/// There is no way to deallocate a single user block: only whole pool can be deallocated (all user blocks dealocated at once)
/// No locks are held while allocating memory; intrinsics are used to allocate next block
/// This design decision (optimization for allocation path) costs unused memory if last block cannot fit in space available
/// Every instance of MemoryArena is Pin<Box<MemoryArena>>; this means it cannot be moved
///
///
/// Allocations:
/// Minimum allocation is 32 bytes (control area of 16 bytes + user block of up to 16 bytes) or ( 1 control paragraph + 1 user block paragraph)
/// Maximum allocation with 1 Mib pool (as implemented) is 1_048_544 bytes (or 65_534 paragraphs) or (1 control paragraph + 65_533 user block paragraphs)
/// Maximum user block allocation is then 1_048_528 bytes (= 16 bytes * 65_533 paragraphs)
/// If a request is made for a user block that would lay beyond pool capacity, the user gets error *and* pool is closed for new allocations (last block is wasted)
/// It is possible that last block request failed due to multi-threading usage
/// In this case, pool will show that next free block have index larger than COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA
/// This indicates that the pool is full
/// Iterating over the list of allocated blocks will stop at last successfully allocated block (paragraph's next free block index will still be zero)
///
/// Alignment:
/// Allocations are aligned to 16 byte boundary. Pool is aligned to 1 MiB boundary
/// Any allocation can find its pool by shifting its address by 20 bits (2^20 = 1 MiB)
/// Each control paragraph has a signature that contains (pool base address and index where next allocation begins)
/// Last allocated block in pool will have (pool base addres, zero) in its control block
/// Number of bits dedicated to index to next allocation has 20 bits but for 1 MiB implementation only 16 bits are used
/// As there are no pointers in control data, only indices, pool can be memoy mapped to a different locations and still be valid
/// Base address would have original mapping but that can be used to indicate that user block has not yet been processed after this new mapping
///
/// Stack requirement:
/// Stack size for thread creating the MemoryArena has to be larger than 1 Mib (MemoryArena requirement) + your functions requirement
/// Suggestion is to create MemoryArenas from specific thread started with enough stack space (see tests for example)
///

/*
bits_in_arena_alloc	alignment	count_paragraphs	bits_in_paragraph_idx	IDX_MASK
17	131072	8192	13	1FFF
18	262144	16384	14	3FFF
19	524288	32768	15	7FFF
20	1048576	65536	16	FFFF
21	2097152	131072	17	1FFFF
22	4194304	262144	18	3FFFF
23	8388608	524288	19	7FFFF
24	16777216	1048576	20	FFFFF
*/

// global constants - RELEASE
#[cfg(not(debug_assertions))] // as set in Cargo.toml
pub mod definitions {
    pub const ONE_MEGABYTE: usize = 1_048_576; // number of bytes in 1 MiB (2^20)
    pub const MEMORY_ARENA_SIZE_IN_BYTES: usize = 16 * ONE_MEGABYTE; // must be multiple of 1 MiB, but no more than 16 MB total (limit is number of bits in paragraph.next_free_idx)
    pub const SIGNATURE_MASK: u64 = !((MEMORY_ARENA_SIZE_IN_BYTES - 1) as u64); // must fit significant (that is non-zero) base address in the signature bits
    pub const PARAGRAPH_IDX_MASK: u64 = !(SIGNATURE_MASK); // the lower bits of signature will have the index of the next (free or alloc'ed) paragraph
    pub const PARAGRAPH_SIZE_IN_BYTES: usize = 16; // a paragraph is a 16 bytes chunk of memory; in our case which has an address that is on a 16 byte boundary
    pub const MEMORY_ARENA_SIZE_IN_PARAGRAPHS: usize =
        MEMORY_ARENA_SIZE_IN_BYTES / PARAGRAPH_SIZE_IN_BYTES; // size of memory arena in paragraphs
    pub const COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA: usize = MEMORY_ARENA_SIZE_IN_PARAGRAPHS - 2; // paragraphs available for allocation 0..COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA

    use crossbeam::atomic::*;
    use std::cell::UnsafeCell;

    #[repr(C,align(1_048_576))] // ONE_MEGABYTE boundary
    #[derive(Debug)]
    pub(crate) struct MemoryArena {
        // 1 MB = Paragraph[65_536]
        // memory arena for allocation begins here
        pub(crate) memory: UnsafeCell<[Paragraph; COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA]>, // indices 0..65_533 // memory must be first memory address within MemoryArena
        // paragraph[65534] // = 1 + COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA
        pub(crate) _available: u64, // contents not yet used, but must be first variable past memory (or update function contains)
        pub(crate) next_available_paragraph_idx: AtomicCell<usize>, // value must be less than COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA; index into memory array that is free for next allocation
        // paragraph[65535] // = 2 + COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA - last 16 bytes in 1 MB block
        pub(crate) future_next_arena_base_addr: AtomicCell<u64>, // when this arena is out of memory and a new allocation is requested, a new arena will fullfil it
        pub(crate) signature: u64, // ((the base address of the arena)>>20)
    }
    #[repr(C,align(16))] // PARAGRAPH_SIZE_IN_BYTES
    #[derive(Copy, Clone, Debug, Default)]
    pub(crate) struct Paragraph {
        pub(crate) paragraph_signature: u64, // ((the base address of the arena)>>20)<<20) & next_[free/allocated]_paragraph_idx
        pub(crate) _available: u64,          // not yet used
    }
}

// global constants - DEBUG
#[cfg(debug_assertions)]
pub mod definitions {
    pub const ONE_MEGABYTE: usize = 1_048_576; // number of bytes in 1 MiB (2^20)
    pub const MEMORY_ARENA_SIZE_IN_BYTES: usize = 4_096; // must be less than 1 MiB for using debugger in the IDE since default stack is 1 Mib
    pub const SIGNATURE_MASK: u64 = !((MEMORY_ARENA_SIZE_IN_BYTES - 1) as u64); // must fit significant (that is non-zero) base address in the signature bits
    pub const PARAGRAPH_IDX_MASK: u64 = !(SIGNATURE_MASK); // the lower bits of signature will have the index of the next (free or alloc'ed) paragraph
    pub const PARAGRAPH_SIZE_IN_BYTES: usize = 16; // a paragraph is a 16 bytes chunk of memory; in our case which has an address that is on a 16 byte boundary
    pub const MEMORY_ARENA_SIZE_IN_PARAGRAPHS: usize =
        MEMORY_ARENA_SIZE_IN_BYTES / PARAGRAPH_SIZE_IN_BYTES; // size of memory arena in paragraphs
    pub const COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA: usize = MEMORY_ARENA_SIZE_IN_PARAGRAPHS - 2; // paragraphs available for allocation 0..COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA

    use crossbeam::atomic::*;
    use std::cell::UnsafeCell;

    #[repr(C,align(4_096))] // must be literal value of MEMORY_ARENA_SIZE_IN_BYTES
    #[derive(Debug)]
    pub(crate) struct MemoryArena {
        // 1 MB = Paragraph[65_536]
        // memory arena for allocation begins here
        pub(crate) memory: UnsafeCell<[Paragraph; COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA]>, // indices 0..65_533 // memory must be first used address within MemoryArena
        // paragraph[65534] // = 1 + COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA
        pub(crate) _available: u64, // contents not yet used, but must be first variable past memory (or change the function contains() accordingly)
        pub(crate) next_available_paragraph_idx: AtomicCell<usize>, // value must be less than COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA; index into memory array that is free for next allocation
        // paragraph[65535] // = 2 + COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA - last 16 bytes in 1 MB block
        pub(crate) future_next_arena_base_addr: AtomicCell<u64>, // when this arena is out of memory and a new allocation is requested, a new arena will fullfil it
        pub(crate) signature: u64, // ((the base address of the arena)>>20)
                                   // Note: next_available_paragraph_idx and future_next_arena_base_addr *must not* be in same paragraph due to intrinsic locking used to access them
    }
    #[repr(C,align(16))] // PARAGRAPH_SIZE_IN_BYTES
    #[derive(Copy, Clone, Debug)]
    #[derive(Default)]
pub(crate) struct Paragraph {
        pub(crate) paragraph_signature: u64, // ((the base address of the arena)>>20)<<20) & next_[free/allocated]_paragraph_idx
        pub(crate) _available: u64,          // not yet used
    }
}

// Paragraph represents a 16 byte chunk of memory
// there will be one header/control paragraph before every arena allocation to indicate where the allocation ends and next allocation begins
// allocation blocks will always be multiple of 16 byte chunks
// when a single byte allocation is requested, a 32 byte allocation will be dedicated to it (1 control paragraph + 1 data paragraph)
// when a 16 byte allocation is requested, a 32 byte allocation will be dedicated to it (1 control paragraph + 1 data paragraph)
// when a 32 byte allocation is requested, a 48 byte allocation will take place (1 control paragraph + 2 data paragraphs)
// there is always a header/control paragraph that indicates where next block begins or where the next free block begins
impl Paragraph {
    pub fn new() -> Self {
        assert_eq!(PARAGRAPH_SIZE_IN_BYTES, size_of::<Paragraph>()); // must forever be valid since this is a paragraph chunk allocator
        Default::default()
    }

    pub fn set_paragraph_signature(&mut self, next_free_paragraph_idx: usize) {
        let mb_aligned_base_addr = (self as *const _ as u64).bitand(SIGNATURE_MASK); // reset lower 20 bits
        self.paragraph_signature = mb_aligned_base_addr.bitor(next_free_paragraph_idx as u64); // "insert" the lower 20 bits
        debug!("set paragraph.signature: 0x{:x}", self.paragraph_signature);
    }

    // returns tuple (memory_arena_base_address, index_to_next_free_paragraph) when paragraph is first allocated
    // after the next free paragraph is allocated, it becomes a paragraph_index_of_next_allocated_paragraph
    pub fn get_paragraph_signature(&self) -> (u64, usize) {
        let (memory_arena_base_address, index_to_next_free_paragraph) = (
            self.paragraph_signature & SIGNATURE_MASK,
            (self.paragraph_signature & PARAGRAPH_IDX_MASK) as usize,
        );
        debug!("get paragraph.signature: (memory_arena_base_address: 0x{:x} ({}), index_to_next_free_paragraph: (0x{:x}) {})",
                    memory_arena_base_address, memory_arena_base_address, index_to_next_free_paragraph, index_to_next_free_paragraph);
        (memory_arena_base_address, index_to_next_free_paragraph)
    }
}


impl From<*mut Paragraph> for Paragraph {
    fn from(raw_ptr: *mut Paragraph) -> Self {
        assert!(!raw_ptr.is_null(), "Received null pointer");
        unsafe {
            // Dereference the raw pointer
            // Make sure that the raw pointer is valid before dereferencing
            *raw_ptr
        }
    }
}

impl MemoryArena {
    fn new() -> Pin<Box<MemoryArena>> {
        // even though the newly created MemoryArena will be instantiated on the heap (that is why we use Box::pin() to create it)
        // the compiler will require a temporary array on the stack size_of([Paragraph; COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA])
        // in RELEASE builds, this is 32 bytes shy of 16 Mib, so the stack of the calling thread needs to be larger than 16 MiB for this code to succeed
        let mut pinned_boxed_arena = Box::pin(MemoryArena {
            memory: UnsafeCell::new(
                [Paragraph {
                    paragraph_signature: 0, // Base address is initially 0
                    _available: 0,
                }; COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA],
            ),
            _available: 0,
            next_available_paragraph_idx: AtomicCell::<usize>::new(0),
            future_next_arena_base_addr: AtomicCell::<u64>::new(0),
            signature: 0,
        });
        let arena = pinned_boxed_arena.deref_mut();
        arena.set_signature();
        debug!(
            "new: Pin<Box<MemoryArena>>: {:p}, size: {}, arena signature: 0x{:016x}",
            arena,
            size_of_val(arena),
            arena.get_signature()
        );
        debug!("MemoryArena::new() returning");
        pinned_boxed_arena
    }

    fn get_mut_paragraph_at_idx(&self, paragraph_idx: usize) -> *mut Paragraph {
        unsafe {
            let mut_arena_memory = self.memory.get();
            &mut (*mut_arena_memory)[paragraph_idx] as *mut Paragraph
        }
    }

    fn set_signature_for_paragraph_at_idx(
        &self,
        next_free_paragraph_idx: usize,
        paragraph_idx: usize,
    ) {
        unsafe {
            let paragraph = self.get_mut_paragraph_at_idx(paragraph_idx);
            (*paragraph).set_paragraph_signature(next_free_paragraph_idx);
        }
    }

    pub fn contains(&self, ptr: NonNull<u8>) -> bool {
        let arena_begin = self.memory.get() as *const _ as u64;
        let arena_beyond_end = &self._available as *const _ as u64; // actually first byte beyond memory arena
        let address = ptr.as_ptr() as u64;
        arena_begin <= address && address < arena_beyond_end
    }

    fn set_signature(&mut self) {
        let signature = (self as *const _ as u64).bitand(SIGNATURE_MASK); // equivalent to (&arena as *const _) & 0xFFFFFFFFFFF00000
        self.signature = signature;
        debug!(
            "set_signature: arena address: {:p}, size: {}, arena signature: 0x{:016x}",
            self,
            size_of_val(self),
            self.signature
        );
    }
    fn get_signature(&self) -> u64 {
        self.signature
    }

    fn room_left_in_paragraphs(&self) -> usize {
        let current_free_index = self.next_available_paragraph_idx.load();
        if current_free_index <= COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA {
            COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA - current_free_index
        } else {
            0
        }
    }

    /// returns largest user block still allocatable in this memory arena
    fn room_left_in_bytes_mut(&mut self) -> usize {
        self.room_left_in_bytes()
    }
    /// returns largest user block still allocatable in this memory arena
    fn room_left_in_bytes(&self) -> usize {
        let count_free_paragraphs = self.room_left_in_paragraphs();
        if count_free_paragraphs > 0 {
            (count_free_paragraphs - 1) * PARAGRAPH_SIZE_IN_BYTES // -1 is for the control paragraph needed for each allocation
        } else {
            0
        }
    }

    fn alloc_bytes_zeroed(&self, num_bytes: usize) -> Option<NonNull<u8>> {
        let layout = Layout::from_size_align(num_bytes, size_of::<Paragraph>()).unwrap();
        self.alloc_zeroed(layout)
    }
    fn alloc_zeroed(&self, layout: Layout) -> Option<NonNull<u8>> {
        // prior to allocation, verify that there is still enough room available in the arena
        let size = layout.size();
        let room_left_bytes = self.room_left_in_bytes();
        if size == 0 || layout.align() > 16 || size > room_left_bytes {
            if layout.size() == 0 {
                // turned off in RELEASE because it is too noisy
                #[cfg(debug_assertions)]
                warn!("zero byte allocation requested but not fullfiled");
            }
            if layout.align() > size_of::<Paragraph>() {
                panic!("alignment > 16 not yet supported");
            };
            if size > room_left_bytes && room_left_bytes > 0 {
                warn!("largest user block possible is {} bytes", room_left_bytes);
            }
            return None;
        }
        let num_paragraphs = 1 + max(size / size_of::<Paragraph>(), 1); // header + user_block

        // allocation happens here
        let base_alloc_idx = self.next_available_paragraph_idx.fetch_add(num_paragraphs);

        // verify there was not a race condition and we ended up with an allocation past the end of the arena
        let user_base_alloc_idx = base_alloc_idx + 1;
        let next_available_paragraph_idx = base_alloc_idx + num_paragraphs;
        debug!(
            "base_alloc_idx= {}, next available paragraph idx= {}",
            base_alloc_idx, next_available_paragraph_idx
        );
        if next_available_paragraph_idx <= COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA {
            self.set_signature_for_paragraph_at_idx(next_available_paragraph_idx, base_alloc_idx);
            unsafe {
                let mut_arena_memory = self.memory.get();
                debug!("successfully allocated {:5} bytes aligned at {} byte boundary (used {} bytes from arena)", size, layout.align(), num_paragraphs * PARAGRAPH_SIZE_IN_BYTES);
                NonNull::new(&mut (*mut_arena_memory)[user_base_alloc_idx] as *mut _ as *mut u8)
            }
        } else {
            // this "partially allocated" block will remain unusable, since it ends past the arena end
            // notice that this block's signature is not set to mark as "not available" for iterators
            debug!(
                "attempt to allocate {} bytes: room_left_bytes: {}",
                size,
                self.room_left_in_bytes()
            );
            None
        }
    }

    /// Usage:
    /// let mut arena = MemoryArena::new(); // ... fill the arena
    ///
    /// for block in arena.iter_mut::<MyType>() {
    ///       // Do something with the block
    /// }
    ///
    pub fn iter_mut<'a, T: 'a>(&'a mut self) -> MemoryArenaIteratorMut<'a, T> {
        MemoryArenaIteratorMut::new(self)
    }
}

struct MemoryArenaIteratorMut<'a, T> {
    arena: &'a mut MemoryArena,
    current_index: usize,
    _marker: std::marker::PhantomData<T>,
}

impl<'a, T: 'a> MemoryArenaIteratorMut<'a, T> {
    /// Creates a new `MemoryArenaIteratorMut` for the given MemoryArena.
    pub fn new(arena: &'a mut MemoryArena) -> Self {
        Self {
            arena,
            current_index: 0, // Start at the beginning of the arena
            _marker: std::marker::PhantomData,
        }
    }
}

impl<'a, T: 'a> Iterator for MemoryArenaIteratorMut<'a, T> {
    type Item = &'a mut T;

    #[inline(never)]
    fn next(&mut self) -> Option<Self::Item> {
        // next free is allowed to be index above valid max but we must never attempt to de-reference it
        if self.current_index >= COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA {
            return None;
        }

        // Check if there is one more item in the list of allocated items
        let control_paragraph = self.arena.get_mut_paragraph_at_idx(self.current_index);
        let (_memory_arena_base_address, index_to_next_free_paragraph) =
            unsafe { (*control_paragraph).get_paragraph_signature() };
        debug!("MemoryArenaIteratorMut::next: paragraph[{}] _memory_arena_base_address {}, index_to_next_free_paragraph {}", self.current_index, _memory_arena_base_address, index_to_next_free_paragraph);
        if self.current_index >= index_to_next_free_paragraph {
            // note: if this alloc was result of a race condition, signature was not set and index_to_next_free_paragraph is zero; also returns here
            return None;
        }

        // Safety: validate type being iterated fits in allocated block
        let user_block_size =
            (index_to_next_free_paragraph - self.current_index) * PARAGRAPH_SIZE_IN_BYTES;
        if user_block_size < std::mem::size_of::<Self::Item>() {
            panic!("allocated user block must fit the enumerated type T");
        }

        // Safety: index is always internal to our arena, therefore valid
        let user_data_ptr = self.arena.get_mut_paragraph_at_idx(self.current_index + 1); // +1 to reach the user data block within the allocated block
        let item = unsafe { &mut *(user_data_ptr as *mut u8 as *mut T) };

        self.current_index = index_to_next_free_paragraph;
        Some(item)
    }
}

// set RUST_LOG=warn & cargo test --release -- --nocapture --test-threads 1
#[cfg(test)]
mod tests {
    use super::*;

    // cargo test --bin rust-paragraph-allocator test_validate_sizes -- --test-threads=1 --nocapture
    #[test]
    fn test_validate_sizes() {
        init_env_logger(); // honor RUST_LOG environment settting

        // Create a thread builder with a stack size that fits our arena
        let stack_size_in_bytes = max(2 * MEMORY_ARENA_SIZE_IN_BYTES, ONE_MEGABYTE);
        let builder = std::thread::Builder::new()
            .stack_size(stack_size_in_bytes)
            .name("test_validate_sizes".into());

        let sizeof_memory_arena = size_of::<MemoryArena>();
        assert_eq!(MEMORY_ARENA_SIZE_IN_BYTES, sizeof_memory_arena, "make sure you changed the alignment if you changed the arena size; requires source edit");
        let sizeof_paragraph = size_of::<Paragraph>();
        assert_eq!(PARAGRAPH_SIZE_IN_BYTES, sizeof_paragraph);

        // Spawn a new thread using the builder to create the arena
        let handle = builder.spawn(|| {
            // This closure runs in the new thread with the large stack
            let sizeof_memory_arena = size_of::<MemoryArena>();
            assert_eq!(MEMORY_ARENA_SIZE_IN_BYTES, sizeof_memory_arena);
            let sizeof_paragraph = size_of::<Paragraph>();
            assert_eq!(PARAGRAPH_SIZE_IN_BYTES, sizeof_paragraph);
            let mut arena = MemoryArena::new();
            let mut_arena = arena.deref_mut();
            let size_mut_arena = size_of_val(mut_arena);
            assert_eq!(MEMORY_ARENA_SIZE_IN_BYTES, size_mut_arena);

            let (header_paragraph, header_paragraph_signature) = unsafe {
                let mut_memory = mut_arena.memory.get();
                (&mut (*mut_memory)[0] as *mut Paragraph, (*mut_memory)[0].paragraph_signature)
            };
            assert_eq!(arena.next_available_paragraph_idx.load(), header_paragraph_signature.bitand(PARAGRAPH_IDX_MASK) as usize);
            debug!("test_validate_sizes: header_paragraph: 0x{:016x}, header paragraph signature: 0x{:016x}", header_paragraph as *const _ as u64, header_paragraph_signature);
        });

        // Wait for the spawned thread to finish
        if let Ok(join_handle) = handle {
            join_handle.join().unwrap();
        } else {
            error!("test_validate_sizes: Error creating the thread.");
        }
    }

    #[test]
    fn test_arena_new() {
        init_env_logger(); // honor RUST_LOG environment settting
        debug!("test_arena_new: starting");

        // Create a thread builder with necessary stack
        let stack_size_in_bytes = max(2 * MEMORY_ARENA_SIZE_IN_BYTES, ONE_MEGABYTE);
        let builder = std::thread::Builder::new()
            .stack_size(stack_size_in_bytes)
            .name("test_arena_new".into());

        let sizeof_memory_arena = size_of::<MemoryArena>();
        assert_eq!(MEMORY_ARENA_SIZE_IN_BYTES, sizeof_memory_arena);
        let sizeof_paragraph = size_of::<Paragraph>();
        assert_eq!(PARAGRAPH_SIZE_IN_BYTES, sizeof_paragraph);

        // Spawn a new thread using the builder
        let handle = builder.spawn(|| {
            debug!("test_arena_new: starting thread");
            let mut arena = MemoryArena::new();
            let allocator = arena.deref_mut();
            let masked_allocator = (allocator as *const _ as u64) & SIGNATURE_MASK;
            assert_eq!(allocator.get_signature(), masked_allocator);
            debug!("test_arena_new: stopping thread");
        });

        // Wait for the spawned thread to finish
        if let Ok(join_handle) = handle {
            join_handle.join().unwrap();
        } else {
            error!("test_validate_sizes: Error creating the thread.");
        }
        debug!("test_arena_new: returning");
    }

    /// verify that memory area contains pattern 0xDEADF0CA
    fn validate_pattern(ptr: *const u8, size: usize) -> bool {
        // Safety Check
        assert!(!ptr.is_null(), "Pointer is null!");
        assert!(size > 0, "Size is zero or negative!");
        debug!(
            "validate_pattern: addr= {:p}, size= {} (0x{:06x})",
            ptr, size, size
        );

        const PATTERN: [u8; 4] = [0xCA, 0xF0, 0xAD, 0xDE]; // "DEADF0CA" in bytes

        // Create a Slice for Reading (Note: *const for immutable access)
        let slice = unsafe { std::slice::from_raw_parts(ptr, size) };

        // Iterate and Compare
        for chunk in slice.chunks_exact(PATTERN.len()) {
            if chunk != PATTERN {
                return false; // Mismatch found
            }
        }

        // Handle Remaining Bytes (If Any)
        let remainder = slice.chunks_exact(PATTERN.len()).remainder();
        remainder == &PATTERN[..remainder.len()]
    }

    /// overwrite memory area with pattern 0xDEADF0CA
    fn fill_in_allocation(ptr: *mut u8, size: usize) {
        // Safety Check: Ensure the pointer is valid and the size is reasonable
        assert!(!ptr.is_null(), "Pointer is null!");
        assert!(size > 0, "Size is zero or negative!");

        // Pattern to Fill
        const PATTERN: [u8; 4] = [0xCA, 0xF0, 0xAD, 0xDE]; // "DEADF0CA" in bytes

        // Create a Slice for Convenient Writing
        let slice = unsafe { std::slice::from_raw_parts_mut(ptr, size) };

        // Efficiently Fill the Slice
        for chunk in slice.chunks_exact_mut(PATTERN.len()) {
            chunk.copy_from_slice(&PATTERN);
        }

        // Handle Remaining Bytes (If Any)
        let remainder = slice.chunks_exact_mut(PATTERN.len()).into_remainder();
        remainder.copy_from_slice(&PATTERN[..remainder.len()]);
    }

    #[test]
    fn test_single_alloc_and_contains() {
        init_env_logger(); // honor RUST_LOG environment settting

        // Create a thread builder with necesary stack
        let stack_size_in_bytes = max(2 * MEMORY_ARENA_SIZE_IN_BYTES, ONE_MEGABYTE);
        let builder = std::thread::Builder::new()
            .stack_size(stack_size_in_bytes)
            .name("test_single_alloc_and_contains".into());

        let sizeof_memory_arena = size_of::<MemoryArena>();
        assert_eq!(MEMORY_ARENA_SIZE_IN_BYTES, sizeof_memory_arena, "make sure you changed the alignment if you changed the arena size; requires source edit");
        let sizeof_paragraph = size_of::<Paragraph>();
        assert_eq!(PARAGRAPH_SIZE_IN_BYTES, sizeof_paragraph);

        // Spawn a new thread using the builder
        let handle = builder.spawn(|| {
            let mut arena = MemoryArena::new();
            let allocator = arena.deref_mut();

            let largest_possible_user_block_size = allocator.room_left_in_bytes_mut();
            let layout = Layout::from_size_align(largest_possible_user_block_size, 16).unwrap();
            if let Some(ptr) = allocator.alloc_zeroed(layout) {
                fill_in_allocation(ptr.as_ptr(), layout.size());
                assert!(allocator.contains(ptr));
                assert!(validate_pattern(ptr.as_ptr(), layout.size()));
            }
        });

        // Wait for the spawned thread to finish
        if let Ok(join_handle) = handle {
            join_handle.join().unwrap();
        } else {
            error!("test_validate_sizes: Error creating the thread.");
        }
    }

    // cargo test --bin rust-paragraph-allocator test_allocate_all_paragraphs -- --test-threads=1 --nocapture
    #[test]
    fn test_allocate_all_paragraphs() {
        init_env_logger(); // honor RUST_LOG environment settting

        // Create a thread builder with necessary stack size
        let stack_size_in_bytes = max(2 * MEMORY_ARENA_SIZE_IN_BYTES, ONE_MEGABYTE);
        let builder = std::thread::Builder::new()
            .stack_size(stack_size_in_bytes)
            .name("test_allocate_all_paragraphs".into());

        // Spawn a new thread using the builder
        let handle = builder.spawn(|| {
            // This closure runs in the new thread
            assert_eq!(MEMORY_ARENA_SIZE_IN_BYTES, size_of::<MemoryArena>(), "make sure you changed the alignment if you changed the arena size; requires source edit");
            assert_eq!(PARAGRAPH_SIZE_IN_BYTES, size_of::<Paragraph>());
            let arena = MemoryArena::new();
            let deref_arena = arena.deref();
            assert_eq!(MEMORY_ARENA_SIZE_IN_BYTES, size_of_val(deref_arena));

            assert_eq!(PARAGRAPH_SIZE_IN_BYTES, size_of::<u128>());
            let num_bytes = size_of::<u128>();
            let mut count_allocs = 0;
            while let Some(ptr) = deref_arena.alloc_bytes_zeroed(num_bytes) {
                count_allocs += 1;
                assert!(arena.contains(ptr));
                let ptr_mut_u128 = ptr.as_ptr() as *mut u128;
                unsafe { *ptr_mut_u128 = count_allocs as u128 };
            }
            debug!("test_allocate_all_paragraphs: allocated {} allocations of {} bytes", count_allocs, num_bytes);
        });

        // Wait for the spawned thread to finish
        if let Ok(join_handle) = handle {
            join_handle.join().unwrap();
        } else {
            error!("test_validate_sizes: Error creating the thread.");
        }
    }

    #[test]
    #[ignore] // used for test driven development only
    fn tdd_paragraph() {
        init_env_logger(); // honor RUST_LOG environment settting

        let mut paragraph = Paragraph::new();
        let mut boxed_paragraph = Box::new(Paragraph::new());
        let mut pinned_boxed_paragraph = Box::pin(Paragraph::new());
        paragraph.set_paragraph_signature(0x111);
        boxed_paragraph.set_paragraph_signature(0x222);
        pinned_boxed_paragraph.set_paragraph_signature(0x444);
        let (base_addr, next_free_idx) = paragraph.get_paragraph_signature();
        debug!(
            "main: paragraph address({:p}), size({}), signature(0x{:x}), 0x{:x})",
            &paragraph,
            size_of_val(&paragraph),
            base_addr,
            next_free_idx
        );
        let (base_addr, next_free_idx) = boxed_paragraph.get_paragraph_signature();
        let unboxed_paragraph = boxed_paragraph.deref();
        debug!(
            "main: boxed_paragraph address({:p}), size({}), signature(0x{:x}), 0x{:x})",
            unboxed_paragraph,
            size_of_val(unboxed_paragraph),
            base_addr,
            next_free_idx
        );
        let (base_addr, next_free_idx) = pinned_boxed_paragraph.get_paragraph_signature();
        let unpined_unboxed_paragraph = pinned_boxed_paragraph.deref();
        debug!(
            "main: pinned_boxed_paragraph address({:p}), size({}), signature(0x{:x}), 0x{:x})",
            unpined_unboxed_paragraph,
            size_of_val(unpined_unboxed_paragraph),
            base_addr,
            next_free_idx
        );
        assert_eq!(paragraph.get_paragraph_signature().1, 0x111);
        assert_eq!(boxed_paragraph.get_paragraph_signature().1, 0x222);
        assert_eq!(pinned_boxed_paragraph.get_paragraph_signature().1, 0x444);
    }

    #[test]
    #[ignore] // used for test driven development only
    fn tdd_room_left() {
        init_env_logger(); // honor RUST_LOG environment settting

        // Create a thread builder with necessary stack size
        let stack_size_in_bytes = max(2 * MEMORY_ARENA_SIZE_IN_BYTES, ONE_MEGABYTE);
        let builder = std::thread::Builder::new()
            .stack_size(stack_size_in_bytes)
            .name("tdd_room_left".into());

        let sizeof_memory_arena = size_of::<MemoryArena>();
        assert_eq!(MEMORY_ARENA_SIZE_IN_BYTES, sizeof_memory_arena, "make sure you changed the alignment if you changed the arena size; requires source edit");
        let sizeof_paragraph = size_of::<Paragraph>();
        assert_eq!(PARAGRAPH_SIZE_IN_BYTES, sizeof_paragraph);

        // Spawn a new thread using the builder
        let handle = builder.spawn(|| {
            init_env_logger();
            let mut binding = MemoryArena::new();
            let memory_arena = binding.deref_mut();

            // get how much room we have on the arena
            let bytes_room_left = memory_arena.room_left_in_bytes_mut();
            debug!("actual bytes_room_left {} bytes in a {} arena", bytes_room_left, MEMORY_ARENA_SIZE_IN_BYTES);
            debug!("attempting to allocate all {} bytes in a {} arena", bytes_room_left, MEMORY_ARENA_SIZE_IN_BYTES);
            if let Some(_ptr) = memory_arena.alloc_bytes_zeroed(bytes_room_left) {
                debug!("it is possible to allocate {} bytes in a {} arena, room_left_in_bytes: {}", bytes_room_left, MEMORY_ARENA_SIZE_IN_BYTES, memory_arena.room_left_in_bytes());
            } else {
                warn!("it is NOT possible to allocate {} bytes in a {} arena, room_left_in_bytes: {}", bytes_room_left, MEMORY_ARENA_SIZE_IN_BYTES, memory_arena.room_left_in_bytes());
            }

            let max_allocation_theoretically_possible = (COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA-2) * PARAGRAPH_SIZE_IN_BYTES + (PARAGRAPH_SIZE_IN_BYTES);
            debug!("theoretical bytes_room_left {} bytes in a {} arena", max_allocation_theoretically_possible, MEMORY_ARENA_SIZE_IN_BYTES);
            //assert_eq!(bytes_room_left, max_allocation_theoretically_possible, "expected room_left_in_bytes() to be maximum possible allocation");

            // Allocate the maximum block allowed on this arena
            for size in (bytes_room_left-20..MEMORY_ARENA_SIZE_IN_BYTES).rev() {
                let layout = Layout::from_size_align(size, 16).unwrap();
                debug!("attempting to allocate {} bytes in a {} arena", size, MEMORY_ARENA_SIZE_IN_BYTES);
                let mut binding = MemoryArena::new();
                let memory_arena = binding.deref_mut();
                if let Some(ptr) = memory_arena.alloc_zeroed(layout) {
                    debug!("it is possible to allocate {} bytes in a {} arena, room_left_in_bytes: {}", size, MEMORY_ARENA_SIZE_IN_BYTES, memory_arena.room_left_in_bytes());
                    assert!(memory_arena.contains(ptr));
                } else {
                    warn!("it is NOT possible to allocate {} bytes in a {} arena, room_left_in_bytes: {}", size, MEMORY_ARENA_SIZE_IN_BYTES, memory_arena.room_left_in_bytes());
                }
            }
        });

        // Wait for the spawned thread to finish
        if let Ok(join_handle) = handle {
            join_handle.join().unwrap();
        } else {
            error!("test_validate_sizes: Error creating the thread.");
        }
    }

    #[test]
    fn test_paragraph_mut_iterator() {
        init_env_logger(); // honor RUST_LOG environment settting

        // Create a thread builder with necessary stack size
        let stack_size_in_bytes = max(2 * MEMORY_ARENA_SIZE_IN_BYTES, ONE_MEGABYTE);
        let builder = std::thread::Builder::new()
            .stack_size(stack_size_in_bytes)
            .name("test_paragraph_mut_iterator".into());

        let sizeof_memory_arena = size_of::<MemoryArena>();
        assert_eq!(MEMORY_ARENA_SIZE_IN_BYTES, sizeof_memory_arena, "make sure you changed the alignment if you changed the arena size; requires source edit");
        let sizeof_paragraph = size_of::<Paragraph>();
        assert_eq!(PARAGRAPH_SIZE_IN_BYTES, sizeof_paragraph);

        // Spawn a new thread using the builder
        let handle = builder.spawn(|| {
            let mut binding = MemoryArena::new();
            let memory_arena = binding.deref_mut();

            // Allocate some Foo instances on the arena
            let layout =
                Layout::from_size_align(size_of::<Paragraph>(), size_of::<Paragraph>()).unwrap();
            let mut last_alloc_idx = 0;
            for idx in 0..2_000_000 {
                let num_bytes_requested = idx % PARAGRAPH_SIZE_IN_BYTES;
                if let Some(ptr) = memory_arena.alloc_bytes_zeroed(num_bytes_requested) {
                    debug!(
                        "ptr[{}] = {:p} returned by MemoryArena::alloc_bytes_zeroed()",
                        last_alloc_idx, ptr
                    );
                    fill_in_allocation(ptr.as_ptr(), size_of::<Paragraph>()); // overwrite every byte of allocation with pattern 0xDEADF0CA
                    last_alloc_idx = last_alloc_idx + 1;
                    assert!(validate_pattern(ptr.as_ptr(), size_of::<Paragraph>()));
                    // validate overwrite stuck
                }
                if let Some(ptr) = memory_arena.alloc_zeroed(layout) {
                    debug!(
                        "ptr[{}] = {:p} returned by MemoryArena::alloc_zeroed()",
                        last_alloc_idx, ptr
                    );
                    fill_in_allocation(ptr.as_ptr(), layout.size()); // overwrite every byte of allocation with pattern 0xDEADF0CA
                    last_alloc_idx = last_alloc_idx + 1;
                    assert!(validate_pattern(ptr.as_ptr(), layout.size())); // validate overwrite stuck
                }
                if memory_arena.room_left_in_bytes() < PARAGRAPH_SIZE_IN_BYTES {
                    break;
                }
            }
            info!(
                "able to make {} usable allocations of {} bytes each",
                last_alloc_idx,
                size_of::<Paragraph>()
            );

            // Create and use the mutable iterator
            let iter = memory_arena.iter_mut::<Paragraph>();
            let mut idx = 0;
            for foo in iter {
                debug!(
                    "foo._available= {} 0x{:016x}",
                    foo._available, foo._available
                );
                debug!(
                    "foo.paragraph_signature= 0x{:016x}",
                    foo.paragraph_signature
                );
                // assert!(validate_pattern(&foo as *const _ as *const u8, size_of::<Paragraph>())); // validate overwrite stuck
                // Do something with the &mut Foo reference (e.g., modify its fields)
                foo._available = idx;
                debug!("setting item[{}]._available: {}", idx, foo._available);
                idx = idx + 1;
            }
            assert_eq!(idx, last_alloc_idx); // verify expected number of items was iterated over
            info!(
                "able to iterate {} usable allocations of {} bytes each",
                idx,
                size_of::<Paragraph>()
            );
            let iter2 = memory_arena.iter_mut::<Paragraph>();
            let mut idx2 = 0;
            for foo in iter2 {
                // Do something with the &mut Foo reference (e.g., reset its fields)
                debug!("getting item[{}]._available: {}", idx2, foo._available);
                assert_eq!(idx2, foo._available); // verify it was modified on last iteration and kept it's changed value
                foo._available = 0; // reset it to original value
                idx2 = idx2 + 1;
            }
            assert_eq!(idx2, last_alloc_idx); // verify expected number of items was iterated over
            assert_eq!(idx2, idx); // verify two iterators gave same results over multiple iterations
            info!(
                "able to iterate {} usable allocations of {} bytes each",
                idx2,
                size_of::<Paragraph>()
            );
        });

        // Wait for the spawned thread to finish
        if let Ok(join_handle) = handle {
            join_handle.join().unwrap();
        } else {
            error!("test_validate_sizes: Error creating the thread.");
        }
    }
}

// honor environment variable RUST_LOG=[trace|debug|info|warn|error] setting - remember to run "cargo test -- --nocapture" to see the logs
fn init_env_logger() {
    if !(log_enabled!(Level::Error)
        | log_enabled!(Level::Warn)
        | log_enabled!(Level::Info)
        | log_enabled!(Level::Trace))
    {
        let _ =
            env_logger::Builder::from_env(env_logger::Env::default().default_filter_or("error"))
                .try_init();
    }

    #[cfg(debug_assertions)]
    info!("DEBUG Target");
    #[cfg(not(debug_assertions))]
    info!("RELEASE Target");

    info!(
        "ONE_MEGABYTE                           : 0x{:016x} ({})",
        ONE_MEGABYTE, ONE_MEGABYTE
    );
    info!(
        "MEMORY_ARENA_SIZE_IN_BYTES             : 0x{:016x} ({})",
        MEMORY_ARENA_SIZE_IN_BYTES, MEMORY_ARENA_SIZE_IN_BYTES
    );
    info!(
        "PARAGRAPH_SIZE_IN_BYTES                : 0x{:016x} ({})",
        PARAGRAPH_SIZE_IN_BYTES, PARAGRAPH_SIZE_IN_BYTES
    );
    info!(
        "MEMORY_ARENA_SIZE_IN_PARAGRAPHS        : 0x{:016x} ({})",
        MEMORY_ARENA_SIZE_IN_PARAGRAPHS, MEMORY_ARENA_SIZE_IN_PARAGRAPHS
    );
    info!(
        "COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA   : 0x{:016x} ({})",
        COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA, COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA
    );
    info!(
        "SIGNATURE_MASK                         : 0x{:016x}",
        SIGNATURE_MASK
    );
    info!(
        "PARAGRAPH_IDX_MASK                     : 0x{:016x}",
        PARAGRAPH_IDX_MASK
    );

    let alignof_memory_arena = align_of::<MemoryArena>();
    debug!(
        "align_of(MemoryArena)                  : 0x{:016x} ({})",
        alignof_memory_arena, alignof_memory_arena
    );

    let sizeof_memory_arena = size_of::<MemoryArena>();
    debug!(
        "size_of(MemoryArena)                   : 0x{:016x} ({})",
        sizeof_memory_arena, sizeof_memory_arena
    );

    let sizeof_allocation_arena =
        size_of::<UnsafeCell<[Paragraph; COUNT_PARAGRAPHS_IN_ALLOCATION_ARENA]>>();
    debug!(
        "size_of(MemoryArena.memory)            : 0x{:016x} ({}))",
        sizeof_allocation_arena, sizeof_allocation_arena
    );

    debug!("Memory_Arena member variables layout                :");
    debug!(
        "Offset,size of field 'memory'                       : {}, {}",
        offset_of!(MemoryArena, memory),
        sizeof_allocation_arena
    );
    debug!(
        "Offset,size of field '_available'                   : {}, {}",
        offset_of!(MemoryArena, _available),
        size_of::<u64>()
    );
    debug!(
        "Offset,size of field 'next_available_paragraph_idx' : {}, {}",
        offset_of!(MemoryArena, next_available_paragraph_idx),
        size_of::<AtomicCell::<usize>>()
    );
    debug!(
        "Offset,size of field 'future_next_arena_base_addr'  : {}, {}",
        offset_of!(MemoryArena, future_next_arena_base_addr),
        size_of::<AtomicCell::<usize>>()
    );
    debug!(
        "Offset,size of field 'signature'                    : {}, {}",
        offset_of!(MemoryArena, signature),
        size_of::<u64>()
    );
    let offset_to_end = offset_of!(MemoryArena, signature) + size_of::<u64>();
    debug!(
        "Offset past end of Memory_Arena                     : {}",
        offset_to_end
    );

    assert_eq!(
        sizeof_memory_arena, MEMORY_ARENA_SIZE_IN_BYTES,
        "make sure you changed the alignment if you changed the arena size; requires source edit"
    );
    assert!(sizeof_allocation_arena < MEMORY_ARENA_SIZE_IN_BYTES);

    #[cfg(not(debug_assertions))]
    assert_eq!(
        alignof_memory_arena,
        core::cmp::min(1_048_576, MEMORY_ARENA_SIZE_IN_BYTES)
    ); // RELEASE alignment is 1 Mib
    #[cfg(debug_assertions)]
    assert_eq!(
        alignof_memory_arena, MEMORY_ARENA_SIZE_IN_BYTES,
        "make sure you changed the alignment if you changed the arena size; requires source edit"
    );
}

fn main() {
    init_env_logger();

    let arena = MemoryArena::new();
    // Example usage:
    let layout = Layout::from_size_align(size_of::<Vec<[u32; 4]>>(), 16).unwrap();
    if let Some(ptr) = arena.alloc_zeroed(layout) {
        debug!("main: arena.alloc_zeroed() returned {:p}", ptr);
        assert!(arena.contains(ptr));
    } else {
        error!("allocation failed")
    }
}
