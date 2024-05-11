#![cfg(windows)]
#![allow(dead_code)]
#![cfg(target_pointer_width = "64")]
use std::alloc::Layout;
use std::cell::UnsafeCell;
use std::ptr::NonNull;
use crossbeam::atomic::*;
use windows::Win32::Foundation::CloseHandle;
use std::ops::{BitOr, BitAnd};
use std::default::Default;
use std::pin::Pin;
use std::cmp::max;
use log::*;
use std::ops::*;

// global constants
const ONE_MEGABYTE: usize = 1_048_576; // number of bytes in 1 MiB (2^20)
const ARENA_SIZE: usize = 1 * ONE_MEGABYTE; // must be multiple of 1 MB, but no more than 16 MB total (limit is number of bits in paragraph.next_free_idx)
const PARAGRAPH_SIZE_IN_BYTES: usize = 16; // a paragraph is a 16 bytes chunk of memory; in our case which has an address that is on a 16 byte boundary
const COUNT_PARAGRAPH_IDX: usize = (ARENA_SIZE/PARAGRAPH_SIZE_IN_BYTES) - 2; // count of paragraphs available for allocation 0..
const MAX_PARAGRAPH_IDX: usize = COUNT_PARAGRAPH_IDX - 1; // all valid paragraph indices are less than this


/// MemoryArena manages allocations within its static memory array
/// It is meant to be written once by possibly multi-threaded user block producers
/// There is no way to deallocate a single user block: only whole pool can be deallocated (all user blocks dealocated at once)
/// 
/// Allocations:
/// Minimum allocation is 32 bytes (control area of 16 bytes + user block of up to 16 bytes) or ( 1 control paragraph + 1 user block paragraph)
/// Maximum allocation with 1 Mib pool (as implemented) is 1_048_544 bytes (or 65_534 paragraphs) or (1 control paragraph + 65_533 user block paragraphs)
/// Maximum user block allocation is then 1_048_528 bytes
/// If a request is made for a block that would lay beyond pool capacity, the user gets error *and* pool is closed for new allocations (last block is wasted)
/// It is possible that last block request failed due to multi-threading usage
/// In this case, pool will show that next free block have index larger than COUNT_PARAGRAPH_IDX
/// This also indicates that the pool is full
/// Iterating over the list of allocated blocks will stop at last successfully allocated block (paragraph next free block index will still be zero)
/// Failed last alloc returns error to requester and arena's next free block index gets reset to MAX_PARAGRAPH_IDX (which is larger than COUNT_PARAGRAPH_IDX)
/// 
/// Alignment:
/// Allocations are aligned to 16 byte boundary. Pool is aligned to 1 MiB boundary
/// Any allocation can find its pool by shifting its address by 20 bits (2^20 = 1 MiB)
/// Control paragraph has a signature that contains (pool base address, index where next allocation begins)
/// Last allocated block in pool will have (pool base addres, zero) in its control block
/// Number of bits dedicated to index to next allocation has 20 bits but for 1 MiB implementation only 16 bits are used
/// As there are no pointers in control data, only indices, pool can be memoy mapped to a different locations and still be valid
/// Base address would have original mapping but that can be used to indicate that user block has not yet been processed after this new mapping
/// 
/// Stack requirement:
/// Stack size for thread creating the MemoryArena has to be larger than 1 Mib + your functions requirement
/// Suggestion is to create MemoryArenas from specific thread started with enough stack space (see tests for example)
/// 
#[repr(align(1_048_576))] // ONE_MEGABYTE boundary
#[derive(Debug)]
struct MemoryArena {
    // 1 MB = Paragraph[65_536]
    // memory arena for allocation begins here
    memory: UnsafeCell<[Paragraph; COUNT_PARAGRAPH_IDX]>, // indices 0..65_533 // memory must be first memory address within MemoryArena
    // paragraph[65534] // = 1 + COUNT_PARAGRAPH_IDX
    _available: u64, // contents not yet used, but must be first variable past memory (or update function contains)
    next_available_paragraph_idx: AtomicCell::<usize>, // value must be less than MAX_PARAGRAPH_IDX; index into memory array that is free for next allocation
    // paragraph[65535] // = 2 + COUNT_PARAGRAPH_IDX - last 16 bytes in 1 MB block
    future_next_arena_base_addr: AtomicCell::<u64>, // when this arena is out of memory and a new allocation is requested, a new arena will fullfil it
    signature: u64, // ((the base address of the arena)>>20)
}

#[repr(align(16))] // PARAGRAPH_SIZE_IN_BYTES
#[derive(Copy, Clone)]
pub struct Paragraph {
    paragraph_signature: u64, // ((the base address of the arena)>>20)<<20) & next_[free/allocated]_paragraph_idx
    _available: u64, // not yet used
}

// represents a 16 byte chunk of memory
// there will be one before every arena allocation to indicate where the allocation ends and next one begins
impl Paragraph {
    pub fn new() -> Self {
        assert_eq!(PARAGRAPH_SIZE_IN_BYTES, std::mem::size_of::<Paragraph>()); // must forever be valid since this is a paragraph chunk allocator
        Default::default()
    }

    pub fn set_paragraph_signature(&mut self, next_free_paragraph_idx: usize) {
        let mb_aligned_base_addr = (self as *const _ as u64 >>20) <<20; // reset lower 20 bits
        self.paragraph_signature = mb_aligned_base_addr.bitand(!(0xFFFFF)).bitor(next_free_paragraph_idx as u64);
        debug!("set paragraph.signature: 0x{:x}", self.paragraph_signature);
    }

    // returns tuple (memory_arena_base_address, index_to_next_free_paragraph) when paragraph is first allocated
    // after the next free paragraph is allocated, it becomes a paragraph_index_of_next_allocated_paragraph
    pub fn get_paragraph_signature(&self) -> (u64, u16) {
        let (a, b) = (self.paragraph_signature & 0xFFFFFFFFFFF00000, (self.paragraph_signature & 0x000000000000FFFF) as u16);
        debug!("get paragraph.signature: (memory_arena_base_address: 0x{:x}, index_to_next_free_paragraph: 0x{:x})", a, b);
        (a, b)
    }
}

impl Default for Paragraph {
    fn default() -> Self {
        // Initialize the fields with appropriate default values
        Paragraph {
            paragraph_signature: 0,
            _available: 0,
        }
    }
}

/*
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
*/

impl MemoryArena {
    fn new() -> Pin<Box<MemoryArena>> {
        debug!("new: being called from : ");
        let mut pinned_boxed_arena = Box::pin(MemoryArena {
            memory: UnsafeCell::new([Paragraph::default(); COUNT_PARAGRAPH_IDX]),
            _available: 0,
            next_available_paragraph_idx: AtomicCell::<usize>::new(0),
            future_next_arena_base_addr: AtomicCell::<u64>::new(0),
            signature: 0,
        });
        let arena = pinned_boxed_arena.deref_mut();
        arena.set_signature();
        arena.set_signature_for_paragraph_at_idx(1, 0);
        debug!("new: Pin<Box<MemoryArena>>: {:p}, size: {}, signature: 0x{:016x}", arena, std::mem::size_of_val(arena), arena.get_signature());
        pinned_boxed_arena
    }

    fn set_signature_for_paragraph_at_idx(&self, next_free_paragraph_idx: usize, paragraph_idx: usize) {
        unsafe {
            let mut_arena_memory = self.memory.get();
            let paragraph = &mut (*mut_arena_memory)[paragraph_idx] as *mut Paragraph;
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
        let signature = ((self as *const _ as u64 ) >> 20) << 20;
        self.signature = signature; // equivalent to (&arena as *const _) & 0xFFFFFFFFFFF00000
        debug!("set_signature: arena address: {:p}, size: {}, signature: 0x{:016x}", self, std::mem::size_of_val(self), self.signature);
    }
    fn get_signature(&self) -> u64 {
        self.signature
    }

    fn alloc_bytes(&self, num_bytes: usize) -> Option<NonNull<u8>> {
        let layout = Layout::from_size_align(num_bytes, std::mem::size_of::<Paragraph>()).unwrap();
        self.alloc_aligned_bytes(layout)
    }
    fn alloc_aligned_bytes(&self, layout: Layout) -> Option<NonNull<u8>> {
        unsafe {
            assert!(layout.align() <= std::mem::size_of::<Paragraph>(), "alignment > 16 not yet implemented");
            let num_paragraphs = 1 + max(layout.size() / std::mem::size_of::<Paragraph>(), 1); // header + user_block
            let index = self.next_available_paragraph_idx.fetch_add(num_paragraphs);
            if index + num_paragraphs <= MAX_PARAGRAPH_IDX {
                let mut_arena_memory = self.memory.get();
                NonNull::new(&mut (*mut_arena_memory)[index] as *mut _ as *mut u8)
            } else {
                let mut new_value = index;
                while let Err(index) = self.next_available_paragraph_idx.compare_exchange(new_value, MAX_PARAGRAPH_IDX) {
                    new_value = index;
                }
                return None;
            }
        }
    }
}

fn main() {

    let arena = MemoryArena::new();
    // Example usage:
    let layout = Layout::from_size_align(std::mem::size_of::<Vec<[u32; 4]>>(), 16).unwrap();
    if let Some(ptr) = arena.alloc_aligned_bytes(layout) {
        debug!("main: arena.alloc_aligned_bytes() returned {:p}", ptr);
        assert!(arena.contains(ptr));
    } else {
        debug!("allocation failed")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::thread;

    // cargo test --bin rust-paragraph-allocator test_validate_sizes -- --test-threads=1 --nocapture
    #[test]
    fn test_validate_sizes() {
        // Create a thread builder with a stack size of 20 MiB
        let builder = thread::Builder::new().stack_size(10 * 1024 * 1024).name("test_validate_sizes".into());

        // Spawn a new thread using the builder
        let handle = builder.spawn(|| {
            // This closure runs in the new thread with the large stack
            assert_eq!(ONE_MEGABYTE, std::mem::size_of::<MemoryArena>());
            assert_eq!(PARAGRAPH_SIZE_IN_BYTES, std::mem::size_of::<Paragraph>());
            let mut arena = MemoryArena::new();
            let mut_arena = arena.deref_mut();
            assert_eq!(ONE_MEGABYTE, std::mem::size_of_val(mut_arena));
            print_stack_extents_win();

            let (header_paragraph, header_signature) = unsafe {
                let mut_memory = mut_arena.memory.get();
                (&mut (*mut_memory)[0] as *mut Paragraph, (*mut_memory)[0].paragraph_signature)
            };

            debug!("test_validate_sizes: header_paragraph          : 0x{:016x}", header_paragraph as *const _ as u64);
            debug!("test_validate_sizes: header_paragraph.signature: 0x{:016x}", header_signature);
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
        let mut arena = MemoryArena::new();
        let allocator = arena.deref_mut();
        assert_eq!(allocator.get_signature(), allocator as *const _ as u64);
    }

    #[test]
    fn test_allocation() {
        let mut arena = MemoryArena::new();
        let allocator = arena.deref_mut();
        let layout = Layout::from_size_align(32, 16).unwrap();
        if let Some(ptr) = allocator.alloc_aligned_bytes(layout) {
            assert!(allocator.contains(ptr));
        }
    }

    #[test]
    fn test_from_raw_parts_mut() { // example from jgengset
        let aligned_address = 0xB8000;
        let _vga = unsafe {
            std::slice::from_raw_parts_mut(aligned_address as *mut u8, 80 * 24)
        };
    }

    #[test]
    fn test_allocate_all_paragraphs() {
        // Create a thread builder with a stack size of 4 MiB
        let builder = thread::Builder::new().stack_size(20 * 1024 * 1024).name("test_allocate_all_paragraphs".into());

        // Spawn a new thread using the builder
        let handle = builder.spawn(|| {
            // This closure runs in the new thread
            assert_eq!(ONE_MEGABYTE, std::mem::size_of::<MemoryArena>());
            assert_eq!(PARAGRAPH_SIZE_IN_BYTES, std::mem::size_of::<Paragraph>());
            let arena = MemoryArena::new();
            let deref_arena = arena.deref();
            assert_eq!(ONE_MEGABYTE, std::mem::size_of_val(deref_arena));
            print_stack_extents_win();

            let num_bytes = std::mem::size_of::<u128>(); 
            let mut count_allocs = 0;
            while let Some(ptr) = deref_arena.alloc_bytes(num_bytes) {
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
    //[ignore] // used for test driver development only
    fn tdd_paragraph() {
        let mut paragraph = Paragraph::new();
        let mut boxed_paragraph = Box::new(Paragraph::new());
        let mut pinned_boxed_paragraph = Box::pin(Paragraph::new());
        paragraph.set_paragraph_signature(0x111);
        boxed_paragraph.set_paragraph_signature(0x222);
        pinned_boxed_paragraph.set_paragraph_signature(0x444);
        print_stack_extents_win();
        let (base_addr, next_free_idx) = paragraph.get_paragraph_signature();
        debug!("main: paragraph address({:p}), size({}), signature(0x{:x}), 0x{:x})", &paragraph, std::mem::size_of_val(&paragraph), base_addr, next_free_idx);
        let (base_addr, next_free_idx) = boxed_paragraph.get_paragraph_signature();
        let unboxed_paragraph = boxed_paragraph.deref();
        debug!("main: boxed_paragraph address({:p}), size({}), signature(0x{:x}), 0x{:x})", unboxed_paragraph, std::mem::size_of_val(unboxed_paragraph), base_addr, next_free_idx);
        let (base_addr, next_free_idx) = pinned_boxed_paragraph.get_paragraph_signature();
        let unpined_unboxed_paragraph = pinned_boxed_paragraph.deref();
        debug!("main: pinned_boxed_paragraph address({:p}), size({}), signature(0x{:x}), 0x{:x})", unpined_unboxed_paragraph, std::mem::size_of_val(unpined_unboxed_paragraph), base_addr, next_free_idx);
        assert_eq!(paragraph.get_paragraph_signature().1, 0x111);
        assert_eq!(boxed_paragraph.get_paragraph_signature().1, 0x222);
        assert_eq!(pinned_boxed_paragraph.get_paragraph_signature().1, 0x444);
    }
}

fn print_stack_extents_win() {
    unsafe {
        // Get the current thread handle
        let thread_handle = windows::Win32::System::Threading::GetCurrentThread();

        // Initialize variables to store stack limits
        let mut stack_base: usize = 0;
        let mut stack_limit: usize = 0;

        // Retrieve the stack limits
        windows::Win32::System::Threading::GetCurrentThreadStackLimits(&mut stack_base, &mut stack_limit);
        let _ = CloseHandle(thread_handle);

        // Print the stack addresses
        info!("\nprint_stack_extents_win: Stack base address : 0x{:016x}", stack_base);
        info!("print_stack_extents_win: Stack limit address: 0x{:016x}", stack_limit);
        let stack_extent = stack_limit - stack_base;
        info!("print_stack_extents_win: Stack extent       : {}  (0x{:x})", stack_extent, stack_extent);
    }
}
