setlocal
:: uncomment next line if you want to build using nightly toolchain
::set TOOLCHAIN=+nightly
cargo %TOOLCHAIN% clean
cargo %TOOLCHAIN% build
cargo %TOOLCHAIN% test --no-run
:: this next line sets the stack size for all executables built to be 10 MB
for /r %%i in (rust*.exe) do "C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Tools\MSVC\14.39.33519\bin\Hostx64\x64\editbin.exe" /nologo /stack:10485760,10485760 %%i
cargo %TOOLCHAIN% run --bin rust-define-global-allocator
cargo %TOOLCHAIN% run --bin rust-paragraph-allocator
cargo %TOOLCHAIN% test -- --test-threads=1 --nocapture
endlocal
