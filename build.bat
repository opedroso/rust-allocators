::
:: Some tests will fail unless the stack for the executable has been extended beyond 2 MB (In Windows, default it 1MB)
::
set _NT_SOURCE_PATH=%~dp0%src
setlocal
set TOOLCHAIN=
set OPTIONS=
set OPTIONS=--offline
set RUSTLOG=debug
:: uncomment next line if you want to build using nightly toolchain
::set TOOLCHAIN=+nightly
if /I "%~1" == "-c" shift & cargo %TOOLCHAIN% clean & cargo %TOOLCHAIN% clean --release %OPTIONS%
if /I "%~1" == "-r" shift & set TARGET=--release & set RUSTLOG=info
cargo %TOOLCHAIN% build %TARGET% %OPTIONS%
cargo %TOOLCHAIN% test %TARGET%  %OPTIONS% --no-run
:: this next line sets the stack size for all executables built to be 100 MB reserved & 1MB committed
for /r %%i in (rust*.exe) do "C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Tools\MSVC\14.39.33519\bin\Hostx64\x64\editbin.exe" /nologo /stack:104857600,1048576 %%i
if /I "%~1" == "-d" shift & SET RUST_LOG=%RUSTLOG%
cargo %TOOLCHAIN% test %TARGET% %OPTIONS% -- --test-threads=1 --nocapture
cargo %TOOLCHAIN% run  %TARGET% %OPTIONS% --bin rust-define-global-allocator -- --nocapture
cargo %TOOLCHAIN% run  %TARGET% %OPTIONS% --bin rust-paragraph-allocator -- --nocapture
endlocal
