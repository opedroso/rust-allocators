@echo on
::
:: Some tests will fail unless the stack for the executable has been extended beyond 2 MB (In Windows, default it 1MB)
::
pushd %~dp0
set _NT_SOURCE_PATH=%~dp0%src
setlocal
set TOOLCHAIN=
set OPTIONS=
set OPTIONS=--offline
set DEFRUSTLOG=debug
:: uncomment next line if you want to build using nightly toolchain
::set TOOLCHAIN=+nightly
if /I "%~1" == "-c" shift & cargo %TOOLCHAIN% clean & cargo %TOOLCHAIN% clean --release %OPTIONS%
if /I "%~1" == "-r" shift & set TARGET=--release & set DEFRUSTLOG=info
cargo %TOOLCHAIN% build %TARGET% %OPTIONS%
cargo %TOOLCHAIN% test %TARGET%  %OPTIONS% --no-run
:: this next line sets the stack size for all executables built to be 100 MB reserved & 1MB committed
call stack.bat
if /I "%~1" == "-d" shift & SET RUST_LOG=%DEFRUSTLOG%
set RU
cargo %TOOLCHAIN% test %TARGET% %OPTIONS% -- --test-threads=1 --nocapture
cargo %TOOLCHAIN% run  %TARGET% %OPTIONS% --bin rust-define-global-allocator -- --nocapture
cargo %TOOLCHAIN% run  %TARGET% %OPTIONS% --bin rust-paragraph-allocator -- --nocapture
endlocal
popd
