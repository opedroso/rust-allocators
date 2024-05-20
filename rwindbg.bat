:: rwindbg.bat
::
:: executes WinDBG with settings to help debug Rust projects
::

:: this script assumes we are executed from base of project (where target directory gets created by cargo build)
if NOT exist ".\target" @echo "Error: No '.\target' directory! Expected to be at rust project directory!"& goto :eof
if NOT exist ".\src" @echo "Error: No '.\src' directory! Expected to be at rust project directory!"& goto :eof

:: this will download source and symbols for your rust toolchain
rustup component add rust-src
:: rustup +nightly component add rust-src

:: all environment variable changes beyond here only valid during script execution
@setlocal


set PDB_CACHE=c:\Symbols
if NOT exist "%PDB_CACHE%" mkdir "%PDB_CACHE%\ms"

:: Microsoft and other public symbol providers are cached to "r:\Symbols\ms"
set _NT_SYMBOL_PATH=cache*%PDB_CACHE%\ms;srv*https://msdl.microsoft.com/download/symbols^
;srv*target\debug^
;srv*target\release^
;srv*target\debug\deps^
;srv*target\release\deps^
;srv*target\debug\build^
;srv*target\release\build^
;srv*%USERPROFILE%\.rustup\toolchains\stable-x86_64-pc-windows-msvc\bin^
;srv*%USERPROFILE%\.rustup\toolchains\stable-x86_64-pc-windows-msvc\lib\rustlib\x86_64-pc-windows-msvc\lib^
;srv*%USERPROFILE%\.rustup\toolchains\nightly-x86_64-pc-windows-msvc\bin^
;srv*%USERPROFILE%\.rustup\toolchains\nightly-x86_64-pc-windows-msvc\lib\rustlib\x86_64-pc-windows-msvc\lib


set PROJECT_SRC_DIR=.\src
set _NT_SOURCE_PATH=%PROJECT_SRC_DIR%^
;%USERPROFILE%\.rustup\toolchains\stable-x86_64-pc-windows-msvc\lib\rustlib\src\rust^
;%USERPROFILE%\.rustup\toolchains\nightly-x86_64-pc-windows-msvc\lib\rustlib\src\rust


:: show our environment variables related to windbg symbols and source paths and rust
set _NT
set RU

:: create a initialization script for windbg (necessary when some commands require double-quote usage)
set WINDBG_INIT_SCRIPT=%TEMP%\rwindbg.windbg
if exist "%WINDBG_INIT_SCRIPT%" del /q/f "%WINDBG_INIT_SCRIPT%"
@echo .reload /f> %WINDBG_INIT_SCRIPT%
@echo sxe *>> %WINDBG_INIT_SCRIPT%
@echo .load uext>> %WINDBG_INIT_SCRIPT%
@echo !uext.help>> %WINDBG_INIT_SCRIPT%
@echo lm>> %WINDBG_INIT_SCRIPT%
@echo sxe -c ^"k;.echo First Chance Exception at this stack above^" -c2 ^"k;.echo Second Chance Exception at this stack above^" e06d7363>> %WINDBG_INIT_SCRIPT%
@echo g>> %WINDBG_INIT_SCRIPT%
@echo windbg -c "$><%WINDBG_INIT_SCRIPT%"

:: run windbg with the argument given 
windbg -o -c "$><%WINDBG_INIT_SCRIPT%" %*

@endlocal