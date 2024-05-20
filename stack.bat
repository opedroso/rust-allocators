pushd %~dp0
:: this next line sets the stack size for all executables built to be 100 MB reserved & 1MB committed
for /r %%i in (rust*.exe) do "C:\Program Files\Microsoft Visual Studio\2022\Community\VC\Tools\MSVC\14.39.33519\bin\Hostx64\x64\editbin.exe" /nologo /stack:104857600,1048576 %%i
popd
exit /b 0