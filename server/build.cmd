@echo off
setlocal enabledelayedexpansion

REM Change to the Projects directory relative to the script location
cd /d "%~dp0\..\Projects"

REM Loop through all directories in Projects
for /d %%F in (*) do (
    set "folder=%%F"
    set "build_script=%%F\build.cmd"

    if exist "!build_script!" (
        echo Start building !folder!
        REM eventcreate /t INFORMATION /id 100 /l APPLICATION /so lean4web /D "Start building !folder!"

        REM Track time
        set "start=%time%"
        
        call "!build_script!"

        REM Get elapsed time
        set "end=%time%"
        call :getDuration "!start!" "!end!" duration

        echo Finished !folder! in !duration!
        REM eventcreate /t INFORMATION /id 101 /l APPLICATION /so lean4web /D "Finished !folder! in !duration!"
    ) else (
        echo Skipping !folder!: build.cmd missing
    )
)

exit /b

:getDuration
setlocal
set "start=%~1"
set "end=%~2"

REM Parse start time
for /f "tokens=1-4 delims=:.," %%a in ("%start%") do (
    set /a "startSec = ((1%%a%%100) * 3600) + (%%b * 60) + %%c"
)
REM Parse end time
for /f "tokens=1-4 delims=:.," %%a in ("%end%") do (
    set /a "endSec = ((1%%a%%100) * 3600) + (%%b * 60) + %%c"
)

set /a elapsed = endSec - startSec
if %elapsed% lss 0 set /a elapsed += 86400

set /a minutes=elapsed / 60
set /a seconds=elapsed %% 60
endlocal & set "%~3=%minutes%:%seconds%"
exit /b
