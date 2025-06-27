@echo off
setlocal enabledelayedexpansion

REM Operate in the directory where this file is located
cd /d "%~dp0"

lake update -R
lake build
