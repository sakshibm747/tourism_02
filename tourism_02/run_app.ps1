Set-StrictMode -Version Latest
$ErrorActionPreference = 'Stop'

$ProjectRoot = Split-Path -Parent $MyInvocation.MyCommand.Path
Set-Location $ProjectRoot

$VenvPython = Join-Path $ProjectRoot ".venv\Scripts\python.exe"
$Requirements = Join-Path $ProjectRoot "requirements.txt"
$HashFile = Join-Path $ProjectRoot ".requirements.sha256"

function Ensure-Venv {
    if (-not (Test-Path $VenvPython)) {
        Write-Host "[setup] Creating project virtual environment..."
        try {
            py -3 -m venv .venv
        }
        catch {
            python -m venv .venv
        }
    }
}

function Get-FileHashValue([string]$Path) {
    return (Get-FileHash -Path $Path -Algorithm SHA256).Hash
}

function Ensure-Pip {
    Write-Host "[setup] Verifying pip in project virtual environment..."
    & $VenvPython -m ensurepip --upgrade *> $null
}

Ensure-Venv
Ensure-Pip

$ReqHash = Get-FileHashValue $Requirements
$SavedHash = ""
if (Test-Path $HashFile) {
    $SavedHash = (Get-Content $HashFile -Raw).Trim()
}

if ($ReqHash -ne $SavedHash) {
    Write-Host "[setup] Installing/updating dependencies from requirements.txt..."
    & $VenvPython -m pip install --disable-pip-version-check -r $Requirements
    Set-Content -Path $HashFile -Value $ReqHash -NoNewline
} else {
    Write-Host "[setup] Dependencies already up to date."
}

Write-Host "[run] Starting Flask app..."
& $VenvPython app.py
