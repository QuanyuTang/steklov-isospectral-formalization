$ErrorActionPreference = 'Stop'
Set-Location (Split-Path $PSScriptRoot -Parent)
foreach ($arguments in @(@('exe', 'cache', 'get'), @('build'))) {
    & lake @arguments
    if ($LASTEXITCODE -ne 0) { throw "Lean verification failed: lake $arguments" }
}
& python scripts/audit.py
if ($LASTEXITCODE -ne 0) { throw 'Proof/type or axiom audit failed' }
& python scripts/check-release.py
if ($LASTEXITCODE -ne 0) { throw 'Release checks failed' }
