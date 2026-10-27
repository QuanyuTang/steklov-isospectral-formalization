$ErrorActionPreference = 'Stop'
Set-Location (Split-Path $PSScriptRoot -Parent)
& python scripts/validate-metadata.py
if ($LASTEXITCODE -ne 0) { throw 'Metadata validation failed; install jsonschema==4.25.1 if needed' }
& python scripts/check-release.py
if ($LASTEXITCODE -ne 0) { throw 'Source release checks failed' }
foreach ($arguments in @(@('exe', 'cache', 'get'), @('build'))) {
    & lake @arguments
    if ($LASTEXITCODE -ne 0) { throw "Lean verification failed: lake $arguments" }
}
& python scripts/audit.py
if ($LASTEXITCODE -ne 0) { throw 'Proof/type or axiom audit failed' }
& python scripts/check-release.py
if ($LASTEXITCODE -ne 0) { throw 'Release checks failed' }
