$ErrorActionPreference = 'Stop'
$env:PYTHONUTF8 = '1'
$env:PYTHONIOENCODING = 'utf-8'
if ([Environment]::OSVersion.Platform -eq [PlatformID]::Win32NT) {
    # Preserve explicit resource settings supplied by the caller.
    if ([string]::IsNullOrEmpty($env:LEAN_NUM_THREADS)) { $env:LEAN_NUM_THREADS = '2' }
    if ([string]::IsNullOrEmpty($env:LEAN_MAIN_USE_THREAD)) { $env:LEAN_MAIN_USE_THREAD = '1' }
    if ([string]::IsNullOrEmpty($env:LEAN_STACK_SIZE_KB)) { $env:LEAN_STACK_SIZE_KB = '65536' }
}
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
