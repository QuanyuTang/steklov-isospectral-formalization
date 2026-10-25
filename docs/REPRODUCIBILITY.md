# Reproduce this release

## Environment

| Component | Pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.28.0` |
| Mathlib | `8f9d9cff6bd728b17a24e163c9402775d9e6a365` |
| Dependency closure | Committed `lake-manifest.json` |

Use elan, Git, and Lean's supported native toolchain. Allow several GiB for dependencies and build artifacts; they are intentionally omitted from the release. Python 3.11+ is used only by the release checker, which has no third-party package dependency.

```sh
lake exe cache get
lake build
python3 scripts/audit.py
python3 scripts/check-release.py
```

On Windows, use `python` in place of `python3` if appropriate. PowerShell convenience entry:

```powershell
./scripts/verify.ps1
```

For POSIX shells:

```sh
sh scripts/verify.sh
```

After the build, `scripts/audit.py` assembles the four original axiom inventories, the final proof/type audit, and the public-entry axiom check into a generated non-module file under `.lake/audit/`. This is necessary because Lean 4.28 forbids `#print axioms` inside a `module` file. The audit templates preserve the original commands and are not imported by the proof library. The single `sorry` warning in `Challenge.lean` is expected; there must be none in the proof library or Solution.

## What is evidence, and what must be rerun

`verification/recorded/local-build.log` and `local-audit.log` are original successful Lean 4.28 logs from the completed proof. They do not certify another toolchain, another source revision, or Palomar acceptance. `verification/release-check.json` records structural and hash checks of this package; local compilation of the new submission surface is recorded separately. Run the commands above for a fresh verification.

The current public layout was additionally built and audited in an independent directory with the verified caches: `verification/package-verification.json` records both exit codes as zero, 8206 build jobs, and 590 unique axiom-inventory targets. Complete output is in `verification/package-build.log` and `verification/package-audit.log`. Source and dependency pins of that build were hash-matched to the delivered files. This does not claim a Comparator or independent-kernel check.

`SOURCE_SHA256SUMS` binds the 176 library modules, four preserved original audit inventories, the standalone audit template, the two submission modules, project pins, and original paper files. `scripts/check-release.py` checks these hashes, module headers, line limits, project pins, comparison targets, the statement-only placeholder, and source/archive correspondence. Its checks are supplementary to Lean and do not prove mathematical fidelity.

## Updating Lean

Changing `lean-toolchain` or Mathlib invalidates the recorded environment-specific build evidence. Port the source, pin canonical Mathlib for the same Lean release, regenerate the manifest, rebuild, rerun the axiom audit, and run the required Palomar Comparator and independent-kernel checks. Preserve this verified release as a tag or immutable commit before a port.
