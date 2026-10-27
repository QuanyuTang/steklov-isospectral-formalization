# Reproduce this release

Recorded commit `6932e18512a776e4edae15bc076f4224ec85e4ad` passed a fresh Lean 4.35.0-rc2 build of all 176 modules, the complete 590-target proof/type and transitive axiom audit, official metadata/source checks, and sandboxed Comparator replay with the bundled Lean and NanoDa kernels. con-ron also accepted.
The historical logs under `verification/recorded/` certify Lean 4.28 only.
See [current status](../PALOMAR_STATUS.md) and [exact evidence](lean435-build-audit-evidence.json).

## Environment

| Component | Pin |
| --- | --- |
| Lean | `leanprover/lean4:v4.35.0-rc2` |
| Mathlib | `065356127b1dc0016f66b7283ce0ce2c4055aa55` |
| Dependency closure | Committed `lake-manifest.json` |

Use elan, Git, and Lean's supported native toolchain. Allow several GiB for dependencies and build artifacts; they are intentionally omitted from the release. The validation scripts use Python 3.10+ and `jsonschema==4.25.1` for the vendored metadata schema.

```sh
python3 -m pip install jsonschema==4.25.1
python3 scripts/validate-metadata.py
lake exe cache get
lake build
python3 scripts/audit.py
python3 scripts/check-release.py
```

The `lean.yml` workflow starts from a fresh checkout, restores only the
canonical Mathlib dependency cache, asserts that compiled `RequestProject`
output is absent, builds every advertised module and both submission entries,
and runs the enforced audit. The final Git diff guard must pass. The separate
Comparator workflow can reuse source-hashed project artifacts to save time.

For Linux sandboxed comparison, install bubblewrap and use the pinned toolchain:

```sh
bash scripts/verify-required-comparator.sh
bash scripts/verify-comparator.sh
```

The first command uses the bundled Comparator with NanoDa and its built-in
Lean checker. The second is the unchanged upstream all-kernel template,
including con-ron. CI saves mandatory evidence before the additional attempt.
Its local ten-minute advisory budget can produce an explicitly inconclusive
timeout; such a timeout is not con-ron acceptance or a prediction of Palomar's
own result. A checker rejection or other error still fails verification.

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

The baseline public layout was additionally built and audited in an independent directory with the verified caches: `verification/package-verification.json` records both exit codes as zero, 8206 build jobs, and 590 unique axiom-inventory targets. Complete output is in `verification/package-build.log` and `verification/package-audit.log`. Source and dependency pins of that build were hash-matched to the baseline files. These logs do not certify the migration candidate or claim a Comparator or independent-kernel check.

`SOURCE_SHA256SUMS` binds the 176 library modules, four preserved original audit inventories, the standalone audit template, the two submission modules, project pins, and original paper files. `scripts/check-release.py` checks these hashes, module headers, line limits, project pins, comparison targets, the statement-only placeholder, and source/archive correspondence. Its checks are supplementary to Lean and do not prove mathematical fidelity.

## Updating Lean

Changing `lean-toolchain` or Mathlib invalidates the recorded environment-specific build evidence. Port the source, pin canonical Mathlib for the same Lean release, regenerate the manifest, rebuild, rerun the axiom audit, and run the required Palomar Comparator and independent-kernel checks. Preserve this verified release as a tag or immutable commit before a port.
