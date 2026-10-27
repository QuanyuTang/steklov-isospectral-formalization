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

The project explicitly passes `-j2` to each compiler and to the audit probe;
`LEAN_NUM_THREADS` alone controls Lake's runtime, not the Lean CLI's default
compiler thread count. On Windows, `verify.ps1` also defaults to a controlled
main thread, a 64 MiB thread stack and UTF-8 Python output, while preserving
explicit caller-supplied Lean resource settings. These execution settings
change neither the statements nor the kernel's trust rules. They address the
stack-overflow failures observed in an initial local Windows build; both
previously failing modules passed standalone checks with the explicit settings.

For POSIX shells:

```sh
sh scripts/verify.sh
```

After the build, `scripts/audit.py` assembles the four original axiom inventories, the final proof/type audit, and the public-entry axiom check into a generated non-module file under `.lake/audit/`. This is necessary because Lean 4.28 forbids `#print axioms` inside a `module` file. The audit templates preserve the original commands and are not imported by the proof library. The single `sorry` warning in `Challenge.lean` is expected; there must be none in the proof library or Solution.

## What is evidence, and what must be rerun

`verification/recorded/local-build.log` and `local-audit.log` are original successful Lean 4.28 logs from the completed proof. They do not certify another toolchain, another source revision, or Palomar acceptance. `verification/release-check.json` records structural and hash checks of this package; local compilation of the new submission surface is recorded separately. Run the commands above for a fresh verification.

The baseline public layout was additionally built and audited in an independent directory with the verified caches: `verification/package-verification.json` records both exit codes as zero, 8206 build jobs, and 590 unique axiom-inventory targets. Complete output is in `verification/package-build.log` and `verification/package-audit.log`. Source and dependency pins of that build were hash-matched to the baseline files. These logs do not certify the migration candidate or claim a Comparator or independent-kernel check.

`SOURCE_SHA256SUMS` binds the 176 library modules, four preserved original audit inventories, the standalone audit template, the two submission modules, project pins, and original paper files. `scripts/check-release.py` checks these hashes, module headers, line limits, project pins, comparison targets, the statement-only placeholder, and source/archive correspondence. Its checks are supplementary to Lean and do not prove mathematical fidelity.

After an intentional edit, run `python3 scripts/refresh-release.py`. It updates `SOURCE_SHA256SUMS`, regenerates `verification/release-check.json`, and refreshes `publication-manifest.json` in that order. This records the new bytes; it does not certify a build or mathematical correctness. Normal release checks also validate the publication manifest. Commit the result and obtain successful full build/audit, bundled Comparator and official full mechanical preflight runs for the exact submitted SHA.

The [2026-10-27 Windows record](../verification/local-windows-20261027/report.json)
includes the full successful build log, fresh 590-target audit, and genuine
Comparator and con-ron output. The selected 34 exporter targets were read from
the pinned Comparator's own target specification. Fresh Challenge/Solution
exports were generated by the bundled exporter, bound to all compiled parts
and source inputs, and supplied through Comparator's `--*-from-export` options;
those flags alone do not establish source correspondence. NanoDa and Lean
accepted, and con-ron accepted the same saved Solution export. A local copy of
Windows `where.exe` under the name `which.exe`, with unique executable resolution
checked on a restricted PATH, supplied the Unix-style location query expected by
the unmodified Comparator. These local checks used no Linux sandbox and do not
replace the standard isolated scripts above. Large compiled artifacts, the
compatibility executable and the full exports are not shipped in the repository.

The historical report's complete 190-entry `proof_input_sha256` map is retained
unchanged. The current library, Solution, pins/configuration and audit inputs
remain byte-identical (189 entries). The previous Challenge is archived at
`verification/challenge-canonical-20261027/Challenge.previous.lean.in` and must
match its historical hash. The release checker reconstructs the new Challenge
with exactly one hardcoded scoped-option insertion before `Label`; all other
bytes must match. The accompanying migration record binds the new source hash
and makes no proof-acceptance claim. Any additional proof-input edit still fails
this guard after ordinary checksum refresh. The old Windows run does not cover
the modified Challenge.

## Canonical Challenge and official mechanical preflight

The [actual Palomar submission](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/40533988514) of
`e5e5383838201fb674f87042dcb8c86ccc761fb2` failed while deriving `Fintype` for
`Label`. The earlier full build/audit and bundled Comparator workflows passed
using candidate Lake options. Palomar deliberately compiles Challenge directly
with the pinned compiler and frozen canonical dependencies, without the candidate
Lake configuration, candidate module outputs or command-line `-D` options.
Thus those two workflows did not test the canonical compilation stage.

The scoped `backward.isDefEq.respectTransparency=false` insertion applies only
to the unchanged `Label` declaration and its deriving clause. To exercise the
actual mechanical path, run the **Palomar mechanical preflight** workflow
(`palomar-mechanical.yml`) and inspect the result for the exact commit. It calls
`PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml` at
`c02bbeaed888df45c4e28c4e99dba540ad21552a`, with matching `pipeline_commit`,
**`mode: full`** and `execution_profile: palomar-standard-v1`. The upstream
`preflight` mode alone does not compile Challenge and would miss this error.

Full mode includes canonical Challenge compilation, protected declaration
exports/comparison, dependency checks, kernel controls and the bundled-kernel
pipeline. This own-repository workflow does not create a registry submission,
run editorial review or register the result. Keep the full-library build/audit
workflow as well: the mechanical pipeline's Solution closure need not cover
all advertised library modules. The older bundled Comparator remains an
additional check rather than a substitute for the official mechanical path.

## Updating Lean

Changing `lean-toolchain` or Mathlib invalidates the recorded environment-specific build evidence. Port the source, pin canonical Mathlib for the same Lean release, regenerate the manifest, rebuild, rerun the axiom audit, and run the required Palomar Comparator and independent-kernel checks. Preserve this verified release as a tag or immutable commit before a port.
