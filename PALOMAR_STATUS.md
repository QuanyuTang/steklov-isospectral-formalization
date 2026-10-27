# Palomar preparation status

Authors and responsible maintainers, in order: **taohu-hub, RGConj, QuanyuTang**.

## Latest proof-source recheck: Windows, 2026-10-27

The proof inputs in this checkout match the complete 190-input fingerprint of
`2d1b0331a534c8c774794252b14152c5be32a3f7`. All 176 modules and both entries
built successfully (9111 jobs), the fresh 590-target audit passed, and the
unmodified pinned Comparator accepted the declaration/definition match and axiom
allowlist. NanoDa and Lean accepted the selected proof closure; con-ron also
accepted the same Solution export (71641 declarations reported by that checker).

This was an **unsandboxed Windows check**, with fresh export generation bound to
source, compiled-part and tool hashes. A Windows executable-location compatibility
bridge was used; no checker binary or submitted Comparator configuration was
modified. The earlier Windows runtime stack failures were resolved through the
documented resource settings before the successful full build.

The original repository's final Linux jobs ran **zero steps**: GitHub reported
failed recent payments or an insufficient spending limit for its owner account.
This message does not establish which condition applies. For the personal copy
`QuanyuTang/steklov-isospectral-formalization`, consult its Actions runs for the
exact commit. The original repository's billing failures do not establish this
copy's result. Each submitted SHA requires successful isolated checks.

[Structured report and logs](verification/local-windows-20261027/report.json) ·
[Source/export/tool bindings](verification/local-windows-20261027/export-bindings.json).
`scripts/check-release.py` rejects changed or missing proof inputs even after
the ordinary release checksums have been refreshed.

## Previously recorded Linux sandbox verification

Recorded commit `6932e18512a776e4edae15bc076f4224ec85e4ad` passed a fresh Lean 4.35.0-rc2 build of all 176 modules, the complete 590-target proof/type and transitive axiom audit, official metadata/source checks, and sandboxed Comparator replay with the bundled Lean and NanoDa kernels.

| Check | Recorded result |
| --- | --- |
| Pins | Lean 4.35.0-rc2; canonical Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55 |
| Fresh full-source build | 176 modules; no restored project artifacts |
| Proof/type and transitive axiom inventory | All 590 targets; only propext, Classical.choice, Quot.sound |
| Fidelity guards | Smooth-infinity contract and both fibreHomeo computational projections passed |
| Metadata and source checks | Official v0.4 schema, source integrity and strict Git diff passed |
| Sandboxed Comparator | Declaration/definition comparison and selected-proof axiom check passed |
| Required bundled kernels | Lean and NanoDa accepted the selected main-result proof closure |
| con-ron advisory | accepted; con-ron, NanoDa and Lean accepted in the additional unchanged upstream all-kernel script. |
| Palomar submission / editorial review / registration | Not performed |

These are checks of that exact snapshot. Subsequent commits require their own successful runs. No Palomar submission, editorial acceptance or registration is claimed.

The complete 590-target audit uses standard Lean. Comparator independently replays the selected `SteklovSubmission.main_result` proof closure; it does not export each audit target separately. `comparator.json` has no fillable definition targets or submitter external kernels. The single deliberate Challenge hole is never imported by Solution.

The proof scope, alternative explicit construction and qualified general-theory limits are documented in [RESULTS.md](docs/RESULTS.md). Historical Lean 4.28 reports remain baseline evidence only.

[Exact build/kernel evidence](docs/lean435-build-audit-evidence.json) · [Submission guide](docs/PALOMAR.md). The personal preparation repository is public at the owner's request. Actual submission requires the owner's final approval.
