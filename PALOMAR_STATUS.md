# Palomar preparation status

Authors and responsible maintainers, in order: **taohu-hub, RGConj, QuanyuTang**.

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

[Exact build/kernel evidence](docs/lean435-build-audit-evidence.json) · [Submission guide](docs/PALOMAR.md). Publication of the private preparation repository and actual submission require the owner's final approval.
