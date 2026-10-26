# Palomar preparation status

Authors and responsible maintainers, in order: **taohu-hub, RGConj, QuanyuTang**.

This is the migration candidate for Lean **4.35.0-rc2**, with canonical Mathlib
commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`.
It is not a registered Palomar result. The retained Lean 4.28 verification
reports are baseline evidence and do not certify this port.

| Check | Current state |
| --- | --- |
| Toolchain and Mathlib pins | Prepared |
| Source checks and official v0.4 metadata schema | Passed in Linux CI |
| Linux namespace sandbox startup | Passed in Linux CI |
| Full Lean 4.35 build | Passed for recorded commit `1d94bf37`; project-cache-free rebuild pending |
| Lean 4.35 public theorem and axiom audit | All 590 targets passed on recorded commit `1d94bf37` |
| Source-preservation guard | Run 12 failed on CRLF/LF differences only; publication normalization fixed for next run |
| Linux sandboxed Comparator, Lean and NanoDa replay | In progress on earlier candidate; current candidate queued |
| con-ron advisory replay | Earlier attempt interrupted; additional attempt follows mandatory checks |
| Palomar mechanical verification | Not submitted |
| Automated editorial review and registration | Not submitted |

The two workflows, `lean.yml` and `palomar.yml`, run on pull requests and
pushes to main, and support manual dispatch. Their logs
will identify the exact tested commit. A GitHub Actions pass is preparation
evidence; it is not a Palomar registration.

The exact successful build/audit commit, artifact digest and remaining limits
are recorded in [the evidence record](docs/lean435-build-audit-evidence.json).
The overall run was not green: its final strict Git diff guard detected text
line endings. The guard remains enabled. New full-library runs start without
project compilation artifacts; only canonical Mathlib dependency caches may be
reused. An earlier candidate's independent replay cannot certify a later commit.

The statement surface is `Challenge.lean` and the proof entry is
`Solution.lean`. Comparator selects `SteklovSubmission.main_result` and has
no fillable definition targets: the concrete definitions and all five main
conclusions are compared in full. The one deliberate `sorry` in the Challenge
is never imported by the Solution.

The source-based theorem correspondence and limitations are documented in
[RESULTS.md](docs/RESULTS.md). The proof uses only `propext`,
`Classical.choice`, and `Quot.sound` in the verified baseline; the same
allowlist is enforced for this port. Neither an extra premise nor an axiom
may replace an uncompleted compatibility fix.

Layout references: [Palomar submission guide](https://palomar-registry.org/how-to-submit),
[official starter](https://github.com/PalomarRegistry/PalomarTemplate), and
[the supplied Polya repository](https://github.com/QuanyuTang/polya-dirichlet-simply-connected-formalization-Palomar-version).
The example's registration does not transfer to this project.
