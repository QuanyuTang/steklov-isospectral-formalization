# Migration candidate — not yet verified

Target: leanprover/lean4:v4.35.0-rc2; Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55.
Recorded commit `fd44fc6172c412ccdc844c112dea5d3df9a26383` passed the fresh
176-module Linux build, all 590 audit targets, official metadata schema and
strict source-preservation checks. Its sandboxed main-proof export was
accepted by NanoDa. The runner then shut down during Lean's replay; a
same-commit retry is in progress. Final verification and packaging remain
incomplete. [Evidence](docs/lean435-build-audit-evidence.json).

Historical files in `verification/recorded/` and `verification/package-*.log`
certify the separately preserved Lean 4.28 baseline only.
