# Provenance and review

## Mathematical source

Tao Hu, Jiachen Shi, Quanyu Tang, *Strictly Convex Steklov-Isospectral Plane Domains*, arXiv:2608.10557v2, revised 15 August 2026. The source is adapted through an explicit degree-seven realization; the five conclusions of its main theorem are retained. Full original TeX and its arXiv source archive are preserved under `paper/`.

## Repository and automation

This is the substantive proof development, not a wrapper around an unpublished external formalization. Public repository maintainers: **taohu-hub, RGConj, QuanyuTang**, as supplied by the project owner. This identifies repository maintenance; it does not certify identity as any particular paper author or claim independent human verification.

The user requested and directed the formalization. **Aristotle, by Harmonic**, performed most proof generation over successive tasks. Its backend model and exact compute expenditure were not disclosed. **OpenAI Codex (GPT-6 family)** organized proof tasks, supplied intermediate mathematical scaffolding, ran local builds and axiom checks, reviewed source correspondence, and prepared the public release. The exact model for every historical step was not retained, so no more precise model attribution is asserted. Total monetary expenditure was not tracked. Recorded elapsed time for the completed proof effort was approximately 36 hours; packaging is separate.

No paper coauthor's endorsement, independent human expert review, or Palomar registration is asserted. The review status is **AI-assisted self-assessment with local machine checking**. Original logs and source hashes are supplied, and the release is intended to enable independent reproduction and mathematical inspection.

## Preserved evidence

The original snapshot has 180 Lean source files: 176 library/configuration modules and four command-only axiom inventories. The latter are preserved byte-for-byte as `verification/templates/*.lean.in`, rather than compiled library modules, because Lean 4.28 forbids `#print axioms` inside a `module`. The remaining 176 library files are unchanged except that the command-only `Main.lean` receives a module header. Thus all mathematical declarations and proof bodies, and all original audit commands, are unchanged. The release checker verifies these contents against the frozen hashes.

`scripts/audit.py` combines those templates with the original final proof/type audit and a public-entry axiom check, then runs the generated non-module file under `.lake/audit/`. Generated `.lake/` files are excluded from public source scans and from the release. The new Solution entry contains no audit side effects and does not import the Challenge.

The toolchain and all resolved dependency revisions are unchanged. The release Lakefile pins Mathlib by full commit, the manifest's `inputRev` is synchronized to that same commit, and the independent Challenge and Solution build targets are added. The original manifest is represented in the recorded verification evidence; changing the dependency label has not changed the resolved source closure.

One historical introductory comment in `RequestProject/MainStatement.lean` says that the end-to-end proof was not yet formalized. That describes the early statement-only stage and is superseded by the actual later proof declarations, especially `MainTheoremClassical.lean`; it has been retained to keep the verified source snapshot byte-identical. The public README and scope report describe the final state.

Original logs and reports in `verification/recorded/` are preserved as evidence of the earlier build. References in those files to `results/run-20/` or `formalization/` describe the original workspace layout; they are not required paths in this public repository. Current reproduction uses the commands in `docs/REPRODUCIBILITY.md`.

The new `Challenge.lean` contains one permitted statement-only placeholder. The proved `Solution.lean` is independent of it. A local build does not establish a Palomar Comparator or independent-kernel result; those checks are explicitly outstanding.
