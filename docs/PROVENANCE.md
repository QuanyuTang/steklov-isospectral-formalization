# Provenance and review

## Source and authorship

The mathematical source is Tao Hu, Jiachen Shi and Quanyu Tang,
*Strictly Convex Steklov-Isospectral Plane Domains*, arXiv:2608.10557v2.
The original PDF, TeX and arXiv source archive are preserved under `paper/`.
Their rights are separate from the formalization's code license.

The formalization authors and responsible maintainers are **taohu-hub,
RGConj, QuanyuTang**, in that order, as specified by the project owner.
These identifiers do not authenticate a particular paper-author identity or
assert any coauthor's endorsement or independent human review.

The user requested and directed the work. **Aristotle (Harmonic)** performed
most proof generation. **OpenAI Codex (GPT-6 family)** coordinated tasks,
provided intermediate proof scaffolding, reviewed statement correspondence,
performed machine checks, repaired compatibility and organized the repository.
The exact backend model for every historical step and monetary cost were not
tracked. The original proof project elapsed time was approximately 36 hours;
release preparation and version migration are separate.

## Baseline and migration evidence

The verified baseline uses Lean 4.28.0 and Mathlib
`8f9d9cff6bd728b17a24e163c9402775d9e6a365`. Its 180 original source files
are identified by the frozen manifest in `verification/recorded/`.
Four command-only audit inventories are preserved as `.lean.in` templates;
the proof library contains 176 modules. The public library's configuration-only
`Main.lean` receives a module header. Audit commands run from a generated
non-module probe under `.lake/audit/` and are not proof dependencies.

The migration target is Lean 4.35.0-rc2 and canonical Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Changes relative to the baseline
are recorded in [migration-changes.json](../verification/migration-changes.json).
The release checker holds the main statement's Lean code fixed and archives
the original statement file; its obsolete introductory comment was corrected
to point to the actual proof entries. Concrete definitions are compared in
full by Comparator, rather than admitted as fillable definitions.

The root Lake configuration records the Lean-provided elaboration compatibility
options used by the port. These change proof elaboration, not the mathematical
statement or kernel acceptance criteria. The solution must still build, satisfy
the three-axiom allowlist and pass the independent-kernel checks.

Historical logs under `verification/recorded/` and `verification/package-*.log`
certify the baseline only. They do not certify the migration. The two GitHub
workflows identify the exact new commit they test; [PALOMAR_STATUS.md](../PALOMAR_STATUS.md)
records the current stage. A failed or unfinished build is not verified.

## Trust and scope

The independent statement imports only canonical Mathlib. Its one deliberate
statement hole is not imported by the Solution. The permitted proof axioms
are `propext`, `Classical.choice` and `Quot.sound`; the audit enforces the
allowlist for every inventory target and rejects missing reports.

Release preparation received a read-only AI source/document review by Aristotle
of commit `fd44fc6172c412ccdc844c112dea5d3df9a26383`. It identified documentation and inventory issues; the
source-map corrections, comments and full-baseline declaration inventory were
then checked separately. This was an AI review, not independent human peer
review or target-toolchain compilation by that reviewer.

Aristotle later authored the idBase and structural good_eq_orbits proof-cost
optimizations. The earlier read-only review does not cover those later patches.
Codex reviewed their exact source differences, unchanged original statements and
computational definitions, and target build/audit/Comparator evidence. The
52 new private proof-support declarations are individually inventoried.

The review status remains AI-assisted assessment with machine checking.
No independent human mathematical peer review, Palomar registration or
institutional endorsement is claimed. [RESULTS.md](RESULTS.md) and
[ERRATA-AND-DEVIATIONS.md](ERRATA-AND-DEVIATIONS.md) describe the actual scope,
concrete representations and alternative proof routes.

On 2026-10-27, Codex performed an additional parallel source review against the
preserved TeX: all five main conclusions and their simultaneous quantifiers,
the ordinary geometric definitions, the actual variational/PDE spectrum bridge,
and the core construction and transplantation chain. No substantiated
mathematical defect was identified in that review. The release repair fixes
stale integrity manifests, branch badges, validation gaps and documentation;
it does not replace the mathematical proof. The structured record at
[final-review.json](../verification/final-review.json) distinguishes this
source review from compilation, independent-kernel replay and human review.
