# Provenance and review

## Source and authorship

The mathematical source is Tao Hu, Jiachen Shi and Quanyu Tang,
*Strictly Convex Steklov-Isospectral Plane Domains*, arXiv:2608.10557v2.
The original PDF, TeX and arXiv source archive are preserved under `paper/`.
Their rights are separate from the formalization's code license.

The formalization authors and responsible maintainers are **Tao Hu,
Jiachen Shi, Quanyu Tang**, in that order, as specified by the project owner.
Their GitHub accounts are `taohu-hub`, `RGConj`, and `QuanyuTang`, respectively.
These account identifiers do not authenticate a particular paper-author identity or
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

The resulting [Windows machine-checking record](../verification/local-windows-20261027/report.json)
binds proof snapshot `2d1b0331a534c8c774794252b14152c5be32a3f7` to the successful
build, full fresh axiom/type audit, locally generated exports and unmodified
bundled checkers. NanoDa, Lean and con-ron accepted the selected main-result
closure. The run was unsandboxed; a Windows executable-location compatibility
bridge did not alter the checkers. The original repository's final Linux CI was
prevented from starting by its owner account's billing/spending restriction.
For the public personal copy, consult its Actions runs for the exact commit;
the original repository's billing failures do not establish this copy's result.
The historical report retains all original 190 input hashes. Following the
canonical Challenge repair described below, the other 189 current inputs remain
byte-identical and the previous Challenge is archived; the historical run does
not cover the new Challenge.

## Public personal copy

On 2026-10-27, at the user's request, the complete `main` history of
[taohu-hub/steklov-isospectral-formalization](https://github.com/taohu-hub/steklov-isospectral-formalization)
through commit `5de09135cd688ce5e6487b16bd44e64f056f7fbc` was copied to
[QuanyuTang/steklov-isospectral-formalization](https://github.com/QuanyuTang/steklov-isospectral-formalization).
The destination is an independent repository rather than a GitHub fork; the
original was public when inspected at the time of copying. The destination was
initially private and was subsequently made public at the user's explicit
request on 2026-10-27. The copy preserves the original
authorship, maintainer ordering, licensing, proof sources and historical evidence.
Ownership of the destination does not change attribution.

Historical Actions links still refer to the original repository and certify
only their recorded snapshots. This personal copy must obtain its own successful
checks for the final submitted commit. Its workflow badges point to its own
Actions runs. Public repository access does not constitute Palomar submission,
editorial acceptance or registration. A later actual submission attempt and the
subsequently registered snapshot are recorded below.

## Canonical Challenge compilation repair

The user's actual submission `r8jnaa28pthg` of
`e5e5383838201fb674f87042dcb8c86ccc761fb2` on 2026-10-27
[failed canonical Challenge compilation](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/40533988514).
The personal-repository full build/audit and bundled Comparator workflows had
passed for that snapshot, but used the candidate Lake configuration. Palomar's
canonical stage intentionally omits that configuration and its compiler options;
`Label`'s generated `Fintype` instance failed under the compiler defaults. The
earlier two green workflows therefore did not establish canonical Challenge
compatibility.

The bounded repair inserts only
`set_option backward.isDefEq.respectTransparency false in` before the existing
`Label` inductive declaration and deriving clause. The old source is archived
byte-for-byte in `verification/challenge-canonical-20261027/`; its hash still
matches the unchanged Windows report. The checker reconstructs the new source
using the single hardcoded insertion and enforces the other 189 input hashes.
This records source preservation, not acceptance of the changed file by a
compiler, independent kernel or registry. Historical reports and genuine logs
are not rewritten.

The added official mechanical preflight calls the pinned PalomarSubmission
pipeline in **full** mode with its standard runner profile. It includes the
canonical Challenge stage absent from the earlier two workflows. Require
successful results on the exact new commit. Running this mechanical workflow
in the personal repository does not create a registry submission or perform
editorial review or registration.

## Palomar registration and author-name metadata

[PALOMAR-2026-10-27-000029, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-27-000029&version=1)
registered source commit `54fddf140bb5fb86ce2eb8fceddb46f20bac1842`.
On 2026-10-28, the project owner requested that the repository's author and
maintainer metadata use the corresponding human names instead of GitHub account
strings. This corrects their displayed representation and preserves the existing
people and order; the account links remain in the README. Historical reports and
the registered version 1 are unchanged. A new source SHA must be submitted under
the existing Palomar ID before a subsequent version can publish the correction.
