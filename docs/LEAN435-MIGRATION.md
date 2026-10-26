# Lean 4.35 migration record

The target is Lean `4.35.0-rc2` and canonical Mathlib
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. The retained successful Lean 4.28
logs certify the baseline. They do not certify these changes.

Aristotle task `81dccf0b-8b15-4407-9ca6-6dac05d49813` supplied a 21-file repair
batch against candidate commit `635ac12bcd94900ed358f1e4e6a8973f7500d937`.
Its environment could not download the target toolchain, so this batch was
explicitly returned as source-only, uncompiled work. The pinned Linux workflows
must validate it. No new build, axiom audit or independent replay pass is claimed.

## Implementation helper signatures

Current Mathlib makes `eLpNorm` infinite when the function is not a.e. strongly
measurable. Some baseline helpers quantified over arbitrary functions; those
formulas are no longer valid without measurability. The migration therefore
records these auxiliary signature changes explicitly:

| Helper | Change |
| --- | --- |
| `SteklovBranch.eLpNorm_two_sq` | Adds a.e. strong measurability of the function. |
| `SteklovC1.eLpNorm_two_sq` | Adds a.e. strong measurability of the function. |
| `SteklovDensity.eLpNorm_moll_le` | Adds a.e. strong measurability of the mollification. |
| `SteklovDensity.exists_bound_eLpNorm` | Restricts its auxiliary function argument to a.e. strongly measurable functions. |
| `SteklovDensity.eLpNorm_add3_le` | Removes three obsolete measurability premises, giving a stronger auxiliary bound. |

The exact before/after source signatures are in
[lean435-signature-changes.json](lean435-signature-changes.json). The helper
names in that file are paired with their source paths. They are implementation
lemmas, not new assumptions of the paper's main or numbered results.
The proposed callers derive the needed conditions from continuity, measurable
derivatives, finite norms, or the measurable representatives of `Lp` functions;
acceptance of those proofs remains subject to the fresh build.

The public Dirichlet-energy identity retains its arbitrary-function scope using
`measurable_fderiv`. All other existing declaration signatures and all concrete
definition bodies in this 21-file batch were compared with the exact uploaded
candidate and found unchanged after stripping comments and whitespace. No
declaration was dropped. This source comparison is supplementary evidence,
not a mathematical fidelity proof or a kernel check.

The new private `parts_card_eq_aux` proves the finite permutation cycle count
through its cycle type and support instead of evaluating a noncomputable cycle
factor construction. The remaining changes adapt topology, derivatives and
measure-theoretic proof APIs. The full 590-target axiom inventory is retained;
only `propext`, `Classical.choice` and `Quot.sound` are permitted in the proofs.

## Subsequent repair batch

Task `9ecf9e68-c557-4f81-ab10-234aa5cf7eae` returned 31 changed files against
commit `0066d2a0df97eddd0fcfb6f70a5fcd8ea8177121`. This batch also requires
fresh target-version compilation; Aristotle did not claim a new build.
The source comparison found no changed theorem statement, concrete definition
body, or dropped declaration. `PolyCover.pathConnectedSpace_total` retains its
statement and binders but is now a theorem rather than a globally registered
instance: its proof parameter cannot be inferred by the new typeclass checker.
Its callers already supply the fact explicitly with `haveI`.
The new private `cycleType22_of_aux` supports symbolic finite-cycle proofs.
Other changes adapt product inequalities, derivatives, integration by parts,
function equalities and `WithLp` pair reconstruction. The five earlier helper
signature changes above remain the complete list of mathematical signature
adaptations in these two repair batches.

Task `17c2b647-7001-44ce-b580-dba56694b49f` supplied a further 10-file proof
repair batch against commit `7aee2a86d4a6c5b7add3a3574eb9bfcfe4268ec5`.
No statement, definition, declaration kind or inventory entry changed in this
batch. Some individual proofs receive bounded increases of `maxRecDepth` or
`maxHeartbeats`; finite computations still use the real kernel through
`decide +kernel`. These resource settings do not add axioms or bypass kernel
verification. The batch also supplies a measurability proof for a limiting
function and uses explicit equivalence facts to avoid stalled instance search.
It remains uncompiled source work until the exact target CI validates it.

Task `8c7275c8-bf02-4265-9ddd-2ec9000b1fe8` returned a three-file batch against
commit `1d2d1f9e4aa1f2f4fb59c7591a57bbfe61322f6b`, addressing the observed
`SingularTransfer`, `DiskGreen` and `FillExtend` errors. It changes proof steps
and the placement of a local resource option, with no statement, definition,
declaration-kind or inventory change. The preceding full-build job was
interrupted by a runner shutdown, while its Comparator job failed at source
compilation; neither supplied a successful new axiom audit or independent
replay. This next source batch must therefore undergo complete validation.

After the sixth Comparator build, Codex supplied two small proof-body fixes:
explicit function arguments for the `L²` triangle inequalities and removal of
an unnecessary tactic after simplification already closed a derivative goal.
No declaration statement or definition changes. Both workflows now explicitly
check out the pull request's submitted head SHA, and record the checkout and
tree hashes; earlier PR runs used GitHub's generated merge checkout.
Complete target validation is still required for the updated snapshot.
