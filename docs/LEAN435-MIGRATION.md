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

The sixth full-library build also exposed a downstream coercion mismatch in
`Degree7RiemannCover`. Codex makes the polynomial evaluation equality explicit
with `change`, unfolding the transported projection by definitional equality.
This additional proof-body repair leaves the theorem statement and all
definitions unchanged and still requires the pinned Linux build.

Task `f5222b23-ccbe-477f-a5fc-fb07e6f2bc1b` supplied five changed files against
commit `96f79e2affe021fedffb029eed32d71ef1ddfb71`. Three proof-body changes address
the eighth build's `OutwardNormal`, `OrbMetricBounds` and `Degree7RiemannCover`
errors. No declaration signature changes, additions or removals occur.

The other two files implement a module-layout correction: the exact original
`MainTheorem` definition moves from `MainStatement.lean` to the end of
`Defs.lean`. `MainStatement.lean` remains as a public re-export, preserving all
176 modules and existing imports. All concrete definitions and the complete
main proposition keep their original code. Both original files are archived
under `verification/templates/`, and the release checker verifies the exact
move against those immutable baseline hashes, rather than accepting arbitrary
edits to either file.

An independent inspection of Lean 4.35's compiled declarations confirmed why
the previous identical source tokens failed strict comparison: the flattened
Challenge reused `Steklov.weightedBoundaryMass._proof_1` for the numeral in
`2 * Real.pi`, whereas the separate original statement module generated
`MainTheorem._proof_1`. The layout correction reproduces the Challenge's
ordinary declaration order. Challenge, the comparison targets, the trusted
judge and the permitted axiom set remain unchanged. No cache-reset command or
other metaprogram is added to the submission. This source-only batch still
requires full target compilation, the 590-target audit and independent replay.

Task `587e1778-5fd6-402d-a67d-d95ba64b5e32` returned three proof-only files
against commit `66ee1559b88b781a6ecaea48c81eb1db41f86876`. Exact input hashes
were verified. The batch replaces a redundant conversion with explicit base-set
and function equalities in `Degree7Bordered`, evaluates the real inner product
in `OutwardNormal` without relying on its implementation's multiplication
order, and combines typed `WithLp` component equalities in `OrbMetricSobolev`.
The last proof has a bounded local heartbeat limit. No declaration, signature,
concrete definition or module changes, and the exact main-statement relocation
is retained. Target compilation and replay remain pending.

The ninth Comparator job failed without downloadable job logs or an evidence
artifact. No success of declaration comparison or independent replay is inferred
from that run. The next workflow preserves the environment before the long
comparison and records resource use in the comparison log, to improve evidence
when a job fails. The official verification script and trust settings are
unchanged.

The tenth run reached `runKernels` after declaration equality and the selected
proof's transitive axiom precheck. Its runner then received a shutdown signal
while executing con-ron, before the mandatory NanoDa and Lean replay could
complete. This is not a kernel acceptance result. The remaining full-library
source errors are two typeclass-inference timeouts in `OrbMetricSpectrum`.

CI now follows the order in [Palomar's current mechanical policy, section 5](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#5-what-mechanical-verification-establishes):
`verify-required-comparator.sh` invokes the unmodified bundled, sandboxed
Comparator with bundled NanoDa, followed by its built-in Lean checker. It keeps
the same theorem, definitions and three permitted axioms. Only after that phase
succeeds does CI run the unchanged upstream all-kernel template script, with
a local ten-minute budget for that additional attempt. A local timeout is
reported as inconclusive, without claiming con-ron acceptance or predicting
Palomar's own advisory outcome. An observed checker rejection or other error
continues to block the workflow. Mandatory evidence is saved before that
additional attempt. No submitted `external_kernels` field is introduced.

Prepared submission entries are cached before replay, and current full-build
caches take precedence over older Comparator caches. These changes reduce
recompilation after infrastructure interruption; final fresh-source compilation
and complete 590-target auditing are still required.

Task `c26643cd-4293-4f38-b0e5-77a76f830c1b` returned the exact-base
`OrbMetricSpectrum.lean` against commit
`e53d40edc0aca2454653ae3511fab7e0490eb7a9`. It supplies typed zero-transport
facts for the continuous linear equivalence and its inverse, replacing three
generic simplification calls by direct proof terms. The complete spectral and
multiplicity statement, every binder and all definitions are unchanged. This
one-file batch has no new declaration or signature change and is still
target-uncompiled until the next Linux workflow validates it.

The eleventh full-library build compiled `OrbMetricSpectrum` and then found
one further no-progress error in `Degree7ConeOrders`. Codex removed the empty
`simp only at h2` command; the following explicit rewrites and all mathematical
declarations are unchanged. The independent-kernel workflow now keeps an
in-progress verification when a new source fix is pushed, queuing the new
snapshot rather than discarding unfinished kernel work. This does not certify
either snapshot until its own required checks finish.
