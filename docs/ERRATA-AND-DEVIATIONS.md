# Errata and deviations

This record compares the development with Hu, Shi and Tang,
*Strictly Convex Steklov-Isospectral Plane Domains*, **arXiv:2608.10557v2**.
Locations refer to that version. An erratum would assert an error in the paper;
a deviation records an encoding, scope or proof-route choice. No paper erratum
is asserted here. Counts are entries, rather than individual occurrences.

| Source | Errata asserted | Deviations |
| --- | --- | --- |
| arXiv:2608.10557v2 | 0 | 4 |

## arXiv:2608.10557v2

### Errata

None asserted. The choices below do not add assumptions to Theorem 1.1.2.

### Deviations

1. **Section 3.2, realization before Lemma 3.2.1 — explicit construction.**
   The proof uses explicit degree-seven polynomials and their verified actual
   monodromy. It does not formalize the general Riemann existence theorem for
   arbitrary permutation data. The paper's fixed point/line construction is
   supplied directly; all five main conclusions retain their quantifiers.
   See [Degree7Polynomial.lean](../RequestProject/Degree7Polynomial.lean) and
   [Degree7Monodromy.lean](../RequestProject/Degree7Monodromy.lean).

2. **Sections 2.2 and 3.3 — concrete metric orbifold models.**
   The actual quotient objects are represented through proved disk-coordinate
   identifications, with cone uniformizers, lifted metrics, metric Sobolev
   spaces and boundary line elements. The common cover is the actual degree-168
   construction for the chosen group and stabilizers. This is not a general
   library of arbitrary orbifolds or all finite-group covers. See
   `SteklovOrb.DiskOrbisurface.prop_2_2_1_metric` in
   [OrbMetricSpectrum.lean](../RequestProject/OrbMetricSpectrum.lean), and
   `Degree7.prop_3_3_1_full` in
   [Degree7Prop331Full.lean](../RequestProject/Degree7Prop331Full.lean).

3. **Theorem 1.1.2(ii) — weighted-disk proof route.**
   The main spectral equality is proved by direct weighted-disk transplantation,
   `FamilyIso.family_spectra_eq`, in
   [FamilyIsospectral.lean](../RequestProject/FamilyIsospectral.lean).
   The quotient-orbifold result is developed separately. The main proof does
   not depend on a second general Sunada operator proof on the covering surface.
   The equality still concerns the full indexed spectrum, with multiplicities.

4. **Section 2.1 and Theorem 1.1.2(ii) — variational encoding and PDE bridge.**
   `Steklov.steklovSpectrum` is an extended-nonnegative-real min-max sequence
   over globally smooth test functions, with admissibility enforcing positive
   boundary mass on nonzero functions. For the constructed domains, the
   development proves the connection with the actual Sobolev and classical
   harmonic Steklov problems; it does not define those problems as aliases of
   the min-max sequence. See [Defs.lean](../RequestProject/Defs.lean) and
   `SteklovCoalescence.mainTheoremClassical_proved` in
   [MainTheoremClassical.lean](../RequestProject/MainTheoremClassical.lean).

## Proof route and scope

The explicit realization, weighted transplantation and concrete quotient
models retain the five conclusions advertised by
`SteklovSubmission.main_result` in [Solution.lean](../Solution.lean).
The stronger classical-spectrum theorem is retained in the library and axiom
inventory; the current Comparator configuration selects the five-conclusion
main entry. The [result map](RESULTS.md) lists the exact supporting declarations.

The general arbitrary-permutation Riemann-existence route, a general orbifold
library and arbitrary finite-group common-cover theorems are outside the
advertised scope. References used for release layout and verification are
listed separately in [third-party notices](THIRD_PARTY_NOTICES.md); they are
not additional mathematical premises.
