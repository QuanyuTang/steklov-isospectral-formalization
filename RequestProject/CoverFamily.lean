module

public import Mathlib
public import RequestProject.ConditionalFamily
public import RequestProject.DiskCoverExistence

/-!
# Conditional assembly with the cover input discharged

**Still conditional scaffolding, not a proof of Theorem 1.1.2.**  The cover input
`IsNormalizedDiskCover` is now *proved* (`exists_paper_diskCover_eventually`), so the assembly of
conclusions (i), (ii), (iv), (v) needs only:

* polynomial data for both labels (monic `P_i` of a common degree `n ≥ 1`, `τ_{i,ε}`), i.e. the
  output of Lemma 3.2.1, which is **not** formalized (its permutation/monodromy properties are
  neither used nor established here);
* the spectral transfer (Proposition 3.3.1, analytic part, **not** formalized), stated for every
  choice of normalized cover data: whenever `ψ_{i,ε}, B_{i,ε}` satisfy `IsNormalizedDiskCover` for
  all small `ε`, then `Spec_St(𝔻, |B_{P,ε}'|) = Spec_St(𝔻, |B_{L,ε}'|)` for all small `ε`.
  (By uniqueness of normalized Riemann maps the cover data are in fact unique, so this is the
  same hypothesis as the paper's.)

Conclusion (iii) (noncongruence) is not addressed.
-/

@[expose] public section

open Complex Metric Set Filter Topology SteklovBlaschke PlaneDomain Steklov

noncomputable section

namespace SteklovCoalescence

open SteklovCritical in
/-- **Conclusions (i), (ii), (iv), (v) of Theorem 1.1.2 from the polynomial data and the
spectral transfer alone** (the cover input is proved). -/
theorem mainTheorem_except_iii_of_spectral_transfer {n : ℕ} (hn : 1 ≤ n)
    (P : Label → Polynomial ℂ) (hP : ∀ i, (P i).Monic) (hdeg : ∀ i, (P i).natDegree = n)
    (τ : Label → ℝ → ℂ) (hτ : ∀ i ε, τ i ε ^ n = (lamStar - 1) * ε)
    (hspec : ∀ ψ B : Label → ℝ → ℂ → ℂ,
      (∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        IsNormalizedDiskCover (paperQ (P i) (τ i) ε) n (ψ i ε) (B i ε)) →
      ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        weightedSteklovSpectrum (fun z => ‖deriv (B Label.P ε) z‖) =
          weightedSteklovSpectrum (fun z => ‖deriv (B Label.L ε) z‖)) :
    MainTheoremExceptNoncongruence := by
  choose ψ B hcov using fun i => exists_paper_diskCover_eventually (hP i) hn (hdeg i) (hτ i)
  exact mainTheorem_except_iii_of_cover_data hn P hP hdeg τ hτ ψ B hcov (hspec ψ B hcov)

end SteklovCoalescence
