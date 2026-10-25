module

public import RequestProject.Defs

/-!
# Statement of Theorem 1.1.2 (main theorem of arXiv:2608.10557v2)

This file records the theorem as the proposition `MainTheorem`. The proof entry is
`SteklovCoalescence.mainTheorem_proved` in `MainTheoremProof.lean`; the stronger entry in
`MainTheoremClassical.lean` also supplies the Sobolev and classical PDE interpretation.
The statement keeps the original quantifier structure: one `ε₀ > 0` and one simultaneous
family `Ω i ε` for `i ∈ {P, L}` and `0 < ε < ε₀`. No unproved geometric or spectral premise
is added to the theorem.
-/

@[expose] public section

open Set PlaneDomain Steklov

/-- **Theorem 1.1.2.** There exist `ε₀ > 0` and a family `Ω i ε` (`i ∈ {P, L}`, `0 < ε < ε₀`)
of plane domains such that
(i) each is bounded, simply connected, strictly convex, with real-analytic Jordan boundary;
(ii) `Spec_St(Ω P ε) = Spec_St(Ω L ε)` including multiplicities;
(iii) distinct labels/parameters give noncongruent domains, and no domain has an
     orientation-reversing Euclidean symmetry;
(iv) each boundary has length `2π`;
(v) there are normalized conformal maps `F i ε : 𝔻 → Ω i ε`, holomorphic near `𝔻̄`, with
    `F i ε → id` in `C^∞(𝔻̄)` as `ε → 0`. -/
def MainTheorem : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Ω : Label → ℝ → Set ℂ,
    -- (i)
    (∀ i ε, 0 < ε → ε < ε₀ →
      IsDomain (Ω i ε) ∧ Bornology.IsBounded (Ω i ε) ∧ SimplyConnectedSpace (Ω i ε) ∧
      IsStrictlyConvexDomain (Ω i ε) ∧ IsRealAnalyticJordanBoundary (Ω i ε)) ∧
    -- (ii)
    (∀ ε, 0 < ε → ε < ε₀ → steklovSpectrum (Ω Label.P ε) = steklovSpectrum (Ω Label.L ε)) ∧
    -- (iii)
    (∀ i j ε ε', 0 < ε → ε < ε₀ → 0 < ε' → ε' < ε₀ → (i, ε) ≠ (j, ε') →
      ¬ Congruent (Ω i ε) (Ω j ε')) ∧
    (∀ i ε, 0 < ε → ε < ε₀ → ¬ HasOrientationReversingSymmetry (Ω i ε)) ∧
    -- (iv)
    (∀ i ε, 0 < ε → ε < ε₀ → boundaryLength (Ω i ε) = ENNReal.ofReal (2 * Real.pi)) ∧
    -- (v)
    (∃ F : Label → ℝ → ℂ → ℂ,
      (∀ i ε, 0 < ε → ε < ε₀ → IsNormalizedConformalMap (F i ε) (Ω i ε)) ∧
      ∀ i, TendstoIdInCInfty (F i))

end
