module

public import RequestProject.ConformalPullback
public import RequestProject.Dilation

/-!
# Proposition 2.3.1 reduces to its realization part

Using the proved conformal pullback (`ConformalPullback.prop_2_1_1`), the spectral conclusion of
Proposition 2.3.1 follows from the existence of the realizing maps.  So `Prop_2_3_1` follows from
`Prop_2_3_1_realization`.  (Both, and the convergence part, are now proved: see
`RequestProject.OuterRealization` and `RequestProject.OuterConvergence`.)
-/

@[expose] public section

open Set Metric MeasureTheory

noncomputable section

namespace Prop231Reduction

/-- The weighted spectrum only depends on the weight on the unit circle. -/
lemma weightedSteklovSpectrum_congr {ρ₁ ρ₂ : ℂ → ℝ} (h : ∀ z ∈ sphere (0 : ℂ) 1, ρ₁ z = ρ₂ z) :
    Steklov.weightedSteklovSpectrum ρ₁ = Steklov.weightedSteklovSpectrum ρ₂ := by
  have hB : Steklov.weightedBoundaryMass ρ₁ = Steklov.weightedBoundaryMass ρ₂ := by
    funext u
    unfold Steklov.weightedBoundaryMass
    refine lintegral_congr fun t => ?_
    rw [h _ (ConformalPullback.exp_mem_sphere t)]
  unfold Steklov.weightedSteklovSpectrum Steklov.weightedSteklovEigenvalue
  rw [hB]

lemma exists_exp_eq_of_mem_sphere {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) :
    ∃ t : ℝ, Complex.exp (t * Complex.I) = z := by
  refine ⟨Complex.arg z, ?_⟩
  have := Complex.norm_mul_exp_arg_mul_I z
  rwa [mem_sphere_zero_iff_norm.1 hz, Complex.ofReal_one, one_mul] at this

/-- **Proposition 2.3.1 from its realization part** (via Proposition 2.1.1). -/
theorem prop_2_3_1_of_realization (h : Prop_2_3_1_realization) : Prop_2_3_1 := by
  intro c hc
  obtain ⟨k, δ, hδ, hreal⟩ := h c hc
  refine ⟨k, δ, hδ, fun ρ hρ hck => ?_⟩
  obtain ⟨F, hFU, hinj, h0, hre, him, hnorm⟩ := hreal ρ hρ hck
  refine ⟨F, hFU, hinj, h0, hre, him, hnorm, ?_⟩
  have hF' : ∀ z ∈ sphere (0 : ℂ) 1, deriv F z ≠ 0 := by
    intro z hz h0'
    obtain ⟨t, rfl⟩ := exists_exp_eq_of_mem_sphere hz
    have := hρ.2 t
    rw [← hnorm _ hz, h0', norm_zero] at this
    exact lt_irrefl _ this
  rw [ConformalPullback.prop_2_1_1 F hFU hinj hF']
  exact weightedSteklovSpectrum_congr hnorm


/-- **Isospectrality transfer (step (ii) of §3.5).**  If `F₁, F₂` are holomorphic near `𝔻̄`,
injective on `𝔻̄`, and realize weights `ρ₁, ρ₂` on `𝕋` (`|F_i'| = ρ_i > 0` there) with
`Spec_St(𝔻, ρ₁) = Spec_St(𝔻, ρ₂)`, then the domains `c·F₁(𝔻)` and `c·F₂(𝔻)` (any `c > 0`)
are Steklov isospectral. -/
theorem isospectral_of_weighted {F₁ F₂ : ℂ → ℂ} {ρ₁ ρ₂ : ℂ → ℝ}
    (hF₁ : ∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ F₁ U)
    (hF₂ : ∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ F₂ U)
    (hinj₁ : InjOn F₁ (closedBall 0 1)) (hinj₂ : InjOn F₂ (closedBall 0 1))
    (hρ₁ : ∀ z ∈ sphere (0 : ℂ) 1, ‖deriv F₁ z‖ = ρ₁ z ∧ 0 < ρ₁ z)
    (hρ₂ : ∀ z ∈ sphere (0 : ℂ) 1, ‖deriv F₂ z‖ = ρ₂ z ∧ 0 < ρ₂ z)
    (hspec : Steklov.weightedSteklovSpectrum ρ₁ = Steklov.weightedSteklovSpectrum ρ₂)
    {c : ℝ} (hc : 0 < c) :
    Steklov.steklovSpectrum ((fun z => (c : ℂ) * z) '' (F₁ '' ball 0 1)) =
      Steklov.steklovSpectrum ((fun z => (c : ℂ) * z) '' (F₂ '' ball 0 1)) := by
  have hF₁' : ∀ z ∈ sphere (0 : ℂ) 1, deriv F₁ z ≠ 0 := fun z hz h0 => by
    have := hρ₁ z hz; rw [← this.1, h0, norm_zero] at this; exact lt_irrefl _ this.2
  have hF₂' : ∀ z ∈ sphere (0 : ℂ) 1, deriv F₂ z ≠ 0 := fun z hz h0 => by
    have := hρ₂ z hz; rw [← this.1, h0, norm_zero] at this; exact lt_irrefl _ this.2
  have h₁ := ConformalPullback.prop_2_1_1 F₁ hF₁ hinj₁ hF₁'
  have h₂ := ConformalPullback.prop_2_1_1 F₂ hF₂ hinj₂ hF₂'
  rw [weightedSteklovSpectrum_congr fun z hz => (hρ₁ z hz).1] at h₁
  rw [weightedSteklovSpectrum_congr fun z hz => (hρ₂ z hz).1] at h₂
  funext k
  unfold Steklov.steklovSpectrum at h₁ h₂ ⊢
  rw [SteklovDilationProof.steklovDilation _ c hc k, SteklovDilationProof.steklovDilation _ c hc k,
    congrFun h₁ k, congrFun h₂ k, hspec]

end Prop231Reduction
