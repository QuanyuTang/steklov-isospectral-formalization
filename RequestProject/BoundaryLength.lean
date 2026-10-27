module

public import RequestProject.ConformalPullback
public import RequestProject.BlaschkePerimeter
public import RequestProject.DilationGeometry

/-!
# Boundary length via the arc-length formula

* `boundaryLength_image_ball`: `|∂F(𝔻)| = ∫_0^{2π} |F'(e^{it})| dt` for `F` holomorphic near `𝔻̄`
  and injective on `𝔻̄`.
* `boundaryLength_eq_of_realAnalyticJordan`: the length of a real-analytic Jordan boundary
  is `∫_0^{2π} |γ'|`.
* `boundaryLength_rescaled_blaschke`: the length step of conclusion (iv) in §3.5 — if
  `|F'| = |B'|` on `𝕋` for a degree-`n` finite Blaschke product `B`, then `(1/n)·F(𝔻)` has
  boundary length `2π`.
-/

@[expose] public section

open Set Filter Topology Metric MeasureTheory PlaneDomain
open scoped ENNReal Real

noncomputable section

namespace BoundaryLength

variable {F : ℂ → ℂ} {U : Set ℂ}

/-- **Length of `∂F(𝔻)`.** -/
theorem boundaryLength_image_ball (hU : IsOpen U) (hcb : closedBall (0 : ℂ) 1 ⊆ U)
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F (closedBall 0 1)) :
    boundaryLength (F '' ball 0 1) =
      ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal ‖deriv F (Complex.exp (t * Complex.I))‖ := by
  unfold boundaryLength
  rw [ConformalPullback.frontier_image_ball hcb hF hinj, ← setLIntegral_one,
    ConformalPullback.boundary_lintegral hU hcb hF hinj measurable_const]
  simp

/-- **Length of a real-analytic Jordan boundary** is the integral of the speed over a period. -/
theorem boundaryLength_eq_of_realAnalyticJordan {Ω : Set ℂ} {γ : ℝ → ℂ}
    (hγa : AnalyticOnNhd ℝ γ univ) (hper : Function.Periodic γ (2 * π))
    (hinj : InjOn γ (Ico 0 (2 * π))) (hrange : range γ = frontier Ω) :
    boundaryLength Ω = ∫⁻ t in Ico 0 (2 * π), ‖deriv γ t‖ₑ := by
  have hd : ∀ t, HasDerivAt γ (deriv γ t) t := fun t =>
    (hγa t (mem_univ t)).differentiableAt.hasDerivAt
  have hc : Continuous (deriv γ) := continuousOn_univ.1 hγa.deriv.continuousOn
  have himg : γ '' Ico 0 (2 * π) = frontier Ω := by
    rw [← hrange]
    refine (image_subset_range _ _).antisymm ?_
    rw [← hper.image_Icc Real.two_pi_pos 0, zero_add]
    rintro _ ⟨t, ht, rfl⟩
    rcases ht.2.lt_or_eq with h | h
    · exact ⟨t, ⟨ht.1, h⟩, rfl⟩
    · refine ⟨0, ⟨le_rfl, Real.two_pi_pos⟩, ?_⟩
      rw [h, ← zero_add (2 * π), hper 0]
  unfold boundaryLength
  rw [← himg]
  exact ArcLength.hausdorffMeasure_image_eq_lintegral hd hc Ico_subset_Icc_self
    measurableSet_Ico hinj


open SteklovBlaschke in
/-- Finite Blaschke products are holomorphic on a neighbourhood of every point of `𝔻̄`. -/
lemma blaschke_differentiableAt {B : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n) {z : ℂ}
    (hz : ‖z‖ ≤ 1) : DifferentiableAt ℂ B z := by
  obtain ⟨η, a, -, ha, rfl⟩ := hB
  have hl : ∀ l ∈ (Finset.univ : Finset (Fin n)), DifferentiableAt ℂ (bfac (a l)) z := by
    intro l _
    unfold bfac
    exact DifferentiableAt.div (by fun_prop) (by fun_prop) (denom_ne_zero (ha l) hz)
  have := (DifferentiableAt.finset_prod hl).const_mul η
  convert this using 2 with w
  simp [Finset.prod_apply]

lemma norm_deriv_comp_exp {B : ℂ → ℂ} {t : ℝ}
    (hB : DifferentiableAt ℂ B (Complex.exp (t * Complex.I))) :
    ‖deriv (fun s : ℝ => B (Complex.exp (s * Complex.I))) t‖ =
      ‖deriv B (Complex.exp (t * Complex.I))‖ := by
  have hc : ∀ s : ℝ, circleMap 0 1 s = Complex.exp (s * Complex.I) := fun s => by
    simp [circleMap]
  have hfun : (fun s : ℝ => B (Complex.exp (s * Complex.I))) = B ∘ circleMap 0 1 := by
    funext s; simp [hc]
  rw [hfun, ← hc t] at *
  rw [((hB.hasDerivAt).comp t (hasDerivAt_circleMap 0 1 t)).deriv, norm_mul, norm_mul,
    Complex.norm_I]
  simp

open SteklovBlaschke in
/-- **Length step of conclusion (iv)** (§3.5).  If `F` is holomorphic near `𝔻̄`, injective on `𝔻̄`,
and `|F'| = |B'|` on `𝕋` for a finite Blaschke product `B` of degree `n ≥ 1`, then the rescaled
domain `(1/n)·F(𝔻)` has boundary length `2π`. -/
theorem boundaryLength_rescaled_blaschke {B : ℂ → ℂ} {n : ℕ} (hn : 0 < n)
    (hB : IsFiniteBlaschke B n) (hU : IsOpen U) (hcb : closedBall (0 : ℂ) 1 ⊆ U)
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F (closedBall 0 1))
    (hρ : ∀ z ∈ sphere (0 : ℂ) 1, ‖deriv F z‖ = ‖deriv B z‖) :
    boundaryLength ((fun z : ℂ => ((n : ℝ)⁻¹) • z) '' (F '' ball 0 1)) =
      ENNReal.ofReal (2 * π) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [SteklovDilationProof.boundaryLength_smul (inv_pos.2 hnpos),
    boundaryLength_image_ball hU hcb hF hinj]
  have hmem : ∀ t : ℝ, Complex.exp (t * Complex.I) ∈ sphere (0 : ℂ) 1 :=
    ConformalPullback.exp_mem_sphere
  have hint : ∫ t in (0 : ℝ)..(2 * π), ‖deriv F (Complex.exp (t * Complex.I))‖ = 2 * π * n := by
    rw [← integral_norm_deriv_blaschke hB]
    refine intervalIntegral.integral_congr fun t _ => ?_
    rw [hρ _ (hmem t), norm_deriv_comp_exp (blaschke_differentiableAt hB
      (le_of_eq (mem_sphere_zero_iff_norm.1 (hmem t))))]
  have hcont : Continuous fun t : ℝ => ‖deriv F (Complex.exp (t * Complex.I))‖ :=
    (((hF.deriv hU).continuousOn).comp_continuous (by fun_prop)
      fun t => hcb (sphere_subset_closedBall (hmem t))).norm
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le] at hint
  rw [← ofReal_integral_eq_lintegral_ofReal
    (hcont.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (ae_of_all _ fun t => norm_nonneg _), hint, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

end BoundaryLength
