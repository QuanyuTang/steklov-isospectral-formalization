module

public import Mathlib

/-!
# The trace inequality on the unit disk

For a `C¹` real function `u` on the plane,
`∫₀^{2π} u(e^{it})² dt ≤ ∫_𝔻 (3 u² + |∇u|²)`.

Proof: along each ray, `f(r) = r² u(r e^{iθ})²` satisfies `f(1) - f(0) = ∫₀¹ f'`, and
`f'(r) ≤ r (3u² + |∇u|²)(r e^{iθ})` for `0 ≤ r ≤ 1`; integrating in `θ` and using polar
coordinates gives the claim.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal

noncomputable section

namespace SteklovH1

/-- The ray integrand: the density `3 u² + ‖Du‖²`. -/
def traceDensity (u : ℂ → ℝ) (z : ℂ) : ℝ := 3 * u z ^ 2 + ‖fderiv ℝ u z‖ ^ 2

lemma traceDensity_nonneg (u : ℂ → ℝ) (z : ℂ) : 0 ≤ traceDensity u z := by
  unfold traceDensity; positivity

lemma continuous_traceDensity {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) :
    Continuous (traceDensity u) := by
  unfold traceDensity
  have h1 : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have h2 : Continuous u := hu.continuous
  fun_prop

/-- Pointwise ray estimate. -/
lemma ray_estimate {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) (θ : ℝ) :
    u (Complex.exp (θ * Complex.I)) ^ 2 ≤
      ∫ r in (0:ℝ)..1, r * traceDensity u (r * Complex.exp (θ * Complex.I)) := by
  set e : ℂ := Complex.exp (θ * Complex.I) with he
  have hne : ‖e‖ = 1 := by rw [he, Complex.norm_exp_ofReal_mul_I]
  set f : ℝ → ℝ := fun r => r ^ 2 * u (r * e) ^ 2 with hf
  set f' : ℝ → ℝ := fun r => 2 * r * u (r * e) ^ 2 +
    r ^ 2 * (2 * u (r * e) * fderiv ℝ u (r * e) e) with hf'
  have hdiff : ∀ r : ℝ, HasDerivAt f (f' r) r := by
    intro r
    have hγ : HasDerivAt (fun r : ℝ => (r : ℂ) * e) e r := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const e)
    have hu' : HasDerivAt (fun r : ℝ => u (r * e)) (fderiv ℝ u (r * e) e) r := by
      have := (hu.differentiable one_ne_zero (r * e)).hasFDerivAt.comp_hasDerivAt r hγ
      convert! this using 1 <;> rfl
    have h2 := (hu'.pow 2)
    have h3 := (hasDerivAt_pow 2 r).mul h2
    convert h3 using 1
    simp [hf']
  have hcont_f' : Continuous f' := by
    have h1 : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
    have hc : Continuous fun r : ℝ => (r : ℂ) * e := by fun_prop
    have hcu : Continuous u := hu.continuous
    simp only [hf']
    have : Continuous fun r : ℝ => fderiv ℝ u (r * e) e :=
      (h1.comp hc).clm_apply continuous_const
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := 1)
    (fun r _ => hdiff r) (hcont_f'.intervalIntegrable 0 1)
  have hf1 : f 1 = u e ^ 2 := by simp [hf]
  have hf0 : f 0 = 0 := by simp [hf]
  rw [hf1, hf0, sub_zero] at hFTC
  rw [← hFTC]
  have hcd : Continuous fun r : ℝ => r * traceDensity u (r * e) := by
    have := continuous_traceDensity hu
    fun_prop
  refine intervalIntegral.integral_mono_on zero_le_one (hcont_f'.intervalIntegrable 0 1)
    (hcd.intervalIntegrable 0 1) (fun r hr => ?_)
  obtain ⟨hr0, hr1⟩ := hr
  simp only [hf', traceDensity]
  set a := u (r * e)
  set D := fderiv ℝ u (r * e) e
  set N := ‖fderiv ℝ u (r * e)‖
  have hD : |D| ≤ N := by
    have := (fderiv ℝ u (r * e)).le_opNorm e
    rw [hne, mul_one] at this
    simpa [Real.norm_eq_abs] using this
  have hN : 0 ≤ N := norm_nonneg _
  have hD2 : D ^ 2 ≤ N ^ 2 := by
    have := sq_abs D ▸ pow_le_pow_left₀ (abs_nonneg D) hD 2
    exact this
  have key : 2 * a * D ≤ a ^ 2 + N ^ 2 := by nlinarith [sq_nonneg (a - D)]
  have hr2 : r ^ 2 ≤ r := by nlinarith
  have hpos : 0 ≤ a ^ 2 + N ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key (sq_nonneg r), mul_le_mul_of_nonneg_right hr2 hpos]

/-- The integral of the ray integral over a full period. -/
lemma integral_rays_eq_disk {H : ℂ → ℝ} (hH : Continuous H) :
    ∫ θ in (0:ℝ)..(2 * π), ∫ r in (0:ℝ)..1, r * H (r * Complex.exp (θ * Complex.I)) =
      ∫ z in Metric.ball (0:ℂ) 1, H z := by
  set F : ℝ × ℝ → ℝ := fun p => p.1 * H (Complex.polarCoord.symm p) with hF
  have hFc : Continuous F := by
    simp only [hF, Complex.polarCoord_symm_apply]; fun_prop
  have hsymm : ∀ r θ : ℝ, Complex.polarCoord.symm (r, θ) = r * Complex.exp (θ * Complex.I) := by
    intro r θ
    rw [Complex.polarCoord_symm_apply, Complex.exp_mul_I, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin]
  set G : ℝ → ℝ := fun θ => ∫ r in (0:ℝ)..1, r * H (r * Complex.exp (θ * Complex.I)) with hG
  -- step 1: periodicity
  have hper : Function.Periodic G (2 * π) := by
    intro θ
    simp only [hG]
    congr 1; ext r
    congr 3
    rw [show ((θ + 2 * π : ℝ) : ℂ) * Complex.I = θ * Complex.I + 2 * π * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have h1 : ∫ θ in (0:ℝ)..(2 * π), G θ = ∫ θ in (-π)..π, G θ := by
    have := hper.intervalIntegral_add_eq 0 (-π)
    simpa [show -π + 2 * π = π by ring] using this
  -- step 2: Fubini on the rectangle
  have hint : IntegrableOn F (Ioo (0:ℝ) 1 ×ˢ Ioo (-π) π) := by
    have : IntegrableOn F (Icc (0:ℝ) 1 ×ˢ Icc (-π) π) :=
      hFc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact this.mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  have h2 : ∫ θ in (-π)..π, G θ = ∫ p in Ioo (0:ℝ) 1 ×ˢ Ioo (-π) π, F p := by
    rw [Measure.volume_eq_prod, setIntegral_prod _ hint,
      intervalIntegral.integral_of_le (by linarith [pi_pos]), integral_Ioc_eq_integral_Ioo]
    rw [integral_integral_swap]
    · refine setIntegral_congr_fun measurableSet_Ioo (fun θ _ => ?_)
      simp only [hG]
      rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
      refine setIntegral_congr_fun measurableSet_Ioo (fun r _ => ?_)
      simp only [hF, hsymm]
    · rw [Measure.prod_restrict]
      exact hint
  -- step 3: polar coordinates
  have h3 : ∫ p in Ioo (0:ℝ) 1 ×ˢ Ioo (-π) π, F p =
      ∫ z in Metric.ball (0:ℂ) 1, H z := by
    rw [← integral_indicator Metric.isOpen_ball.measurableSet,
      ← Complex.integral_comp_polarCoord_symm]
    have hsub : Ioo (0:ℝ) 1 ×ˢ Ioo (-π) π ⊆ polarCoord.target := by
      rw [polarCoord_target]
      exact prod_mono Ioo_subset_Ioi_self subset_rfl
    rw [← integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
    rw [← integral_indicator polarCoord.open_target.measurableSet]
    congr 1; ext p
    by_cases hp : p ∈ polarCoord.target
    · rw [indicator_of_mem hp]
      rw [polarCoord_target] at hp
      obtain ⟨hp1, hp2⟩ := hp
      have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
        rw [Complex.norm_polarCoord_symm, abs_of_pos hp1]
      by_cases h1 : p.1 < 1
      · have hm : p ∈ Ioo (0:ℝ) 1 ×ˢ Ioo (-π) π := ⟨⟨hp1, h1⟩, hp2⟩
        have hb : Complex.polarCoord.symm p ∈ Metric.ball (0:ℂ) 1 := by
          rw [mem_ball_zero_iff, hn]; exact h1
        rw [indicator_of_mem hm, indicator_of_mem hb]
        simp [hF, smul_eq_mul]
      · have hm : p ∉ Ioo (0:ℝ) 1 ×ˢ Ioo (-π) π := fun h => h1 h.1.2
        have hb : Complex.polarCoord.symm p ∉ Metric.ball (0:ℂ) 1 := by
          rw [mem_ball_zero_iff, hn]; exact h1
        rw [indicator_of_notMem hm, indicator_of_notMem hb, smul_zero]
    · rw [indicator_of_notMem hp, indicator_of_notMem (fun h => hp (hsub h))]
  rw [h1, h2, h3]

/-- **Trace inequality on the unit disk** (for `C¹` functions on the plane). -/
theorem trace_ineq {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) :
    ∫ t in (0:ℝ)..(2 * π), u (Complex.exp (t * Complex.I)) ^ 2 ≤
      ∫ z in Metric.ball (0:ℂ) 1, traceDensity u z := by
  rw [← integral_rays_eq_disk (continuous_traceDensity hu)]
  have hcu : Continuous u := hu.continuous
  refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ (fun θ _ => ray_estimate hu θ)
  · exact (by fun_prop : Continuous fun t : ℝ => u (Complex.exp (t * Complex.I)) ^ 2)
      |>.intervalIntegrable _ _
  · refine Continuous.intervalIntegrable ?_ _ _
    have hc := continuous_traceDensity hu
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop) 0 1

end SteklovH1
