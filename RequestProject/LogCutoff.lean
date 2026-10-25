module

public import Mathlib

/-!
# Logarithmic cut-off functions (capacity of a point in the plane)

For `0 < r < 1` and a centre `s ∈ ℂ`, `logCut s r` is a `C^∞` function on the plane with
`0 ≤ logCut s r ≤ 1`, equal to `1` on `‖z - s‖ ≤ r²` and to `0` on `‖z - s‖ ≥ r`, and with
Dirichlet energy `∫ |∇ logCut s r|² ≤ C / |log r|` for a constant `C` independent of `r` and `s`.
Hence the energy tends to `0` as `r → 0⁺`: a point has zero capacity in dimension two.
This is the analytic fact behind the removal of interior branch (cone) points.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace SteklovBranch

/-- The logarithmic cut-off centred at `s` with parameter `r`. -/
def logCut (s : ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  if ‖z - s‖ ≤ r ^ 2 then 1
  else smoothTransition (Real.log (‖z - s‖ ^ 2) * (2 * Real.log r)⁻¹ - 1)

/-- The formula used away from the centre. -/
def logCutFormula (s : ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  smoothTransition (Real.log (‖z - s‖ ^ 2) * (2 * Real.log r)⁻¹ - 1)

theorem log_sq_mul_inv (x r : ℝ) :
    Real.log (x ^ 2) * (2 * Real.log r)⁻¹ = Real.log x / Real.log r := by
  rw [Real.log_pow]; push_cast
  by_cases h : Real.log r = 0
  · simp [h]
  · field_simp

variable {s : ℂ} {r : ℝ}

theorem logCut_eq_formula (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : z ≠ s) :
    logCut s r z = logCutFormula s r z := by
  unfold logCut logCutFormula
  rw [log_sq_mul_inv]
  split_ifs with h
  · symm
    apply smoothTransition.one_of_one_le
    have hpos : 0 < ‖z - s‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
    have hlr : Real.log r < 0 := Real.log_neg hr0 hr1
    have : Real.log ‖z - s‖ ≤ 2 * Real.log r := by
      rw [← Real.log_rpow hr0]
      exact Real.log_le_log hpos (by simpa using h)
    rw [le_sub_iff_add_le, le_div_iff_of_neg hlr]
    linarith
  · rfl

theorem logCut_nonneg (z : ℂ) : 0 ≤ logCut s r z := by
  unfold logCut; split_ifs
  · exact zero_le_one
  · exact smoothTransition.nonneg _

theorem logCut_le_one (z : ℂ) : logCut s r z ≤ 1 := by
  unfold logCut; split_ifs
  · exact le_rfl
  · exact smoothTransition.le_one _

theorem logCut_eq_zero (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : r ≤ ‖z - s‖) :
    logCut s r z = 0 := by
  have hne : z ≠ s := by
    rintro rfl; simp at hz; linarith
  rw [logCut_eq_formula hr0 hr1 hne, logCutFormula, log_sq_mul_inv]
  apply smoothTransition.zero_of_nonpos
  have hlr : Real.log r < 0 := Real.log_neg hr0 hr1
  have : Real.log r ≤ Real.log ‖z - s‖ := Real.log_le_log hr0 hz
  rw [sub_nonpos, div_le_iff_of_neg hlr]
  linarith

theorem logCut_eq_one {z : ℂ} (hz : ‖z - s‖ ≤ r ^ 2) : logCut s r z = 1 := by
  simp [logCut, hz]

theorem contDiffAt_logCutFormula {z : ℂ} (hz : z ≠ s) :
    ContDiffAt ℝ ∞ (logCutFormula s r) z := by
  have hpos : 0 < ‖z - s‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have h1 : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w - s‖ ^ 2) z :=
    ((contDiffAt_norm ℝ (sub_ne_zero.2 hz)).comp z ((contDiffAt_id).sub contDiffAt_const)).pow 2
  have h2 : ContDiffAt ℝ ∞ (fun w : ℂ => Real.log (‖w - s‖ ^ 2)) z :=
    (Real.contDiffAt_log.2 (by positivity)).comp (f := fun w : ℂ => ‖w - s‖ ^ 2) z h1
  exact (smoothTransition.contDiff (n := ⊤)).contDiffAt.comp z
    ((h2.mul contDiffAt_const).sub contDiffAt_const)

theorem contDiff_logCut (hr0 : 0 < r) (hr1 : r < 1) : ContDiff ℝ ∞ (logCut s r) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = s
  · subst hz
    have : logCut z r =ᶠ[𝓝 z] fun _ => 1 := by
      have hball : Metric.ball z (r ^ 2) ∈ 𝓝 z := Metric.ball_mem_nhds _ (by positivity)
      filter_upwards [hball] with w hw
      exact logCut_eq_one (by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw.le)
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have : logCut s r =ᶠ[𝓝 z] logCutFormula s r := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact logCut_eq_formula hr0 hr1 hw
    exact (contDiffAt_logCutFormula hz).congr_of_eventuallyEq this

/-- A bound for the derivative of the smooth transition function, supported in `[0,1]`. -/
theorem exists_deriv_smoothTransition_bound :
    ∃ K, 0 ≤ K ∧ ∀ t, |deriv smoothTransition t| ≤ K * (Icc (0:ℝ) 1).indicator 1 t := by
  have hc : Continuous (deriv smoothTransition) :=
    (smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨K, hK⟩ :=
    (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max K 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Icc (0:ℝ) 1
  · simp only [indicator_of_mem ht, Pi.one_apply, mul_one]
    exact (hK t ht).trans (le_max_left _ _)
  · simp only [indicator_of_notMem ht, mul_zero, abs_nonpos_iff]
    rcases not_and_or.1 ht with h | h
    · push_neg at h
      have : smoothTransition =ᶠ[𝓝 t] fun _ => 0 := by
        filter_upwards [Iio_mem_nhds h] with x hx using smoothTransition.zero_of_nonpos hx.le
      rw [this.deriv_eq]; simp
    · push_neg at h
      have : smoothTransition =ᶠ[𝓝 t] fun _ => 1 := by
        filter_upwards [Ioi_mem_nhds h] with x hx using smoothTransition.one_of_one_le hx.le
      rw [this.deriv_eq]; simp

theorem norm_fderiv_logCutFormula_le {K : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hK0 : 0 ≤ K)
    (hK : ∀ t, |deriv smoothTransition t| ≤ K * (Icc (0:ℝ) 1).indicator 1 t) {z : ℂ}
    (hz : z ≠ s) :
    ‖fderiv ℝ (logCutFormula s r) z‖ ≤
      (Icc (r^2) r).indicator (fun t => K / (|Real.log r| * t)) ‖z - s‖ := by
  have hpos : 0 < ‖z - s‖ := norm_pos_iff.2 (sub_ne_zero.2 hz)
  have hlr : Real.log r < 0 := Real.log_neg hr0 hr1
  have h1 : HasFDerivAt (fun w : ℂ => ‖w - s‖ ^ 2) _ z := ((hasFDerivAt_id z).sub_const s).norm_sq
  have h2 := h1.log (by simpa using sub_ne_zero.2 hz)
  have h3 := (h2.mul_const (2 * Real.log r)⁻¹).sub_const 1
  have h4 := (((smoothTransition.contDiff (n := 1)).differentiable (by norm_num)).differentiableAt
    (x := Real.log (‖z - s‖ ^ 2) * (2 * Real.log r)⁻¹ - 1)).hasDerivAt.comp_hasFDerivAt z h3
  have h5 : HasFDerivAt (logCutFormula s r) _ z := h4
  rw [h5.fderiv]
  set φ := Real.log (‖z - s‖ ^ 2) * (2 * Real.log r)⁻¹ - 1 with hφ
  have hφ' : φ = Real.log ‖z - s‖ / Real.log r - 1 := by rw [hφ, log_sq_mul_inv]
  have hcomp : ‖(2:ℕ) • ((innerSL ℝ) (id z - s)).comp (ContinuousLinearMap.id ℝ ℂ)‖ ≤
      2 * ‖z - s‖ := by
    refine norm_nsmul_le.trans ?_
    rw [ContinuousLinearMap.comp_id, innerSL_apply_norm]; simp
  by_cases hm : ‖z - s‖ ∈ Icc (r^2) r
  · rw [indicator_of_mem hm]
    calc _ ≤ |deriv smoothTransition φ| *
          (|(2 * Real.log r)⁻¹| * ((‖z - s‖ ^ 2)⁻¹ * (2 * ‖z - s‖))) := by
          rw [norm_smul, norm_smul, norm_smul]
          simp only [Real.norm_eq_abs, abs_inv, abs_pow, abs_norm]
          gcongr
      _ ≤ K * (|(2 * Real.log r)⁻¹| * ((‖z - s‖ ^ 2)⁻¹ * (2 * ‖z - s‖))) := by
          gcongr
          refine (hK φ).trans ?_
          by_cases h : φ ∈ Icc (0:ℝ) 1 <;> simp [h, hK0]
      _ = K / (|Real.log r| * ‖z - s‖) := by
          rw [abs_inv, abs_mul]; simp; field_simp
  · rw [indicator_of_notMem hm]
    have hφn : φ ∉ Icc (0:ℝ) 1 := by
      intro hφm
      apply hm
      rw [hφ'] at hφm
      obtain ⟨ha, hb⟩ := hφm
      rw [sub_nonneg, le_div_iff_of_neg hlr] at ha
      rw [sub_le_iff_le_add, div_le_iff_of_neg hlr] at hb
      constructor
      · have : Real.log (r ^ 2) ≤ Real.log ‖z - s‖ := by rw [Real.log_pow]; push_cast; linarith
        exact (Real.log_le_log_iff (by positivity) hpos).1 this
      · exact (Real.log_le_log_iff hpos hr0).1 (by linarith)
    have h0 : deriv smoothTransition φ = 0 := by
      have := hK φ; rw [indicator_of_notMem hφn] at this; simpa using this
    simp [h0]

/-- Pointwise bound for the gradient of the logarithmic cut-off. -/
theorem norm_fderiv_logCut_le {K : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hK0 : 0 ≤ K)
    (hK : ∀ t, |deriv smoothTransition t| ≤ K * (Icc (0:ℝ) 1).indicator 1 t) (z : ℂ) :
    ‖fderiv ℝ (logCut s r) z‖ ≤
      (Icc (r^2) r).indicator (fun t => K / (|Real.log r| * t)) ‖z - s‖ := by
  by_cases hz : z = s
  · subst hz
    have : logCut z r =ᶠ[𝓝 z] fun _ => 1 := by
      have hball : Metric.ball z (r ^ 2) ∈ 𝓝 z := Metric.ball_mem_nhds _ (by positivity)
      filter_upwards [hball] with w hw
      exact logCut_eq_one (by rw [Metric.mem_ball, dist_eq_norm] at hw; exact hw.le)
    rw [this.fderiv_eq, fderiv_const_apply, norm_zero]
    apply indicator_nonneg
    intro t ht
    exact div_nonneg hK0 (mul_nonneg (abs_nonneg _) ((sq_nonneg r).trans ht.1))
  · have : logCut s r =ᶠ[𝓝 z] logCutFormula s r := by
      filter_upwards [isOpen_ne.mem_nhds hz] with w hw
      exact logCut_eq_formula hr0 hr1 hw
    rw [this.fderiv_eq]
    exact norm_fderiv_logCutFormula_le hr0 hr1 hK0 hK hz

theorem lintegral_Icc_div (c a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hc : 0 ≤ c) :
    ∫⁻ t in Icc a b, ENNReal.ofReal (c / t) = ENNReal.ofReal (c * Real.log (b / a)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
    simp_rw [div_eq_mul_inv]
    rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha (ha.trans_le hab),
      div_eq_mul_inv]
  · refine (ContinuousOn.integrableOn_Icc ?_)
    exact continuousOn_const.div continuousOn_id (fun t ht => (ha.trans_le ht.1).ne')
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact div_nonneg hc (ha.le.trans ht.1)

theorem lintegral_polarTarget_fst (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ p in polarCoord.target, f p.1 = (∫⁻ t in Ioi 0, f t) * ENNReal.ofReal (2 * π) := by
  rw [polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have := lintegral_prod_mul (μ := volume.restrict (Ioi (0:ℝ)))
    (ν := volume.restrict (Ioo (-π) π)) (f := f) (g := fun _ => 1) hf.aemeasurable
    aemeasurable_const
  simp only [mul_one] at this
  rw [this]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo, one_mul]
  congr 1; congr 1; ring

/-- Integral of a radial function over the plane. -/
theorem lintegral_radial (g : ℝ → ℝ≥0∞) (hg : Measurable g) (s : ℂ) :
    ∫⁻ z : ℂ, g ‖z - s‖ = (∫⁻ t in Ioi 0, ENNReal.ofReal t * g t) * ENNReal.ofReal (2 * π) := by
  have h1 : ∫⁻ z : ℂ, g ‖z - s‖ = ∫⁻ z : ℂ, g ‖z‖ := by
    have := lintegral_add_right_eq_self (μ := (volume : Measure ℂ)) (fun z => g ‖z - s‖) s
    simpa using this.symm
  rw [h1, ← Complex.lintegral_comp_polarCoord_symm]
  have h2 : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • g ‖Complex.polarCoord.symm p‖ =
      ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 * g p.1 := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
    rw [Complex.norm_polarCoord_symm, abs_of_pos (by rw [polarCoord_target] at hp; exact hp.1)]
    rfl
  rw [h2, lintegral_polarTarget_fst (fun t => ENNReal.ofReal t * g t)
    (ENNReal.measurable_ofReal.mul hg)]

/-- **Capacity estimate.** The Dirichlet energy of the logarithmic cut-off is at most
`2π K² / |log r|`, where `K` bounds the derivative of the smooth transition function. -/
theorem lintegral_fderiv_logCut_le {K : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hK0 : 0 ≤ K)
    (hK : ∀ t, |deriv smoothTransition t| ≤ K * (Icc (0:ℝ) 1).indicator 1 t) :
    ∫⁻ z, ‖fderiv ℝ (logCut s r) z‖ₑ ^ 2 ≤ ENNReal.ofReal (2 * π * K ^ 2 / |Real.log r|) := by
  have hlr : Real.log r < 0 := Real.log_neg hr0 hr1
  have hL : 0 < |Real.log r| := abs_pos.2 hlr.ne
  set g : ℝ → ℝ≥0∞ := (Icc (r^2) r).indicator
    (fun t => ENNReal.ofReal (K ^ 2 / (|Real.log r| ^ 2 * t ^ 2))) with hg
  have hgm : Measurable g := by
    refine Measurable.indicator ?_ measurableSet_Icc
    exact ENNReal.measurable_ofReal.comp (by fun_prop)
  have hpt : ∀ z, ‖fderiv ℝ (logCut s r) z‖ₑ ^ 2 ≤ g ‖z - s‖ := by
    intro z
    have hb := norm_fderiv_logCut_le (s := s) hr0 hr1 hK0 hK z
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    by_cases hm : ‖z - s‖ ∈ Icc (r^2) r
    · rw [indicator_of_mem hm] at hb
      rw [hg, indicator_of_mem hm]
      apply ENNReal.ofReal_le_ofReal
      calc ‖fderiv ℝ (logCut s r) z‖ ^ 2 ≤ (K / (|Real.log r| * ‖z - s‖)) ^ 2 := by
            gcongr
        _ = _ := by ring
    · rw [indicator_of_notMem hm] at hb
      have : ‖fderiv ℝ (logCut s r) z‖ = 0 := le_antisymm hb (norm_nonneg _)
      simp [this]
  calc ∫⁻ z, ‖fderiv ℝ (logCut s r) z‖ₑ ^ 2 ≤ ∫⁻ z, g ‖z - s‖ := lintegral_mono hpt
    _ = (∫⁻ t in Ioi 0, ENNReal.ofReal t * g t) * ENNReal.ofReal (2 * π) :=
        lintegral_radial g hgm s
    _ = ENNReal.ofReal (K ^ 2 / |Real.log r| ^ 2 * Real.log (r / r ^ 2)) *
          ENNReal.ofReal (2 * π) := by
        congr 1
        have hsub : Icc (r^2) r ⊆ Ioi 0 := fun t ht => (by positivity : (0:ℝ) < r^2).trans_le ht.1
        rw [← lintegral_Icc_div _ _ _ (by positivity) (by nlinarith) (by positivity)]
        rw [hg]
        simp_rw [← indicator_mul_right]
        rw [lintegral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
          inter_eq_left.2 hsub]
        refine setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
        have ht0 : 0 < t := (by positivity : (0:ℝ) < r^2).trans_le ht.1
        rw [← ENNReal.ofReal_mul ht0.le]
        congr 1
        field_simp
    _ = ENNReal.ofReal (2 * π * K ^ 2 / |Real.log r|) := by
        have hlog : 0 ≤ Real.log (r / r ^ 2) := by
          apply Real.log_nonneg; rw [le_div_iff₀ (by positivity)]; nlinarith
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have : Real.log (r / r ^ 2) = - Real.log r := by
          rw [Real.log_div hr0.ne' (by positivity), Real.log_pow]; push_cast; ring
        rw [this, abs_of_neg hlr]
        field_simp

end SteklovBranch
