module

public import Mathlib

/-!
# Primitives, logarithms and square roots on star-shaped domains

For an open set `U ⊆ ℂ`, star-shaped with respect to `0`, and `h` holomorphic on `U`, the function
`G(z) = ∫₀¹ z h(tz) dt` is a primitive of `h` on `U` (differentiation under the integral sign and
`d/dt (t h(tz)) = h(tz) + tz h'(tz)`).  Consequently every zero-free holomorphic function on `U`
has a holomorphic logarithm and a holomorphic square root.
-/

@[expose] public section

open Set Filter Topology Metric MeasureTheory intervalIntegral

noncomputable section

namespace SteklovRiemann

variable {U : Set ℂ}

lemma starConvex_smul_mem (hs : StarConvex ℝ 0 U) {z : ℂ} (hz : z ∈ U) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : (t : ℂ) * z ∈ U := by
  have := hs hz (sub_nonneg.2 ht1) ht0 (by ring)
  simpa [Complex.real_smul] using this

/-- The radial integral `∫₀¹ z h(tz) dt`. -/
def radialPrimitive (h : ℂ → ℂ) (z : ℂ) : ℂ := ∫ t in (0 : ℝ)..1, z * h (t * z)

/-- **Primitive on a star-shaped domain.** -/
theorem hasDerivAt_radialPrimitive (hU : IsOpen U) (hs : StarConvex ℝ 0 U) {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    HasDerivAt (radialPrimitive h) (h z₀) z₀ := by
  -- compact neighbourhood of the segment `[0, z₀]`
  set K : Set ℂ := (fun t : ℝ => (t : ℂ) * z₀) '' Icc 0 1 with hK
  have hKc : IsCompact K := (isCompact_Icc).image (by fun_prop)
  have hKU : K ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩; exact starConvex_smul_mem hs hz₀ ht.1 ht.2
  obtain ⟨δ, hδ, hδU⟩ := hKc.exists_thickening_subset_open hU hKU
  set K' := cthickening (δ / 2) K with hK'
  have hK'c : IsCompact K' := hKc.cthickening
  have hK'U : K' ⊆ U := (cthickening_subset_thickening' hδ (by linarith) K).trans hδU
  have hh' : DifferentiableOn ℂ (deriv h) U := hh.deriv hU
  obtain ⟨C₁, hC₁⟩ := hK'c.exists_bound_of_continuousOn (hh.continuousOn.mono hK'U)
  obtain ⟨C₂, hC₂⟩ := hK'c.exists_bound_of_continuousOn (hh'.continuousOn.mono hK'U)
  have hmem : ∀ x ∈ ball z₀ (δ / 2), ∀ t ∈ Icc (0 : ℝ) 1, (t : ℂ) * x ∈ K' := by
    intro x hx t ht
    refine mem_cthickening_of_dist_le _ ((t : ℂ) * z₀) _ _ ⟨t, ht, rfl⟩ ?_
    rw [dist_eq_norm, ← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ht.1]
    have := mem_ball.1 hx; rw [dist_eq_norm] at this
    calc t * ‖x - z₀‖ ≤ 1 * ‖x - z₀‖ := by gcongr; exact ht.2
      _ ≤ δ / 2 := by linarith
  have hdiffAt : ∀ w ∈ U, HasDerivAt h (deriv h w) w := fun w hw =>
    (hh.differentiableAt (hU.mem_nhds hw)).hasDerivAt
  set F : ℂ → ℝ → ℂ := fun x t => x * h (t * x) with hF
  set F' : ℂ → ℝ → ℂ := fun x t => h (t * x) + x * (t * deriv h (t * x)) with hF'
  have hcontF : ∀ x ∈ ball z₀ (δ / 2), ContinuousOn (F x) (Icc 0 1) := by
    intro x hx
    refine continuousOn_const.mul ?_
    refine (hh.continuousOn.mono hK'U).comp (by fun_prop) (fun t ht => hmem x hx t ht)
  have hcontF' : ∀ x ∈ ball z₀ (δ / 2), ContinuousOn (F' x) (Icc 0 1) := by
    intro x hx
    refine ContinuousOn.add ?_ (continuousOn_const.mul ?_)
    · exact (hh.continuousOn.mono hK'U).comp (by fun_prop) (fun t ht => hmem x hx t ht)
    · refine (Complex.continuous_ofReal.continuousOn).mul ?_
      exact (hh'.continuousOn.mono hK'U).comp (by fun_prop) (fun t ht => hmem x hx t ht)
  have hz₀b : z₀ ∈ ball z₀ (δ / 2) := mem_ball_self (by linarith)
  have hIoc : uIoc (0 : ℝ) 1 ⊆ Icc 0 1 := by
    rw [uIoc_of_le zero_le_one]; exact Ioc_subset_Icc_self
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := 0) (b := 1) (F := F) (F' := F') (x₀ := z₀)
    (bound := fun _ => C₁ + (‖z₀‖ + δ) * C₂) (ball_mem_nhds z₀ (by linarith : (0:ℝ) < δ / 2))
    (by
      filter_upwards [ball_mem_nhds z₀ (by linarith : (0:ℝ) < δ / 2)] with x hx
      exact ((hcontF x hx).mono hIoc).aestronglyMeasurable measurableSet_uIoc)
    ((hcontF z₀ hz₀b).intervalIntegrable_of_Icc zero_le_one)
    (((hcontF' z₀ hz₀b).mono hIoc).aestronglyMeasurable measurableSet_uIoc)
    (by
      refine Filter.Eventually.of_forall fun t ht x hx => ?_
      have ht' := hIoc ht
      have hm := hmem x hx t ht'
      simp only [hF']
      have hx' : ‖x‖ ≤ ‖z₀‖ + δ := by
        have := mem_ball.1 hx; rw [dist_eq_norm] at this
        have := norm_le_norm_add_norm_sub' x z₀
        linarith
      have htn : ‖(t : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht'.1]; exact ht'.2
      have hC₂0 : 0 ≤ C₂ := (norm_nonneg _).trans (hC₂ _ hm)
      calc ‖h (t * x) + x * (t * deriv h (t * x))‖
          ≤ ‖h (t * x)‖ + ‖x‖ * (‖(t : ℂ)‖ * ‖deriv h (t * x)‖) := by
            refine (norm_add_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ C₁ + (‖z₀‖ + δ) * (1 * C₂) := by
            have h1 := hC₁ _ hm
            have h2 := hC₂ _ hm
            have h3 : ‖(t : ℂ)‖ * ‖deriv h (t * x)‖ ≤ 1 * C₂ :=
              mul_le_mul htn h2 (norm_nonneg _) zero_le_one
            have h4 : ‖x‖ * (‖(t : ℂ)‖ * ‖deriv h (t * x)‖) ≤ (‖z₀‖ + δ) * (1 * C₂) :=
              mul_le_mul hx' h3 (by positivity) ((norm_nonneg _).trans hx')
            linarith
        _ = C₁ + (‖z₀‖ + δ) * C₂ := by ring)
    _root_.intervalIntegrable_const
    (by
      refine Filter.Eventually.of_forall fun t ht x hx => ?_
      have ht' := hIoc ht
      have hm := hK'U (hmem x hx t ht')
      have h1 : HasDerivAt (fun x : ℂ => (t : ℂ) * x) (t : ℂ) x := by
        simpa using (hasDerivAt_id x).const_mul (t : ℂ)
      have h2 := (hdiffAt _ hm).comp x h1
      have h3 := (hasDerivAt_id x).mul h2
      simp only [hF, hF']
      convert! h3 using 1
      simp only [Function.comp, id]; ring)
  -- evaluate the integral of the derivative
  have hval : ∫ t in (0 : ℝ)..1, F' z₀ t = h z₀ := by
    have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
        HasDerivAt (fun t : ℝ => (t : ℂ) * h (t * z₀)) (F' z₀ t) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      have hm := hKU ⟨t, ht, rfl⟩
      have h1 : HasDerivAt (fun w : ℂ => w * h (w * z₀))
          (1 * h (t * z₀) + t * (deriv h (t * z₀) * z₀)) (t : ℂ) := by
        refine (hasDerivAt_id (t : ℂ)).mul ?_
        have := (hdiffAt _ hm).comp (t : ℂ) (hasDerivAt_mul_const z₀)
        convert! this using 1 <;> first | rfl | simp
      have h2 := h1.comp_ofReal
      convert! h2 using 1
      simp only [hF']; ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((hcontF' z₀ hz₀b).intervalIntegrable_of_Icc zero_le_one)]
    simp
  have := key.2
  rw [hval] at this
  exact this

/-- **Holomorphic logarithm on a star-shaped domain.** -/
theorem exists_log_of_starConvex (hU : IsOpen U) (hs : StarConvex ℝ 0 U) (h0 : (0 : ℂ) ∈ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf0 : ∀ z ∈ U, f z ≠ 0) :
    ∃ L : ℂ → ℂ, DifferentiableOn ℂ L U ∧ ∀ z ∈ U, Complex.exp (L z) = f z := by
  set G := radialPrimitive (fun z => deriv f z / f z) with hG
  have hq : DifferentiableOn ℂ (fun z => deriv f z / f z) U := (hf.deriv hU).div hf hf0
  have hGd : ∀ z ∈ U, HasDerivAt G (deriv f z / f z) z := fun z hz =>
    hasDerivAt_radialPrimitive hU hs hq hz
  have hfd : ∀ z ∈ U, HasDerivAt f (deriv f z) z := fun z hz =>
    (hf.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  set E : ℂ → ℂ := fun z => f z * Complex.exp (-G z) with hE
  have hEd : ∀ z ∈ U, HasDerivAt E 0 z := by
    intro z hz
    have := (hfd z hz).mul ((hGd z hz).neg.cexp)
    convert! this using 1
    field_simp [hf0 z hz]
    ring
  have hEconst : ∀ z ∈ U, E z = E 0 := by
    intro z hz
    refine hU.is_const_of_deriv_eq_zero ((hs.isPathConnected h0).isConnected.isPreconnected)
      (fun w hw => (hEd w hw).differentiableAt.differentiableWithinAt) (fun w hw => ?_) hz h0
    exact (hEd w hw).deriv
  have hE0 : E 0 ≠ 0 := mul_ne_zero (hf0 0 h0) (Complex.exp_ne_zero _)
  refine ⟨fun z => G z + Complex.log (E 0), ?_, ?_⟩
  · exact (fun z hz => (hGd z hz).differentiableAt.differentiableWithinAt.add_const _)
  · intro z hz
    rw [Complex.exp_add, Complex.exp_log hE0, ← hEconst z hz, hE]
    simp only
    rw [mul_left_comm, ← Complex.exp_add]
    simp

/-- **Holomorphic square root on a star-shaped domain.** -/
theorem exists_sqrt_of_starConvex (hU : IsOpen U) (hs : StarConvex ℝ 0 U) (h0 : (0 : ℂ) ∈ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf0 : ∀ z ∈ U, f z ≠ 0) :
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, g z ^ 2 = f z := by
  obtain ⟨L, hL, hLe⟩ := exists_log_of_starConvex hU hs h0 hf hf0
  refine ⟨fun z => Complex.exp (L z / 2), ?_, fun z hz => ?_⟩
  · exact (hL.div_const 2).cexp
  · rw [← Complex.exp_nat_mul, ← hLe z hz]; congr 1; push_cast; ring

end SteklovRiemann
