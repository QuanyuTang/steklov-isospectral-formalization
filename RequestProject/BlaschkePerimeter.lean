module

public import RequestProject.Blaschke

/-!
# Boundary length of a finite Blaschke product (the integral in (3.5) of the paper)

For a finite Blaschke product `B` of degree `n`,
`∫₀^{2π} |d/dt B(e^{it})| dt = 2π n`
(the argument of the boundary values increases by `2πn`).  This is the analytic identity behind
the perimeter formula `|∂Ω_{j,ε}| = ∫₀^{2π} |B'_{j,ε}(e^{it})| dt = 2πn` of §3.5.  The proof
computes `∫₀^{2π} (1 - |a|²)/|e^{it} - a|² dt = 2π` via the circle integral
`∮ ((z - a)⁻¹ + ā/(1 - ā z)) dz = 2πi`.

This module proves the analytic integral identity. The geometric bridge to
one-dimensional Hausdorff measure is developed separately in
`RequestProject.ArcLength` and `RequestProject.BoundaryLength`, and used by the
final family construction.
-/

@[expose] public section

open Complex Metric Set

noncomputable section

namespace SteklovBlaschke

/-- On the circle, `z ((z - a)⁻¹ + ā/(1 - ā z)) = (1 - |a|²)/|z - a|²`. -/
lemma circle_logDeriv_identity {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    z * ((z - a)⁻¹ + (starRingEnd ℂ) a / (1 - (starRingEnd ℂ) a * z)) = (bdens a z : ℂ) := by
  have hd := denom_ne_zero ha hz.le
  have hza : z - a ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; subst h; rw [hz] at ha; exact lt_irrefl _ ha
  have hn : (normSq (z - a) : ℂ) ≠ 0 := by exact_mod_cast (normSq_pos.2 hza).ne'
  have hzc : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, normSq_eq_norm_sq, hz]; norm_num
  have key : (z - a) * (1 - (starRingEnd ℂ) a * z) = z * (normSq (z - a) : ℂ) := by
    rw [← Complex.mul_conj (z - a), map_sub]
    linear_combination (-(z - a)) * hzc
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have e1 : (z - a)⁻¹ = (1 - (starRingEnd ℂ) a * z) / (z * (normSq (z - a) : ℂ)) := by
    rw [eq_div_iff (mul_ne_zero hz0 hn), ← key]; field_simp
  have e2 : (starRingEnd ℂ) a / (1 - (starRingEnd ℂ) a * z) =
      (starRingEnd ℂ) a * (z - a) / (z * (normSq (z - a) : ℂ)) := by
    rw [div_eq_div_iff hd (mul_ne_zero hz0 hn), ← key]; ring
  have hna : (normSq a : ℂ) = (starRingEnd ℂ) a * a := Complex.normSq_eq_conj_mul_self
  rw [e1, e2, bdens]
  push_cast
  rw [hna]
  field_simp
  ring

lemma continuous_bdens_circle {a : ℂ} (ha : ‖a‖ < 1) :
    Continuous fun t : ℝ => bdens a (exp (t * I)) := by
  unfold bdens
  refine continuous_const.div (Complex.continuous_normSq.comp
    ((by fun_prop : Continuous fun t : ℝ => exp (t * I)).sub continuous_const)) ?_
  intro t
  have hza : exp (t * I) - a ≠ 0 := by
    intro h; rw [sub_eq_zero] at h
    have := norm_exp_ofReal_mul_I t; rw [h] at this; rw [this] at ha; exact lt_irrefl _ ha
  exact (normSq_pos.2 hza).ne'

/-- `∫₀^{2π} (1 - |a|²)/|e^{it} - a|² dt = 2π` for `|a| < 1`. -/
theorem integral_bdens {a : ℂ} (ha : ‖a‖ < 1) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), bdens a (exp (t * I)) = 2 * Real.pi := by
  set F : ℂ → ℂ := fun z => (z - a)⁻¹ + (starRingEnd ℂ) a / (1 - (starRingEnd ℂ) a * z)
  have ha' : a ∈ ball (0 : ℂ) 1 := by rwa [mem_ball, dist_zero_right]
  have hg_cont : ContinuousOn (fun z : ℂ => (starRingEnd ℂ) a / (1 - (starRingEnd ℂ) a * z))
      (closedBall 0 1) := by
    refine continuousOn_const.div (by fun_prop) ?_
    intro z hz
    rw [mem_closedBall, dist_zero_right] at hz
    exact denom_ne_zero ha hz
  have h1 : ∮ z in C(0, 1), (z - a)⁻¹ = 2 * Real.pi * I :=
    circleIntegral.integral_sub_inv_of_mem_ball ha'
  have h2 : ∮ z in C(0, 1), (starRingEnd ℂ) a / (1 - (starRingEnd ℂ) a * z) = 0 := by
    refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable zero_le_one
      Set.countable_empty hg_cont ?_
    intro z hz
    rw [diff_empty, mem_ball, dist_zero_right] at hz
    exact (differentiableAt_const _).div (by fun_prop) (denom_ne_zero ha hz.le)
  have hF : ∮ z in C(0, 1), F z = 2 * Real.pi * I := by
    have hi1 : CircleIntegrable (fun z : ℂ => (z - a)⁻¹) 0 1 :=
      (circleIntegrable_sub_inv_iff.2 (Or.inr (by
        rw [abs_one, mem_sphere, dist_zero_right]; exact ha.ne)))
    have hi2 : CircleIntegrable (fun z : ℂ => (starRingEnd ℂ) a / (1 - (starRingEnd ℂ) a * z))
        0 1 :=
      (hg_cont.mono sphere_subset_closedBall).circleIntegrable zero_le_one
    rw [circleIntegral.integral_add hi1 hi2, h1, h2, add_zero]
  have hint : ∮ z in C(0, 1), F z =
      ∫ t in (0 : ℝ)..(2 * Real.pi), I * (bdens a (exp (t * I)) : ℂ) := by
    unfold circleIntegral
    refine intervalIntegral.integral_congr fun t _ => ?_
    have hc : circleMap 0 1 t = exp (t * I) := by simp [circleMap]
    simp only [deriv_circleMap, hc, smul_eq_mul]
    rw [← circle_logDeriv_identity ha (norm_exp_ofReal_mul_I t)]
    simp only [F]
    ring
  rw [hint, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal] at hF
  have := mul_left_cancel₀ I_ne_zero (hF.trans (mul_comm _ _))
  exact_mod_cast this

/-- **Boundary length of a finite Blaschke product.**  If `B` is a finite Blaschke product of
degree `n`, then `∫₀^{2π} |d/dt B(e^{it})| dt = 2πn`. -/
theorem integral_norm_deriv_blaschke {B : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), ‖deriv (fun s : ℝ => B (exp (s * I))) t‖ =
      2 * Real.pi * n := by
  obtain ⟨η, a, hη, ha, rfl⟩ := hB
  have hBA : BdryArg (fun z => η * ∏ l, bfac (a l) z) (fun z => ∑ l, bdens (a l) z) := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := bdryArg_prod Finset.univ a ha z hz
    refine ⟨by simp only at h1 ⊢; rw [norm_mul, hη, one_mul]; exact h1, h2, ?_⟩
    have := h3.const_mul η
    convert this using 1
    simp only
    ring
  simp_rw [norm_deriv_circle hBA]
  rw [intervalIntegral.integral_finset_sum (fun l _ =>
    (continuous_bdens_circle (ha l)).intervalIntegrable _ _)]
  simp_rw [integral_bdens (ha _)]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end SteklovBlaschke

end
