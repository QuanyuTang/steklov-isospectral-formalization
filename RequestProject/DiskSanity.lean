module

public import RequestProject.Defs

/-!
# Sanity check: the unit disk satisfies the regularity predicates of Theorem 1.1.2 (i)

This shows that the predicates `IsDomain`, `SimplyConnectedSpace`, `IsStrictlyConvexDomain`,
`IsRealAnalyticJordanBoundary` used in `MainTheorem` are satisfiable by the expected model
example (the limit domain of the construction), so conclusion (i) is not vacuous or
unsatisfiable by design.  The identity map is also a normalized conformal map of `𝔻` onto
itself in the sense of `IsNormalizedConformalMap`.
-/

@[expose] public section

open Set Metric Complex PlaneDomain

namespace SteklovSanity

theorem unitDisk_isDomain : IsDomain (ball (0 : ℂ) 1) :=
  ⟨isOpen_ball, (convex_ball (0 : ℂ) 1).isConnected ⟨0, mem_ball_self one_pos⟩⟩

theorem unitDisk_simplyConnected : SimplyConnectedSpace (ball (0 : ℂ) 1) := by
  haveI := (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, mem_ball_self one_pos⟩
  exact SimplyConnectedSpace.ofContractible _

theorem unitDisk_strictlyConvex : IsStrictlyConvexDomain (ball (0 : ℂ) 1) := by
  unfold IsStrictlyConvexDomain
  rw [closure_ball (0 : ℂ) one_ne_zero]
  exact strictConvex_closedBall ℝ 0 1

theorem unitDisk_realAnalyticJordan : IsRealAnalyticJordanBoundary (ball (0 : ℂ) 1) := by
  refine ⟨fun t : ℝ => exp (t * I), ?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    have h1 : AnalyticAt ℝ (fun t : ℝ => (t : ℂ) * I) t :=
      ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
    have h2 : AnalyticAt ℝ exp ((t : ℂ) * I) :=
      (analyticOnNhd_cexp _ (mem_univ _)).restrictScalars
    exact h2.comp (f := fun t : ℝ => (t : ℂ) * I) h1
  · intro t
    simp only [ofReal_add, ofReal_mul, ofReal_ofNat, add_mul]
    rw [exp_add]
    have : exp (2 * (Real.pi : ℂ) * I) = 1 := exp_two_pi_mul_I
    rw [this, mul_one]
  · intro s hs t ht hst
    simp only at hst
    obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.1 hst
    have hk' : s = t + k * (2 * Real.pi) := by
      have := congrArg Complex.im hk
      simp at this
      linarith
    have hk0 : k = 0 := by
      have hpi := Real.pi_pos
      obtain ⟨hs0, hs1⟩ := hs
      obtain ⟨ht0, ht1⟩ := ht
      have h1 : (k : ℝ) * (2 * Real.pi) < 2 * Real.pi := by linarith
      have h2 : -(2 * Real.pi) < (k : ℝ) * (2 * Real.pi) := by linarith
      have h3 : (k : ℝ) < 1 := by nlinarith
      have h4 : (-1 : ℝ) < k := by nlinarith
      have : k < 1 := by exact_mod_cast h3
      have : -1 < k := by exact_mod_cast h4
      omega
    rw [hk', hk0]; simp
  · intro t
    have : HasDerivAt (fun s : ℝ => exp (s * I)) (I * exp (t * I)) t := by
      have := ((hasDerivAt_id (t : ℂ)).mul_const I).cexp.comp_ofReal
      simpa [mul_comm] using this
    rw [this.deriv]
    exact mul_ne_zero I_ne_zero (exp_ne_zero _)
  · rw [frontier_ball (0 : ℂ) one_ne_zero]
    ext z
    simp only [mem_range, mem_sphere, dist_zero_right]
    constructor
    · rintro ⟨t, rfl⟩; exact norm_exp_ofReal_mul_I t
    · intro hz
      refine ⟨arg z, ?_⟩
      have := norm_mul_exp_arg_mul_I z
      rw [hz] at this
      simpa using this

theorem id_isNormalizedConformalMap : IsNormalizedConformalMap id (ball (0 : ℂ) 1) := by
  refine ⟨⟨univ, isOpen_univ, subset_univ _, differentiableOn_id⟩, injOn_id _, image_id _,
    rfl, ?_, ?_⟩ <;> simp

end SteklovSanity
