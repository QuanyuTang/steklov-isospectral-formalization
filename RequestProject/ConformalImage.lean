module

public import RequestProject.ConformalPullback

/-!
# Topological and boundary-regularity properties of `F(𝔻)` (towards conclusion (i))

For `F` holomorphic on a neighbourhood of `𝔻̄`, injective on `𝔻̄`, with `F' ≠ 0` on `𝕋`, the
domain `Ω = F(𝔻)` is a bounded, simply connected domain whose boundary is a real-analytic Jordan
curve.  (Strict convexity is *not* claimed here; it needs a curvature argument.)
-/

@[expose] public section

open Set Filter Topology Metric PlaneDomain
open scoped Real

noncomputable section

namespace ConformalImage

variable {F : ℂ → ℂ} {U : Set ℂ}

theorem isDomain_image_ball (hcb : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U)
    (hinj : InjOn F (closedBall 0 1)) : IsDomain (F '' ball 0 1) := by
  refine ⟨HolInv.isOpen_image (hF.mono (ball_subset_closedBall.trans hcb))
    (hinj.mono ball_subset_closedBall) subset_rfl isOpen_ball, ?_⟩
  exact (isConnected_ball one_pos).image _
    (hF.continuousOn.mono (ball_subset_closedBall.trans hcb))

theorem isBounded_image_ball (hcb : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U) :
    Bornology.IsBounded (F '' ball 0 1) :=
  ((isCompact_closedBall 0 1).image_of_continuousOn (hF.continuousOn.mono hcb)).isBounded.subset
    (image_mono ball_subset_closedBall)

/-- `F` restricts to a homeomorphism `𝔻 ≃ₜ F(𝔻)`. -/
def homeomorphBall (hcb : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U)
    (hinj : InjOn F (closedBall 0 1)) : ball (0 : ℂ) 1 ≃ₜ F '' ball 0 1 := by
  refine (Equiv.Set.imageOfInjOn F _ (hinj.mono ball_subset_closedBall)).toHomeomorphOfContinuousOpen
    ?_ ?_
  · exact ((hF.continuousOn.mono (ball_subset_closedBall.trans hcb)).restrict).subtype_mk _
  · intro s hs
    obtain ⟨O, hO, rfl⟩ := isOpen_induced_iff.1 hs
    have hopen : IsOpen (F '' (O ∩ ball 0 1)) :=
      HolInv.isOpen_image (hF.mono (ball_subset_closedBall.trans hcb))
        (hinj.mono ball_subset_closedBall) inter_subset_right (hO.inter isOpen_ball)
    refine isOpen_induced_iff.2 ⟨_, hopen, ?_⟩
    ext ⟨w, x, hx, rfl⟩
    simp only [mem_preimage, mem_image, Subtype.exists, Equiv.Set.imageOfInjOn, Equiv.coe_fn_mk,
      Subtype.mk.injEq]
    constructor
    · rintro ⟨y, ⟨hyO, hy⟩, hyx⟩
      have := (hinj.mono ball_subset_closedBall) hy hx hyx
      subst this
      exact ⟨y, hy, hyO, rfl⟩
    · rintro ⟨y, hy, hyO, hyx⟩
      exact ⟨y, ⟨hyO, hy⟩, hyx⟩

theorem simplyConnected_image_ball (hcb : closedBall (0 : ℂ) 1 ⊆ U)
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F (closedBall 0 1)) :
    SimplyConnectedSpace (F '' ball 0 1) := by
  haveI := (convex_ball (0 : ℂ) 1).contractibleSpace ⟨0, mem_ball_self one_pos⟩
  haveI : SimplyConnectedSpace (ball (0 : ℂ) 1) := SimplyConnectedSpace.ofContractible _
  exact (homeomorphBall hcb hF hinj).symm.toHomotopyEquiv.simplyConnectedSpace

/-- The boundary of `F(𝔻)` is a real-analytic Jordan curve. -/
theorem realAnalyticJordan_image_ball (hU : IsOpen U) (hcb : closedBall (0 : ℂ) 1 ⊆ U)
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F (closedBall 0 1))
    (hF' : ∀ z ∈ sphere (0 : ℂ) 1, deriv F z ≠ 0) :
    IsRealAnalyticJordanBoundary (F '' ball 0 1) := by
  set c := circleMap (0 : ℂ) 1
  have hc : ∀ t : ℝ, c t = Complex.exp (t * Complex.I) := fun t => by simp [c, circleMap]
  have hsph : ∀ t, c t ∈ sphere (0 : ℂ) 1 := fun t => by
    rw [mem_sphere_zero_iff_norm]; simp [c]
  have hU' : ∀ t, c t ∈ U := fun t => hcb (sphere_subset_closedBall (hsph t))
  refine ⟨F ∘ c, ?_, ?_, ?_, ?_, ?_⟩
  · intro t _
    have hFa : AnalyticAt ℂ F (c t) := hF.analyticOnNhd hU _ (hU' t)
    have hca : AnalyticAt ℝ c t := by
      have : c = fun s : ℝ => Complex.exp ((s : ℂ) * Complex.I) := funext hc
      rw [this]
      exact (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
        ((Complex.ofRealCLM.analyticAt t).mul analyticAt_const)
    exact (hFa.restrictScalars (𝕜 := ℝ)).comp hca
  · intro t
    exact congrArg F (periodic_circleMap 0 1 t)
  · have := injOn_circleMap_of_abs_sub_le' (a := 0) (b := 2 * π) (c := 0) (R := 1) one_ne_zero
      (by simp)
    exact hinj.comp this fun t _ => sphere_subset_closedBall (hsph t)
  · intro t
    rw [((hF.differentiableAt (hU.mem_nhds (hU' t))).hasDerivAt.comp t
      (hasDerivAt_circleMap 0 1 t)).deriv]
    refine mul_ne_zero (hF' _ (hsph t)) (mul_ne_zero ?_ Complex.I_ne_zero)
    intro h0
    have := hsph t
    rw [show c t = 0 from h0, mem_sphere_zero_iff_norm, norm_zero] at this
    exact zero_ne_one this
  · rw [ConformalPullback.frontier_image_ball hcb hF hinj, range_comp,
      ← (periodic_circleMap 0 1).image_Ioc Real.two_pi_pos 0, zero_add, image_circleMap_Ioc,
      abs_one]

end ConformalImage
