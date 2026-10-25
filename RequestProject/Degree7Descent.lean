module

public import RequestProject.RegFillMetric
public import RequestProject.Degree7QuotientDisk

/-!
# Descent of the metric of `R̄` to the quotient disk coordinate

Let `Θ : (interior M_ε)/H ≃ₜ 𝔻` be the quotient-disk identification with `ψ (Θ [w]) = K (Ev w)` and
`B (Θ [w]) = b_ε w` (`quotient_interior_disk`), where `Ev : R̄ → ℂ` is holomorphic, `K` entire,
and `ψ` injective holomorphic on `𝔻`.  Write `Π = Θ ∘ [·]` for the quotient projection of
`interior M_ε` in the disk coordinate.

* `quotient_chart`: in every atlas chart `e` of `R̄` at a point of `interior M_ε`, `Π ∘ e⁻¹` agrees
  near the point with the **holomorphic** map `T = ψ⁻¹ ∘ K ∘ Ev ∘ e⁻¹`, and `b_ε ∘ e⁻¹ = B ∘ T`
  there.
* **`metric_descends`**: away from the cone points of the quotient orbisurface
  `pullbackOrb L hB`, the metric of `R̄` (`regMetric L e`, constructed on `R̄` itself) is the pull
  back by `T` of the metric of `pullbackOrb L hB`:
  `regMetric L e z = (pullbackOrb L hB).lam (T z) · |T'(z)|²`.
  So `pullbackOrb L hB` carries exactly the metric induced on the quotient by the deck-invariant
  metric of `R̄` (the descended metric is determined by this identity on the dense set of points
  where `T' ≠ 0`).
-/

@[expose] public section

open Polynomial Set Filter Topology Metric PolyCover LocalMonodromy SteklovRegularCover
  SteklovPunctured SteklovFill SteklovRiemann Manifold SteklovOrb SteklovCoalescence
  SteklovCritical
open scoped ContDiff

noncomputable section

namespace Degree7

variable {s : ℂ}

/-- The inverse of an injective holomorphic map of `𝔻` is holomorphic on the image. -/
lemma analyticAt_invFunOn_disk {ψ : ℂ → ℂ} (hψd : DifferentiableOn ℂ ψ (ball 0 1))
    (hψi : InjOn ψ (ball 0 1)) {p : ℂ} (hp : p ∈ ball (0 : ℂ) 1) :
    AnalyticAt ℂ (Function.invFunOn ψ (ball 0 1)) (ψ p) := by
  have hopen : IsOpen (ψ '' ball 0 1) := HolInv.isOpen_image hψd hψi subset_rfl isOpen_ball
  have hd : DifferentiableOn ℂ (Function.invFunOn ψ (ball 0 1)) (ψ '' ball 0 1) := by
    rintro _ ⟨q, hq, rfl⟩
    exact (HolInv.hasDerivAt_invFunOn isOpen_ball hψd hψi hq
      (HolInv.deriv_ne_zero_of_injOn isOpen_ball hψd hψi hq)).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (hopen.mem_nhds ⟨p, hp, rfl⟩)

variable {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {ε : ℝ} {H : Subgroup (deckGroup f₀)}
  {Ev : RegFill hs f₀ → ℂ} {K ψ B : ℂ → ℂ}

/-- **The quotient projection in charts is holomorphic.** -/
theorem quotient_chart
    (hEv : haveI := (regFill_riemannSurface hs f₀).2.1; ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev)
    (hK : Differentiable ℂ K) (hψd : DifferentiableOn ℂ ψ (ball 0 1)) (hψi : InjOn ψ (ball 0 1))
    (Θ : QuotOn hs f₀ (interior (bordered hs f₀ ε)) H ≃ₜ ball (0 : ℂ) 1)
    (hΘ : ∀ w, ψ (Θ (Quotient.mk _ w)) = K (Ev w) ∧ B (Θ (Quotient.mk _ w)) = bdf hs f₀ ε w)
    {e : OpenPartialHomeomorph (RegFill hs f₀) ℂ} (he : e ∈ atlas ℂ (RegFill hs f₀)) {z : ℂ}
    (hz : z ∈ e.target) (hzi : e.symm z ∈ interior (bordered hs f₀ ε)) :
    AnalyticAt ℂ (fun x => Function.invFunOn ψ (ball 0 1) (K (Ev (e.symm x)))) z ∧
      (∀ᶠ x in 𝓝 z, ∃ hx : e.symm x ∈ interior (bordered hs f₀ ε),
        (Θ (Quotient.mk _ ⟨e.symm x, hx⟩) : ℂ) =
          Function.invFunOn ψ (ball 0 1) (K (Ev (e.symm x)))) ∧
      (bdf hs f₀ ε ∘ e.symm) =ᶠ[𝓝 z]
        B ∘ fun x => Function.invFunOn ψ (ball 0 1) (K (Ev (e.symm x))) := by
  haveI := (regFill_riemannSurface hs f₀).2.1
  set T := fun x => Function.invFunOn ψ (ball 0 1) (K (Ev (e.symm x)))
  have hT_eq : ∀ x (hx : e.symm x ∈ interior (bordered hs f₀ ε)),
      T x = (Θ (Quotient.mk _ ⟨e.symm x, hx⟩) : ℂ) := by
    intro x hx
    show Function.invFunOn ψ (ball 0 1) (K (Ev (e.symm x))) = _
    rw [← (hΘ ⟨e.symm x, hx⟩).1]
    exact HolInv.invFunOn_apply_self hψi (Θ _).2
  have hev : ∀ᶠ x in 𝓝 z, e.symm x ∈ interior (bordered hs f₀ ε) :=
    (e.continuousAt_symm hz).preimage_mem_nhds (isOpen_interior.mem_nhds hzi)
  refine ⟨?_, ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun x => K (Ev (e.symm x))) z :=
      (hK.analyticAt _).comp (analyticAt_chart_fun hEv he hz)
    have h2 : K (Ev (e.symm z)) = ψ (Θ (Quotient.mk _ ⟨e.symm z, hzi⟩)) :=
      (hΘ ⟨e.symm z, hzi⟩).1.symm
    have h3 : AnalyticAt ℂ (Function.invFunOn ψ (ball 0 1)) (K (Ev (e.symm z))) := by
      rw [h2]; exact analyticAt_invFunOn_disk hψd hψi (Θ _).2
    exact AnalyticAt.comp (g := Function.invFunOn ψ (ball 0 1))
      (f := fun x => K (Ev (e.symm x))) h3 h1
  · filter_upwards [hev] with x hx using ⟨hx, (hT_eq x hx).symm⟩
  · filter_upwards [hev] with x hx
    show bdf hs f₀ ε (e.symm x) = B (T x)
    rw [hT_eq x hx]
    exact (hΘ ⟨e.symm x, hx⟩).2.symm

/-- **The metric of `R̄` descends to the metric of the quotient orbisurface.** -/
theorem metric_descends (h0 : 0 < ε) (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3)
    (hEv : haveI := (regFill_riemannSurface hs f₀).2.1; ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev)
    (hK : Differentiable ℂ K) (hψd : DifferentiableOn ℂ ψ (ball 0 1)) (hψi : InjOn ψ (ball 0 1))
    (Θ : QuotOn hs f₀ (interior (bordered hs f₀ ε)) H ≃ₜ ball (0 : ℂ) 1)
    (hΘ : ∀ w, ψ (Θ (Quotient.mk _ w)) = K (Ev w) ∧ B (Θ (Quotient.mk _ w)) = bdf hs f₀ ε w)
    {V : Set ℂ} (hB : IsBranchedDiskMap B V (ε : ℂ) (lamStar * ε) 2 3 L.U)
    {e : OpenPartialHomeomorph (RegFill hs f₀) ℂ} (he : e ∈ atlas ℂ (RegFill hs f₀)) {z : ℂ}
    (hz : z ∈ e.target) (hzi : e.symm z ∈ interior (bordered hs f₀ ε))
    (hcone : Function.invFunOn ψ (ball 0 1) (K (Ev (e.symm z))) ∉
      coneSet B V (ε : ℂ) (lamStar * ε)) :
    regMetric L e z = (pullbackOrb L hB).lam (Function.invFunOn ψ (ball 0 1) (K (Ev (e.symm z)))) *
      ‖deriv (fun x => Function.invFunOn ψ (ball 0 1) (K (Ev (e.symm x)))) z‖ ^ 2 := by
  haveI := (regFill_riemannSurface hs f₀).2.1
  obtain ⟨hTa, hTΘ, hF⟩ := quotient_chart hEv hK hψd hψi Θ hΘ he hz hzi
  set T := fun x => Function.invFunOn ψ (ball 0 1) (K (Ev (e.symm x)))
  have hzd : z ∈ chartDom L e :=
    ⟨hz, bordered_subset_metricDom L (interior_subset hzi)⟩
  have hloc := isLocalBranched_chart h0 L he
  -- `T` takes values in `𝔻 ⊆ V`
  have hTV : ∀ᶠ x in 𝓝 z, T x ∈ V := by
    filter_upwards [hTΘ] with x ⟨hx, hxe⟩
    show Function.invFunOn ψ (ball 0 1) (K (Ev (e.symm x))) ∈ V
    rw [← hxe]; exact hB.cb (ball_subset_closedBall (Θ _).2)
  have hTzV : T z ∈ V := hTV.self_of_nhds
  refine pullback_law hF hTa (hloc.smooth hzd).1.continuousAt
    (smooth_at_noncone hB hTzV hcone).1.continuousAt ?_
  filter_upwards [nhdsWithin_le_nhds (hloc.eventually_good hzd), self_mem_nhdsWithin,
    nhdsWithin_le_nhds hTV, nhdsWithin_le_nhds hF] with x hg hne hxV hFx
  obtain ⟨hxW, hxu, hxv⟩ := hg hne
  have hFx' : B (T x) = (bdf hs f₀ ε ∘ e.symm) x := hFx.symm
  refine ⟨hloc.pbLam_eq hxW hxu hxv, pbLam_eq hB hxV (by rw [hFx']; exact hxu)
    (by rw [hFx']; exact hxv), (hB.analytic _ hxV).differentiableAt⟩

end Degree7
