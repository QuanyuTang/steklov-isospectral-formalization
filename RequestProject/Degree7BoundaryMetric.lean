module

public import RequestProject.Degree7GeomLemmas

/-!
# The metric and the quotient map at the physical boundary `∂M_ε`

Let `Θ̄ : M_ε / H ≃ₜ closed 𝔻` be the closed quotient identification with `B ∘ Θ̄ = b_ε`
(`closed_quotient_disk`).  At a boundary point `w ∈ ∂M_ε` and an atlas chart `e` at `w`
(`boundary_metric`):

* the quotient map `x ↦ Θ̄[e⁻¹ x]` (defined on `e(M_ε)`) is the restriction of the holomorphic map
  `T = B_loc⁻¹ ∘ b_ε ∘ e⁻¹` defined on a full neighbourhood of `e w` (`B_loc⁻¹` a local inverse of
  `B` near the circle) — analytic compatibility across the boundary;
* `b_ε ∘ e⁻¹ = B ∘ T` near `e w`, and the metric of `R̄` is the pull-back of the metric of
  `pullbackOrb L hB` there: `λ_e(e w) = λ_X(T(e w)) |T'(e w)|²`;
* in the collar the metric of `R̄` is `|d b_ε|²`, and the **boundary line element** of the quotient
  orbisurface (`|B'|`, `lineDensity_pullbackOrb`) pulls back to `|d b_ε|`:
  `lineDensity_X(T(e w)) · |T'(e w)| = |(b_ε ∘ e⁻¹)'(e w)|`.
-/

@[expose] public section

open Polynomial Set Filter Topology Metric PolyCover LocalMonodromy SteklovRegularCover
  SteklovPunctured SteklovFill SteklovRiemann Manifold SteklovOrb SteklovCoalescence
  SteklovCritical
open scoped ContDiff

noncomputable section

namespace Degree7

variable {s : ℂ} {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {H : Subgroup (deckGroup f₀)}
  {ε : ℝ} {B : ℂ → ℂ}

lemma bdry_subset_bordered : borderedBdry hs f₀ ε ⊆ bordered hs f₀ ε := fun w hw => by
  rw [borderedBdry_eq] at hw; rw [bordered_eq]; exact le_of_eq hw

/-- **The quotient map and the metric at the boundary.** -/
theorem boundary_metric (h0 : 0 < ε) (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3)
    {V : Set ℂ} (hB : IsBranchedDiskMap B V (ε : ℂ) (lamStar * ε) 2 3 L.U)
    (Θc : QuotOn hs f₀ (bordered hs f₀ ε) H ≃ₜ closedBall (0 : ℂ) 1)
    (hΘB : ∀ w : bordered hs f₀ ε, B (Θc (Quotient.mk _ w)) = bdf hs f₀ ε w)
    (hΘS : ∀ w : bordered hs f₀ ε, (w : RegFill hs f₀) ∈ borderedBdry hs f₀ ε ↔
      (Θc (Quotient.mk _ w) : ℂ) ∈ sphere (0 : ℂ) 1)
    {w : RegFill hs f₀} (hw : w ∈ borderedBdry hs f₀ ε)
    {e : OpenPartialHomeomorph (RegFill hs f₀) ℂ} (he : e ∈ atlas ℂ (RegFill hs f₀))
    (hwe : w ∈ e.source) :
    ∃ T : ℂ → ℂ, AnalyticAt ℂ T (e w) ∧
      (∀ᶠ x in 𝓝 (e w), ∀ hx : e.symm x ∈ bordered hs f₀ ε,
        (Θc (Quotient.mk _ ⟨e.symm x, hx⟩) : ℂ) = T x) ∧
      (bdf hs f₀ ε ∘ e.symm) =ᶠ[𝓝 (e w)] B ∘ T ∧
      T (e w) ∈ sphere (0 : ℂ) 1 ∧
      regMetric L e (e w) = (pullbackOrb L hB).lam (T (e w)) * ‖deriv T (e w)‖ ^ 2 ∧
      regMetric L e (e w) = ‖deriv (bdf hs f₀ ε ∘ e.symm) (e w)‖ ^ 2 ∧
      (pullbackOrb L hB).lineDensity (T (e w)) * ‖deriv T (e w)‖ =
        ‖deriv (bdf hs f₀ ε ∘ e.symm) (e w)‖ := by
  haveI := (regFill_riemannSurface hs f₀).2.1
  have hwM : w ∈ bordered hs f₀ ε := bdry_subset_bordered hw
  set z := e w
  have hz : z ∈ e.target := e.map_source hwe
  have hez : e.symm z = w := e.left_inv hwe
  set p : ℂ := (Θc (Quotient.mk _ ⟨w, hwM⟩) : ℂ)
  have hps : p ∈ sphere (0 : ℂ) 1 := (hΘS ⟨w, hwM⟩).1 hw
  have hpV : p ∈ V := hB.cb (sphere_subset_closedBall hps)
  have hBp : B p = bdf hs f₀ ε w := hΘB ⟨w, hwM⟩
  have hBn : ‖B p‖ = 1 := by rw [hBp]; exact hw
  have hBu : B p ≠ ε := fun h => by
    have := L.u_mem; rw [← h, hBn] at this; exact lt_irrefl _ this
  have hBv : B p ≠ lamStar * ε := fun h => by
    have := L.v_mem; rw [← h, hBn] at this; exact lt_irrefl _ this
  have hBd : deriv B p ≠ 0 := hB.crit p hpV hBu hBv
  have hBa : AnalyticAt ℂ B p := hB.analytic p hpV
  -- a ball about `p` in `V`, where `B` is injective with nonzero derivative
  obtain ⟨ρ₃, hρ₃, hρ₃V⟩ := Metric.isOpen_iff.1 hB.isOpen p hpV
  have hBdV : DifferentiableOn ℂ B V := fun x hx => (hB.analytic x hx).differentiableWithinAt
  obtain ⟨ρ₁, hρ₁, hinj⟩ := HolInv.exists_ball_injOn hB.isOpen hBdV hpV hBd
  obtain ⟨ρ₂, hρ₂, hρ₂d⟩ := Metric.eventually_nhds_iff_ball.1
    (hBa.deriv.continuousAt.eventually (isOpen_ne.mem_nhds hBd))
  set ρ := min ρ₁ (min ρ₂ ρ₃)
  have hρ : 0 < ρ := lt_min hρ₁ (lt_min hρ₂ hρ₃)
  set Y := ball p ρ
  have hY1 : Y ⊆ ball p ρ₁ := ball_subset_ball (min_le_left _ _)
  have hY2 : Y ⊆ ball p ρ₂ := ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
  have hY3 : Y ⊆ ball p ρ₃ := ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _))
  have hYinj : InjOn B Y := hinj.mono hY1
  have hBdY : DifferentiableOn ℂ B Y := hBdV.mono (hY3.trans hρ₃V)
  set G := Function.invFunOn B Y
  have hWo : IsOpen (B '' Y) := HolInv.isOpen_image hBdY hYinj subset_rfl isOpen_ball
  have hGd : DifferentiableOn ℂ G (B '' Y) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (HolInv.hasDerivAt_invFunOn isOpen_ball hBdY hYinj hy
      (hρ₂d y (hY2 hy))).differentiableAt.differentiableWithinAt
  -- the chart representation of `b_ε`
  set F := bdf hs f₀ ε ∘ e.symm
  have hFa : AnalyticAt ℂ F z := analyticAt_chart_fun (contMDiff_bdf hs f₀ ε) he hz
  have hFz : F z = B p := by simp only [F, Function.comp, hez, hBp]
  have hFW : F z ∈ B '' Y := ⟨p, mem_ball_self hρ, hFz.symm⟩
  set T : ℂ → ℂ := fun x => G (F x)
  have hTa : AnalyticAt ℂ T z :=
    AnalyticAt.comp (g := G) (f := F) (hGd.analyticAt (hWo.mem_nhds hFW)) hFa
  have hTz : T z = p := by
    show G (F z) = p
    rw [hFz]; exact HolInv.invFunOn_apply_self hYinj (mem_ball_self hρ)
  have hFT : F =ᶠ[𝓝 z] B ∘ T := by
    filter_upwards [hFa.continuousAt.preimage_mem_nhds (hWo.mem_nhds hFW)] with x hx
    exact (Function.invFunOn_eq (f := B) hx).symm
  -- the quotient map agrees with `T` on `e(M_ε)` near `z`
  have hΘcont : Continuous fun w' : bordered hs f₀ ε => (Θc (Quotient.mk _ w') : ℂ) :=
    continuous_subtype_val.comp (Θc.continuous.comp continuous_quotient_mk')
  obtain ⟨O, hO, hOsub⟩ := (mem_nhds_subtype _ ⟨w, hwM⟩ _).1
    ((hΘcont.continuousAt (x := ⟨w, hwM⟩)).preimage_mem_nhds (isOpen_ball.mem_nhds
      (mem_ball_self hρ)))
  have hΘT : ∀ᶠ x in 𝓝 z, ∀ hx : e.symm x ∈ bordered hs f₀ ε,
      (Θc (Quotient.mk _ ⟨e.symm x, hx⟩) : ℂ) = T x := by
    have hOz : O ∈ 𝓝 (e.symm z) := by rw [hez]; exact hO
    filter_upwards [(e.continuousAt_symm hz).preimage_mem_nhds hOz] with x hx hxM
    have hmem : (Θc (Quotient.mk _ ⟨e.symm x, hxM⟩) : ℂ) ∈ Y := hOsub (show e.symm x ∈ O from hx)
    show _ = G (F x)
    have hB' : B (Θc (Quotient.mk _ ⟨e.symm x, hxM⟩)) = F x := hΘB ⟨e.symm x, hxM⟩
    rw [← hB']
    exact (HolInv.invFunOn_apply_self hYinj hmem).symm
  -- the metric law at `z`
  have hzd : z ∈ chartDom L e := ⟨hz, by
    show bdf hs f₀ ε (e.symm z) ∈ L.U
    rw [hez]; exact bordered_subset_metricDom L hwM⟩
  have hloc := isLocalBranched_chart h0 L he
  have hpcone : p ∉ coneSet B V (ε : ℂ) (lamStar * ε) := fun h => by
    rcases h.2.1 with h' | h'
    · exact hBu h'
    · exact hBv h'
  have hTV : ∀ᶠ x in 𝓝 z, T x ∈ V := hTa.continuousAt.preimage_mem_nhds
    (hB.isOpen.mem_nhds (by rw [hTz]; exact hpV))
  have hlaw : regMetric L e z = pbLam L B (T z) * ‖deriv T z‖ ^ 2 := by
    refine pullback_law hFT hTa (hloc.smooth hzd).1.continuousAt ?_ ?_
    · rw [hTz]; exact (smooth_at_noncone hB hpV hpcone).1.continuousAt
    · filter_upwards [nhdsWithin_le_nhds (hloc.eventually_good hzd), self_mem_nhdsWithin,
        nhdsWithin_le_nhds hTV, nhdsWithin_le_nhds hFT] with x hg hne hxV hFx
      obtain ⟨hxW, hxu, hxv⟩ := hg hne
      have hFx' : B (T x) = F x := hFx.symm
      exact ⟨hloc.pbLam_eq hxW hxu hxv, pbLam_eq hB hxV (by rw [hFx']; exact hxu)
        (by rw [hFx']; exact hxv), (hB.analytic _ hxV).differentiableAt⟩
  -- collar: the metric is `|d b_ε|²`
  obtain ⟨ρc, hρc, hcol⟩ := L.collar
  have hFu : F z ≠ ε := by rw [hFz]; exact hBu
  have hFv : F z ≠ lamStar * ε := by rw [hFz]; exact hBv
  have hcollar : regMetric L e z = ‖deriv F z‖ ^ 2 := by
    rw [show regMetric L e z = pbLam L F z from rfl, hloc.pbLam_eq hzd hFu hFv, pbFml,
      hcol _ (hloc.mapsTo hzd) (by
        show ρc < ‖F z‖
        rw [hFz, hBn]; exact hρc), one_mul]
  have hchain : deriv F z = deriv B (T z) * deriv T z := by
    rw [hFT.deriv_eq]
    exact ((hB.analytic _ (by rw [hTz]; exact hpV)).differentiableAt.hasDerivAt.comp z
      hTa.differentiableAt.hasDerivAt).deriv
  refine ⟨T, hTa, hΘT, hFT, by rw [hTz]; exact hps, hlaw, hcollar, ?_⟩
  rw [lineDensity_pullbackOrb hB (by rw [hTz]; exact hps), hchain, norm_mul]

end Degree7
