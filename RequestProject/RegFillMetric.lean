module

public import RequestProject.PullbackLaw
public import RequestProject.Degree7SubgroupIdent

/-!
# The deck-invariant pulled-back metric on the completed covering surface `R̄`

Let `R̄ = RegFill hs f₀` be the branched completion of the actual common regular `GL(3, 𝔽₂)`-cover
(a Riemann surface, `regFill_riemannSurface`), `b_ε = bdf hs f₀ ε = A_ε ∘ π̄ : R̄ → ℂ`, and
`L : BaseOrbMetric ε (λ_* ε) 2 3` any base orbifold metric (cone orders `2`, `3` at the branch
values `ε = A_ε(0)`, `λ_* ε = A_ε(1)`).

**Encoding.** A conformal Riemannian metric on the Riemann surface `R̄` is given by its conformal
factors in the charts of the atlas: for a chart `e`, `regMetric L e : ℂ → ℝ`, defined on
`chartDom L e = e(b_ε⁻¹(L.U))`, an open neighbourhood of the chart image of the compact bordered
surface `M_ε` (`bordered_subset_metricDom`), such that the metric is `regMetric L e (z) |dz|²`.
Here `regMetric L e = pbLam L (b_ε ∘ e⁻¹)`: the factor `λ₀(b_ε ∘ e⁻¹)|(b_ε ∘ e⁻¹)'|²` at
generic points, extended by continuity.

* `isLocalBranched_chart`: in every atlas chart `b_ε ∘ e⁻¹` is ramified of order exactly `2` over
  `ε` and `3` over `λ_* ε` (the cusp charts read `t ↦ A_ε(cB + t^dB)`), unramified elsewhere.
* **`regMetric_smooth`**: every conformal factor is `C^∞` and positive on its whole domain,
  including at the filled (cusp) points; `regMetric_eq` gives the formula off the branch fibres,
  `regMetric_cusp` the formula in the actual cusp charts.
* **`regMetric_transform`**: for any holomorphic `Φ : R̄ → R̄` with `b_ε ∘ Φ = b_ε`, the transition
  map `T = e' ∘ Φ ∘ e⁻¹` is holomorphic and `λ_e = (λ_{e'} ∘ T) |T'|²` — at **every** point,
  including the filled points.  With `Φ = id` this is the **conformal transition law**
  (`regMetric_transition`: the factors define one metric); with `Φ` an extended deck
  transformation it is the **deck invariance** (`regMetric_deck`: each deck transformation is a
  local isometry).

No smoothness, invariance or descent is assumed: all of it is derived from the local power models
of the completion and from the structure of `L`.
-/

@[expose] public section

open Polynomial Set Filter Topology Metric PolyCover LocalMonodromy SteklovRegularCover
  SteklovPunctured SteklovFill SteklovRiemann Manifold SteklovOrb SteklovCoalescence
  SteklovCritical
open scoped ContDiff

noncomputable section

namespace SteklovOrb

/-- Holomorphic maps between Riemann surfaces are holomorphic in any pair of atlas charts. -/
theorem analyticAt_chart_rep {M M' : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] [TopologicalSpace M'] [ChartedSpace ℂ M'] [IsManifold 𝓘(ℂ) ω M']
    {f : M → M'} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) {e : OpenPartialHomeomorph M ℂ}
    {e' : OpenPartialHomeomorph M' ℂ} (he : e ∈ atlas ℂ M) (he' : e' ∈ atlas ℂ M') {z : ℂ}
    (hz : z ∈ e.target) (hfz : f (e.symm z) ∈ e'.source) :
    AnalyticAt ℂ (e' ∘ f ∘ e.symm) z := by
  have hx : e.symm z ∈ e.source := e.map_target hz
  have h := (contMDiffWithinAt_iff_of_mem_maximalAtlas (s := Set.univ)
    (IsManifold.subset_maximalAtlas he) (IsManifold.subset_maximalAtlas he') hx hfz).1
    (hf (e.symm z)).contMDiffWithinAt
  simp only [OpenPartialHomeomorph.extend_coe, OpenPartialHomeomorph.extend_coe_symm,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp, Function.comp_id,
    Set.preimage_univ, Set.range_id, Set.univ_inter, contDiffWithinAt_univ, e.right_inv hz] at h
  exact h.2.analyticAt

/-- A holomorphic function on a Riemann surface is holomorphic in every atlas chart. -/
theorem analyticAt_chart_fun {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ω M] {f : M → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    {e : OpenPartialHomeomorph M ℂ} (he : e ∈ atlas ℂ M) {z : ℂ} (hz : z ∈ e.target) :
    AnalyticAt ℂ (f ∘ e.symm) z := by
  have h := analyticAt_chart_rep hf he (e' := OpenPartialHomeomorph.refl ℂ)
    (by simp [atlas, ChartedSpace.atlas]) hz (by simp)
  simpa using h

end SteklovOrb

namespace Degree7

variable {s : ℂ}

lemma lamc_ne_zero {ε : ℝ} (h0 : 0 < ε) : (lamStar - 1) * (ε : ℂ) ≠ 0 :=
  mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast h0.ne')

lemma affA_eq_u_iff {ε : ℝ} (h0 : 0 < ε) (z : ℂ) : affA ε z = (ε : ℂ) ↔ z = 0 := by
  unfold affA
  constructor
  · intro h
    have : (lamStar - 1) * (ε : ℂ) * z = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_left (lamc_ne_zero h0)
  · rintro rfl; ring

lemma affA_eq_v_iff {ε : ℝ} (h0 : 0 < ε) (z : ℂ) : affA ε z = lamStar * (ε : ℂ) ↔ z = 1 := by
  unfold affA
  constructor
  · intro h
    have : (lamStar - 1) * (ε : ℂ) * (z - 1) = 0 := by linear_combination h
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (lamc_ne_zero h0))
  · rintro rfl; ring

lemma contMDiff_bdf (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (ε : ℝ) :
    haveI := (regFill_riemannSurface hs f₀).2.1
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (bdf hs f₀ ε) := by
  haveI := (regFill_riemannSurface hs f₀).2.1
  have hA : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (affA ε) := by
    rw [contMDiff_iff_contDiff]
    unfold affA
    exact contDiff_const.add (contDiff_const.mul contDiff_id)
  exact hA.comp (regFill_riemannSurface hs f₀).2.2.1

/-- The conformal factor, in the chart `e`, of the pull-back of `L` through `b_ε`. -/
def regMetric {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {ε : ℝ}
    (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3) (e : OpenPartialHomeomorph (RegFill hs f₀) ℂ) :
    ℂ → ℝ :=
  pbLam L (bdf hs f₀ ε ∘ e.symm)

/-- Its domain in the chart `e`: the chart image of `b_ε⁻¹(L.U) ⊇ M_ε`. -/
def chartDom {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {ε : ℝ}
    (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3) (e : OpenPartialHomeomorph (RegFill hs f₀) ℂ) :
    Set ℂ :=
  e.target ∩ e.symm ⁻¹' (bdf hs f₀ ε ⁻¹' L.U)

/-- The compact bordered surface lies in the domain of the metric. -/
lemma bordered_subset_metricDom {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {ε : ℝ}
    (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3) :
    bordered hs f₀ ε ⊆ bdf hs f₀ ε ⁻¹' L.U := fun w hw =>
  L.cb (mem_closedBall_zero_iff.2 hw)

lemma regFillProj_inl (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (f : RegCov f₀) :
    regFillProj hs f₀ (Fill.inl f) = coverProjC hs f₀ f := rfl

lemma cuspChart_symm_inl {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13}
    (j : BIdx (regProj f₀) cB (1 / 2)) {t : ℂ} (ht : t ∈ ball (0 : ℂ) ((regEnds hs f₀).r j))
    (h0 : t ≠ 0) : ∃ f, (Fill.cuspChart (E := regEnds hs f₀) j).symm t = Fill.inl f :=
  ⟨_, Fill.cuspInv_of_mem (E := regEnds hs f₀) ⟨h0, mem_ball_zero_iff.1 ht⟩⟩

lemma regFillProj_cusp_symm {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13}
    (j : BIdx (regProj f₀) cB (1 / 2)) {t : ℂ} (ht : t ∈ ball (0 : ℂ) ((regEnds hs f₀).r j)) :
    regFillProj hs f₀ ((Fill.cuspChart (E := regEnds hs f₀) j).symm t) = cB j.1 + t ^ (dB j.1) :=
  Fill.πFill_cuspChart_symm (E := regEnds hs f₀) (fun j => cB j.1) (fun j => dB j.1)
    (regEnds_pow hs f₀) j ht (dB_pos j.1)

lemma cB_dB (b : Bool) : (cB b = 0 ∧ dB b = 2) ∨ (cB b = 1 ∧ dB b = 3) := by
  cases b
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- **In every atlas chart, `b_ε ∘ e⁻¹` has exactly the ramification of the base cone orders.** -/
theorem isLocalBranched_chart {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {ε : ℝ}
    (h0 : 0 < ε) (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3)
    {e : OpenPartialHomeomorph (RegFill hs f₀) ℂ} (he : e ∈ atlas ℂ (RegFill hs f₀)) :
    IsLocalBranched L (bdf hs f₀ ε ∘ e.symm) (chartDom L e) := by
  have hc := lamc_ne_zero h0
  have hopen : IsOpen (chartDom L e) :=
    e.continuousOn_symm.isOpen_inter_preimage e.open_target
      (L.isOpen_U.preimage (continuous_bdf hs f₀ ε))
  rcases Fill.mem_atlas_iff.1 he with ⟨e₀, he₀, rfl⟩ | ⟨j, rfl⟩
  · -- a chart of the unbranched cover: `b_ε ∘ e⁻¹ = A_ε`
    have hform : ∀ z ∈ e₀.target, (bdf hs f₀ ε ∘ (Fill.liftChart e₀).symm) z = affA ε z := by
      intro z hz
      show affA ε (regFillProj hs f₀ (Fill.inl (e₀.symm z))) = affA ε z
      rw [regFillProj_inl, (chartsAre_regCov hs f₀).apply_symm he₀ hz]
    have hnot : ∀ z ∈ e₀.target, z ≠ 0 ∧ z ≠ 1 := by
      intro z hz
      have h := coverProjC_not_mem hs f₀ (e₀.symm z)
      rw [(chartsAre_regCov hs f₀).apply_symm he₀ hz] at h
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at h
      exact h
    have hev : ∀ z ∈ chartDom L (Fill.liftChart e₀),
        (bdf hs f₀ ε ∘ (Fill.liftChart e₀).symm) =ᶠ[𝓝 z] affA ε := by
      intro z hz
      filter_upwards [e₀.open_target.mem_nhds hz.1] with x hx using hform x hx
    have hAa : ∀ z, AnalyticAt ℂ (affA ε) z := fun z => by
      unfold affA; exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    refine ⟨hopen, fun z hz => (hAa z).congr (hev z hz).symm, fun z hz => hz.2, ?_, ?_, ?_⟩
    · intro z hz _ _
      rw [(hev z hz).deriv_eq]
      have : HasDerivAt (affA ε) ((lamStar - 1) * ε) z := by
        unfold affA
        simpa using ((hasDerivAt_id z).const_mul ((lamStar - 1) * (ε : ℂ))).const_add (ε : ℂ)
      rw [this.deriv]; exact hc
    · intro z hz hu
      exfalso
      rw [hform z hz.1, affA_eq_u_iff h0] at hu
      exact (hnot z hz.1).1 hu
    · intro z hz hv
      exfalso
      rw [hform z hz.1, affA_eq_v_iff h0] at hv
      exact (hnot z hz.1).2 hv
  · -- a cusp chart: `b_ε ∘ e⁻¹ (t) = A_ε (cB + t^dB)`
    set r := (regEnds hs f₀).r j
    have htarget : (Fill.cuspChart (E := regEnds hs f₀) j).target = ball 0 r := rfl
    have hform : ∀ t ∈ ball (0 : ℂ) r, (bdf hs f₀ ε ∘ (Fill.cuspChart j).symm) t =
        affA ε (cB j.1 + t ^ (dB j.1)) := by
      intro t ht
      show affA ε (regFillProj hs f₀ _) = _
      rw [regFillProj_cusp_symm j ht]
    have hev : ∀ t ∈ chartDom L (Fill.cuspChart (E := regEnds hs f₀) j),
        (bdf hs f₀ ε ∘ (Fill.cuspChart j).symm) =ᶠ[𝓝 t]
          fun x => affA ε (cB j.1 + x ^ (dB j.1)) := by
      intro t ht
      filter_upwards [isOpen_ball.mem_nhds (htarget ▸ ht.1)] with x hx using hform x hx
    have hpa : ∀ t, AnalyticAt ℂ (fun x => affA ε (cB j.1 + x ^ (dB j.1))) t := fun t => by
      unfold affA
      exact analyticAt_const.add (analyticAt_const.mul (analyticAt_const.add (analyticAt_id.pow _)))
    -- off `t = 0`, the value is not a branch value
    have hgen : ∀ t ∈ ball (0 : ℂ) r, t ≠ 0 →
        affA ε (cB j.1 + t ^ (dB j.1)) ≠ ε ∧ affA ε (cB j.1 + t ^ (dB j.1)) ≠ lamStar * ε := by
      intro t ht ht0
      obtain ⟨f, hf⟩ := cuspChart_symm_inl j ht ht0
      have h1 := regFillProj_cusp_symm j ht
      rw [hf, regFillProj_inl] at h1
      have h2 := coverProjC_not_mem hs f₀ f
      rw [h1] at h2
      simp only [mem_insert_iff, mem_singleton_iff, not_or] at h2
      exact ⟨fun h => h2.1 ((affA_eq_u_iff h0 _).1 h), fun h => h2.2 ((affA_eq_v_iff h0 _).1 h)⟩
    have hderiv : ∀ t, HasDerivAt (fun x => affA ε (cB j.1 + x ^ (dB j.1)))
        ((lamStar - 1) * ε * ((dB j.1 : ℂ) * t ^ (dB j.1 - 1))) t := by
      intro t
      unfold affA
      have := (((hasDerivAt_pow (dB j.1) t).const_add (cB j.1)).const_mul
        ((lamStar - 1) * (ε : ℂ))).const_add (ε : ℂ)
      first
        | simpa using this
        | simpa [Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.neg_def, Function.comp_def] using this
        | exact (this.congr_deriv (by first | rfl | simp | (simp; ring))).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun _ => by first | rfl | simp | (simp; ring))
    refine ⟨hopen, fun t ht => (hpa t).congr (hev t ht).symm, fun t ht => ht.2, ?_, ?_, ?_⟩
    · intro t ht hu hv
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [hform 0 ht.1, zero_pow (dB_pos j.1).ne', add_zero] at hu hv
        rcases cB_dB j.1 with ⟨h, -⟩ | ⟨h, -⟩
        · exact hu (by rw [h]; exact (affA_eq_u_iff h0 0).2 rfl)
        · exact hv (by rw [h]; exact (affA_eq_v_iff h0 1).2 rfl)
      rw [(hev t ht).deriv_eq, (hderiv t).deriv]
      exact mul_ne_zero hc (mul_ne_zero (by exact_mod_cast (dB_pos j.1).ne')
        (pow_ne_zero _ ht0))
    · intro t ht hu
      have ht0 : t = 0 := by
        by_contra ht0
        exact (hgen t ht.1 ht0).1 (by rw [← hform t ht.1]; exact hu)
      subst ht0
      rw [hform 0 ht.1, zero_pow (dB_pos j.1).ne', add_zero, affA_eq_u_iff h0] at hu
      have hd : dB j.1 = 2 := by
        rcases cB_dB j.1 with ⟨-, h⟩ | ⟨h, -⟩
        · exact h
        · rw [h] at hu; exact absurd hu one_ne_zero
      refine ⟨fun _ => (lamStar - 1) * (ε : ℂ), analyticAt_const, hc, ?_⟩
      filter_upwards [hev 0 ht] with x hx
      rw [hx, hu, hd]; unfold affA; ring
    · intro t ht hv
      have ht0 : t = 0 := by
        by_contra ht0
        exact (hgen t ht.1 ht0).2 (by rw [← hform t ht.1]; exact hv)
      subst ht0
      rw [hform 0 ht.1, zero_pow (dB_pos j.1).ne', add_zero, affA_eq_v_iff h0] at hv
      have hd : dB j.1 = 3 := by
        rcases cB_dB j.1 with ⟨h, -⟩ | ⟨-, h⟩
        · rw [h] at hv; exact absurd hv.symm one_ne_zero
        · exact h
      refine ⟨fun _ => (lamStar - 1) * (ε : ℂ), analyticAt_const, hc, ?_⟩
      filter_upwards [hev 0 ht] with x hx
      rw [hx, hv, hd]; unfold affA; ring

/-- **Smoothness and positivity of the pulled-back metric on `R̄`**, in every atlas chart and at
every point of its domain (in particular at the filled points). -/
theorem regMetric_smooth {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {ε : ℝ} (h0 : 0 < ε)
    (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3)
    {e : OpenPartialHomeomorph (RegFill hs f₀) ℂ} (he : e ∈ atlas ℂ (RegFill hs f₀))
    {z : ℂ} (hz : z ∈ chartDom L e) :
    ContDiffAt ℝ ∞ (regMetric L e) z ∧ 0 < regMetric L e z :=
  (isLocalBranched_chart h0 L he).smooth hz

/-- The metric is `λ₀(b_ε)|d b_ε|²` off the fibres over the branch values. -/
theorem regMetric_eq {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {ε : ℝ} (h0 : 0 < ε)
    (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3)
    {e : OpenPartialHomeomorph (RegFill hs f₀) ℂ} (he : e ∈ atlas ℂ (RegFill hs f₀))
    {z : ℂ} (hz : z ∈ chartDom L e) (hu : bdf hs f₀ ε (e.symm z) ≠ ε)
    (hv : bdf hs f₀ ε (e.symm z) ≠ lamStar * ε) :
    regMetric L e z = L.lam (bdf hs f₀ ε (e.symm z)) * ‖deriv (bdf hs f₀ ε ∘ e.symm) z‖ ^ 2 :=
  (isLocalBranched_chart h0 L he).pbLam_eq hz hu hv

/-- **The metric in the actual cusp charts**: at a filled point `j` over `cB j` (inertia order
`dB j`), `b_ε ∘ e⁻¹ (t) = A_ε(cB + t^dB)`; the factor is `λ₀(A_ε(cB + t^dB))·|(λ_*-1)ε·dB·t^(dB-1)|²`
for `t ≠ 0`, and it is smooth and positive at `t = 0`. -/
theorem regMetric_cusp {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1 / 3) (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3)
    (j : BIdx (regProj f₀) cB (1 / 2)) :
    (∀ t ∈ ball (0 : ℂ) ((regEnds hs f₀).r j),
      bdf hs f₀ ε ((Fill.cuspChart (E := regEnds hs f₀) j).symm t) =
        affA ε (cB j.1 + t ^ (dB j.1))) ∧
    (∀ t ∈ ball (0 : ℂ) ((regEnds hs f₀).r j), t ≠ 0 →
      t ∈ chartDom L (Fill.cuspChart (E := regEnds hs f₀) j) →
      regMetric L (Fill.cuspChart (E := regEnds hs f₀) j) t =
        L.lam (affA ε (cB j.1 + t ^ (dB j.1))) *
          ‖(lamStar - 1) * ε * ((dB j.1 : ℂ) * t ^ (dB j.1 - 1))‖ ^ 2) ∧
    0 ∈ chartDom L (Fill.cuspChart (E := regEnds hs f₀) j) ∧
    ContDiffAt ℝ ∞ (regMetric L (Fill.cuspChart (E := regEnds hs f₀) j)) 0 ∧
    0 < regMetric L (Fill.cuspChart (E := regEnds hs f₀) j) 0 := by
  have he : Fill.cuspChart (E := regEnds hs f₀) j ∈ atlas ℂ (RegFill hs f₀) :=
    Fill.mem_atlas_iff.2 (Or.inr ⟨j, rfl⟩)
  have hform : ∀ t ∈ ball (0 : ℂ) ((regEnds hs f₀).r j),
      bdf hs f₀ ε ((Fill.cuspChart (E := regEnds hs f₀) j).symm t) =
        affA ε (cB j.1 + t ^ (dB j.1)) := fun t ht => by
    show affA ε (regFillProj hs f₀ _) = _
    rw [regFillProj_cusp_symm j ht]
  have h0mem : (0 : ℂ) ∈ chartDom L (Fill.cuspChart (E := regEnds hs f₀) j) := by
    refine ⟨mem_ball_self ((regEnds hs f₀).r_pos j), ?_⟩
    show bdf hs f₀ ε _ ∈ L.U
    rw [hform 0 (mem_ball_self ((regEnds hs f₀).r_pos j)), zero_pow (dB_pos j.1).ne', add_zero]
    obtain ⟨hu, hv⟩ := branchValues_mem_disk h0 h1
    rcases cB_dB j.1 with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · exact L.cb (mem_closedBall_zero_iff.2 (by rw [(affA_eq_u_iff h0 0).2 rfl]; exact hu.le))
    · exact L.cb (mem_closedBall_zero_iff.2 (by rw [(affA_eq_v_iff h0 1).2 rfl]; exact hv.le))
  refine ⟨hform, fun t ht ht0 htd => ?_, h0mem, regMetric_smooth h0 L he h0mem⟩
  obtain ⟨f, hf⟩ := cuspChart_symm_inl j ht ht0
  have hgen : bdf hs f₀ ε ((Fill.cuspChart (E := regEnds hs f₀) j).symm t) ≠ ε ∧
      bdf hs f₀ ε ((Fill.cuspChart (E := regEnds hs f₀) j).symm t) ≠ lamStar * ε := by
    rw [hf]
    show affA ε (coverProjC hs f₀ f) ≠ ε ∧ affA ε (coverProjC hs f₀ f) ≠ lamStar * ε
    have h2 := coverProjC_not_mem hs f₀ f
    simp only [mem_insert_iff, mem_singleton_iff, not_or] at h2
    exact ⟨fun h => h2.1 ((affA_eq_u_iff h0 _).1 h), fun h => h2.2 ((affA_eq_v_iff h0 _).1 h)⟩
  rw [regMetric_eq h0 L he htd hgen.1 hgen.2, hform t ht]
  congr 2
  have hev : (bdf hs f₀ ε ∘ (Fill.cuspChart (E := regEnds hs f₀) j).symm) =ᶠ[𝓝 t]
      fun x => affA ε (cB j.1 + x ^ (dB j.1)) := by
    filter_upwards [isOpen_ball.mem_nhds ht] with x hx using hform x hx
  rw [hev.deriv_eq]
  unfold affA
  have := (((hasDerivAt_pow (dB j.1) t).const_add (cB j.1)).const_mul
    ((lamStar - 1) * (ε : ℂ))).const_add (ε : ℂ)
  first
    | simpa using this.deriv
    | simpa [Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.neg_def, Function.comp_def] using this.deriv

/-- **The conformal transformation law** under any holomorphic self-map preserving `b_ε`. -/
theorem regMetric_transform {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {ε : ℝ} (h0 : 0 < ε)
    (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3) {Φ : RegFill hs f₀ → RegFill hs f₀}
    (hΦ : haveI := (regFill_riemannSurface hs f₀).2.1; ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Φ)
    (hΦb : ∀ w, bdf hs f₀ ε (Φ w) = bdf hs f₀ ε w)
    {e e' : OpenPartialHomeomorph (RegFill hs f₀) ℂ} (he : e ∈ atlas ℂ (RegFill hs f₀))
    (he' : e' ∈ atlas ℂ (RegFill hs f₀)) {z : ℂ} (hz : z ∈ chartDom L e)
    (hzΦ : Φ (e.symm z) ∈ e'.source) :
    AnalyticAt ℂ (e' ∘ Φ ∘ e.symm) z ∧ (e' ∘ Φ ∘ e.symm) z ∈ chartDom L e' ∧
      regMetric L e z = regMetric L e' ((e' ∘ Φ ∘ e.symm) z) *
        ‖deriv (e' ∘ Φ ∘ e.symm) z‖ ^ 2 := by
  haveI := (regFill_riemannSurface hs f₀).2.1
  set T := e' ∘ Φ ∘ e.symm
  have hT : AnalyticAt ℂ T z := analyticAt_chart_rep hΦ he he' hz.1 hzΦ
  have hTz : T z ∈ chartDom L e' := by
    refine ⟨e'.map_source hzΦ, ?_⟩
    show bdf hs f₀ ε (e'.symm (e' (Φ (e.symm z)))) ∈ L.U
    rw [e'.left_inv hzΦ, hΦb]; exact hz.2
  have hcont : ContinuousAt (Φ ∘ e.symm) z :=
    hΦ.continuous.continuousAt.comp (e.continuousAt_symm hz.1)
  have hF : (bdf hs f₀ ε ∘ e.symm) =ᶠ[𝓝 z] (bdf hs f₀ ε ∘ e'.symm) ∘ T := by
    filter_upwards [hcont.preimage_mem_nhds (e'.open_source.mem_nhds hzΦ)] with x hx
    simp only [Function.comp, T]
    have hx' : Φ (e.symm x) ∈ e'.source := hx
    rw [e'.left_inv hx', hΦb]
  exact ⟨hT, hTz, (isLocalBranched_chart h0 L he).law (isLocalBranched_chart h0 L he') hz hTz hF hT⟩

/-- **Transition law**: the conformal factors in two charts are related by `|T'|²`. -/
theorem regMetric_transition {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {ε : ℝ}
    (h0 : 0 < ε) (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3)
    {e e' : OpenPartialHomeomorph (RegFill hs f₀) ℂ} (he : e ∈ atlas ℂ (RegFill hs f₀))
    (he' : e' ∈ atlas ℂ (RegFill hs f₀)) {z : ℂ} (hz : z ∈ chartDom L e)
    (hz' : e.symm z ∈ e'.source) :
    AnalyticAt ℂ (e' ∘ e.symm) z ∧ regMetric L e z =
      regMetric L e' ((e' ∘ e.symm) z) * ‖deriv (e' ∘ e.symm) z‖ ^ 2 := by
  haveI := (regFill_riemannSurface hs f₀).2.1
  obtain ⟨h1, -, h3⟩ := regMetric_transform h0 L (Φ := id) contMDiff_id (fun _ => rfl) he he' hz hz'
  exact ⟨h1, h3⟩

/-- **Deck invariance**: every extended deck transformation (including at the filled points) is a
local isometry of the pulled-back metric. -/
theorem regMetric_deck {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {ε : ℝ} (h0 : 0 < ε)
    (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3) (σ : deckGroup f₀)
    {e e' : OpenPartialHomeomorph (RegFill hs f₀) ℂ} (he : e ∈ atlas ℂ (RegFill hs f₀))
    (he' : e' ∈ atlas ℂ (RegFill hs f₀)) {z : ℂ} (hz : z ∈ chartDom L e)
    (hzσ : regFillAct hs f₀ σ (e.symm z) ∈ e'.source) :
    AnalyticAt ℂ (e' ∘ regFillAct hs f₀ σ ∘ e.symm) z ∧
      (e' ∘ regFillAct hs f₀ σ ∘ e.symm) z ∈ chartDom L e' ∧
      regMetric L e z = regMetric L e' ((e' ∘ regFillAct hs f₀ σ ∘ e.symm) z) *
        ‖deriv (e' ∘ regFillAct hs f₀ σ ∘ e.symm) z‖ ^ 2 := by
  have hb : ∀ w, bdf hs f₀ ε (regFillAct hs f₀ σ w) = bdf hs f₀ ε w := fun w => by
    unfold bdf; rw [(regFill_deckAction hs f₀).2.2.2.1 σ w]
  exact regMetric_transform h0 L ((regFill_deckAction hs f₀).1 σ) hb he he' hz hzσ

end Degree7
