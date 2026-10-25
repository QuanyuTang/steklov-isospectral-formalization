module

public import RequestProject.PunctureFilling
public import RequestProject.LocalHomeoRiemann

/-!
# The filled branched cover is a Riemann surface

Let `π : Y → ℂ` define the Riemann surface structure of `Y` (all charts are restrictions of `π`,
`ChartsAre Y π`), and let `E` be punctured-disk ends of `Y` whose coordinates satisfy
`(Φ j x)^(d j) = π x - c j` (local power models of `π`, `d j ≥ 1`).  Then the filling
`Fill E` is a Riemann surface (`isManifold_fill`), with charts the transported charts of `Y` and the
cusp charts, and the extension `πFill` of `π` by `cusp j ↦ c j` is holomorphic
(`contMDiff_πFill`); in the cusp chart it is `t ↦ c j + t^(d j)`.
-/

@[expose] public section

open Set Topology Manifold SteklovPunctured SteklovRiemann
open scoped ContDiff

noncomputable section

namespace SteklovFill

variable {Y : Type*} [TopologicalSpace Y] {J : Type*} {E : Ends Y J}

namespace Fill

/-- A chart of `Y` transported to the filling. -/
def liftChart (e₀ : OpenPartialHomeomorph Y ℂ) : OpenPartialHomeomorph (Fill E) ℂ where
  toFun
    | Sum.inl y => e₀ y
    | Sum.inr _ => 0
  invFun z := inl (e₀.symm z)
  source := inl '' e₀.source
  target := e₀.target
  map_source' := by
    rintro _ ⟨y, hy, rfl⟩; exact e₀.map_source hy
  map_target' z hz := ⟨_, e₀.map_target hz, rfl⟩
  left_inv' := by
    rintro _ ⟨y, hy, rfl⟩
    show inl (e₀.symm (e₀ y)) = inl y
    rw [e₀.left_inv hy]
  right_inv' z hz := by
    show e₀ (e₀.symm z) = z
    exact e₀.right_inv hz
  open_source := isOpenMap_inl _ e₀.open_source
  open_target := e₀.open_target
  continuousOn_toFun := by
    rw [continuousOn_open_iff (isOpenMap_inl _ e₀.open_source)]
    intro O hO
    have : inl '' e₀.source ∩ (fun w : Fill E => match w with
        | Sum.inl y => e₀ y
        | Sum.inr _ => 0) ⁻¹' O = inl '' (e₀.source ∩ e₀ ⁻¹' O) := by
      ext w
      simp only [mem_inter_iff, mem_image, mem_preimage]
      constructor
      · rintro ⟨⟨y, hy, rfl⟩, hO'⟩; exact ⟨y, ⟨hy, hO'⟩, rfl⟩
      · rintro ⟨y, ⟨hy, hO'⟩, rfl⟩; exact ⟨⟨y, hy, rfl⟩, hO'⟩
    rw [this]
    exact isOpenMap_inl _ (e₀.continuousOn.isOpen_inter_preimage e₀.open_source hO)
  continuousOn_invFun := continuous_inl.comp_continuousOn e₀.continuousOn_symm

lemma liftChart_inl (e₀ : OpenPartialHomeomorph Y ℂ) (y : Y) :
    liftChart (E := E) e₀ (inl y) = e₀ y := rfl

lemma liftChart_symm (e₀ : OpenPartialHomeomorph Y ℂ) (z : ℂ) :
    (liftChart (E := E) e₀).symm z = inl (e₀.symm z) := rfl

variable [ChartedSpace ℂ Y]

/-- The charted space structure of the filling. -/
instance instChartedSpace : ChartedSpace ℂ (Fill E) where
  atlas := {e | ∃ e₀ ∈ atlas ℂ Y, e = liftChart e₀} ∪ range cuspChart
  chartAt
    | Sum.inl y => liftChart (chartAt ℂ y)
    | Sum.inr j => cuspChart j
  mem_chart_source
    | Sum.inl y => ⟨y, mem_chart_source ℂ y, rfl⟩
    | Sum.inr _ => Or.inr rfl
  chart_mem_atlas
    | Sum.inl y => Or.inl ⟨_, chart_mem_atlas ℂ y, rfl⟩
    | Sum.inr j => Or.inr ⟨j, rfl⟩

/-- The extension of `π` to the filling by `cusp j ↦ c j`. -/
def πFill (π : Y → ℂ) (c : J → ℂ) : Fill E → ℂ
  | Sum.inl y => π y
  | Sum.inr j => c j

lemma mem_atlas_iff {e : OpenPartialHomeomorph (Fill E) ℂ} :
    e ∈ atlas ℂ (Fill E) ↔ (∃ e₀ ∈ atlas ℂ Y, e = liftChart e₀) ∨ ∃ j, e = cuspChart j := by
  show e ∈ {e | ∃ e₀ ∈ atlas ℂ Y, e = liftChart e₀} ∪ range cuspChart ↔ _
  simp only [mem_union, mem_setOf_eq, mem_range]
  exact or_congr Iff.rfl ⟨fun ⟨j, h⟩ => ⟨j, h.symm⟩, fun ⟨j, h⟩ => ⟨j, h.symm⟩⟩

variable {π : Y → ℂ} (hπ : ChartsAre Y π) (c : J → ℂ) (d : J → ℕ) (hd : ∀ j, 0 < d j)
  (hpow : ∀ j (x : E.U j), ((E.Φ j x : pdisk (E.r j)) : ℂ) ^ (d j) = π x - c j)
include hπ hpow

include hd in
/-- In a chart of `Y`, the end coordinate is a holomorphic `d`-th root of `z - c`. -/
lemma differentiableOn_lift_cusp (e₀ : OpenPartialHomeomorph Y ℂ) (he₀ : e₀ ∈ atlas ℂ Y)
    (j : J) : DifferentiableOn ℂ ((liftChart (E := E) e₀).symm.trans (cuspChart j))
      ((liftChart (E := E) e₀).symm.trans (cuspChart j)).source := by
  set f := (liftChart (E := E) e₀).symm.trans (cuspChart j)
  intro z hz
  have hcont : ContinuousAt f z := f.continuousAt hz
  have hz' := hz
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz'
  obtain ⟨hzt, hzs⟩ := hz'
  have hU : e₀.symm z ∈ E.U j := by
    rcases mem_cuspSet.1 hzs with ⟨y, hy, h⟩ | h
    · rw [liftChart_symm] at h; rw [inl_injective h]; exact hy
    · exact absurd h (inl_ne_cusp _ j)
  have hfz : f z = ((E.Φ j ⟨_, hU⟩ : pdisk (E.r j)) : ℂ) := by
    show cuspFun j (inl (e₀.symm z)) = _
    rw [cuspFun_inl hU]
  have hne : f z ≠ 0 := by rw [hfz]; exact (E.Φ j ⟨_, hU⟩).2.1
  have hloc : ∀ᶠ w in 𝓝 z, c j + (f w) ^ (d j) = w := by
    filter_upwards [f.open_source.mem_nhds hz] with w hw
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw
    obtain ⟨hwt, hws⟩ := hw
    have hUw : e₀.symm w ∈ E.U j := by
      rcases mem_cuspSet.1 hws with ⟨y, hy, h⟩ | h
      · rw [liftChart_symm] at h; rw [inl_injective h]; exact hy
      · exact absurd h (inl_ne_cusp _ j)
    show c j + (cuspFun j (inl (e₀.symm w))) ^ (d j) = w
    rw [cuspFun_inl hUw, hpow j ⟨_, hUw⟩]
    simp only
    rw [hπ.apply_symm he₀ hwt]; ring
  have hF : HasDerivAt (fun t : ℂ => c j + t ^ (d j)) ((d j : ℂ) * (f z) ^ (d j - 1)) (f z) := by
    simpa using ((hasDerivAt_pow (d j) (f z)).const_add (c j))
  have hF' : (d j : ℂ) * (f z) ^ (d j - 1) ≠ 0 :=
    mul_ne_zero (by exact_mod_cast (hd j).ne') (pow_ne_zero _ hne)
  exact (HasDerivAt.of_local_left_inverse hcont hF hF' hloc).differentiableAt.differentiableWithinAt

/-- In the cusp chart, a chart of `Y` reads `t ↦ c + t^d`. -/
lemma lift_cusp_symm_eq (e₀ : OpenPartialHomeomorph Y ℂ) (he₀ : e₀ ∈ atlas ℂ Y) (j : J)
    {t : ℂ} (ht : t ∈ ((cuspChart (E := E) j).symm.trans (liftChart e₀)).source) :
    ((cuspChart (E := E) j).symm.trans (liftChart e₀)) t = c j + t ^ (d j) := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at ht
  obtain ⟨-, hts⟩ := ht
  have htp : t ∈ pdisk (E.r j) := by
    by_contra h
    have : (cuspChart (E := E) j).symm t = cusp j := by
      show cuspInv j t = cusp j
      rw [cuspInv, dif_neg h]
    rw [mem_preimage, this] at hts
    obtain ⟨y, -, hy⟩ := hts
    exact inl_ne_cusp y j hy
  show liftChart e₀ (cuspInv j t) = _
  rw [cuspInv_of_mem htp, liftChart_inl, hπ e₀ he₀]
  have := hpow j ((E.Φ j).symm ⟨t, htp⟩)
  simp only [Homeomorph.apply_symm_apply] at this
  rw [this]; ring

omit hπ hpow [ChartedSpace ℂ Y] in
lemma cusp_cusp_source_eq {j j' : J} {t : ℂ}
    (ht : t ∈ ((cuspChart (E := E) j).symm.trans (cuspChart j')).source) : j = j' := by
  by_contra hjj
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at ht
  obtain ⟨ht1, ht2⟩ := ht
  have h1 := (cuspChart (E := E) j).map_target ht1
  exact Set.disjoint_left.1 (cuspSet_disjoint hjj) h1 ht2

include hd in
/-- **The filling is a Riemann surface.** -/
theorem isManifold_fill : IsManifold 𝓘(ℂ) ω (Fill E) := by
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, preimage_id_eq, range_id, inter_univ]
  rcases mem_atlas_iff.1 he with ⟨e₀, he₀, rfl⟩ | ⟨j, rfl⟩ <;>
    rcases mem_atlas_iff.1 he' with ⟨e₀', he₀', rfl⟩ | ⟨j', rfl⟩
  · refine contDiffOn_id.congr fun z hz => ?_
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
    show liftChart (E := E) e₀' (inl (e₀.symm z)) = z
    rw [liftChart_inl, hπ e₀' he₀', hπ.apply_symm he₀ hz.1]
  · exact (differentiableOn_lift_cusp hπ c d hd hpow e₀ he₀ j').contDiffOn
      (OpenPartialHomeomorph.open_source _)
  · refine ((contDiffOn_const (c := c j)).add (contDiffOn_id.pow (d j))).congr fun t ht => ?_
    rw [lift_cusp_symm_eq hπ c d hpow e₀' he₀' j ht]; rfl
  · refine contDiffOn_id.congr fun t ht => ?_
    have hjj := cusp_cusp_source_eq ht
    subst hjj
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at ht
    exact (cuspChart j).right_inv ht.1

omit hpow in
/-- `πFill` near a point of `Y`, in the transported chart. -/
lemma πFill_liftChart_symm {e₀ : OpenPartialHomeomorph Y ℂ} (he₀ : e₀ ∈ atlas ℂ Y) {z : ℂ}
    (hz : z ∈ e₀.target) : πFill (E := E) π c ((liftChart e₀).symm z) = z := by
  show π (e₀.symm z) = z
  exact hπ.apply_symm he₀ hz

omit hπ [ChartedSpace ℂ Y] in
/-- `πFill` in a cusp chart is `t ↦ c j + t^(d j)`. -/
lemma πFill_cuspChart_symm (j : J) {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) (E.r j))
    (hd : 0 < d j) : πFill (E := E) π c ((cuspChart j).symm t) = c j + t ^ (d j) := by
  show πFill π c (cuspInv j t) = _
  by_cases h : t ∈ pdisk (E.r j)
  · rw [cuspInv_of_mem h]
    show π _ = _
    have := hpow j ((E.Φ j).symm ⟨t, h⟩)
    simp only [Homeomorph.apply_symm_apply] at this
    rw [this]; ring
  · have : t = 0 := by by_contra h0; exact h ⟨h0, mem_ball_zero_iff.1 ht⟩
    subst this
    rw [cuspInv_zero, zero_pow hd.ne']
    show c j = c j + 0; ring

include hd in
/-- **The extended projection is holomorphic** on the filling. -/
theorem contMDiff_πFill :
    haveI := isManifold_fill hπ c d hd hpow
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (πFill (E := E) π c) := by
  haveI := isManifold_fill hπ c d hd hpow
  intro x
  -- a local formula `πFill = F ∘ chartAt x` on the chart source
  obtain ⟨F, hF, hFeq⟩ : ∃ F : ℂ → ℂ, ContDiff ℂ ω F ∧
      ∀ z ∈ (chartAt ℂ x).target, πFill (E := E) π c ((chartAt ℂ x).symm z) = F z := by
    rcases x with y | j
    · exact ⟨id, contDiff_id, fun z hz => πFill_liftChart_symm hπ c
        (chart_mem_atlas ℂ y) hz⟩
    · exact ⟨fun t => c j + t ^ (d j), contDiff_const.add (contDiff_id.pow _),
        fun t ht => πFill_cuspChart_symm c d hpow j ht (hd j)⟩
  have hsrc : ∀ w ∈ (chartAt ℂ x).source, πFill (E := E) π c w = F (chartAt ℂ x w) := by
    intro w hw
    rw [← hFeq _ ((chartAt ℂ x).map_source hw), (chartAt ℂ x).left_inv hw]
  rw [contMDiffAt_iff]
  refine ⟨?_, ?_⟩
  · have hev : (fun w => F (chartAt ℂ x w)) =ᶠ[𝓝 x] πFill (E := E) π c := by
      filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with w hw
      exact (hsrc w hw).symm
    exact ContinuousAt.congr (hF.continuous.continuousAt.comp
      ((chartAt ℂ x).continuousAt (mem_chart_source ℂ x))) hev
  · have hx := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
    refine (hF.contDiffAt.contDiffWithinAt (s := range 𝓘(ℂ))).congr_of_eventuallyEq ?_ ?_
    · simp only [modelWithCornersSelf_coe, range_id, nhdsWithin_univ]
      filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℂ)) x] with z hz
      simp only [extChartAt, OpenPartialHomeomorph.extend, Function.comp_apply,
        modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, PartialEquiv.coe_trans,
        PartialEquiv.coe_trans_symm, OpenPartialHomeomorph.toFun_eq_coe, id_eq,
        ModelWithCorners.toPartialEquiv_coe, ModelWithCorners.toPartialEquiv_coe_symm,
        OpenPartialHomeomorph.coe_coe_symm, PartialEquiv.trans_target, ModelWithCorners.target_eq,
        preimage_id_eq, range_id, chartAt_self_eq, OpenPartialHomeomorph.refl_apply] at hz ⊢
      exact hFeq z (by simpa using hz)
    · simp only [extChartAt, OpenPartialHomeomorph.extend, Function.comp_apply,
        modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, PartialEquiv.coe_trans,
        PartialEquiv.coe_trans_symm, OpenPartialHomeomorph.toFun_eq_coe, id_eq,
        ModelWithCorners.toPartialEquiv_coe, ModelWithCorners.toPartialEquiv_coe_symm,
        OpenPartialHomeomorph.coe_coe_symm, chartAt_self_eq, OpenPartialHomeomorph.refl_apply]
      exact hFeq _ hx

end Fill

end SteklovFill
