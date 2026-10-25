module

public import RequestProject.BranchedCompletion

/-!
# Extending maps over filled punctures

Let `E` be punctured-disk ends of `Y` and `g : Y → Y` a continuous map sending each end `U j` into
an end `U (b j)` with `‖Φ_{b j}(g y)‖ = ‖Φ_j y‖`.  Then `Fill.map g b`, defined by `g` on `Y` and
by `cusp j ↦ cusp (b j)`, is continuous (`Fill.continuous_map`).  If moreover `Y` carries charts
given by a projection `π` with `π ∘ g = π`, `c ∘ b = c`, `d ∘ b = d`, `r ∘ b = r` and
`Φ_j^(d j) = π - c j`, then in every cusp chart `Fill.map g b` is a rotation `t ↦ ζ t` with
`ζ^(d j) = 1` (`Fill.exists_rotation`) and `Fill.map g b` is holomorphic (`Fill.contMDiff_map`).

For the ends of a covering with local power models (`branchEnds`), every continuous map `g` over
the base induces such a map of ends (`bMap`), compatible with composition (`bMap_comp`,
`bMap_id`).
-/

@[expose] public section

open Set Topology SteklovPunctured Manifold SteklovRiemann
open scoped ContDiff

noncomputable section

namespace SteklovFill

section General

variable {Y : Type*} [TopologicalSpace Y] {J : Type*} {E : Ends Y J}

namespace Fill

/-- The extension of `g : Y → Y` to the filling, sending `cusp j` to `cusp (b j)`. -/
def map (g : Y → Y) (b : J → J) : Fill E → Fill E
  | Sum.inl y => inl (g y)
  | Sum.inr j => cusp (b j)

@[simp] lemma map_inl (g : Y → Y) (b : J → J) (y : Y) :
    map (E := E) g b (inl y) = inl (g y) := rfl

@[simp] lemma map_cusp (g : Y → Y) (b : J → J) (j : J) :
    map (E := E) g b (cusp j) = cusp (b j) := rfl

lemma map_comp (g h : Y → Y) (b b' : J → J) :
    map (E := E) (g ∘ h) (b ∘ b') = map g b ∘ map h b' := by
  funext w; rcases w with y | j <;> rfl

lemma map_id : map (E := E) id id = id := by
  funext w; rcases w with y | j <;> rfl

/-- The compatibility of a map with the end coordinates. -/
def EndCompat (E : Ends Y J) (g : Y → Y) (b : J → J) : Prop :=
  ∀ j (y : Y) (hy : y ∈ E.U j), ∃ h : g y ∈ E.U (b j),
    ‖((E.Φ (b j) ⟨g y, h⟩ : pdisk (E.r (b j))) : ℂ)‖ = ‖((E.Φ j ⟨y, hy⟩ : pdisk (E.r j)) : ℂ)‖

/-- **Continuity of the extended map.** -/
theorem continuous_map {g : Y → Y} {b : J → J} (hg : Continuous g) (hgb : EndCompat E g b) :
    Continuous (map (E := E) g b) := by
  rw [continuous_def]
  intro W hW
  rw [isOpen_iff] at hW ⊢
  refine ⟨?_, fun j hj => ?_⟩
  · have : (inl ⁻¹' (map (E := E) g b ⁻¹' W) : Set Y) = g ⁻¹' (inl ⁻¹' W) := rfl
    rw [this]; exact hW.1.preimage hg
  · obtain ⟨ε, hε, hsub⟩ := hW.2 (b j) hj
    refine ⟨ε, hε, ?_⟩
    rintro _ ⟨⟨y, hy⟩, hyε, rfl⟩
    obtain ⟨h, hn⟩ := hgb j y hy
    exact hsub ⟨⟨g y, h⟩, by rw [mem_setOf_eq, hn]; exact hyε, rfl⟩

/-- The extension of a homeomorphism compatible with the ends, as a homeomorphism. -/
def homeoMap (g : Y ≃ₜ Y) (b : J ≃ J) (hgb : EndCompat E g b) (hgb' : EndCompat E g.symm b.symm) :
    Fill E ≃ₜ Fill E where
  toFun := map g b
  invFun := map g.symm b.symm
  left_inv w := by rcases w with y | j <;> simp [map, inl, cusp]
  right_inv w := by rcases w with y | j <;> simp [map, inl, cusp]
  continuous_toFun := continuous_map g.continuous hgb
  continuous_invFun := continuous_map g.symm.continuous hgb'

lemma πFill_map (π : Y → ℂ) (c : J → ℂ) {g : Y → Y} {b : J → J} (hπg : ∀ y, π (g y) = π y)
    (hcb : ∀ j, c (b j) = c j) (w : Fill E) : πFill π c (map g b w) = πFill π c w := by
  rcases w with y | j
  · exact hπg y
  · exact hcb j

/-- A chart-formula criterion for holomorphy at a point. -/
lemma contMDiffAt_of_formula {M M' : Type*} [TopologicalSpace M] [ChartedSpace ℂ M]
    [TopologicalSpace M'] [ChartedSpace ℂ M'] {f : M → M'} {x : M} (hf : ContinuousAt f x)
    {F : ℂ → ℂ} (hF : ContDiff ℂ ω F)
    (hFeq : ∀ z ∈ (chartAt ℂ x).target, chartAt ℂ (f x) (f ((chartAt ℂ x).symm z)) = F z) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
  rw [contMDiffAt_iff]
  refine ⟨hf, ?_⟩
  have hx := (chartAt ℂ x).map_source (mem_chart_source ℂ x)
  refine (hF.contDiffAt.contDiffWithinAt (s := range 𝓘(ℂ))).congr_of_eventuallyEq ?_ ?_
  · simp only [modelWithCornersSelf_coe, range_id, nhdsWithin_univ]
    filter_upwards [extChartAt_target_mem_nhds (I := 𝓘(ℂ)) x] with z hz
    simp only [extChartAt, OpenPartialHomeomorph.extend, Function.comp_apply,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, PartialEquiv.coe_trans,
      PartialEquiv.coe_trans_symm, OpenPartialHomeomorph.toFun_eq_coe, id_eq,
      ModelWithCorners.toPartialEquiv_coe, ModelWithCorners.toPartialEquiv_coe_symm,
      OpenPartialHomeomorph.coe_coe_symm, PartialEquiv.trans_target, ModelWithCorners.target_eq,
      preimage_id_eq, range_id] at hz ⊢
    exact hFeq z (by simpa using hz)
  · simp only [extChartAt, OpenPartialHomeomorph.extend, Function.comp_apply,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, PartialEquiv.coe_trans,
      PartialEquiv.coe_trans_symm, OpenPartialHomeomorph.toFun_eq_coe, id_eq,
      ModelWithCorners.toPartialEquiv_coe, ModelWithCorners.toPartialEquiv_coe_symm,
      OpenPartialHomeomorph.coe_coe_symm]
    exact hFeq _ hx

lemma isPreconnected_pdisk {r : ℝ} (hr : 0 < r) : IsPreconnected (univ : Set (pdisk r)) := by
  haveI : Fact (0 < r) := ⟨hr⟩
  have h := (isPreconnected_univ (α := Hp r)).image (expP r)
    (isCoveringMap_expP r).continuous.continuousOn
  rwa [image_univ, (expP_surjective r).range_eq] at h

variable {π : Y → ℂ} (c : J → ℂ) (d : J → ℕ) (hd : ∀ j, 0 < d j)
  (hpow : ∀ j (x : E.U j), ((E.Φ j x : pdisk (E.r j)) : ℂ) ^ (d j) = π x - c j)
  {g : Y → Y} {b : J → J} (hg : Continuous g) (hgb : EndCompat E g b)
  (hπg : ∀ y, π (g y) = π y) (hcb : ∀ j, c (b j) = c j) (hdb : ∀ j, d (b j) = d j)

include hd hpow hg hgb hπg hcb hdb in
/-- **In cusp charts the extended map is a rotation by a root of unity.** -/
theorem exists_rotation (j : J) :
    ∃ ζ : ℂ, ζ ^ (d j) = 1 ∧ ∀ t ∈ Metric.ball (0 : ℂ) (E.r j),
      cuspFun (b j) (map (E := E) g b (cuspInv j t)) = ζ * t := by
  have hmem : ∀ u : pdisk (E.r j), g ((E.Φ j).symm u) ∈ E.U (b j) := fun u =>
    (hgb j _ ((E.Φ j).symm u).2).1
  set h : pdisk (E.r j) → ℂ := fun u =>
    cuspFun (b j) (inl (E := E) (g ((E.Φ j).symm u))) / (u : ℂ)
  have hval : ∀ u : pdisk (E.r j), cuspFun (b j) (inl (E := E) (g ((E.Φ j).symm u))) ^ (d j) =
      (u : ℂ) ^ (d j) := by
    intro u
    rw [cuspFun_inl (hmem u)]
    have h1 := hpow (b j) ⟨_, hmem u⟩
    have h2 := hpow j ((E.Φ j).symm u)
    rw [Homeomorph.apply_symm_apply] at h2
    rw [← hdb j, h1, hdb j, h2]
    simp only [hπg, hcb]
  have hroot : ∀ u, h u ^ (d j) = 1 := by
    intro u
    simp only [h, div_pow, hval u]
    exact div_self (pow_ne_zero _ u.2.1)
  have hcont : Continuous h := by
    refine Continuous.div ?_ continuous_subtype_val fun u => u.2.1
    exact (cuspChart (E := E) (b j)).continuousOn.comp_continuous
      (continuous_inl.comp (hg.comp (continuous_subtype_val.comp (E.Φ j).symm.continuous)))
      fun u => Or.inl ⟨_, hmem u, rfl⟩
  have hT : IsDiscrete ((Polynomial.nthRoots (d j) (1 : ℂ)).toFinset : Set ℂ) :=
    (Finset.finite_toSet _).isDiscrete
  have hmaps : MapsTo h univ ((Polynomial.nthRoots (d j) (1 : ℂ)).toFinset : Set ℂ) :=
    fun u _ => by
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      rw [Polynomial.mem_nthRoots (hd j)]; exact hroot u
  -- a base point
  have hr := E.r_pos j
  set u₀ : pdisk (E.r j) := ⟨(E.r j / 2 : ℝ), by
    refine ⟨by exact_mod_cast (half_pos hr).ne', ?_⟩
    rw [Complex.norm_real, Real.norm_of_nonneg (half_pos hr).le]; linarith⟩
  refine ⟨h u₀, hroot u₀, fun t ht => ?_⟩
  by_cases h0 : t = 0
  · subst h0
    rw [cuspInv_zero, map_cusp, cuspFun_cusp, mul_zero]
  · have htp : t ∈ pdisk (E.r j) := ⟨h0, mem_ball_zero_iff.1 ht⟩
    have hconst := (isPreconnected_pdisk hr).constant_of_mapsTo hT hcont.continuousOn hmaps
      (mem_univ (⟨t, htp⟩ : pdisk (E.r j))) (mem_univ u₀)
    rw [← hconst, cuspInv_of_mem htp, map_inl]
    simp only [h]
    rw [div_mul_cancel₀ _ h0]

variable [ChartedSpace ℂ Y] (hπ : ChartsAre Y π)

include hπ hd hpow hg hgb hπg hcb hdb in
/-- **The extended map is holomorphic** on the filled Riemann surface. -/
theorem contMDiff_map :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (map (E := E) g b) := by
  intro x
  have hcont := (continuous_map hg hgb).continuousAt (x := x)
  rcases x with y | j
  · refine contMDiffAt_of_formula hcont contDiff_id fun z hz => ?_
    show liftChart (chartAt ℂ (g y)) (inl (g ((chartAt ℂ y).symm z))) = z
    rw [liftChart_inl, hπ _ (chart_mem_atlas ℂ (g y)), hπg, ← hπ _ (chart_mem_atlas ℂ y)]
    exact (chartAt ℂ y).right_inv hz
  · obtain ⟨ζ, -, hζ⟩ := exists_rotation c d hd hpow hg hgb hπg hcb hdb j
    exact contMDiffAt_of_formula hcont (contDiff_const.mul contDiff_id) fun t ht => hζ t ht

end Fill

end General

section Branch

variable {S : Set ℂ} {Y : Type*} [TopologicalSpace Y] {q : Y → S} {I : Type*}
  {c : I → ℂ} {ρ : ℝ}

/-- A map over the base, restricted to the preimage of a punctured disk. -/
def liftV (g : Y → Y) (hg : ∀ y, q (g y) = q y) {c₀ : ℂ} :
    q ⁻¹' nbhdSet S c₀ ρ → q ⁻¹' nbhdSet S c₀ ρ :=
  fun v => ⟨g v, by simp only [mem_preimage, hg]; exact v.2⟩

/-- The induced map of ends: the end containing the image of the representative. -/
def bMap (g : Y → Y) (hg : ∀ y, q (g y) = q y) (j : BIdx q c ρ) : BIdx q c ρ :=
  ⟨j.1, ⟨pathComponent (liftV g hg j.rep), _, rfl⟩⟩

@[simp] lemma bMap_fst (g : Y → Y) (hg : ∀ y, q (g y) = q y) (j : BIdx q c ρ) :
    (bMap g hg j).1 = j.1 := rfl

lemma continuous_liftV {g : Y → Y} (hgc : Continuous g) (hg : ∀ y, q (g y) = q y) {c₀ : ℂ} :
    Continuous (liftV (ρ := ρ) (S := S) g hg (c₀ := c₀)) :=
  (hgc.comp (continuous_subtype_val)).subtype_mk _

lemma joined_map {X X' : Type*} [TopologicalSpace X] [TopologicalSpace X'] {x y : X}
    (h : Joined x y) {f : X → X'} (hf : Continuous f) : Joined (f x) (f y) :=
  ⟨h.somePath.map hf⟩

lemma BIdx.ext' {j j' : BIdx q c ρ} (h1 : j.1 = j'.1)
    (h2 : ∀ (h : j.1 = j'.1), (h ▸ j.2 : CompIdx q c ρ j'.1).1 = j'.2.1) : j = j' := by
  obtain ⟨i, P, hP⟩ := j
  obtain ⟨i', P', hP'⟩ := j'
  simp only at h1
  subst h1
  have := h2 rfl
  simp only at this
  subst this
  rfl

lemma mem_bMap_rep {g : Y → Y} (hgc : Continuous g) (hg : ∀ y, q (g y) = q y)
    {j : BIdx q c ρ} {v : q ⁻¹' nbhdSet S (c j.1) ρ} (hv : v ∈ pathComponent j.rep) :
    liftV g hg v ∈ pathComponent (bMap g hg j).rep := by
  have h := BIdx.eq_rep (bMap g hg j)
  change pathComponent (liftV g hg j.rep) = _ at h
  rw [← h]
  exact joined_map hv (continuous_liftV hgc hg)

lemma mem_range_bMap {g : Y → Y} (hgc : Continuous g) (hg : ∀ y, q (g y) = q y)
    {j : BIdx q c ρ} {y : Y} (hy : y ∈ range (incl (q := q) j.rep)) :
    g y ∈ range (incl (q := q) (bMap g hg j).rep) := by
  obtain ⟨x, rfl⟩ := hy
  exact ⟨⟨liftV g hg x.1, mem_bMap_rep hgc hg x.2⟩, rfl⟩

lemma bMap_id (j : BIdx q c ρ) : bMap id (fun _ => rfl) j = j := by
  refine BIdx.ext' rfl fun _ => ?_
  change pathComponent (liftV id _ j.rep) = j.2.1
  rw [BIdx.eq_rep j]; rfl

lemma bMap_comp {g h : Y → Y} (hgc : Continuous g)
    (hg : ∀ y, q (g y) = q y) (hh : ∀ y, q (h y) = q y) (j : BIdx q c ρ) :
    bMap (g ∘ h) (fun y => (hg (h y)).trans (hh y)) j = bMap g hg (bMap h hh j) := by
  refine BIdx.ext' rfl fun _ => ?_
  change pathComponent (liftV (g ∘ h) _ j.rep) = pathComponent (liftV g hg (bMap h hh j).rep)
  have h1 : (bMap h hh j).rep ∈ pathComponent (liftV h hh j.rep) := by
    have := BIdx.eq_rep (bMap h hh j)
    change pathComponent (liftV h hh j.rep) = _ at this
    rw [this]; exact mem_pathComponent_self _
  have h2 := joined_map h1 (continuous_liftV hgc hg)
  exact (pathComponent_congr h2).symm

variable [LocPathConnectedSpace Y] (hq : IsCoveringMap q) (d : I → ℕ)
  (hmodel : ∀ i (y : q ⁻¹' nbhdSet S (c i) ρ), ∃ Φ : LocComp q y ≃ₜ pdisk (rootRad ρ (d i)),
    ∀ x, ((Φ x : ℂ)) ^ (d i) = (q (incl y x) : ℂ) - c i)

/-- **Maps over the base are compatible with the ends** of `branchEnds`. -/
lemma endCompat_bMap (hρ : 0 < ρ) (hcS : ∀ i, c i ∉ S) (hd : ∀ i, 0 < d i)
    (hdisj : ∀ i i', i ≠ i' → ∀ z : ℂ, z - c i ∈ pdisk ρ → z - c i' ∉ pdisk ρ)
    {g : Y → Y} (hgc : Continuous g) (hg : ∀ y, q (g y) = q y) :
    Fill.EndCompat (branchEnds hq d hmodel hρ hcS hd hdisj) g (bMap g hg) := by
  intro j y hy
  refine ⟨mem_range_bMap hgc hg hy, ?_⟩
  have h1 := branchEnds_pow hq d hmodel hρ hcS hd hdisj (bMap g hg j) ⟨g y,
    mem_range_bMap hgc hg hy⟩
  have h2 := branchEnds_pow hq d hmodel hρ hcS hd hdisj j ⟨y, hy⟩
  simp only [bMap_fst] at h1
  have h3 := congrArg norm (h1.trans ((congrArg (fun z : S => (z : ℂ) - c j.1) (hg y)).trans
    h2.symm))
  simp only [norm_pow] at h3
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (hd j.1).ne').1 h3

end Branch

end SteklovFill
