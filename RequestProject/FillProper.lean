module

public import RequestProject.BranchedCompletion

/-!
# Properness of branched completions

* `isCompact_preimage_of_isCoveringMap`: a covering map with finite fibres over a locally compact
  Hausdorff space is proper (preimages of compact sets are compact);
* `Fill.isCompact_preimage_πFill`: if a map `π : Y → ℂ` is proper over the complement of the
  puncture values, the ends cover a uniform punctured neighbourhood of every puncture value, and
  there are finitely many ends, then the extended branched projection `πFill` is proper;
* `exists_bIdx_of_mem` and `finite_bIdx`: for the ends of a covering with local power models
  (`branchEnds`), every point over a punctured disk lies in an end, and there are finitely many
  ends when the fibres are finite.
-/

@[expose] public section

open Set Topology SteklovPunctured Filter

noncomputable section

namespace SteklovFill

/-- **A covering map with finite fibres is proper.** -/
theorem isCompact_preimage_of_isCoveringMap {E X : Type*} [TopologicalSpace E]
    [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] {f : E → X}
    (hf : IsCoveringMap f) (hfin : ∀ x, Finite (f ⁻¹' {x})) {K : Set X} (hK : IsCompact K) :
    IsCompact (f ⁻¹' K) := by
  -- compact pieces over compact subsets of evenly covered neighbourhoods
  have key : ∀ x : X, ∃ N ∈ 𝓝 x, ∀ C ⊆ N, IsCompact C → IsCompact (f ⁻¹' C) := by
    intro x
    obtain ⟨hdisc, U, hxU, hU, hfU, H, hH⟩ := hf x
    haveI := hfin x
    refine ⟨U, hU.mem_nhds hxU, fun C hCU hC => ?_⟩
    have hCU' : IsCompact ((Subtype.val : U → X) ⁻¹' C) := by
      rw [hU.isOpenEmbedding_subtypeVal.isInducing.isCompact_iff, Subtype.image_preimage_coe,
        inter_eq_right.2 hCU]
      exact hC
    have hprod : IsCompact (((Subtype.val : U → X) ⁻¹' C) ×ˢ (univ : Set (f ⁻¹' {x}))) :=
      hCU'.prod isCompact_univ
    have himg := (hprod.image H.symm.continuous).image (continuous_subtype_val)
    convert himg using 1
    ext e
    simp only [mem_preimage, mem_image, mem_prod, mem_univ, and_true]
    constructor
    · intro he
      have heU : e ∈ f ⁻¹' U := hCU he
      refine ⟨H.symm (H ⟨e, heU⟩), ⟨H ⟨e, heU⟩, ?_, rfl⟩, by simp⟩
      show ((H ⟨e, heU⟩).1 : X) ∈ C
      rw [hH]; exact he
    · rintro ⟨e', ⟨p, hp, rfl⟩, rfl⟩
      have : (H (H.symm p)).1.1 = f (H.symm p) := hH _
      rw [H.apply_symm_apply] at this
      rw [← this]; exact hp
  choose N hN hNC using key
  have hN' : ∀ x, ∃ M ∈ 𝓝 x, M ⊆ N x ∧ IsCompact M := fun x =>
    let ⟨M, hM, hMN, hMc⟩ := local_compact_nhds (hN x)
    ⟨M, hM, hMN, hMc⟩
  choose M hM hMN hMc using hN'
  obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover M (fun x _ => hM x)
  have : f ⁻¹' K = ⋃ x ∈ t, f ⁻¹' (K ∩ M x) := by
    ext e; simp only [mem_preimage, mem_iUnion, mem_inter_iff, exists_prop]
    constructor
    · intro he
      obtain ⟨x, hxt, hx⟩ := mem_iUnion₂.1 (ht he)
      exact ⟨x, hxt, he, hx⟩
    · rintro ⟨x, -, he, -⟩; exact he
  rw [this]
  exact t.isCompact_biUnion fun x _ =>
    hNC x _ (inter_subset_right.trans (hMN x)) (hK.inter_right (hMc x).isClosed)

variable {Y : Type*} [TopologicalSpace Y] {J : Type*} {E : Ends Y J}

namespace Fill

/-- **Properness of the branched projection of a filling.** -/
theorem isCompact_preimage_πFill [Finite J] (π : Y → ℂ) (c : J → ℂ) (d : J → ℕ)
    (hd : ∀ j, 0 < d j)
    (hpow : ∀ j (x : E.U j), ((E.Φ j x : pdisk (E.r j)) : ℂ) ^ (d j) = π x - c j)
    (hcont : Continuous (πFill (E := E) π c))
    (B : Set ℂ) (hY : ∀ K : Set ℂ, IsCompact K → Disjoint K B → IsCompact (π ⁻¹' K))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hcov : ∀ y, ∀ b ∈ B, ‖π y - b‖ < ρ → ∃ j, c j = b ∧ y ∈ E.U j)
    {K : Set ℂ} (hK : IsCompact K) : IsCompact (πFill (E := E) π c ⁻¹' K) := by
  -- a uniform small radius
  obtain ⟨δ, hδ0, hδρ, hδr⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < ρ ∧ ∀ j, δ < E.r j ^ (d j) := by
    have h1 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ j, δ < E.r j ^ (d j) :=
      eventually_all.2 fun j => nhdsWithin_le_nhds
        (eventually_lt_nhds (pow_pos (E.r_pos j) _))
    have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ), δ < ρ := nhdsWithin_le_nhds (eventually_lt_nhds hρ)
    obtain ⟨δ, ⟨h1, h2⟩, h3⟩ := ((h1.and h2).and self_mem_nhdsWithin).exists
    exact ⟨δ, h3, h2, h1⟩
  set K' := K \ ⋃ b ∈ B, Metric.ball b δ
  have hK' : IsCompact K' :=
    hK.diff (isOpen_biUnion fun _ _ => Metric.isOpen_ball)
  have hK'c : Disjoint K' B := Set.disjoint_left.2 fun z hz hzB =>
    hz.2 (mem_iUnion₂.2 ⟨z, hzB, Metric.mem_ball_self hδ0⟩)
  set T : J → Set ℂ := fun j => {t | ‖t‖ ^ (d j) ≤ δ}
  have hTr : ∀ j, T j ⊆ Metric.ball 0 (E.r j) := by
    intro j t ht
    rw [mem_ball_zero_iff]
    exact lt_of_pow_lt_pow_left₀ (d j) (E.r_pos j).le (lt_of_le_of_lt ht (hδr j))
  have hTc : ∀ j, IsCompact (T j) := by
    intro j
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_le (continuous_norm.pow _) continuous_const) ?_
    exact Metric.isBounded_ball.subset (hTr j)
  have hcpt : IsCompact (inl '' (π ⁻¹' K') ∪ ⋃ j, cuspInv (E := E) j '' T j) :=
    ((hY K' hK' hK'c).image continuous_inl).union (isCompact_iUnion fun j =>
      (hTc j).image_of_continuousOn ((cuspChart (E := E) j).continuousOn_symm.mono (hTr j)))
  refine hcpt.of_isClosed_subset (hK.isClosed.preimage hcont) ?_
  rintro (y | j) hw
  · change π y ∈ K at hw
    by_cases hy : π y ∈ ⋃ b ∈ B, Metric.ball b δ
    · obtain ⟨b, hb, hj⟩ := mem_iUnion₂.1 hy
      rw [Metric.mem_ball, dist_eq_norm] at hj
      obtain ⟨j', hcj, hyU⟩ := hcov y b hb (hj.trans hδρ)
      refine Or.inr (mem_iUnion.2 ⟨j', ⟨((E.Φ j' ⟨y, hyU⟩ : pdisk (E.r j')) : ℂ), ?_, ?_⟩⟩)
      · show ‖_‖ ^ (d j') ≤ δ
        rw [← norm_pow, hpow j' ⟨y, hyU⟩, hcj]; exact hj.le
      · rw [cuspInv_of_mem (E.Φ j' ⟨y, hyU⟩).2]; simp; rfl
    · exact Or.inl ⟨y, ⟨hw, hy⟩, rfl⟩
  · refine Or.inr (mem_iUnion.2 ⟨j, 0, ?_, cuspInv_zero j⟩)
    show ‖(0 : ℂ)‖ ^ (d j) ≤ δ
    rw [norm_zero, zero_pow (hd j).ne']; exact hδ0.le

end Fill

section Branch

variable {S : Set ℂ} {q : Y → S} {I : Type*} {c : I → ℂ} {ρ : ℝ}

/-- Every point over a punctured disk lies in one of the ends over it. -/
lemma exists_bIdx_of_mem {i : I} {y : Y} (hy : (q y : ℂ) - c i ∈ pdisk ρ) :
    ∃ j : BIdx q c ρ, j.1 = i ∧ y ∈ range (incl (q := q) j.rep) := by
  set v : q ⁻¹' nbhdSet S (c i) ρ := ⟨y, hy⟩
  set j : BIdx q c ρ := ⟨i, pathComponent v, v, rfl⟩
  refine ⟨j, rfl, ⟨⟨v, ?_⟩, rfl⟩⟩
  have h := BIdx.eq_rep j
  change pathComponent v = pathComponent j.rep at h
  change v ∈ pathComponent j.rep
  rw [← h]; exact mem_pathComponent_self v

variable [LocallyPathConnectedSpace Y] (hq : IsCoveringMap q) (d : I → ℕ)
  (hmodel : ∀ i (y : q ⁻¹' nbhdSet S (c i) ρ), ∃ Φ : LocComp q y ≃ₜ pdisk (rootRad ρ (d i)),
    ∀ x, ((Φ x : ℂ)) ^ (d i) = (q (incl y x) : ℂ) - c i)

omit [LocallyPathConnectedSpace Y] in
include hmodel in
/-- **Finitely many ends.**  With finitely many punctures and finite fibres, the ends of a
covering with local power models are finite in number. -/
lemma finite_bIdx [Finite I] (hρ : 0 < ρ) (hd : ∀ i, 0 < d i)
    (hdisj : ∀ i i', i ≠ i' → ∀ z : ℂ, z - c i ∈ pdisk ρ → z - c i' ∉ pdisk ρ)
    (hfin : ∀ x, Finite (q ⁻¹' {x})) : Finite (BIdx q c ρ) := by
  -- the point of each end lying over `c i + ρ/2`
  have ht : ∀ i, ((rootRad (ρ / 2) (d i) : ℝ) : ℂ) ∈ pdisk (rootRad ρ (d i)) := by
    intro i
    refine ⟨by exact_mod_cast (rootRad_pos _ _).ne', ?_⟩
    rw [Complex.norm_real, Real.norm_of_nonneg (rootRad_pos _ _).le]
    unfold rootRad
    apply Real.exp_lt_exp.2
    have hdi : (0 : ℝ) < d i := by exact_mod_cast hd i
    apply div_lt_div_of_pos_right _ hdi
    exact Real.log_lt_log (by positivity) (by linarith)
  let F : BIdx q c ρ → Y := fun j =>
    incl j.rep ((branchModel d hmodel j).symm ⟨_, ht j.1⟩)
  have hF : ∀ j, (q (F j) : ℂ) = c j.1 + ρ / 2 := by
    intro j
    have h := branchModel_pow d hmodel j ((branchModel d hmodel j).symm ⟨_, ht j.1⟩)
    rw [Homeomorph.apply_symm_apply] at h
    have h2 : ((rootRad (ρ / 2) (d j.1) : ℝ) : ℂ) ^ (d j.1) = ((ρ / 2 : ℝ) : ℂ) := by
      haveI : Fact (0 < ρ / 2) := ⟨by positivity⟩
      rw [← Complex.ofReal_pow, rootRad_pow (hd j.1)]
    simp only at h
    rw [h2] at h
    change _ = (q (F j) : ℂ) - c j.1 at h
    rw [eq_sub_iff_add_eq] at h
    rw [← h]; push_cast; ring
  have hFinj : Function.Injective F := by
    intro j j' h
    by_contra hne
    exact Set.disjoint_left.1 (branch_disj hdisj hne) (mem_range_self _)
      (h ▸ mem_range_self _ : F j ∈ range (incl (q := q) j'.rep))
  set P : Set ℂ := range fun i => c i + ρ / 2
  have hP : (q ⁻¹' ((Subtype.val : S → ℂ) ⁻¹' P)).Finite :=
    ((finite_range _).preimage Subtype.val_injective.injOn).preimage'
      fun x _ => by haveI := hfin x; exact Set.toFinite _
  haveI := hP.to_subtype
  exact Finite.of_injective (fun j => (⟨F j, ⟨j.1, (hF j).symm⟩⟩ :
    q ⁻¹' ((Subtype.val : S → ℂ) ⁻¹' P))) fun j j' h => hFinj (congrArg Subtype.val h)

end Branch

end SteklovFill
