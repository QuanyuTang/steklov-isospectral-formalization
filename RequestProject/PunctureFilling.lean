module

public import RequestProject.PuncturedDiskCover

/-!
# Filling in punctures: the one-point completion of punctured-disk ends

Let `Y` be a topological space with a family of pairwise disjoint open subsets `U j` (the *ends*),
each homeomorphic to a punctured disk `{0 < |t| < r j}` by `Φ j`, such that the closed punctured
subdisks `{0 < |t| ≤ ε}` are closed in `Y`.  The space `Fill E = Y ⊕ J` gets the topology in which a
set is open iff its trace on `Y` is open and, whenever it contains the new point `j`, it contains a
punctured neighbourhood `Φ j⁻¹{0 < |t| < ε}` of the end.  We prove:

* `isOpenEmbedding_inl`: `Y` is an open subspace of `Fill E`;
* `cuspChart j`: the extension of `Φ j` by `j ↦ 0` is a homeomorphism from the open set
  `U j ∪ {j}` onto the disk `{|t| < r j}`;
* `t2Space` : `Fill E` is Hausdorff when `Y` is.

This is the topological "analytic fill-in" of punctures used for branched covers.
-/

@[expose] public section

open Set Topology SteklovPunctured

noncomputable section

namespace SteklovFill

/-- Punctured-disk ends of a space `Y`, indexed by `J`. -/
structure Ends (Y : Type*) [TopologicalSpace Y] (J : Type*) where
  /-- the end neighbourhoods -/
  U : J → Set Y
  isOpen_U : ∀ j, IsOpen (U j)
  /-- radii -/
  r : J → ℝ
  r_pos : ∀ j, 0 < r j
  /-- the punctured-disk coordinates -/
  Φ : ∀ j, U j ≃ₜ pdisk (r j)
  disj : Pairwise fun j j' => Disjoint (U j) (U j')
  closed : ∀ j (ε : ℝ), 0 < ε → ε < r j →
    IsClosed (Subtype.val '' {x : U j | ‖((Φ j x : pdisk (r j)) : ℂ)‖ ≤ ε})

variable {Y : Type*} [TopologicalSpace Y] {J : Type*} (E : Ends Y J)

namespace Ends

/-- The punctured neighbourhood `Φ j⁻¹{0 < |t| < ε}` of the end `j`, as a subset of `Y`. -/
def nbd (j : J) (ε : ℝ) : Set Y :=
  Subtype.val '' {x : E.U j | ‖((E.Φ j x : pdisk (E.r j)) : ℂ)‖ < ε}

lemma isOpen_nbd (j : J) (ε : ℝ) : IsOpen (E.nbd j ε) :=
  (E.isOpen_U j).isOpenMap_subtype_val _
    (isOpen_lt (continuous_norm.comp (continuous_subtype_val.comp (E.Φ j).continuous))
      continuous_const)

lemma nbd_subset_U (j : J) (ε : ℝ) : E.nbd j ε ⊆ E.U j := by
  rintro _ ⟨x, -, rfl⟩; exact x.2

lemma nbd_mono (j : J) {ε ε' : ℝ} (h : ε ≤ ε') : E.nbd j ε ⊆ E.nbd j ε' := by
  rintro _ ⟨x, hx, rfl⟩; exact ⟨x, lt_of_lt_of_le hx h, rfl⟩

lemma mem_nbd {j : J} {ε : ℝ} {y : Y} (hy : y ∈ E.U j) :
    y ∈ E.nbd j ε ↔ ‖((E.Φ j ⟨y, hy⟩ : pdisk (E.r j)) : ℂ)‖ < ε := by
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro h; exact ⟨⟨y, hy⟩, h, rfl⟩

end Ends

/-- The space with the punctures filled in. -/
def Fill (_E : Ends Y J) : Type _ := Y ⊕ J

namespace Fill

variable {E}

/-- The original space inside the filling. -/
def inl : Y → Fill E := Sum.inl

/-- The new point filling the end `j`. -/
def cusp (j : J) : Fill E := Sum.inr j

lemma inl_injective : Function.Injective (inl (E := E)) := Sum.inl_injective

lemma inl_ne_cusp (y : Y) (j : J) : inl (E := E) y ≠ cusp j := Sum.inl_ne_inr

lemma cusp_injective : Function.Injective (cusp (E := E)) := Sum.inr_injective

variable (E) in
/-- The topology of the filling. -/
instance instTop : TopologicalSpace (Fill E) where
  IsOpen W := IsOpen (inl ⁻¹' W : Set Y) ∧ ∀ j, cusp j ∈ W → ∃ ε > 0, E.nbd j ε ⊆ inl ⁻¹' W
  isOpen_univ := ⟨isOpen_univ, fun _ _ => ⟨1, one_pos, subset_univ _⟩⟩
  isOpen_inter W W' hW hW' := by
    refine ⟨hW.1.inter hW'.1, fun j hj => ?_⟩
    obtain ⟨ε, hε, h⟩ := hW.2 j hj.1
    obtain ⟨ε', hε', h'⟩ := hW'.2 j hj.2
    exact ⟨min ε ε', lt_min hε hε', fun y hy =>
      ⟨h (E.nbd_mono j (min_le_left _ _) hy), h' (E.nbd_mono j (min_le_right _ _) hy)⟩⟩
  isOpen_sUnion S hS := by
    refine ⟨?_, fun j hj => ?_⟩
    · rw [preimage_sUnion]
      exact isOpen_biUnion fun W hW => (hS W hW).1
    · obtain ⟨W, hW, hjW⟩ := hj
      obtain ⟨ε, hε, h⟩ := (hS W hW).2 j hjW
      exact ⟨ε, hε, fun y hy => ⟨W, hW, h hy⟩⟩

lemma isOpen_iff {W : Set (Fill E)} :
    IsOpen W ↔ IsOpen (inl ⁻¹' W : Set Y) ∧
      ∀ j, cusp j ∈ W → ∃ ε > 0, E.nbd j ε ⊆ inl ⁻¹' W := Iff.rfl

lemma continuous_inl : Continuous (inl (E := E)) :=
  ⟨fun _ hW => hW.1⟩

lemma isOpenMap_inl : IsOpenMap (inl (E := E)) := by
  intro V hV
  refine ⟨by rwa [inl_injective.preimage_image], fun j hj => ?_⟩
  obtain ⟨y, -, hy⟩ := hj
  exact absurd hy (inl_ne_cusp y j)

/-- **`Y` is an open subspace of its filling.** -/
theorem isOpenEmbedding_inl : IsOpenEmbedding (inl (E := E)) :=
  .of_continuous_injective_isOpenMap continuous_inl inl_injective isOpenMap_inl

/-- The open set `U j ∪ {cusp j}`. -/
def cuspSet (j : J) : Set (Fill E) := inl '' E.U j ∪ {cusp j}

lemma isOpen_cuspSet (j : J) : IsOpen (cuspSet (E := E) j) := by
  refine ⟨?_, fun j' hj' => ?_⟩
  · have : inl ⁻¹' cuspSet (E := E) j = E.U j := by
      ext y
      simp only [cuspSet, mem_preimage, mem_union, mem_image, mem_singleton_iff]
      constructor
      · rintro (⟨y', hy', h⟩ | h)
        · rw [← inl_injective h]; exact hy'
        · exact absurd h (inl_ne_cusp y j)
      · intro hy; exact Or.inl ⟨y, hy, rfl⟩
    rw [this]; exact E.isOpen_U j
  · have hj : j' = j := by
      rcases hj' with ⟨y, -, h⟩ | h
      · exact absurd h (inl_ne_cusp y j')
      · exact cusp_injective h
    subst hj
    exact ⟨E.r j', E.r_pos j', fun y hy => Or.inl ⟨y, E.nbd_subset_U j' _ hy, rfl⟩⟩

open Classical in
/-- The coordinate of the cusp chart: `Φ j` on `U j`, and `0` elsewhere. -/
def cuspFun (j : J) : Fill E → ℂ
  | Sum.inl y => if h : y ∈ E.U j then ((E.Φ j ⟨y, h⟩ : pdisk (E.r j)) : ℂ) else 0
  | Sum.inr _ => 0

open Classical in
/-- The inverse of the cusp chart. -/
def cuspInv (j : J) (t : ℂ) : Fill E :=
  if h : t ∈ pdisk (E.r j) then inl ((E.Φ j).symm ⟨t, h⟩ : Y) else cusp j

lemma cuspFun_inl {j : J} {y : Y} (hy : y ∈ E.U j) :
    cuspFun j (inl (E := E) y) = ((E.Φ j ⟨y, hy⟩ : pdisk (E.r j)) : ℂ) := by
  simp only [cuspFun, inl]; rw [dif_pos hy]

lemma cuspFun_cusp (j j' : J) : cuspFun j (cusp (E := E) j') = 0 := rfl

lemma cuspInv_zero (j : J) : cuspInv (E := E) j 0 = cusp j := by
  rw [cuspInv, dif_neg (fun h => h.1 rfl)]

lemma cuspInv_of_mem {j : J} {t : ℂ} (ht : t ∈ pdisk (E.r j)) :
    cuspInv (E := E) j t = inl ((E.Φ j).symm ⟨t, ht⟩ : Y) := by
  rw [cuspInv, dif_pos ht]

lemma mem_cuspSet {j : J} {w : Fill E} :
    w ∈ cuspSet j ↔ (∃ y ∈ E.U j, w = inl y) ∨ w = cusp j := by
  simp only [cuspSet, mem_union, mem_image, mem_singleton_iff]
  constructor
  · rintro (⟨y, hy, rfl⟩ | h)
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr h
  · rintro (⟨y, hy, rfl⟩ | h)
    · exact Or.inl ⟨y, hy, rfl⟩
    · exact Or.inr h

/-- **The cusp chart**: `U j ∪ {cusp j} ≃ {|t| < r j}`, extending `Φ j` by `cusp j ↦ 0`. -/
def cuspChart (j : J) : OpenPartialHomeomorph (Fill E) ℂ where
  toFun := cuspFun j
  invFun := cuspInv j
  source := cuspSet j
  target := Metric.ball 0 (E.r j)
  map_source' w hw := by
    rcases mem_cuspSet.1 hw with ⟨y, hy, rfl⟩ | rfl
    · rw [cuspFun_inl hy, mem_ball_zero_iff]; exact (E.Φ j ⟨y, hy⟩).2.2
    · rw [cuspFun_cusp, mem_ball_zero_iff, norm_zero]; exact E.r_pos j
  map_target' t ht := by
    by_cases h : t ∈ pdisk (E.r j)
    · rw [cuspInv_of_mem h]; exact Or.inl ⟨_, ((E.Φ j).symm ⟨t, h⟩).2, rfl⟩
    · rw [cuspInv, dif_neg h]; exact Or.inr rfl
  left_inv' w hw := by
    rcases mem_cuspSet.1 hw with ⟨y, hy, rfl⟩ | rfl
    · rw [cuspFun_inl hy, cuspInv_of_mem (E.Φ j ⟨y, hy⟩).2]
      simp
    · rw [cuspFun_cusp, cuspInv_zero]
  right_inv' t ht := by
    by_cases h : t ∈ pdisk (E.r j)
    · rw [cuspInv_of_mem h, cuspFun_inl ((E.Φ j).symm ⟨t, h⟩).2]
      simp
    · have : t = 0 := by
        by_contra h0
        exact h ⟨h0, mem_ball_zero_iff.1 ht⟩
      subst this
      rw [cuspInv_zero, cuspFun_cusp]
  open_source := isOpen_cuspSet j
  open_target := Metric.isOpen_ball
  continuousOn_toFun := by
    rw [continuousOn_open_iff (isOpen_cuspSet j)]
    intro O hO
    refine ⟨?_, fun j' hj' => ?_⟩
    · have : inl ⁻¹' (cuspSet (E := E) j ∩ cuspFun j ⁻¹' O) =
          Subtype.val '' ((E.Φ j) ⁻¹' (Subtype.val ⁻¹' O)) := by
        ext y
        simp only [mem_preimage, mem_inter_iff, mem_image]
        constructor
        · rintro ⟨hy, hO'⟩
          have hyU : y ∈ E.U j := by
            rcases mem_cuspSet.1 hy with ⟨y', hy', h⟩ | h
            · rw [inl_injective h]; exact hy'
            · exact absurd h (inl_ne_cusp y j)
          rw [cuspFun_inl hyU] at hO'
          exact ⟨⟨y, hyU⟩, hO', rfl⟩
        · rintro ⟨x, hx, rfl⟩
          refine ⟨Or.inl ⟨x.1, x.2, rfl⟩, ?_⟩
          rw [cuspFun_inl x.2]; exact hx
      rw [this]
      exact (E.isOpen_U j).isOpenMap_subtype_val _
        ((hO.preimage continuous_subtype_val).preimage (E.Φ j).continuous)
    · have hj : j' = j := by
        rcases mem_cuspSet.1 hj'.1 with ⟨y, -, h⟩ | h
        · exact absurd h.symm (inl_ne_cusp y j')
        · exact cusp_injective h
      subst hj
      have h0 : (0 : ℂ) ∈ O := hj'.2
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO 0 h0
      refine ⟨ε, hε, fun y hy => ?_⟩
      have hyU := E.nbd_subset_U j' ε hy
      refine ⟨Or.inl ⟨y, hyU, rfl⟩, ?_⟩
      show cuspFun j' (inl y) ∈ O
      rw [cuspFun_inl hyU]
      exact hball (mem_ball_zero_iff.2 ((E.mem_nbd hyU).1 hy))
  continuousOn_invFun := by
    rw [continuousOn_open_iff Metric.isOpen_ball]
    intro W hW
    have hpd : IsOpen (pdisk (E.r j)) := isOpen_pdisk _
    -- the punctured part
    have h1 : IsOpen (Subtype.val '' ((E.Φ j).symm ⁻¹' (Subtype.val ⁻¹' (inl ⁻¹' W))) :
        Set ℂ) :=
      hpd.isOpenMap_subtype_val _
        ((hW.1.preimage continuous_subtype_val).preimage (E.Φ j).symm.continuous)
    by_cases hc : cusp j ∈ W
    · obtain ⟨ε, hε, hnbd⟩ := hW.2 j hc
      have : Metric.ball 0 (E.r j) ∩ cuspInv j ⁻¹' W =
          Subtype.val '' ((E.Φ j).symm ⁻¹' (Subtype.val ⁻¹' (inl ⁻¹' W))) ∪
            Metric.ball 0 (min ε (E.r j)) := by
        ext t
        simp only [mem_inter_iff, mem_preimage, mem_union, mem_image]
        constructor
        · rintro ⟨ht, htW⟩
          by_cases h : t ∈ pdisk (E.r j)
          · rw [cuspInv_of_mem h] at htW
            exact Or.inl ⟨⟨t, h⟩, htW, rfl⟩
          · right
            have : t = 0 := by
              by_contra h0; exact h ⟨h0, mem_ball_zero_iff.1 ht⟩
            subst this; exact Metric.mem_ball_self (lt_min hε (E.r_pos j))
        · rintro (⟨x, hx, rfl⟩ | ht)
          · refine ⟨mem_ball_zero_iff.2 x.2.2, ?_⟩
            rw [cuspInv_of_mem x.2]; exact hx
          · refine ⟨Metric.ball_subset_ball (min_le_right _ _) ht, ?_⟩
            by_cases h : t ∈ pdisk (E.r j)
            · rw [cuspInv_of_mem h]
              apply hnbd
              refine (E.mem_nbd ((E.Φ j).symm ⟨t, h⟩).2).2 ?_
              simp only [Subtype.coe_eta, Homeomorph.apply_symm_apply]
              exact lt_of_lt_of_le (mem_ball_zero_iff.1 ht) (min_le_left _ _)
            · rw [cuspInv, dif_neg h]; exact hc
      rw [this]; exact h1.union Metric.isOpen_ball
    · have : Metric.ball 0 (E.r j) ∩ cuspInv j ⁻¹' W =
          Subtype.val '' ((E.Φ j).symm ⁻¹' (Subtype.val ⁻¹' (inl ⁻¹' W))) := by
        ext t
        simp only [mem_inter_iff, mem_preimage, mem_image]
        constructor
        · rintro ⟨ht, htW⟩
          by_cases h : t ∈ pdisk (E.r j)
          · rw [cuspInv_of_mem h] at htW
            exact ⟨⟨t, h⟩, htW, rfl⟩
          · rw [cuspInv, dif_neg h] at htW; exact absurd htW hc
        · rintro ⟨x, hx, rfl⟩
          refine ⟨mem_ball_zero_iff.2 x.2.2, ?_⟩
          rw [cuspInv_of_mem x.2]; exact hx
      rw [this]; exact h1

/-- A basic neighbourhood `{cusp j} ∪ Φ j⁻¹{0 < |t| < ε}` of a cusp. -/
def cuspNbd (j : J) (ε : ℝ) : Set (Fill E) := insert (cusp j) (inl '' E.nbd j ε)

lemma isOpen_cuspNbd (j : J) {ε : ℝ} (hε : 0 < ε) : IsOpen (cuspNbd (E := E) j ε) := by
  refine ⟨?_, fun j' hj' => ?_⟩
  · have : inl ⁻¹' cuspNbd (E := E) j ε = E.nbd j ε := by
      ext y
      simp only [cuspNbd, mem_preimage, mem_insert_iff, mem_image]
      constructor
      · rintro (h | ⟨y', hy', h⟩)
        · exact absurd h (inl_ne_cusp y j)
        · rw [← inl_injective h]; exact hy'
      · intro hy; exact Or.inr ⟨y, hy, rfl⟩
    rw [this]; exact E.isOpen_nbd j ε
  · have hj : j' = j := by
      rcases hj' with h | ⟨y, -, h⟩
      · exact cusp_injective h
      · exact absurd h (inl_ne_cusp y j')
    subst hj
    exact ⟨ε, hε, fun y hy => Or.inr ⟨y, hy, rfl⟩⟩

lemma cusp_mem_cuspNbd (j : J) (ε : ℝ) : cusp (E := E) j ∈ cuspNbd j ε := mem_insert _ _

lemma cuspSet_disjoint {j j' : J} (h : j ≠ j') :
    Disjoint (cuspSet (E := E) j) (cuspSet j') := by
  rw [Set.disjoint_left]
  intro w hw hw'
  rcases mem_cuspSet.1 hw with ⟨y, hy, rfl⟩ | rfl
  · rcases mem_cuspSet.1 hw' with ⟨y', hy', h'⟩ | h'
    · rw [inl_injective h'] at hy
      exact Set.disjoint_left.1 (E.disj h) hy hy'
    · exact inl_ne_cusp y j' h'
  · rcases mem_cuspSet.1 hw' with ⟨y', -, h'⟩ | h'
    · exact inl_ne_cusp y' j h'.symm
    · exact h (cusp_injective h')

/-- A point of `Y` and a cusp have disjoint neighbourhoods. -/
lemma separate_inl_cusp (y : Y) (j : J) :
    ∃ u v : Set (Fill E), IsOpen u ∧ IsOpen v ∧ inl y ∈ u ∧ cusp j ∈ v ∧ Disjoint u v := by
  set ε := E.r j / 2 with hε
  have hε0 : 0 < ε := half_pos (E.r_pos j)
  have hεr : ε < E.r j := half_lt_self (E.r_pos j)
  set F := Subtype.val '' {x : E.U j | ‖((E.Φ j x : pdisk (E.r j)) : ℂ)‖ ≤ ε}
  have hF : IsClosed F := E.closed j ε hε0 hεr
  by_cases hy : y ∈ F
  · obtain ⟨x, hx, rfl⟩ := hy
    set a := ‖((E.Φ j x : pdisk (E.r j)) : ℂ)‖
    have ha : 0 < a := norm_pos_iff.2 (E.Φ j x).2.1
    refine ⟨inl '' (Subtype.val '' {x' : E.U j | a / 2 < ‖((E.Φ j x' : pdisk (E.r j)) : ℂ)‖}),
      cuspNbd j (a / 2), isOpenMap_inl _ ((E.isOpen_U j).isOpenMap_subtype_val _
        (isOpen_lt continuous_const
          (continuous_norm.comp (continuous_subtype_val.comp (E.Φ j).continuous)))),
      isOpen_cuspNbd j (half_pos ha), ⟨x.1, ⟨x, half_lt_self ha, rfl⟩, rfl⟩,
      cusp_mem_cuspNbd j _, ?_⟩
    rw [Set.disjoint_left]
    rintro w ⟨_, ⟨x', hx', rfl⟩, rfl⟩ hw
    rcases hw with h | ⟨y'', hy'', h⟩
    · exact inl_ne_cusp _ j h
    · rw [inl_injective h] at hy''
      rw [E.mem_nbd x'.2] at hy''
      exact absurd (lt_trans hx' hy'') (lt_irrefl _)
  · refine ⟨inl '' Fᶜ, cuspNbd j ε, isOpenMap_inl _ hF.isOpen_compl, isOpen_cuspNbd j hε0,
      ⟨y, hy, rfl⟩, cusp_mem_cuspNbd j _, ?_⟩
    rw [Set.disjoint_left]
    rintro w ⟨y', hy', rfl⟩ hw
    rcases hw with h | ⟨y'', hy'', h⟩
    · exact inl_ne_cusp _ j h
    · rw [← inl_injective h] at hy'
      apply hy'
      obtain ⟨x, hx, rfl⟩ := hy''
      exact ⟨x, by simp only [mem_setOf_eq] at hx ⊢; exact hx.le, rfl⟩

/-- **The filling is Hausdorff.** -/
instance t2Space [T2Space Y] : T2Space (Fill E) := by
  refine ⟨fun w w' hne => ?_⟩
  rcases w with y | j <;> rcases w' with y' | j'
  · have hne' : y ≠ y' := fun h => hne (congrArg Sum.inl h)
    obtain ⟨u, v, hu, hv, hyu, hyv, huv⟩ := t2_separation hne'
    exact ⟨inl '' u, inl '' v, isOpenMap_inl _ hu, isOpenMap_inl _ hv, ⟨y, hyu, rfl⟩,
      ⟨y', hyv, rfl⟩, (disjoint_image_iff inl_injective).2 huv⟩
  · exact separate_inl_cusp y j'
  · obtain ⟨u, v, hu, hv, h1, h2, h3⟩ := separate_inl_cusp (E := E) y' j
    exact ⟨v, u, hv, hu, h2, h1, h3.symm⟩
  · have hjj : j ≠ j' := fun h => hne (congrArg Sum.inr h)
    exact ⟨cuspSet j, cuspSet j', isOpen_cuspSet j, isOpen_cuspSet j', Or.inr rfl, Or.inr rfl,
      cuspSet_disjoint hjj⟩

end Fill

end SteklovFill
