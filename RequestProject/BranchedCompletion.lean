module

public import RequestProject.LocalInertia
public import RequestProject.PunctureFillingRiemann

/-!
# Branched completion of a covering of a plane domain from local power models

Let `q : Y → S` be a covering of a domain `S ⊆ ℂ`, let `c i ∉ S` (`i : I`) be punctures whose
punctured `ρ`-disks lie in `S` and are pairwise disjoint, and suppose that over each punctured disk
every path component of `q⁻¹{0 < |z - c i| < ρ}` is a power cover `z = c i + Φ^(d i)` (as proved
for the actual cover in `Degree7Inertia.lean`).  Then these path components are punctured-disk ends
of `Y` (`branchEnds`) satisfying the hypotheses of `PunctureFilling.lean`, with
`(Φ j x)^(d j) = q x - c j`.  Filling them produces the branched completion of `q`.
-/

@[expose] public section

open Set Topology SteklovPunctured

noncomputable section

namespace SteklovFill

variable {S : Set ℂ} {Y : Type*} [TopologicalSpace Y] {q : Y → S} {I : Type*}
  {c : I → ℂ} {ρ : ℝ}

/-- The path components of `q⁻¹{0 < |z - c i| < ρ}`. -/
def CompIdx (q : Y → S) (c : I → ℂ) (ρ : ℝ) (i : I) : Type _ :=
  {P : Set (q ⁻¹' nbhdSet S (c i) ρ) // ∃ y, P = pathComponent y}

/-- The ends: all such path components, for all punctures. -/
def BIdx (q : Y → S) (c : I → ℂ) (ρ : ℝ) : Type _ := Σ i, CompIdx q c ρ i

/-- A representative point of an end. -/
def BIdx.rep (j : BIdx q c ρ) : q ⁻¹' nbhdSet S (c j.1) ρ := j.2.2.choose

lemma BIdx.eq_rep (j : BIdx q c ρ) : j.2.1 = pathComponent j.rep := j.2.2.choose_spec

lemma isOpen_nbhdSet (c₀ : ℂ) : IsOpen (nbhdSet S c₀ ρ) :=
  (isOpen_pdisk ρ).preimage ((continuous_subtype_val).sub continuous_const)

variable [LocPathConnectedSpace Y]

lemma isOpenEmbedding_incl (hq : Continuous q) {c₀ : ℂ} (y₀ : q ⁻¹' nbhdSet S c₀ ρ) :
    IsOpenEmbedding (incl (q := q) y₀) := by
  have hV : IsOpen (q ⁻¹' nbhdSet S c₀ ρ) := (isOpen_nbhdSet c₀).preimage hq
  haveI : LocPathConnectedSpace (q ⁻¹' nbhdSet S c₀ ρ) := hV.locPathConnectedSpace
  exact hV.isOpenEmbedding_subtypeVal.comp (IsOpen.pathComponent y₀).isOpenEmbedding_subtypeVal


variable (hq : IsCoveringMap q) (d : I → ℕ)
  (hmodel : ∀ i (y : q ⁻¹' nbhdSet S (c i) ρ), ∃ Φ : LocComp q y ≃ₜ pdisk (rootRad ρ (d i)),
    ∀ x, ((Φ x : ℂ)) ^ (d i) = (q (incl y x) : ℂ) - c i)

/-- The chosen power-model coordinate on an end. -/
def branchModel (j : BIdx q c ρ) : LocComp q j.rep ≃ₜ pdisk (rootRad ρ (d j.1)) :=
  (hmodel j.1 j.rep).choose

omit [LocPathConnectedSpace Y] in
lemma branchModel_pow (j : BIdx q c ρ) (x : LocComp q j.rep) :
    ((branchModel d hmodel j x : ℂ)) ^ (d j.1) = (q (incl j.rep x) : ℂ) - c j.1 :=
  (hmodel j.1 j.rep).choose_spec x

include hq in
/-- The end coordinate on the image of an end in `Y`. -/
def branchPhi (j : BIdx q c ρ) : range (incl (q := q) j.rep) ≃ₜ pdisk (rootRad ρ (d j.1)) :=
  ((isOpenEmbedding_incl hq.continuous j.rep).isEmbedding.toHomeomorph).symm.trans
    (branchModel d hmodel j)

lemma branchPhi_pow (j : BIdx q c ρ) (x : range (incl (q := q) j.rep)) :
    ((branchPhi hq d hmodel j x : ℂ)) ^ (d j.1) = (q x : ℂ) - c j.1 := by
  have h := branchModel_pow d hmodel j
    (((isOpenEmbedding_incl hq.continuous j.rep).isEmbedding.toHomeomorph).symm x)
  have hx : incl j.rep (((isOpenEmbedding_incl hq.continuous j.rep).isEmbedding.toHomeomorph).symm
      x) = x := by
    have := ((isOpenEmbedding_incl hq.continuous j.rep).isEmbedding.toHomeomorph).apply_symm_apply x
    exact congrArg Subtype.val this
  rw [hx] at h
  exact h

omit [LocPathConnectedSpace Y] in
lemma mem_pdisk_of_mem_range {j : BIdx q c ρ} {y : Y} (hy : y ∈ range (incl (q := q) j.rep)) :
    (q y : ℂ) - c j.1 ∈ pdisk ρ := by
  obtain ⟨x, rfl⟩ := hy; exact x.1.2

omit [LocPathConnectedSpace Y] in
/-- Distinct ends are disjoint. -/
lemma branch_disj
    (hdisj : ∀ i i', i ≠ i' → ∀ z : ℂ, z - c i ∈ pdisk ρ → z - c i' ∉ pdisk ρ) :
    Pairwise fun j j' : BIdx q c ρ =>
      Disjoint (range (incl (q := q) j.rep)) (range (incl (q := q) j'.rep)) := by
  intro j j' hne
  rw [Set.disjoint_left]
  rintro y hy hy'
  by_cases hi : j.1 = j'.1
  · obtain ⟨i, P, hP⟩ := j
    obtain ⟨i', P', hP'⟩ := j'
    simp only at hi
    subst hi
    apply hne
    obtain ⟨x, rfl⟩ := hy
    obtain ⟨x', hx'⟩ := hy'
    have hxx : x'.1 = x.1 := Subtype.ext hx'
    have h1 : P = pathComponent x.1 :=
      (BIdx.eq_rep ⟨i, P, hP⟩).trans (pathComponent_congr x.2).symm
    have h2 : P' = pathComponent x'.1 :=
      (BIdx.eq_rep ⟨i, P', hP'⟩).trans (pathComponent_congr x'.2).symm
    rw [hxx] at h2
    have : P = P' := h1.trans h2.symm
    subst this
    rfl
  · exact hdisj _ _ hi _ (mem_pdisk_of_mem_range hy) (mem_pdisk_of_mem_range hy')


/-- Closed punctured subdisks of an end are closed in `Y`. -/
lemma branch_closed (hρ : 0 < ρ) (hcS : ∀ i, c i ∉ S) (hd : ∀ i, 0 < d i) (j : BIdx q c ρ)
    (ε : ℝ) (hε : 0 < ε) (hεr : ε < rootRad ρ (d j.1)) :
    IsClosed (Subtype.val '' {x : range (incl (q := q) j.rep) |
      ‖((branchPhi hq d hmodel j x : pdisk (rootRad ρ (d j.1))) : ℂ)‖ ≤ ε}) := by
  haveI : Fact (0 < ρ) := ⟨hρ⟩
  set A := Subtype.val '' {x : range (incl (q := q) j.rep) |
      ‖((branchPhi hq d hmodel j x : pdisk (rootRad ρ (d j.1))) : ℂ)‖ ≤ ε}
  have hdj := hd j.1
  have hnorm : ∀ x : range (incl (q := q) j.rep),
      ‖((branchPhi hq d hmodel j x : pdisk (rootRad ρ (d j.1))) : ℂ)‖ ≤ ε ↔
        ‖(q x : ℂ) - c j.1‖ ≤ ε ^ (d j.1) := by
    intro x
    rw [← branchPhi_pow hq d hmodel j x, norm_pow]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le hdj.ne').symm
  have hεd : ε ^ (d j.1) < ρ := by
    have := pow_lt_pow_left₀ hεr hε.le hdj.ne'
    rwa [rootRad_pow hdj] at this
  set B := {y : Y | ‖(q y : ℂ) - c j.1‖ ≤ ε ^ (d j.1)}
  have hB : IsClosed B := isClosed_le
    (continuous_norm.comp ((continuous_subtype_val.comp hq.continuous).sub continuous_const))
    continuous_const
  have hAB : A ⊆ B := by
    rintro _ ⟨x, hx, rfl⟩; exact (hnorm x).1 hx
  refine isClosed_of_closure_subset fun y hy => ?_
  have hyB : y ∈ B := hB.closure_subset_iff.2 hAB hy
  have hne : (q y : ℂ) ≠ c j.1 := fun h => hcS j.1 (h ▸ (q y).2)
  have hyV : q y ∈ nbhdSet S (c j.1) ρ := ⟨sub_ne_zero.2 hne, lt_of_le_of_lt hyB hεd⟩
  set V := q ⁻¹' nbhdSet S (c j.1) ρ
  have hVo : IsOpen V := (isOpen_nbhdSet (c j.1)).preimage hq.continuous
  haveI : LocPathConnectedSpace V := hVo.locPathConnectedSpace
  set z : V := ⟨y, hyV⟩
  have hsub : (Subtype.val ⁻¹' A : Set V) ⊆ pathComponent j.rep := by
    rintro w ⟨x, -, hxw⟩
    obtain ⟨x', hx'⟩ := x.2
    have : x'.1 = w := Subtype.ext (hx'.trans hxw)
    rw [← this]; exact x'.2
  have hzcl : z ∈ closure (Subtype.val ⁻¹' A : Set V) := by
    rw [IsInducing.subtypeVal.closure_eq_preimage_closure_image, Subtype.image_preimage_coe]
    have : V ∩ A = A := inter_eq_right.2 (by
      rintro _ ⟨x, -, rfl⟩; obtain ⟨x', hx'⟩ := x.2; rw [← hx']; exact x'.1.2)
    rw [this]; exact hy
  have hz : z ∈ pathComponent j.rep :=
    (IsClosed.pathComponent j.rep).closure_subset_iff.2 hsub hzcl
  have hyr : y ∈ range (incl (q := q) j.rep) := ⟨⟨z, hz⟩, rfl⟩
  exact ⟨⟨y, hyr⟩, (hnorm ⟨y, hyr⟩).2 hyB, rfl⟩

/-- **The punctured-disk ends of a covering with local power models.** -/
def branchEnds (hρ : 0 < ρ) (hcS : ∀ i, c i ∉ S) (hd : ∀ i, 0 < d i)
    (hdisj : ∀ i i', i ≠ i' → ∀ z : ℂ, z - c i ∈ pdisk ρ → z - c i' ∉ pdisk ρ) :
    Ends Y (BIdx q c ρ) where
  U j := range (incl (q := q) j.rep)
  isOpen_U j := (isOpenEmbedding_incl hq.continuous j.rep).isOpen_range
  r j := rootRad ρ (d j.1)
  r_pos _ := rootRad_pos _ _
  Φ j := branchPhi hq d hmodel j
  disj := branch_disj hdisj
  closed j ε hε hεr := branch_closed hq d hmodel hρ hcS hd j ε hε hεr

lemma branchEnds_pow (hρ : 0 < ρ) (hcS : ∀ i, c i ∉ S) (hd : ∀ i, 0 < d i)
    (hdisj : ∀ i i', i ≠ i' → ∀ z : ℂ, z - c i ∈ pdisk ρ → z - c i' ∉ pdisk ρ)
    (j : BIdx q c ρ) (x : (branchEnds hq d hmodel hρ hcS hd hdisj).U j) :
    (((branchEnds hq d hmodel hρ hcS hd hdisj).Φ j x : pdisk _) : ℂ) ^ (d j.1) =
      (q x : ℂ) - c j.1 :=
  branchPhi_pow hq d hmodel j x

end SteklovFill
