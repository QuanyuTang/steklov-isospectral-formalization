module

public import Mathlib

/-!
# Disjoint union of two covering maps

For covering maps `p₁ : E₁ → X`, `p₂ : E₂ → X`, the map `Sum.elim p₁ p₂ : E₁ ⊕ E₂ → X` is a
covering map (`isCoveringMap_sumElim`), its fibres are the disjoint unions of the fibres
(`card_fibre_sumElim`), and its monodromy acts summandwise (`monodromy_sumElim_inl`,
`monodromy_sumElim_inr`).
-/

@[expose] public section

open Topology Set

noncomputable section

namespace SteklovRegularCover

variable {E E₁ E₂ X : Type*} [TopologicalSpace E] [TopologicalSpace E₁] [TopologicalSpace E₂]
  [TopologicalSpace X]

/-- Restriction of an even-covering homeomorphism to a smaller base set. -/
theorem restrictEven {f : E → X} {U V : Set X} {I : Type*} [TopologicalSpace I]
    (H : f ⁻¹' U ≃ₜ U × I) (hH : ∀ e, (H e).1.1 = f e) (hVU : V ⊆ U) :
    ∃ K : f ⁻¹' V ≃ₜ V × I, ∀ e, (K e).1.1 = f e := by
  have hmemS : ∀ vi : V × I, f (H.symm (Set.inclusion hVU vi.1, vi.2)).1 ∈ V := fun vi => by
    rw [← hH, H.apply_symm_apply]; exact vi.1.2
  refine ⟨
    { toFun := fun e => (⟨f e.1, e.2⟩, (H ⟨e.1, hVU e.2⟩).2)
      invFun := fun vi => ⟨(H.symm (Set.inclusion hVU vi.1, vi.2)).1, hmemS vi⟩
      left_inv := fun e => ?_
      right_inv := fun vi => ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }, fun e => rfl⟩
  · apply Subtype.ext
    show (H.symm (Set.inclusion hVU ⟨f e.1, e.2⟩, (H ⟨e.1, hVU e.2⟩).2)).1 = e.1
    have h1 : Set.inclusion hVU ⟨f e.1, e.2⟩ = (H ⟨e.1, hVU e.2⟩).1 :=
      Subtype.ext (hH ⟨e.1, hVU e.2⟩).symm
    rw [h1, Prod.mk.eta, H.symm_apply_apply]
  · obtain ⟨v, i⟩ := vi
    refine Prod.ext (Subtype.ext ?_) ?_
    · show f (H.symm (Set.inclusion hVU v, i)).1 = v
      rw [← hH, H.apply_symm_apply]
    · show (H ⟨(H.symm (Set.inclusion hVU v, i)).1, _⟩).2 = i
      rw [Subtype.coe_eta, H.apply_symm_apply]
  · refine Continuous.prodMk (Continuous.subtype_mk ?_ _) ?_
    · exact (continuous_subtype_val.comp (continuous_fst.comp (H.continuous.comp
        (Continuous.subtype_mk (continuous_subtype_val (p := fun e => e ∈ f ⁻¹' V)) _)))).congr
        fun e => hH ⟨e.1, hVU e.2⟩
    · exact continuous_snd.comp (H.continuous.comp
        (Continuous.subtype_mk continuous_subtype_val _))
  · exact Continuous.subtype_mk (continuous_subtype_val.comp (H.symm.continuous.comp
      (((continuous_inclusion hVU).comp continuous_fst).prodMk continuous_snd))) _

/-- The preimage of a set under `Sum.elim p₁ p₂` is the disjoint union of the preimages. -/
def sumPreimageHomeo (p₁ : E₁ → X) (p₂ : E₂ → X) (U : Set X) (hU₁ : IsOpen (p₁ ⁻¹' U))
    (hU₂ : IsOpen (p₂ ⁻¹' U)) :
    (p₁ ⁻¹' U) ⊕ (p₂ ⁻¹' U) ≃ₜ (Sum.elim p₁ p₂ ⁻¹' U) := by
  let e : (p₁ ⁻¹' U) ⊕ (p₂ ⁻¹' U) ≃ (Sum.elim p₁ p₂ ⁻¹' U) :=
    (Equiv.subtypeSum (p := fun x => Sum.elim p₁ p₂ x ∈ U)).symm
  have hc : Continuous e := by
    refine continuous_sum_dom.2 ⟨?_, ?_⟩
    · exact Continuous.subtype_mk (continuous_inl.comp continuous_subtype_val) _
    · exact Continuous.subtype_mk (continuous_inr.comp continuous_subtype_val) _
  have hcomp : ((Subtype.val : (Sum.elim p₁ p₂ ⁻¹' U) → E₁ ⊕ E₂) ∘ e) =
      Sum.map Subtype.val Subtype.val := by
    funext x; rcases x with x | x <;> rfl
  have hopen : IsOpenMap e := by
    intro O hO
    have h1 : IsOpen (((Subtype.val : (Sum.elim p₁ p₂ ⁻¹' U) → E₁ ⊕ E₂) ∘ e) '' O) := by
      rw [hcomp]
      exact (hU₁.isOpenMap_subtype_val.sumMap hU₂.isOpenMap_subtype_val) O hO
    have h2 : e '' O = Subtype.val ⁻¹' (((Subtype.val : (Sum.elim p₁ p₂ ⁻¹' U) → E₁ ⊕ E₂) ∘ e) '' O) := by
      rw [Set.image_comp, Set.preimage_image_eq _ Subtype.val_injective]
    rw [h2]
    exact h1.preimage continuous_subtype_val
  exact e.toHomeomorphOfContinuousOpen hc hopen

/-- **The disjoint union of two covering maps is a covering map.** -/
theorem isCoveringMap_sumElim {p₁ : E₁ → X} {p₂ : E₂ → X} (h₁ : IsCoveringMap p₁)
    (h₂ : IsCoveringMap p₂) : IsCoveringMap (Sum.elim p₁ p₂) := by
  intro x
  obtain ⟨hI₁, U₁, hxU₁, hU₁, -, H₁, hH₁⟩ := h₁ x
  obtain ⟨hI₂, U₂, hxU₂, hU₂, -, H₂, hH₂⟩ := h₂ x
  haveI := hI₁; haveI := hI₂
  set U := U₁ ∩ U₂
  have hU : IsOpen U := hU₁.inter hU₂
  obtain ⟨K₁, hK₁⟩ := restrictEven H₁ hH₁ (inter_subset_left : U ⊆ U₁)
  obtain ⟨K₂, hK₂⟩ := restrictEven H₂ hH₂ (inter_subset_right : U ⊆ U₂)
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage
    (I := (p₁ ⁻¹' {x}) ⊕ (p₂ ⁻¹' {x})) ⟨inferInstance, U, ⟨hxU₁, hxU₂⟩, hU, ?_, ?_⟩
  · exact hU.preimage ((continuous_sum_dom (f := Sum.elim p₁ p₂)).2
      ⟨h₁.continuous, h₂.continuous⟩)
  refine ⟨((sumPreimageHomeo p₁ p₂ U (hU.preimage h₁.continuous)
    (hU.preimage h₂.continuous)).symm.trans (K₁.sumCongr K₂)).trans
    (Homeomorph.prodSumDistrib).symm, fun e => ?_⟩
  obtain ⟨e | e, he⟩ := e
  · exact hK₁ ⟨e, he⟩
  · exact hK₂ ⟨e, he⟩

omit [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace X] in
/-- The fibre of `Sum.elim p₁ p₂` is the disjoint union of the fibres. -/
lemma card_fibre_sumElim (p₁ : E₁ → X) (p₂ : E₂ → X) (x : X) [Finite (p₁ ⁻¹' {x})]
    [Finite (p₂ ⁻¹' {x})] :
    Nat.card (Sum.elim p₁ p₂ ⁻¹' {x}) = Nat.card (p₁ ⁻¹' {x}) + Nat.card (p₂ ⁻¹' {x}) := by
  rw [← Nat.card_sum]
  exact Nat.card_congr (Equiv.subtypeSum (p := fun y => Sum.elim p₁ p₂ y ∈ ({x} : Set X)))

/-- **Monodromy of the disjoint union on the first summand.** -/
theorem monodromy_sumElim_inl {p₁ : E₁ → X} {p₂ : E₂ → X} (h₁ : IsCoveringMap p₁)
    (h₂ : IsCoveringMap p₂) {x y : X} (γ : Path.Homotopic.Quotient x y) (e : p₁ ⁻¹' {x}) :
    ((isCoveringMap_sumElim h₁ h₂).monodromy γ ⟨Sum.inl e.1, e.2⟩ : E₁ ⊕ E₂) =
      Sum.inl (h₁.monodromy γ e).1 := by
  induction γ using Quotient.inductionOn with
  | h γ =>
    show (isCoveringMap_sumElim h₁ h₂).liftPath (γ : C(unitInterval, X)) (Sum.inl e.1) _ 1 =
      Sum.inl (h₁.liftPath (γ : C(unitInterval, X)) e.1 _ 1)
    have key : (⟨Sum.inl, continuous_inl⟩ : C(E₁, E₁ ⊕ E₂)).comp
        (h₁.liftPath (γ : C(unitInterval, X)) e.1 (γ.source.trans e.2.symm)) =
        (isCoveringMap_sumElim h₁ h₂).liftPath (γ : C(unitInterval, X)) (Sum.inl e.1)
          (γ.source.trans e.2.symm) := by
      rw [IsCoveringMap.eq_liftPath_iff']
      refine ⟨funext fun t => ?_, ?_⟩
      · exact congrFun (h₁.liftPath_lifts _ _ _) t
      · show Sum.inl (h₁.liftPath _ _ _ 0) = Sum.inl e.1
        rw [h₁.liftPath_zero]
    rw [← key]
    rfl

/-- **Monodromy of the disjoint union on the second summand.** -/
theorem monodromy_sumElim_inr {p₁ : E₁ → X} {p₂ : E₂ → X} (h₁ : IsCoveringMap p₁)
    (h₂ : IsCoveringMap p₂) {x y : X} (γ : Path.Homotopic.Quotient x y) (e : p₂ ⁻¹' {x}) :
    ((isCoveringMap_sumElim h₁ h₂).monodromy γ ⟨Sum.inr e.1, e.2⟩ : E₁ ⊕ E₂) =
      Sum.inr (h₂.monodromy γ e).1 := by
  induction γ using Quotient.inductionOn with
  | h γ =>
    show (isCoveringMap_sumElim h₁ h₂).liftPath (γ : C(unitInterval, X)) (Sum.inr e.1) _ 1 =
      Sum.inr (h₂.liftPath (γ : C(unitInterval, X)) e.1 _ 1)
    have key : (⟨Sum.inr, continuous_inr⟩ : C(E₂, E₁ ⊕ E₂)).comp
        (h₂.liftPath (γ : C(unitInterval, X)) e.1 (γ.source.trans e.2.symm)) =
        (isCoveringMap_sumElim h₁ h₂).liftPath (γ : C(unitInterval, X)) (Sum.inr e.1)
          (γ.source.trans e.2.symm) := by
      rw [IsCoveringMap.eq_liftPath_iff']
      refine ⟨funext fun t => ?_, ?_⟩
      · exact congrFun (h₂.liftPath_lifts _ _ _) t
      · show Sum.inr (h₂.liftPath _ _ _ 0) = Sum.inr e.1
        rw [h₂.liftPath_zero]
    rw [← key]
    rfl

/-! ### Labelling the fibre of the disjoint union -/

section label

variable {p₁ : E₁ → X} {p₂ : E₂ → X} {A : X} {a b : ℕ}

/-- The labelling of the fibre of `Sum.elim p₁ p₂` by `Fin (a + b)` obtained from labellings of the
two fibres (first summand: labels `castAdd`, second: `natAdd`). -/
def sumLabel (L₁ : p₁ ⁻¹' {A} ≃ Fin a) (L₂ : p₂ ⁻¹' {A} ≃ Fin b) :
    Sum.elim p₁ p₂ ⁻¹' {A} ≃ Fin (a + b) :=
  (Equiv.subtypeSum (p := fun c => Sum.elim p₁ p₂ c ∈ ({A} : Set X))).trans
    ((L₁.sumCongr L₂).trans finSumFinEquiv)

omit [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace X] in
lemma sumLabel_of_inl (L₁ : p₁ ⁻¹' {A} ≃ Fin a) (L₂ : p₂ ⁻¹' {A} ≃ Fin b)
    (w : Sum.elim p₁ p₂ ⁻¹' {A}) (x : p₁ ⁻¹' {A}) (hw : w.1 = Sum.inl x.1) :
    sumLabel L₁ L₂ w = Fin.castAdd b (L₁ x) := by
  obtain ⟨w, hw'⟩ := w
  obtain ⟨x, hx⟩ := x
  simp only at hw
  subst hw
  show finSumFinEquiv ((L₁.sumCongr L₂) (Sum.inl ⟨x, hw'⟩)) = _
  rw [Equiv.sumCongr_apply, Sum.map_inl, finSumFinEquiv_apply_left]

omit [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace X] in
lemma sumLabel_of_inr (L₁ : p₁ ⁻¹' {A} ≃ Fin a) (L₂ : p₂ ⁻¹' {A} ≃ Fin b)
    (w : Sum.elim p₁ p₂ ⁻¹' {A}) (x : p₂ ⁻¹' {A}) (hw : w.1 = Sum.inr x.1) :
    sumLabel L₁ L₂ w = Fin.natAdd a (L₂ x) := by
  obtain ⟨w, hw'⟩ := w
  obtain ⟨x, hx⟩ := x
  simp only at hw
  subst hw
  show finSumFinEquiv ((L₁.sumCongr L₂) (Sum.inr ⟨x, hw'⟩)) = _
  rw [Equiv.sumCongr_apply, Sum.map_inr, finSumFinEquiv_apply_right]

omit [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace X] in
lemma sumLabel_symm_castAdd (L₁ : p₁ ⁻¹' {A} ≃ Fin a) (L₂ : p₂ ⁻¹' {A} ≃ Fin b) (j : Fin a) :
    (sumLabel L₁ L₂).symm (Fin.castAdd b j) = ⟨Sum.inl (L₁.symm j).1, (L₁.symm j).2⟩ := by
  rw [Equiv.symm_apply_eq, sumLabel_of_inl L₁ L₂ _ (L₁.symm j) rfl, Equiv.apply_symm_apply]

omit [TopologicalSpace E₁] [TopologicalSpace E₂] [TopologicalSpace X] in
lemma sumLabel_symm_natAdd (L₁ : p₁ ⁻¹' {A} ≃ Fin a) (L₂ : p₂ ⁻¹' {A} ≃ Fin b) (j : Fin b) :
    (sumLabel L₁ L₂).symm (Fin.natAdd a j) = ⟨Sum.inr (L₂.symm j).1, (L₂.symm j).2⟩ := by
  rw [Equiv.symm_apply_eq, sumLabel_of_inr L₁ L₂ _ (L₂.symm j) rfl, Equiv.apply_symm_apply]

/-- **Monodromy in the combined labelling, first block.** -/
theorem sumLabel_monodromy_castAdd (h₁ : IsCoveringMap p₁) (h₂ : IsCoveringMap p₂)
    (L₁ : p₁ ⁻¹' {A} ≃ Fin a) (L₂ : p₂ ⁻¹' {A} ≃ Fin b) (γ : Path.Homotopic.Quotient A A)
    (j : Fin a) :
    sumLabel L₁ L₂ ((isCoveringMap_sumElim h₁ h₂).monodromy γ
        ((sumLabel L₁ L₂).symm (Fin.castAdd b j))) =
      Fin.castAdd b (L₁ (h₁.monodromy γ (L₁.symm j))) := by
  apply sumLabel_of_inl
  have h := monodromy_sumElim_inl h₁ h₂ γ (L₁.symm j)
  rw [sumLabel_symm_castAdd, h]

/-- **Monodromy in the combined labelling, second block.** -/
theorem sumLabel_monodromy_natAdd (h₁ : IsCoveringMap p₁) (h₂ : IsCoveringMap p₂)
    (L₁ : p₁ ⁻¹' {A} ≃ Fin a) (L₂ : p₂ ⁻¹' {A} ≃ Fin b) (γ : Path.Homotopic.Quotient A A)
    (j : Fin b) :
    sumLabel L₁ L₂ ((isCoveringMap_sumElim h₁ h₂).monodromy γ
        ((sumLabel L₁ L₂).symm (Fin.natAdd a j))) =
      Fin.natAdd a (L₂ (h₂.monodromy γ (L₂.symm j))) := by
  apply sumLabel_of_inr
  have h := monodromy_sumElim_inr h₁ h₂ γ (L₂.symm j)
  rw [sumLabel_symm_natAdd, h]

end label

end SteklovRegularCover
