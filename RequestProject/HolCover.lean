module

public import Mathlib

/-!
# Holomorphic maps on a compact set are coverings over their regular values

If `B` is continuous on a compact `K ⊆ ℂ` and, at every point of `K` over a set `Xs`, `B` is analytic
with nonzero derivative and the point is interior to `K`, then `B : K → ℂ` is a covering map over
`Xs` (`isCoveringMapOn_of_compact`).  This is the inverse function theorem combined with Mathlib's
criterion for proper local homeomorphisms.
-/

@[expose] public section

open Set Filter Topology

noncomputable section

namespace HolCover

/-- A junk-extended inverse with values in a subtype. -/
def invF (K : Set ℂ) [Nonempty K] (g : ℂ → ℂ) (w : ℂ) : K := by
  classical
  exact if h : g w ∈ K then ⟨g w, h⟩ else Classical.arbitrary K

lemma invF_val {K : Set ℂ} [Nonempty K] {g : ℂ → ℂ} {w : ℂ} (h : g w ∈ K) :
    (invF K g w : ℂ) = g w := by
  simp [invF, h]

/-- A partial homeomorphism `φ₀` of `ℂ` restricted to an open subset `O` of a subset `K`, viewed
on the subtype `K`. -/
def subtypeOPH {K : Set ℂ} [Nonempty K] (φ₀ : OpenPartialHomeomorph ℂ ℂ) (O : Set ℂ)
    (hO : IsOpen O) (hOK : O ⊆ K) : OpenPartialHomeomorph K ℂ where
  toFun := fun e => φ₀ e
  invFun := invF K φ₀.symm
  source := Subtype.val ⁻¹' (O ∩ φ₀.source)
  target := φ₀ '' (O ∩ φ₀.source)
  map_source' := fun e he => ⟨e, he, rfl⟩
  map_target' := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 : φ₀.symm (φ₀ z) = z := φ₀.left_inv hz.2
    have h2 : φ₀.symm (φ₀ z) ∈ K := by rw [h1]; exact hOK hz.1
    show (invF K φ₀.symm (φ₀ z) : ℂ) ∈ O ∩ φ₀.source
    rw [invF_val h2, h1]; exact hz
  left_inv' := by
    intro e he
    have h1 : φ₀.symm (φ₀ e) = e := φ₀.left_inv he.2
    have h2 : φ₀.symm (φ₀ e) ∈ K := by rw [h1]; exact e.2
    apply Subtype.ext
    rw [invF_val h2, h1]
  right_inv' := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 : φ₀.symm (φ₀ z) = z := φ₀.left_inv hz.2
    have h2 : φ₀.symm (φ₀ z) ∈ K := by rw [h1]; exact hOK hz.1
    show φ₀ (invF K φ₀.symm (φ₀ z) : ℂ) = φ₀ z
    rw [invF_val h2, h1]
  open_source := (hO.inter φ₀.open_source).preimage continuous_subtype_val
  open_target := φ₀.isOpen_image_of_subset_source (hO.inter φ₀.open_source) inter_subset_right
  continuousOn_toFun := φ₀.continuousOn.comp continuous_subtype_val.continuousOn
    (fun e he => he.2)
  continuousOn_invFun := by
    rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
    refine (φ₀.continuousOn_symm.mono ?_).congr ?_
    · rintro _ ⟨z, hz, rfl⟩; exact φ₀.map_source hz.2
    · rintro _ ⟨z, hz, rfl⟩
      have h1 : φ₀.symm (φ₀ z) = z := φ₀.left_inv hz.2
      have h2 : φ₀.symm (φ₀ z) ∈ K := by rw [h1]; exact hOK hz.1
      exact invF_val h2

lemma subtypeOPH_coe {K : Set ℂ} [Nonempty K] (φ₀ : OpenPartialHomeomorph ℂ ℂ) (O : Set ℂ)
    (hO : IsOpen O) (hOK : O ⊆ K) : ⇑(subtypeOPH φ₀ O hO hOK) = fun e : K => φ₀ e := rfl

lemma subtypeOPH_source {K : Set ℂ} [Nonempty K] (φ₀ : OpenPartialHomeomorph ℂ ℂ) (O : Set ℂ)
    (hO : IsOpen O) (hOK : O ⊆ K) :
    (subtypeOPH φ₀ O hO hOK).source = Subtype.val ⁻¹' (O ∩ φ₀.source) := rfl

/-- **Covering criterion.** -/
theorem isCoveringMapOn_of_compact {B : ℂ → ℂ} {K Xs : Set ℂ} (hK : IsCompact K)
    (hBc : ContinuousOn B K)
    (hreg : ∀ z ∈ K, B z ∈ Xs → z ∈ interior K ∧ AnalyticAt ℂ B z ∧ deriv B z ≠ 0) :
    IsCoveringMapOn (fun e : K => B e) Xs := by
  by_cases hne : Nonempty K
  swap
  · haveI : IsEmpty K := not_nonempty_iff.1 hne
    exact IsCoveringMapOn.of_isEmpty (f := fun e : K => B e) (s := Xs)
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  refine IsCoveringMapOn.of_openPartialHomeomorph (f := fun e : K => B e) hBc.restrict
    fun e he => ?_
  obtain ⟨hint, han, hd⟩ := hreg e e.2 he
  have hs := han.hasStrictDerivAt.hasStrictFDerivAt_equiv hd
  refine ⟨subtypeOPH (hs.toOpenPartialHomeomorph B) (interior K) isOpen_interior
    interior_subset, ⟨hint, hs.mem_toOpenPartialHomeomorph_source⟩, ?_⟩
  rw [subtypeOPH_coe, hs.toOpenPartialHomeomorph_coe]

/-- The restricted covering map `B⁻¹(Xs) ∩ K → Xs`. -/
theorem isCoveringMap_of_compact {B : ℂ → ℂ} {K Xs : Set ℂ} (hK : IsCompact K)
    (hBc : ContinuousOn B K)
    (hreg : ∀ z ∈ K, B z ∈ Xs → z ∈ interior K ∧ AnalyticAt ℂ B z ∧ deriv B z ≠ 0) :
    IsCoveringMap (Xs.restrictPreimage (fun e : K => B e)) :=
  (isCoveringMapOn_of_compact hK hBc hreg).isCoveringMap_restrictPreimage

end HolCover
