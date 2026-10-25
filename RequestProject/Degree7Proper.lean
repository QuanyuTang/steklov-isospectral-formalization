module

public import RequestProject.Degree7Completion
public import RequestProject.FillProper

/-!
# Properness of the branched completion of the actual regular cover

For `s² = -7` and any ordered complete fibre `f₀`, the branched completion
`RegFill hs f₀` of the regular `GL(3, 𝔽₂)` cover has finitely many added points
(`finite_regEnds`), and its branched projection `regFillProj : RegFill hs f₀ → ℂ` is a **proper**
map (`isProperMap_regFillProj`).  Consequently the preimage of every closed disk is a compact subset
of the Riemann surface `RegFill hs f₀` (`isCompact_preimage_closedBall`).
-/

@[expose] public section

open Polynomial Set PolyCover LocalMonodromy SteklovRegularCover SteklovPunctured SteklovFill
  SteklovRiemann Topology

noncomputable section

namespace Degree7

variable {s : ℂ}

/-- The fibres of the regular cover are finite (they inject into ordered tuples of points of a
fibre of `p_s ⊔ p_{-s}`). -/
lemma finite_regProj_fibre (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13)
    (x : Base (pPoly s)) : Finite (regProj f₀ ⁻¹' {x}) := by
  haveI : Finite (projSum hs ⁻¹' {x}) :=
    Nat.finite_of_card_ne_zero (by rw [card_fibre_projSum hs x]; omega)
  refine Finite.of_injective (fun f : regProj f₀ ⁻¹' {x} =>
    (fun i => (⟨f.1.1.1 i, (ordProj_apply _ _ f.1.1 i).trans f.2⟩ : projSum hs ⁻¹' {x}))) ?_
  intro f f' h
  apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
  funext i
  exact congrArg Subtype.val (congrFun h i)

/-- **Finitely many branch points** are added in the completion. -/
lemma finite_regEnds (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    Finite (BIdx (regProj f₀) cB (1 / 2)) :=
  finite_bIdx dB (regModel hs f₀) (by norm_num) dB_pos cB_disj (finite_regProj_fibre hs f₀)

/-- **The branched projection of the completion is proper**: preimages of compact sets are
compact. -/
theorem isCompact_preimage_regFillProj (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13)
    {K : Set ℂ} (hK : IsCompact K) : IsCompact (regFillProj hs f₀ ⁻¹' K) := by
  haveI := finite_regEnds hs f₀
  haveI := locPathConnectedSpace_base hs
  haveI : LocallyCompactSpace (Base (pPoly s)) := (isOpen_base hs).locallyCompactSpace
  refine Fill.isCompact_preimage_πFill (E := regEnds hs f₀) (coverProjC hs f₀)
    (fun j => cB j.1) (fun j => dB j.1)
    (fun j => dB_pos j.1) (regEnds_pow hs f₀) (regFill_riemannSurface hs f₀).2.2.1.continuous
    {0, 1} ?_ (by norm_num : (0 : ℝ) < 1 / 2) ?_ hK
  · intro K hK hKB
    have hKS : K ⊆ (critVals (pPoly s))ᶜ := by
      rw [critVals_pPoly hs]; intro z hz hz'; exact Set.disjoint_left.1 hKB hz hz'
    have hK' : IsCompact ((Subtype.val : Base (pPoly s) → ℂ) ⁻¹' K) := by
      rw [(isOpen_base hs).isOpenEmbedding_subtypeVal.isInducing.isCompact_iff,
        Subtype.image_preimage_coe, inter_eq_right.2 hKS]
      exact hK
    exact isCompact_preimage_of_isCoveringMap
      (isCoveringMap_regProj (isCoveringMap_projSum hs) f₀) (finite_regProj_fibre hs f₀) hK'
  · intro y b hb hy
    have hyB : coverProjC hs f₀ y ∉ ({0, 1} : Set ℂ) := by
      rw [← critVals_pPoly hs]; exact (regProj f₀ y).2
    have hne : coverProjC hs f₀ y ≠ b := fun h => hyB (h ▸ hb)
    obtain ⟨i, rfl⟩ : ∃ i, cB i = b := by
      rcases hb with rfl | rfl
      · exact ⟨false, rfl⟩
      · exact ⟨true, rfl⟩
    obtain ⟨j, hj1, hjy⟩ := exists_bIdx_of_mem (q := regProj f₀) (c := cB) (ρ := 1 / 2)
      (i := i) (y := y) ⟨sub_ne_zero.2 hne, hy⟩
    exact ⟨j, by simp only [hj1], hjy⟩

/-- **Properness** of the branched projection, in Mathlib's sense. -/
theorem isProperMap_regFillProj (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    IsProperMap (regFillProj hs f₀) :=
  isProperMap_iff_isCompact_preimage.2
    ⟨(regFill_riemannSurface hs f₀).2.2.1.continuous,
      fun _ hK => isCompact_preimage_regFillProj hs f₀ hK⟩

/-- The preimage of any closed disk under the branched projection is compact. -/
theorem isCompact_preimage_closedBall (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13)
    (z₀ : ℂ) (R : ℝ) : IsCompact (regFillProj hs f₀ ⁻¹' Metric.closedBall z₀ R) :=
  isCompact_preimage_regFillProj hs f₀ (isCompact_closedBall z₀ R)

end Degree7
