module

public import RequestProject.Degree7Deck
public import RequestProject.GeneralDiskCovers

/-!
# The compact bordered piece of the branched completion

With the paper's affine normalisation `A_ε(z) = ε + (λ_* - 1) ε z` (so that
`q_ε = A_ε ∘ p` is the polynomial of Lemma 3.2.1), put
`M_ε = (A_ε ∘ regFillProj)⁻¹(closed unit disk) ⊆ RegFill hs f₀` and
`∂M_ε = (A_ε ∘ regFillProj)⁻¹(unit circle)`.  For `0 < ε < 1/3` we prove (`regBordered`):

* `M_ε` is compact (properness of the branched projection) and invariant under the extended
  deck action;
* all added (branch) points lie over `A_ε⁻¹{ε, λ_* ε}` strictly inside the unit disk, so `∂M_ε`
  lies in the unbranched part `R`, where the deck action is free;
* **boundary collar:** there is `r < 1` such that over the region `{|w| > r}` (which contains the
  circle) `A_ε ∘ π` restricted to `R` is a covering map, of degree `168`, and every point of
  `RegFill hs f₀` over this region lies in `R`.
-/

@[expose] public section

open Polynomial Set PolyCover LocalMonodromy SteklovRegularCover SteklovPunctured SteklovFill
  SteklovRiemann Topology Manifold SteklovCritical SteklovCoalescence

noncomputable section

namespace Degree7

variable {s : ℂ}

/-- The paper's affine normalisation `A_ε(z) = ε + (λ_* - 1) ε z`. -/
def affA (ε : ℝ) (z : ℂ) : ℂ := ε + (lamStar - 1) * ε * z

lemma affA_coverPoly (p : ℂ[X]) (ε : ℝ) (z : ℂ) :
    (SteklovDiskCovers.coverPoly p ε).eval z = affA ε (p.eval z) :=
  SteklovDiskCovers.eval_coverPoly p ε z

/-- `A_ε` as a homeomorphism of `ℂ` (`ε ≠ 0`). -/
def affHomeo {ε : ℝ} (hε : ε ≠ 0) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ ((lamStar - 1) * ε)
    (mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast hε))).trans
    (Homeomorph.addLeft (ε : ℂ))

lemma affHomeo_apply {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) : affHomeo hε z = affA ε z := rfl

lemma affA_zero (ε : ℝ) : affA ε 0 = ε := by simp [affA]

lemma affA_one (ε : ℝ) : affA ε 1 = lamStar * ε := by simp [affA]; ring

/-- The compact bordered piece `M_ε`. -/
def bordered (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (ε : ℝ) : Set (RegFill hs f₀) :=
  {w | ‖affA ε (regFillProj hs f₀ w)‖ ≤ 1}

/-- Its boundary `∂M_ε`. -/
def borderedBdry (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (ε : ℝ) :
    Set (RegFill hs f₀) :=
  {w | ‖affA ε (regFillProj hs f₀ w)‖ = 1}

/-- The radius of the inner edge of the collar. -/
def collarRad (ε : ℝ) : ℝ := (1 + max ‖(ε : ℂ)‖ ‖lamStar * ε‖) / 2

lemma collarRad_lt {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 3) : collarRad ε < 1 := by
  obtain ⟨ha, hb⟩ := branchValues_mem_disk h0 h1
  have := max_lt ha hb
  unfold collarRad; linarith

lemma lt_collarRad {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 3) :
    ‖(ε : ℂ)‖ < collarRad ε ∧ ‖lamStar * ε‖ < collarRad ε := by
  obtain ⟨ha, hb⟩ := branchValues_mem_disk h0 h1
  have h1' := le_max_left ‖(ε : ℂ)‖ ‖lamStar * ε‖
  have h2' := le_max_right ‖(ε : ℂ)‖ ‖lamStar * ε‖
  have := max_lt ha hb
  unfold collarRad
  constructor <;> linarith

/-- Points over the collar region are not branch values. -/
lemma not_branch_of_collar {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 3) {z : ℂ}
    (hz : collarRad ε < ‖affA ε z‖) : z ∉ ({0, 1} : Set ℂ) := by
  obtain ⟨ha, hb⟩ := lt_collarRad h0 h1
  rintro (rfl | rfl)
  · rw [affA_zero] at hz; linarith
  · rw [affA_one] at hz; linarith

/-- **The compact bordered piece of the branched completion.** -/
theorem regBordered (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1 / 3) :
    IsCompact (bordered hs f₀ ε) ∧
    (∀ σ w, regFillAct hs f₀ σ w ∈ bordered hs f₀ ε ↔ w ∈ bordered hs f₀ ε) ∧
    (∀ j, ‖affA ε (regFillProj hs f₀ (Fill.cusp j))‖ < collarRad ε) ∧
    (∀ w ∈ borderedBdry hs f₀ ε, (∃ f, w = Fill.inl f) ∧
      ∀ σ, regFillAct hs f₀ σ w = w → σ = 1) ∧
    collarRad ε < 1 ∧
    (∀ w : RegFill hs f₀, collarRad ε < ‖affA ε (regFillProj hs f₀ w)‖ → ∃ f, w = Fill.inl f) ∧
    IsCoveringMapOn (fun f => affA ε (coverProjC hs f₀ f)) {z | collarRad ε < ‖z‖} ∧
    (∀ x : Base (pPoly s), Nat.card (regProj f₀ ⁻¹' {x}) = 168 →
      Nat.card {f // affA ε (coverProjC hs f₀ f) = affA ε x} = 168) := by
  have hε : ε ≠ 0 := h0.ne'
  obtain ⟨ha, hb⟩ := lt_collarRad h0 h1
  have hr1 := collarRad_lt h0 h1
  -- the added points
  have hcusp : ∀ j, ‖affA ε (regFillProj hs f₀ (Fill.cusp j))‖ < collarRad ε := by
    rintro ⟨i, P⟩
    cases i
    · show ‖affA ε 0‖ < _; rw [affA_zero]; exact ha
    · show ‖affA ε 1‖ < _; rw [affA_one]; exact hb
  have hinl : ∀ w : RegFill hs f₀, collarRad ε < ‖affA ε (regFillProj hs f₀ w)‖ →
      ∃ f, w = Fill.inl f := by
    rintro (f | j) hw
    · exact ⟨f, rfl⟩
    · exact absurd hw (not_lt.2 (hcusp j).le)
  have hAct := regFill_deckAction hs f₀
  refine ⟨?_, fun σ w => ?_, hcusp, fun w hw => ?_, hr1, hinl, ?_, ?_⟩
  · -- compactness
    have hK : IsCompact (affA ε ⁻¹' Metric.closedBall (0 : ℂ) 1) := by
      have := (affHomeo hε).isCompact_preimage.2 (isCompact_closedBall (0 : ℂ) 1)
      exact this
    have := isCompact_preimage_regFillProj hs f₀ hK
    convert this using 1
    ext w; simp [bordered]
  · show ‖affA ε (regFillProj hs f₀ (regFillAct hs f₀ σ w))‖ ≤ 1 ↔ _
    rw [hAct.2.2.2.1]; rfl
  · have hw' : collarRad ε < ‖affA ε (regFillProj hs f₀ w)‖ := by
      rw [show ‖affA ε (regFillProj hs f₀ w)‖ = 1 from hw]; exact hr1
    refine ⟨hinl w hw', fun σ hσ => hAct.2.2.2.2.2.2.2.2 σ w ?_ ?_ hσ⟩
    · intro h; exact not_branch_of_collar h0 h1 hw' (Or.inl h)
    · intro h; exact not_branch_of_collar h0 h1 hw' (Or.inr h)
  · -- the collar covering
    haveI := locPathConnectedSpace_base hs
    have hcov := isCoveringMap_regProj (isCoveringMap_projSum hs) f₀
    set S' : Set ℂ := affA ε ⁻¹' {z | collarRad ε < ‖z‖}
    have hS' : IsCoveringMapOn (fun f : RegCov f₀ => ((regProj f₀ f : Base (pPoly s)) : ℂ)) S' := by
      intro x hx
      have hxB : x ∈ (critVals (pPoly s))ᶜ := by
        rw [critVals_pPoly hs]; exact not_branch_of_collar h0 h1 hx
      exact (IsEvenlyCovered.subtypeVal_comp _ (isOpen_base hs)
        (hcov ⟨x, hxB⟩)).to_isEvenlyCovered_preimage
    have := hS'.homeomorph_comp (affHomeo hε)
    -- Lean 4.35: no `convert`.  The base sets are identified by an explicit set equality; the
    -- covering functions agree definitionally (`affHomeo_apply` and `coverProjC` are `rfl`), with
    -- an explicit function equality as fallback.
    have hset : {z : ℂ | collarRad ε < ‖z‖} = (affHomeo hε).symm ⁻¹' S' := by
      ext z
      change collarRad ε < ‖z‖ ↔ collarRad ε < ‖affA ε ((affHomeo hε).symm z)‖
      rw [← affHomeo_apply hε, Homeomorph.apply_symm_apply]
    first
      | rw [hset]
      | rw [← hset] at this
    first
      | exact this
      | (have hfun : (fun f : RegCov f₀ => affA ε (coverProjC hs f₀ f)) =
            ((affHomeo hε) ∘ fun f : RegCov f₀ => ((regProj f₀ f : Base (pPoly s)) : ℂ)) := by
          funext f
          exact (affHomeo_apply hε _).symm
         rw [hfun]
         exact this)
  · intro x hx
    rw [← hx]
    refine Nat.card_congr ?_
    refine Equiv.subtypeEquivRight fun f => ?_
    have hinj : Function.Injective (affA ε) := (affHomeo hε).injective
    simp only [mem_preimage, mem_singleton_iff]
    constructor
    · intro h; exact Subtype.ext (hinj h)
    · intro h; simp only [coverProjC, h]

end Degree7
