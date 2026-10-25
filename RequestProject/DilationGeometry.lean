module

public import RequestProject.Dilation

/-!
# Geometric quantities under dilation (normalization step of §3.5)

In §3.5 the domains `Ω_{j,ε}` (boundary length `2πn`) are rescaled to `Ω̂ = Ω/n`.  The paper
states that isospectrality (proved in `RequestProject.Dilation`), pairwise noncongruence and the
absence of orientation-reversing symmetries are preserved and that the boundary length becomes
`2π`.  Here we prove the scaling facts for boundary length, congruence and orientation-reversing
symmetries, for an arbitrary dilation factor `c > 0`.
-/

@[expose] public section

open MeasureTheory Set PlaneDomain
open scoped ENNReal Pointwise

noncomputable section

namespace SteklovDilationProof

variable {c : ℝ}

/-- Boundary length scales linearly: `|∂(cΩ)| = c |∂Ω|`. -/
theorem boundaryLength_smul (hc : 0 < c) (Ω : Set ℂ) :
    boundaryLength ((fun z : ℂ => c • z) '' Ω) = ENNReal.ofReal c * boundaryLength Ω := by
  unfold boundaryLength
  have hfr : frontier ((fun z : ℂ => c • z) '' Ω) = c • frontier Ω := by
    show frontier ((Homeomorph.smulOfNeZero c hc.ne') '' Ω) = _
    rw [← Homeomorph.image_frontier]
    exact Set.image_smul (a := c) (t := frontier Ω)
  rw [hfr, Measure.hausdorffMeasure_smul₀ zero_le_one hc.ne', NNReal.rpow_one, ENNReal.smul_def,
    smul_eq_mul]
  congr 1
  rw [ENNReal.ofReal_eq_coe_nnreal hc.le]
  congr 1
  ext
  simp [abs_of_pos hc]

/-- Conjugating an isometry by the dilation `z ↦ c z`. -/
def conjIso (hc : 0 < c) (J : ℂ ≃ᵢ ℂ) : ℂ ≃ᵢ ℂ where
  toFun z := c • J (c⁻¹ • z)
  invFun z := c • J.symm (c⁻¹ • z)
  left_inv z := by
    simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, IsometryEquiv.symm_apply_apply,
      mul_inv_cancel₀ hc.ne']
  right_inv z := by
    simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, IsometryEquiv.apply_symm_apply,
      mul_inv_cancel₀ hc.ne']
  isometry_toFun := by
    refine Isometry.of_dist_eq fun a b => ?_
    rw [dist_smul₀, J.dist_eq, dist_smul₀, ← mul_assoc, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_inv, abs_of_pos hc, mul_inv_cancel₀ hc.ne', one_mul]

lemma conjIso_apply (hc : 0 < c) (J : ℂ ≃ᵢ ℂ) (z : ℂ) : conjIso hc J z = c • J (c⁻¹ • z) := rfl

lemma image_conjIso (hc : 0 < c) (J : ℂ ≃ᵢ ℂ) (A : Set ℂ) :
    conjIso hc J '' ((fun z : ℂ => c • z) '' A) = (fun z : ℂ => c • z) '' (J '' A) := by
  rw [Set.image_image, Set.image_image]
  congr 1
  ext z
  simp only [conjIso_apply, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- Congruence is invariant under a common dilation. -/
theorem congruent_smul_iff (hc : 0 < c) (A B : Set ℂ) :
    Congruent ((fun z : ℂ => c • z) '' A) ((fun z : ℂ => c • z) '' B) ↔ Congruent A B := by
  constructor
  · rintro ⟨J, hJ⟩
    refine ⟨conjIso (inv_pos.2 hc) J, ?_⟩
    have h1 : (fun z : ℂ => c⁻¹ • z) '' ((fun z : ℂ => c • z) '' A) = A := by
      rw [Set.image_image]; simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, Set.image_id']
    have h2 : (fun z : ℂ => c⁻¹ • z) '' ((fun z : ℂ => c • z) '' B) = B := by
      rw [Set.image_image]; simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, Set.image_id']
    rw [← h1, image_conjIso, hJ, h2]
  · rintro ⟨J, hJ⟩
    exact ⟨conjIso hc J, by rw [image_conjIso, hJ]⟩

/-- Orientation-reversing symmetries are invariant under dilation. -/
theorem orientationReversing_smul_iff (hc : 0 < c) (A : Set ℂ) :
    HasOrientationReversingSymmetry ((fun z : ℂ => c • z) '' A) ↔
      HasOrientationReversingSymmetry A := by
  have key : ∀ (d : ℝ), 0 < d → ∀ A : Set ℂ, HasOrientationReversingSymmetry A →
      HasOrientationReversingSymmetry ((fun z : ℂ => d • z) '' A) := by
    rintro d hd A ⟨a, b, ha, hab⟩
    refine ⟨a, d • b, ha, ?_⟩
    have : (fun z => a * (starRingEnd ℂ) z + d • b) ∘ (fun z : ℂ => d • z) =
        (fun z : ℂ => d • z) ∘ (fun z => a * (starRingEnd ℂ) z + b) := by
      ext z
      simp only [Function.comp_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]
      ring
    rw [Set.image_image]
    change ((fun z => a * (starRingEnd ℂ) z + d • b) ∘ (fun z : ℂ => d • z)) '' A = _
    rw [this, Set.image_comp, hab]
  constructor
  · intro h
    have := key c⁻¹ (inv_pos.2 hc) _ h
    rwa [Set.image_image, show (fun x : ℂ => c⁻¹ • c • x) = id by
      ext; simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, id], Set.image_id] at this
  · exact key c hc A

end SteklovDilationProof

end
