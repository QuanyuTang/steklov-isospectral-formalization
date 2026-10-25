module

public import Mathlib

/-!
# Smooth `C¹`-approximation of compactly supported `C¹` maps

`SteklovC1.exists_smooth_C1_approx`: a compactly supported `C¹` map `Φ : ℂ → ℂ` is, for every
`ε > 0`, uniformly `ε`-close together with its derivative to a `C^∞` map (a mollification).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ContDiff Convolution

noncomputable section

namespace SteklovC1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Uniform closeness of a mollification of a continuous compactly supported function. -/
lemma moll_close {g : ℂ → E} (hc : Continuous g) (hs : HasCompactSupport g) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ b : ContDiffBump (0 : ℂ), b.rOut < δ → ∀ x,
      dist ((b.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x) (g x) ≤ ε := by
  obtain ⟨δ, hδ, hu⟩ := Metric.uniformContinuous_iff.mp
    (hs.uniformContinuous_of_continuous hc) ε hε
  refine ⟨δ, hδ, fun b hb x => ?_⟩
  refine b.dist_normed_convolution_le hc.aestronglyMeasurable (fun y hy => (hu ?_).le)
  exact (Metric.mem_ball.mp hy).trans hb

/-- **Smooth `C¹` approximation.** -/
theorem exists_smooth_C1_approx {Φ : ℂ → ℂ} (hΦ : ContDiff ℝ 1 Φ) (hc : HasCompactSupport Φ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ Ψ : ℂ → ℂ, ContDiff ℝ ∞ Ψ ∧ (∀ x, ‖Ψ x - Φ x‖ ≤ ε) ∧
      ∀ x, ‖fderiv ℝ Ψ x - fderiv ℝ Φ x‖ ≤ ε := by
  have hΦc : Continuous Φ := hΦ.continuous
  have hdc : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv one_ne_zero
  have hds : HasCompactSupport (fderiv ℝ Φ) := hc.fderiv (𝕜 := ℝ)
  obtain ⟨δ₁, hδ₁, h₁⟩ := moll_close hΦc hc hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := moll_close hdc hds hε
  set r := min δ₁ δ₂ / 2 with hr
  have hr0 : 0 < r := by positivity
  let b : ContDiffBump (0 : ℂ) := ⟨r / 2, r, by positivity, by linarith⟩
  have hb1 : b.rOut < δ₁ := by
    show r < δ₁; rw [hr]; linarith [min_le_left δ₁ δ₂, lt_min hδ₁ hδ₂]
  have hb2 : b.rOut < δ₂ := by
    show r < δ₂; rw [hr]; linarith [min_le_right δ₁ δ₂, lt_min hδ₁ hδ₂]
  set η := b.normed volume
  set Ψ := η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Φ with hΨ
  have hloc : LocallyIntegrable η volume :=
    (b.continuous_normed (μ := volume)).locallyIntegrable
  refine ⟨Ψ, ?_, fun x => ?_, fun x => ?_⟩
  · exact (b.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left _
      (b.contDiff_normed (μ := volume) (n := ⊤)) hΦc.locallyIntegrable
  · rw [← dist_eq_norm]; exact h₁ b hb1 x
  · have hd := hc.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ) hloc hΦ x
    rw [hd.fderiv, ← dist_eq_norm]
    have heq : (η ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℂ →L[ℝ] ℂ).precompR ℂ, volume]
        fderiv ℝ Φ) x = (η ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fderiv ℝ Φ) x := by
      simp only [convolution_def]
      congr 1
    rw [heq]
    exact h₂ b hb2 x

end SteklovC1

namespace SteklovC1

/-- **Stability of compositions under `C¹`-small perturbations.**  If `e : ℂ → ℝ` is `C¹` and
`Φ : ℂ → ℂ` is `C¹` with compact support, then `e ∘ Ψ` is uniformly `C¹`-close to `e ∘ Φ`
whenever `Ψ` is differentiable and uniformly `C¹`-close enough to `Φ`. -/
theorem comp_C1_close {e : ℂ → ℝ} (he : ContDiff ℝ 1 e) {Φ : ℂ → ℂ} (hΦ : ContDiff ℝ 1 Φ)
    (hc : HasCompactSupport Φ) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ Ψ : ℂ → ℂ, Differentiable ℝ Ψ → (∀ x, ‖Ψ x - Φ x‖ ≤ δ) →
      (∀ x, ‖fderiv ℝ Ψ x - fderiv ℝ Φ x‖ ≤ δ) → ∀ x,
        |e (Ψ x) - e (Φ x)| ≤ ε ∧ ‖fderiv ℝ (e ∘ Ψ) x - fderiv ℝ (e ∘ Φ) x‖ ≤ ε := by
  -- bounds on `Φ` and `DΦ`
  obtain ⟨R, hR⟩ := (hc.isCompact_range hΦ.continuous).isBounded.subset_closedBall 0
  have hdc : Continuous (fderiv ℝ Φ) := hΦ.continuous_fderiv one_ne_zero
  obtain ⟨CΦ, hCΦ⟩ := ((hc.fderiv (𝕜 := ℝ)).isCompact_range hdc).isBounded.subset_closedBall 0
  set K := closedBall (0 : ℂ) (R + 1)
  have hK : IsCompact K := isCompact_closedBall 0 _
  have hec : Continuous e := he.continuous
  have hedc : Continuous (fderiv ℝ e) := he.continuous_fderiv one_ne_zero
  obtain ⟨Ce, hCe⟩ := (hK.image hedc).isBounded.subset_closedBall 0
  have hCe' : ∀ y ∈ K, ‖fderiv ℝ e y‖ ≤ Ce := fun y hy => by
    simpa using hCe ⟨y, hy, rfl⟩
  have hCΦ' : ∀ x, ‖fderiv ℝ Φ x‖ ≤ CΦ := fun x => by simpa using hCΦ ⟨x, rfl⟩
  have hCΦ0 : 0 ≤ CΦ := (norm_nonneg _).trans (hCΦ' 0)
  have hR0 : 0 ≤ R := (norm_nonneg (Φ 0)).trans (by simpa using hR ⟨0, rfl⟩)
  have hCe0 : 0 ≤ Ce := (norm_nonneg _).trans (hCe' 0 (by simp [K]; linarith))
  obtain ⟨δ₁, hδ₁, hu₁⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hec.continuousOn) ε hε
  set ε' := ε / (2 * (CΦ + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  obtain ⟨δ₂, hδ₂, hu₂⟩ := Metric.uniformContinuousOn_iff.mp
    (hK.uniformContinuousOn_of_continuous hedc.continuousOn) ε' hε'0
  set δ := min (min 1 (δ₁ / 2)) (min (δ₂ / 2) (ε / (2 * (Ce + 1)))) with hδ
  have hδ0 : 0 < δ := by positivity
  refine ⟨δ, hδ0, fun Ψ hΨ h0 h1 x => ?_⟩
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδδ₁ : δ < δ₁ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _))
    (by linarith)
  have hδδ₂ : δ < δ₂ := lt_of_le_of_lt ((min_le_right _ _).trans (min_le_left _ _))
    (by linarith)
  have hδCe : δ ≤ ε / (2 * (Ce + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hΦx : ‖Φ x‖ ≤ R := by simpa using hR ⟨x, rfl⟩
  have hΦK : Φ x ∈ K := by
    simp only [K, mem_closedBall, dist_zero_right]; linarith
  have hΨK : Ψ x ∈ K := by
    simp only [K, mem_closedBall, dist_zero_right]
    have := norm_le_norm_add_norm_sub' (Ψ x) (Φ x)
    linarith [h0 x]
  have hdist : dist (Ψ x) (Φ x) < δ₁ := by rw [dist_eq_norm]; linarith [h0 x]
  have hdist₂ : dist (Ψ x) (Φ x) < δ₂ := by rw [dist_eq_norm]; linarith [h0 x]
  refine ⟨?_, ?_⟩
  · have := hu₁ _ hΨK _ hΦK hdist
    rw [Real.dist_eq] at this
    exact this.le
  · have hd1 : fderiv ℝ (e ∘ Ψ) x = (fderiv ℝ e (Ψ x)).comp (fderiv ℝ Ψ x) :=
      fderiv_comp x ((he.differentiable one_ne_zero) _) (hΨ x)
    have hd2 : fderiv ℝ (e ∘ Φ) x = (fderiv ℝ e (Φ x)).comp (fderiv ℝ Φ x) :=
      fderiv_comp x ((he.differentiable one_ne_zero) _) ((hΦ.differentiable one_ne_zero) x)
    rw [hd1, hd2]
    have hsplit : (fderiv ℝ e (Ψ x)).comp (fderiv ℝ Ψ x) - (fderiv ℝ e (Φ x)).comp (fderiv ℝ Φ x)
        = (fderiv ℝ e (Ψ x) - fderiv ℝ e (Φ x)).comp (fderiv ℝ Ψ x) +
          (fderiv ℝ e (Φ x)).comp (fderiv ℝ Ψ x - fderiv ℝ Φ x) := by
      ext v; simp
    rw [hsplit]
    have hA : ‖fderiv ℝ e (Ψ x) - fderiv ℝ e (Φ x)‖ ≤ ε' := by
      have := hu₂ _ hΨK _ hΦK hdist₂
      rw [dist_eq_norm] at this; exact this.le
    have hB : ‖fderiv ℝ Ψ x‖ ≤ CΦ + 1 := by
      have := norm_le_norm_add_norm_sub' (fderiv ℝ Ψ x) (fderiv ℝ Φ x)
      linarith [h1 x, hCΦ' x]
    calc ‖(fderiv ℝ e (Ψ x) - fderiv ℝ e (Φ x)).comp (fderiv ℝ Ψ x) +
          (fderiv ℝ e (Φ x)).comp (fderiv ℝ Ψ x - fderiv ℝ Φ x)‖
        ≤ ‖fderiv ℝ e (Ψ x) - fderiv ℝ e (Φ x)‖ * ‖fderiv ℝ Ψ x‖ +
          ‖fderiv ℝ e (Φ x)‖ * ‖fderiv ℝ Ψ x - fderiv ℝ Φ x‖ :=
          (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
            (ContinuousLinearMap.opNorm_comp_le _ _))
      _ ≤ ε' * (CΦ + 1) + Ce * δ := by
          gcongr
          · exact hCe' _ hΦK
          · exact (h1 x).trans le_rfl
      _ ≤ ε / 2 + ε / 2 := by
          gcongr
          · rw [hε']; field_simp; linarith
          · calc Ce * δ ≤ (Ce + 1) * (ε / (2 * (Ce + 1))) := by
                  gcongr
                  linarith
              _ = ε / 2 := by field_simp
      _ = ε := by ring

end SteklovC1
