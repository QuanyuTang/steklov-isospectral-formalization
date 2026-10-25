module

public import RequestProject.Defs

/-!
# Approximate transfer of min–max values

`Steklov.minMax_le_of_approx`: if every admissible test space for `(E₁, B₁)` can be mapped by a
linear map `T` into smooth functions with `E₂(Tu) ≤ (1+η) E₁(u) + η B₁(u)` and
`B₁(u) ≤ (1+η) B₂(Tu)` (for an arbitrary `η > 0`), then `minMax E₂ B₂ k ≤ minMax E₁ B₁ k`.
This is the approximate version of `Steklov.minMax_le_of_transfer`.
-/

@[expose] public section

open scoped ENNReal ContDiff

noncomputable section

namespace Steklov

/-- ENNReal bookkeeping: `(a E + b B) / (B / c) ≤ c (a (E/B) + b)` for `B ≠ 0, ⊤`. -/
lemma ennreal_ratio_bound {E B E' B' : ℝ≥0∞} {a b c : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ⊤)
    (hB0 : B ≠ 0) (hBt : B ≠ ⊤) (hE : E' ≤ a * E + b * B) (hB : B ≤ c * B') :
    E' / B' ≤ c * (a * (E / B) + b) := by
  have hB'0 : B' ≠ 0 := by
    rintro rfl; rw [mul_zero] at hB; exact hB0 (le_antisymm hB (zero_le))
  have h1 : E' / B' ≤ (a * E + b * B) / (B / c) := by
    refine ENNReal.div_le_div hE ?_
    rw [ENNReal.div_le_iff hc hc']
    rwa [mul_comm]
  refine h1.trans (le_of_eq ?_)
  rw [ENNReal.div_eq_inv_mul, ENNReal.inv_div (Or.inl hc') (Or.inl hc), ENNReal.div_eq_inv_mul]
  calc B⁻¹ * c * (a * E + b * B) = c * (a * (B⁻¹ * E) + b * (B⁻¹ * B)) := by ring
    _ = c * (a * (E / B) + b) := by
        rw [ENNReal.inv_mul_cancel hB0 hBt, mul_one, ENNReal.div_eq_inv_mul]

/-- **Approximate min–max transfer.** -/
theorem minMax_le_of_approx {E₁ B₁ E₂ B₂ : (ℂ → ℝ) → ℝ≥0∞} (hB₂ : B₂ 0 = 0) {k : ℕ}
    (hfin : ∀ u, ContDiff ℝ ∞ u → B₁ u ≠ ⊤)
    (happrox : ∀ V : Submodule ℝ (ℂ → ℝ), AdmissibleSpace B₁ k V → ∀ η : ℝ, 0 < η →
      ∃ T : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ), ∀ u ∈ V, ContDiff ℝ ∞ (T u) ∧
        E₂ (T u) ≤ ENNReal.ofReal (1 + η) * E₁ u + ENNReal.ofReal η * B₁ u ∧
        B₁ u ≤ ENNReal.ofReal (1 + η) * B₂ (T u)) :
    minMax E₂ B₂ k ≤ minMax E₁ B₁ k := by
  unfold minMax
  refine le_iInf₂ fun V hV => ?_
  set M := ⨆ (u : ℂ → ℝ) (_ : u ∈ V) (_ : u ≠ 0), E₁ u / B₁ u with hM
  -- the bound for a fixed `η`
  have key : ∀ η : ℝ, 0 < η →
      (⨅ (W : Submodule ℝ (ℂ → ℝ)) (_ : AdmissibleSpace B₂ k W),
        ⨆ (u : ℂ → ℝ) (_ : u ∈ W) (_ : u ≠ 0), E₂ u / B₂ u) ≤
      ENNReal.ofReal (1 + η) * (ENNReal.ofReal (1 + η) * M + ENNReal.ofReal η) := by
    intro η hη
    obtain ⟨T, hT⟩ := happrox V hV η hη
    obtain ⟨hsm, hdim, hpos⟩ := hV
    have hc0 : ENNReal.ofReal (1 + η) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; linarith
    have hTz : ∀ u ∈ V, T u = 0 → u = 0 := by
      intro u hu h0
      by_contra hne
      apply hpos u hu hne
      have := (hT u hu).2.2
      rw [h0, hB₂, mul_zero] at this
      exact le_antisymm this (zero_le)
    have hinj : Function.Injective (T.domRestrict V) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      intro u hu
      exact Subtype.ext (hTz u u.2 hu)
    have hW : AdmissibleSpace B₂ k (V.map T) := by
      refine ⟨?_, ?_, ?_⟩
      · rintro _ ⟨u, hu, rfl⟩; exact (hT u hu).1
      · rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj, hdim]
      · rintro _ ⟨u, hu, rfl⟩ hne h0
        have hu0 : u ≠ 0 := by rintro rfl; exact hne (map_zero T)
        have := (hT u hu).2.2
        rw [h0, mul_zero] at this
        exact hpos u hu hu0 (le_antisymm this (zero_le))
    refine (iInf₂_le (V.map T) hW).trans ?_
    refine iSup₂_le fun w hw => iSup_le fun hne => ?_
    obtain ⟨u, hu, rfl⟩ := hw
    have hu0 : u ≠ 0 := by rintro rfl; exact hne (map_zero T)
    have hle : E₁ u / B₁ u ≤ M :=
      le_iSup₂_of_le (f := fun u (_ : u ∈ V) => ⨆ (_ : u ≠ 0), E₁ u / B₁ u) u hu
        (le_iSup_of_le hu0 le_rfl)
    refine (ennreal_ratio_bound hc0 ENNReal.ofReal_ne_top (hpos u hu hu0) (hfin u (hsm u hu))
      (hT u hu).2.1 (hT u hu).2.2).trans ?_
    gcongr
  -- let `η → 0`
  rcases eq_or_ne M ⊤ with hMt | hMt
  · rw [hMt]; exact le_top
  refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
  set m := M.toReal with hm
  have hMm : M = ENNReal.ofReal m := (ENNReal.ofReal_toReal hMt).symm
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  set η : ℝ := min 1 (δ / (3 * m + 2)) with hηdef
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηδ : η * (3 * m + 2) ≤ δ := by
    have := min_le_right 1 (δ / (3 * m + 2))
    rw [← hηdef] at this
    calc η * (3 * m + 2) ≤ δ / (3 * m + 2) * (3 * m + 2) := by gcongr
      _ = δ := by field_simp
  refine (key η hη0).trans ?_
  have hreal : (1 + η) * ((1 + η) * m + η) ≤ m + δ := by
    nlinarith [mul_le_mul_of_nonneg_right hη1 (mul_nonneg hη0.le hm0),
      mul_le_mul_of_nonneg_right hη1 hη0.le]
  rw [hMm, ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) hη0.le,
    ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_coe_nnreal]
  exact (ENNReal.ofReal_le_ofReal hreal).trans ENNReal.ofReal_add_le

end Steklov
