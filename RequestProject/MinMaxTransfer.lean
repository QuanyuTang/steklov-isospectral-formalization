module

public import RequestProject.Defs

/-!
# Transfer of min–max values along linear maps of test functions

If a linear map `T` of test functions preserves smoothness, Dirichlet-type numerators and
boundary masses, then the min–max values for `(E₂, B₂)` are at most those for `(E₁, B₁)`.
Applying this in both directions gives equality of the variational spectra.
-/

@[expose] public section

open scoped ENNReal ContDiff

noncomputable section

namespace Steklov

/-- **Min–max transfer.** -/
theorem minMax_le_of_transfer {E₁ B₁ E₂ B₂ : (ℂ → ℝ) → ℝ≥0∞}
    (T : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ)) (hB₂ : B₂ 0 = 0)
    (hT : ∀ u, ContDiff ℝ ∞ u → ContDiff ℝ ∞ (T u) ∧ E₂ (T u) = E₁ u ∧ B₂ (T u) = B₁ u)
    (k : ℕ) : minMax E₂ B₂ k ≤ minMax E₁ B₁ k := by
  unfold minMax
  refine le_iInf₂ fun V hV => ?_
  obtain ⟨hsm, hdim, hpos⟩ := hV
  have hTz : ∀ u ∈ V, T u = 0 → u = 0 := by
    intro u hu h0
    by_contra hne
    apply hpos u hu hne
    rw [← (hT u (hsm u hu)).2.2, h0, hB₂]
  have hinj : Function.Injective (T.domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    exact Subtype.ext (hTz u u.2 hu)
  have hW : AdmissibleSpace B₂ k (V.map T) := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩; exact (hT u (hsm u hu)).1
    · rw [← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj, hdim]
    · rintro _ ⟨u, hu, rfl⟩ hne
      have hu0 : u ≠ 0 := by rintro rfl; exact hne (map_zero T)
      rw [(hT u (hsm u hu)).2.2]
      exact hpos u hu hu0
  refine (iInf₂_le (V.map T) hW).trans ?_
  refine iSup₂_le fun w hw => iSup_le fun hne => ?_
  obtain ⟨u, hu, rfl⟩ := hw
  have hu0 : u ≠ 0 := by rintro rfl; exact hne (map_zero T)
  rw [(hT u (hsm u hu)).2.1, (hT u (hsm u hu)).2.2]
  exact le_iSup₂_of_le (f := fun u (_ : u ∈ V) => ⨆ (_ : u ≠ 0), E₁ u / B₁ u) u hu
    (le_iSup_of_le hu0 le_rfl)

end Steklov
