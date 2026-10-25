module

public import RequestProject.ActualKernel

/-!
# Steklov isospectrality of the actual degree-seven disk-cover families

For `s² = -7`, monic normalizations `P₊ = monicP s aP`, `P₋ = monicP (-s) aM` (`aP⁷ = -b_s`,
`aM⁷ = -b_{-s}`) and any `τ` with `τ(ε)⁷ = (λ_* - 1) ε`, the normalized disk covers
`B_{±,ε} = Q_{±,ε} ∘ ψ_{±,ε}` of the paper's polynomials `Q_{±,ε} = paperQ P_± τ ε` have **equal
weighted Steklov spectra** `σ_k(𝔻, |B'_{+,ε}|) = σ_k(𝔻, |B'_{-,ε}|)` for every `k` and every
`0 < ε < 1/10` (`family_spectra_eq`), for **any** choice of normalized disk covers; such covers
exist for all small `ε` (`exists_family_isospectral`).
-/

@[expose] public section

open Complex Metric Set Filter Topology Polynomial

noncomputable section

namespace FamilyIso

open SteklovBlaschke SteklovCoalescence SteklovCritical Degree7 ActualKernel

lemma norm_lamStar_sub_one_le : ‖lamStar - 1‖ ≤ 2 := by
  have : lamStar - 1 = 1 + I := by simp only [lamStar]; ring
  rw [this]
  calc ‖(1 : ℂ) + I‖ ≤ ‖(1 : ℂ)‖ + ‖I‖ := norm_add_le _ _
    _ = 2 := by simp; norm_num

/-- **Isospectrality of the actual families** (any normalized disk covers, `0 < ε < 1/10`). -/
theorem family_spectra_eq {s aP aM : ℂ} (hs : s ^ 2 = -7) (haP : aP ^ 7 = -bconst s)
    (haM : aM ^ 7 = -bconst (-s)) {τ : ℝ → ℂ} (hτ : ∀ ε, τ ε ^ 7 = (lamStar - 1) * ε)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 10) {ψP BP ψM BM : ℂ → ℂ}
    (hP : IsNormalizedDiskCover (paperQ (monicP s aP) τ ε) 7 ψP BP)
    (hM : IsNormalizedDiskCover (paperQ (monicP (-s) aM) τ ε) 7 ψM BM) :
    Steklov.weightedSteklovSpectrum (fun z => ‖deriv BP z‖) =
      Steklov.weightedSteklovSpectrum (fun z => ‖deriv BM z‖) := by
  have hs' : (-s) ^ 2 = -7 := neg_sq_seven hs
  set δ : ℂ := (lamStar - 1) * ε with hδdef
  have hδ : δ ≠ 0 := mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast hε0.ne')
  have hτ0 : τ ε ≠ 0 := by
    intro h; have := hτ ε; rw [h, zero_pow (by norm_num)] at this; exact hδ this.symm
  have ha0 : ∀ {t a : ℂ}, t ^ 2 = -7 → a ^ 7 = -bconst t → a ≠ 0 := by
    intro t a ht ha h; rw [h, zero_pow (by norm_num)] at ha
    exact bconst_ne_zero ht (neg_eq_zero.1 ha.symm)
  have hsmall : ‖(ε : ℂ)‖ + ‖δ‖ < 1 / 2 := by
    rw [hδdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
    have := norm_lamStar_sub_one_le
    nlinarith
  have hform : ∀ {t a : ℂ} {ψ B : ℂ → ℂ}, t ^ 2 = -7 → a ^ 7 = -bconst t →
      IsNormalizedDiskCover (paperQ (monicP t a) τ ε) 7 ψ B →
      ∀ z : ℂ, ‖z‖ < 1 → B z = ε + δ * pfun t ((a / τ ε) * ψ z) := by
    intro t a ψ B ht ha hc z hz
    rw [hc.2.2.2.2.2.2.2 z (mem_ball_zero_iff.2 hz), paperQ, monicP_eval ht ha]
    congr 2
    field_simp
  have hκ : ∀ {t a : ℂ}, t ^ 2 = -7 → a ^ 7 = -bconst t → a / τ ε ≠ 0 :=
    fun ht ha => div_ne_zero (ha0 ht ha) hτ0
  funext k
  exact (spectra_eq_of_disk_data hs hδ hsmall (hκ hs' haM) (hκ hs haP)
    hM.2.2.2.2.2.2.1 hP.2.2.2.2.2.2.1 hM.1 hM.2.1 hP.1 hP.2.1 (hform hs' haM hM)
    (hform hs haP hP) k).symm

/-- **Existence and isospectrality**: for `s = i√7` and the monic normalizations of `p_{±s}`,
there are `ε₀ > 0` and normalized disk covers `ψ_{±,ε}, B_{±,ε}` of the paper's polynomials for
all `0 < ε < ε₀`, and their weighted Steklov spectra coincide. -/
theorem exists_family_isospectral {τ : ℝ → ℂ} (hτ : ∀ ε, τ ε ^ 7 = (lamStar - 1) * ε) :
    ∃ aP aM : ℂ, aP ^ 7 = -bconst (I * Real.sqrt 7) ∧ aM ^ 7 = -bconst (-(I * Real.sqrt 7)) ∧
      ∃ ε₀ > (0 : ℝ), ∃ ψP BP ψM BM : ℝ → ℂ → ℂ, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        IsNormalizedDiskCover (paperQ (monicP (I * Real.sqrt 7) aP) τ ε) 7 (ψP ε) (BP ε) ∧
        IsNormalizedDiskCover (paperQ (monicP (-(I * Real.sqrt 7)) aM) τ ε) 7 (ψM ε) (BM ε) ∧
        Steklov.weightedSteklovSpectrum (fun z => ‖deriv (BP ε) z‖) =
          Steklov.weightedSteklovSpectrum (fun z => ‖deriv (BM ε) z‖) := by
  set s : ℂ := I * Real.sqrt 7
  have hs : s ^ 2 = -7 := i_sqrt7_sq.1
  have hs' : (-s) ^ 2 = -7 := neg_sq_seven hs
  obtain ⟨aP, -, haP, hmP, hdP, -, -⟩ := exists_monic_normalization hs
  obtain ⟨aM, -, haM, hmM, hdM, -, -⟩ := exists_monic_normalization hs'
  obtain ⟨ε₁, hε₁, ψP, BP, hP⟩ := exists_paper_diskCover hmP (by norm_num) hdP hτ
  obtain ⟨ε₂, hε₂, ψM, BM, hM⟩ := exists_paper_diskCover hmM (by norm_num) hdM hτ
  refine ⟨aP, aM, haP, haM, min (min ε₁ ε₂) (1 / 10), lt_min (lt_min hε₁ hε₂) (by norm_num),
    ψP, BP, ψM, BM, fun ε hε0 hε => ?_⟩
  have h1 : ε < ε₁ := hε.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have h2 : ε < ε₂ := hε.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have h3 : ε < 1 / 10 := hε.trans_le (min_le_right _ _)
  exact ⟨hP ε hε0 h1, hM ε hε0 h2,
    family_spectra_eq hs haP haM hτ hε0 h3 (hP ε hε0 h1) (hM ε hε0 h2)⟩

end FamilyIso

end
