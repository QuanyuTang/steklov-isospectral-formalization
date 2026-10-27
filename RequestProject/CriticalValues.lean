module

public import Mathlib

/-!
# Elementary steps in Sections 3.2–3.5

* The branch values `u_ε = ε`, `v_ε = λ_* ε` with `λ_* = 2 + i`; both lie in `𝔻` for
  `0 < ε < 1/3` (`branchValues_mem_disk`).
* **Critical-value matching** (the final step of the noncongruence argument, §3.5):
  - orientation-preserving case: `{ε, λ_* ε} = {η ε', η λ_* ε'}` with `|η| = 1`, `ε, ε' > 0`
    forces `ε = ε'` and `η = 1` (`critical_values_match`);
  - orientation-reversing case: `{ε, λ_* ε} = {η ε', η λ̄_* ε'}` is impossible
    (`critical_values_no_reflection`).
* **Coalescence estimate** (Proposition 3.4.1): if `τ_ε^n = δ_ε = (λ_* - 1) ε` then for every
  `0 ≤ k < n`, `δ_ε τ_ε^{-k} → 0` as `ε → 0⁺` (`coalescence_coeff_tendsto_zero`), which is the
  coefficient convergence `Q_{j,ε} → z^n`.
-/

@[expose] public section

open Filter Topology Complex

namespace SteklovCritical

/-- The fixed nonreal parameter `λ_* = 2 + i` with `|λ_*| > 1`. -/
noncomputable def lamStar : ℂ := 2 + I

lemma normSq_lamStar : normSq lamStar = 5 := by
  simp [lamStar, normSq_apply]; norm_num

lemma lamStar_im : lamStar.im = 1 := by simp [lamStar]

lemma one_lt_norm_lamStar : 1 < ‖lamStar‖ := by
  have h : ‖lamStar‖ ^ 2 = 5 := by rw [← normSq_eq_norm_sq, normSq_lamStar]
  nlinarith [norm_nonneg lamStar]

lemma lamStar_not_real : lamStar ∉ Set.range ((↑) : ℝ → ℂ) := by
  rintro ⟨r, hr⟩
  have := congrArg Complex.im hr
  simp [lamStar] at this

/-- For `0 < ε < 1/3` both branch values `ε` and `λ_* ε` lie in the open unit disk. -/
theorem branchValues_mem_disk {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 3) :
    ‖(ε : ℂ)‖ < 1 ∧ ‖lamStar * ε‖ < 1 := by
  refine ⟨by rw [norm_real, Real.norm_eq_abs, abs_of_pos h0]; linarith, ?_⟩
  have h : ‖lamStar * ε‖ ^ 2 = 5 * ε ^ 2 := by
    rw [← normSq_eq_norm_sq, normSq_mul, normSq_lamStar, normSq_ofReal]; ring
  nlinarith [norm_nonneg (lamStar * ε)]

private lemma nsq_smul (η : ℂ) (hη : ‖η‖ = 1) (c : ℂ) (r : ℝ) :
    normSq (η * c * r) = normSq c * r ^ 2 := by
  have : normSq η = 1 := by rw [normSq_eq_norm_sq, hη]; norm_num
  rw [normSq_mul, normSq_mul, this, normSq_ofReal]; ring

/-- **Orientation-preserving matching.** If `{ε, λ_* ε} = {η ε', η λ_* ε'}` with `|η| = 1` and
`ε, ε' > 0`, then `ε = ε'` and `η = 1`.  The general form allows any `c` with `|c| > 1` in place
of `λ_*` on the right (for the orientation-reversing case `c = λ̄_*`). -/
theorem critical_values_match_gen {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') {η c : ℂ}
    (hη : ‖η‖ = 1) (hc : normSq c = 5)
    (h : ({(ε : ℂ), lamStar * ε} : Set ℂ) = {η * ε', η * c * ε'}) :
    ε = ε' ∧ η = 1 := by
  have m1 : (ε : ℂ) ∈ ({η * ε', η * c * ε'} : Set ℂ) := h ▸ (by simp)
  have m2 : η * (ε' : ℂ) ∈ ({(ε : ℂ), lamStar * ε} : Set ℂ) := h ▸ (by simp)
  have hηsq : normSq η = 1 := by rw [normSq_eq_norm_sq, hη]; norm_num
  have key : (ε : ℂ) = η * ε' := by
    rcases m1 with h1 | h1
    · exact h1
    · exfalso
      have e1 : ε ^ 2 = 5 * ε' ^ 2 := by
        have := congrArg normSq h1
        rw [normSq_ofReal, nsq_smul η hη c ε', hc] at this; nlinarith
      rcases m2 with h2 | h2
      · have := congrArg normSq h2
        rw [normSq_mul, hηsq, normSq_ofReal, normSq_ofReal] at this
        nlinarith
      · have := congrArg normSq h2
        rw [normSq_mul, hηsq, normSq_ofReal, normSq_mul, normSq_lamStar, normSq_ofReal] at this
        nlinarith
  have hee : ε = ε' := by
    have := congrArg normSq key
    rw [normSq_ofReal, normSq_mul, hηsq, normSq_ofReal] at this
    nlinarith
  refine ⟨hee, ?_⟩
  subst hee
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have : (1 : ℂ) * ε = η * ε := by simpa using key
  exact (mul_right_cancel₀ hε0 this).symm

/-- **Orientation-preserving matching** (§3.5). -/
theorem critical_values_match {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') {η : ℂ} (hη : ‖η‖ = 1)
    (h : ({(ε : ℂ), lamStar * ε} : Set ℂ) = {η * ε', η * lamStar * ε'}) :
    ε = ε' ∧ η = 1 :=
  critical_values_match_gen hε hε' hη normSq_lamStar h

/-- **Orientation-reversing exclusion** (§3.5): the critical-value sets
`{ε, λ_* ε}` and `{η ε', η λ̄_* ε'}` never coincide. -/
theorem critical_values_no_reflection {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') {η : ℂ}
    (hη : ‖η‖ = 1) :
    ({(ε : ℂ), lamStar * ε} : Set ℂ) ≠ {η * ε', η * (starRingEnd ℂ) lamStar * ε'} := by
  intro h
  have hc : normSq ((starRingEnd ℂ) lamStar) = 5 := by rw [normSq_conj, normSq_lamStar]
  obtain ⟨rfl, rfl⟩ := critical_values_match_gen hε hε' hη hc h
  have m : lamStar * (ε : ℂ) ∈ ({1 * (ε : ℂ), 1 * (starRingEnd ℂ) lamStar * ε} : Set ℂ) :=
    h ▸ (by simp)
  have hε0 : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  rcases m with h1 | h1
  · have := congrArg Complex.im h1
    simp [lamStar] at this
    exact hε.ne' this
  · rw [one_mul] at h1
    have := congrArg Complex.im (mul_right_cancel₀ hε0 h1)
    simp [lamStar] at this
    norm_num at this

/-- `|δ τ^{-k}| = |τ|^{n-k}` when `τ^n = δ` and `k < n` (equivalently `|δ|^{1-k/n}`). -/
lemma norm_coeff (n k : ℕ) (hk : k < n) (δ τ : ℂ) (hτ : τ ^ n = δ) :
    ‖δ * τ⁻¹ ^ k‖ = ‖τ‖ ^ (n - k) := by
  rw [← hτ, norm_mul, norm_pow, norm_pow, norm_inv]
  rcases eq_or_ne ‖τ‖ 0 with h0 | h0
  · rw [h0, zero_pow (by omega), zero_pow (by omega), zero_mul]
  · rw [pow_sub₀ _ h0 hk.le, inv_pow]

/-- **Coalescence of coefficients** (Proposition 3.4.1).  If `τ_ε^n = δ_ε = (λ_* - 1)ε` then for
each `0 ≤ k < n` the coefficient `δ_ε τ_ε^{-k}` of `Q_{j,ε}` tends to `0` as `ε → 0⁺`. -/
theorem coalescence_coeff_tendsto_zero (n k : ℕ) (hk : k < n) (τ : ℝ → ℂ)
    (hτ : ∀ ε, τ ε ^ n = (lamStar - 1) * ε) :
    Tendsto (fun ε : ℝ => (lamStar - 1) * ε * (τ ε)⁻¹ ^ k) (𝓝[>] 0) (𝓝 0) := by
  refine Tendsto.mono_left ?_ nhdsWithin_le_nhds
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simp_rw [norm_coeff n k hk _ _ (hτ _)]
  have hn : 0 < n := by omega
  have hnorm : ∀ ε : ℝ, ‖τ ε‖ = (‖lamStar - 1‖ * |ε|) ^ (1 / (n : ℝ)) := by
    intro ε
    have h1 : ‖τ ε‖ ^ n = ‖lamStar - 1‖ * |ε| := by
      rw [← norm_pow, hτ, norm_mul, norm_real, Real.norm_eq_abs]
    rw [← h1, one_div, Real.pow_rpow_inv_natCast (norm_nonneg _) hn.ne']
  have ht : Tendsto (fun ε : ℝ => ‖τ ε‖) (𝓝 0) (𝓝 0) := by
    simp_rw [hnorm]
    have hc : Continuous (fun ε : ℝ => (‖lamStar - 1‖ * |ε|) ^ (1 / (n : ℝ))) :=
      (Real.continuous_rpow_const (by positivity)).comp (continuous_const.mul continuous_abs)
    have := hc.tendsto 0
    simp only [abs_zero, mul_zero] at this
    rwa [Real.zero_rpow (by positivity)] at this
  have := ht.pow (n - k)
  rwa [zero_pow (by omega)] at this

end SteklovCritical
