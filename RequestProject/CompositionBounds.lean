module

public import Mathlib

/-!
# Smallness of derivatives under composition

* `CompositionBounds.norm_iteratedFDerivWithin_comp_le_small` — if all derivatives of order
  `1, …, n` of `f` at `x` are at most `δ ≤ 1`, and the derivatives of `g` of order `≤ n` at
  `f x` are at most `C`, then `‖D^n (g ∘ f)(x)‖ ≤ n! · C · δ` (from Mathlib's Faà di Bruno
  bound `norm_iteratedFDerivWithin_comp_le`, with `D = δ^{1/n}`).
* `CompositionBounds.log_comp_bound` — for `c > 0` and every order `n` there is `K` such that
  `|∂^n (log (c + g) - log c)| ≤ K δ` whenever `|g^{(j)}| ≤ δ ≤ min 1 (c/2)` for `j ≤ n`.
-/

@[expose] public section

open Set Filter Topology
open scoped Nat ContDiff

noncomputable section

namespace CompositionBounds

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F G : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedAddCommGroup G]
  [NormedSpace 𝕜 G]

/-- **Composition with a map whose derivatives are small.** -/
theorem norm_iteratedFDerivWithin_comp_le_small {g : F → G} {f : E → F} {n : ℕ} {s : Set E}
    {t : Set F} {x : E} {N : WithTop ℕ∞} (hg : ContDiffOn 𝕜 N g t) (hf : ContDiffOn 𝕜 N f s)
    (hn : (n : WithTop ℕ∞) ≤ N) (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s)
    (hst : MapsTo f s t) (hx : x ∈ s) (hn1 : 1 ≤ n) {C δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hC : ∀ i, i ≤ n → ‖iteratedFDerivWithin 𝕜 i g t (f x)‖ ≤ C)
    (hD : ∀ i, 1 ≤ i → i ≤ n → ‖iteratedFDerivWithin 𝕜 i f s x‖ ≤ δ) :
    ‖iteratedFDerivWithin 𝕜 n (g ∘ f) s x‖ ≤ n ! * C * δ := by
  set D : ℝ := δ ^ (1 / (n : ℝ)) with hD_def
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hpow : ∀ i : ℕ, D ^ i = δ ^ (1 / (n : ℝ) * i) := by
    intro i
    rw [Real.rpow_mul hδ0, Real.rpow_natCast]
  have hDn : D ^ n = δ := by
    rw [hpow, one_div_mul_cancel hnpos.ne', Real.rpow_one]
  have hDi : ∀ i, 1 ≤ i → i ≤ n → δ ≤ D ^ i := by
    intro i hi1 hin
    rw [hpow]
    conv_lhs => rw [← Real.rpow_one δ]
    refine Real.rpow_le_rpow_of_exponent_ge' hδ0 hδ1 (by positivity) ?_
    rw [one_div_mul_eq_div, div_le_one hnpos]
    exact_mod_cast hin
  have := norm_iteratedFDerivWithin_comp_le hg hf hn ht hs hst hx hC
    (D := D) (fun i hi1 hin => (hD i hi1 hin).trans (hDi i hi1 hin))
  rwa [hDn] at this

/-- Uniform bounds on derivatives of `log` on `[c/2, 3c/2]`. -/
lemma log_iteratedFDerivWithin_bound {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∃ C, ∀ i ≤ n, ∀ y ∈ Icc (c / 2) (3 * c / 2),
      ‖iteratedFDerivWithin ℝ i Real.log (Ioi (c / 4)) y‖ ≤ C := by
  have hcd : ContDiffOn ℝ ∞ Real.log (Ioi (c / 4)) :=
    Real.contDiffOn_log.mono fun y hy => by
      simp only [mem_Ioi] at hy; simp only [mem_compl_iff, mem_singleton_iff]; linarith
  have hsub : Icc (c / 2) (3 * c / 2) ⊆ Ioi (c / 4) := fun y hy => by
    simp only [mem_Ioi]; linarith [hy.1]
  have hone : ∀ i : ℕ, ∃ C, ∀ y ∈ Icc (c / 2) (3 * c / 2),
      ‖iteratedFDerivWithin ℝ i Real.log (Ioi (c / 4)) y‖ ≤ C := by
    intro i
    have hcont := hcd.continuousOn_iteratedFDerivWithin (m := i)
      (WithTop.coe_le_coe.2 le_top) (isOpen_Ioi.uniqueDiffOn)
    exact (isCompact_Icc).exists_bound_of_continuousOn (hcont.mono hsub)
  induction n with
  | zero =>
    obtain ⟨C, hC⟩ := hone 0
    exact ⟨C, fun i hi y hy => by
      rw [Nat.le_zero.1 hi]; exact hC y hy⟩
  | succ n ih =>
    obtain ⟨C₁, hC₁⟩ := ih
    obtain ⟨C₂, hC₂⟩ := hone (n + 1)
    refine ⟨max C₁ C₂, fun i hi y hy => ?_⟩
    rcases Nat.lt_or_ge i (n + 1) with h | h
    · exact (hC₁ i (by omega) y hy).trans (le_max_left _ _)
    · rw [show i = n + 1 by omega]; exact (hC₂ y hy).trans (le_max_right _ _)

lemma abs_log_add_sub_log_le {c x : ℝ} (hc : 0 < c) (hx : |x| ≤ c / 2) :
    |Real.log (c + x) - Real.log c| ≤ 2 / c * |x| := by
  have hcx : c / 2 ≤ c + x := by linarith [neg_abs_le x]
  have hcx0 : 0 < c + x := by linarith
  rw [abs_le]
  constructor
  · have h1 : Real.log (c / (c + x)) ≤ c / (c + x) - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hc.ne' hcx0.ne'] at h1
    have h2 : c / (c + x) - 1 = -x / (c + x) := by field_simp; ring
    have h3 : -x / (c + x) ≤ 2 / c * |x| := by
      rw [div_le_iff₀ hcx0]
      have : -x ≤ |x| := neg_le_abs x
      have : 2 / c * |x| * (c + x) ≥ 2 / c * |x| * (c / 2) := by
        gcongr
      have : 2 / c * |x| * (c / 2) = |x| := by field_simp
      linarith
    linarith
  · have h1 : Real.log ((c + x) / c) ≤ (c + x) / c - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div hcx0.ne' hc.ne'] at h1
    have h2 : (c + x) / c - 1 = x / c := by field_simp; ring
    have h3 : x / c ≤ 2 / c * |x| := by
      rw [div_le_iff₀ hc]
      have : x ≤ |x| := le_abs_self x
      have : 2 / c * |x| * c = 2 * |x| := by field_simp
      linarith [abs_nonneg x]
    linarith

/-- **Derivatives of `log (c + g) - log c` are controlled by those of `g`.** -/
theorem log_comp_bound {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ g : ℝ → ℝ, ContDiff ℝ ∞ g → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → δ ≤ c / 2 →
      (∀ j ≤ n, ∀ t, |iteratedDeriv j g t| ≤ δ) →
      ∀ t, |iteratedDeriv n (fun s => Real.log (c + g s) - Real.log c) t| ≤ K * δ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨2 / c, by positivity, fun g _ δ hδ0 _ hδc hg t => ?_⟩
    simp only [iteratedDeriv_zero]
    have h0 := hg 0 le_rfl t
    simp only [iteratedDeriv_zero] at h0
    calc |Real.log (c + g t) - Real.log c| ≤ 2 / c * |g t| :=
          abs_log_add_sub_log_le hc (h0.trans hδc)
      _ ≤ 2 / c * δ := by gcongr
  · obtain ⟨C, hC⟩ := log_iteratedFDerivWithin_bound hc n
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) c ⟨by linarith, by linarith⟩)
    refine ⟨n ! * C, by positivity, fun g hg δ hδ0 hδ1 hδc hbd t => ?_⟩
    have hfun : (fun s => Real.log (c + g s) - Real.log c) =
        fun s => -Real.log c + (Real.log ∘ fun s => c + g s) s := by
      funext s; simp only [Function.comp_apply]; ring
    rw [hfun, iteratedDeriv_const_add hn, ← Real.norm_eq_abs,
      ← norm_iteratedFDeriv_eq_norm_iteratedDeriv,
      ← iteratedFDerivWithin_univ]
    have hmaps : MapsTo (fun s => c + g s) univ (Ioi (c / 4)) := by
      intro s _
      have := hbd 0 (Nat.zero_le _) s
      simp only [iteratedDeriv_zero] at this
      simp only [mem_Ioi]
      linarith [neg_abs_le (g s)]
    have hlog : ContDiffOn ℝ ∞ Real.log (Ioi (c / 4)) :=
      Real.contDiffOn_log.mono fun y hy => by
        simp only [mem_Ioi] at hy; simp only [mem_compl_iff, mem_singleton_iff]; linarith
    refine norm_iteratedFDerivWithin_comp_le_small hlog
      (contDiff_const.add hg).contDiffOn (WithTop.coe_le_coe.2 le_top)
      isOpen_Ioi.uniqueDiffOn uniqueDiffOn_univ hmaps (mem_univ t) hn hδ0 hδ1
      (fun i hi => hC i hi _ ?_) (fun i hi1 hin => ?_)
    · have := hbd 0 (Nat.zero_le _) t
      simp only [iteratedDeriv_zero, abs_le] at this
      constructor <;> linarith [this.1, this.2]
    · rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
        iteratedDeriv_const_add (by omega), Real.norm_eq_abs]
      exact hbd i hin t

end CompositionBounds

end
