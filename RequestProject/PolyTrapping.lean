module

public import Mathlib

/-!
# Disk trapping and root localization for nearly monomial polynomials (Proposition 3.4.1)

For `Q(z) = zⁿ + ∑_{k<n} q_k z^k` with all `|q_k| ≤ s`:

* `norm_polyQ_le`: `|Q(z)| ≤ |z|ⁿ + n s` on `𝔻̄`;
* `norm_polyQ_ge`: `|Q(z)| ≥ |z| - n s` for `|z| ≥ 1`;
* `polyQ_root_small`: every root satisfies `|z| < ρ` as soon as `n s < ρⁿ` (`0 < ρ ≤ 1`);
* `ball_subset_component`, `preimage_subset_ball`: `B(0,r) ⊆ D ⊆ Q⁻¹(𝔻) ⊆ B(0,R)` for the
  component `D` of `Q⁻¹(𝔻)` containing `0`, when `rⁿ + n s < 1` and `1 + n s ≤ R`.
-/

@[expose] public section

open Complex Metric Set Filter Topology

noncomputable section

namespace SteklovCoalescence

/-- The nearly monomial polynomial `zⁿ + ∑_{k<n} q_k z^k`. -/
def polyQ (n : ℕ) (q : Fin n → ℂ) (z : ℂ) : ℂ := z ^ n + ∑ k : Fin n, q k * z ^ (k : ℕ)

lemma polyQ_continuous (n : ℕ) (q : Fin n → ℂ) : Continuous (polyQ n q) := by
  unfold polyQ; fun_prop

lemma polyQ_differentiable (n : ℕ) (q : Fin n → ℂ) : Differentiable ℂ (polyQ n q) := by
  unfold polyQ; fun_prop

variable {n : ℕ} {q : Fin n → ℂ} {s : ℝ}

lemma norm_sum_le_of_le_one (hq : ∀ k, ‖q k‖ ≤ s) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖∑ k : Fin n, q k * z ^ (k : ℕ)‖ ≤ n * s := by
  calc ‖∑ k : Fin n, q k * z ^ (k : ℕ)‖ ≤ ∑ k : Fin n, ‖q k * z ^ (k : ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, s := by
        gcongr with k
        rw [norm_mul, norm_pow]
        exact (mul_le_mul (hq k) (pow_le_one₀ (norm_nonneg _) hz) (by positivity)
          ((norm_nonneg _).trans (hq k))).trans (by rw [mul_one])
    _ = n * s := by simp

lemma norm_sum_le_of_one_le (hq : ∀ k, ‖q k‖ ≤ s) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖∑ k : Fin n, q k * z ^ (k : ℕ)‖ ≤ n * s * ‖z‖ ^ (n - 1) := by
  calc ‖∑ k : Fin n, q k * z ^ (k : ℕ)‖ ≤ ∑ k : Fin n, ‖q k * z ^ (k : ℕ)‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, s * ‖z‖ ^ (n - 1) := by
        gcongr with k
        rw [norm_mul, norm_pow]
        exact mul_le_mul (hq k) (pow_le_pow_right₀ hz (by omega)) (by positivity)
          ((norm_nonneg _).trans (hq k))
    _ = n * s * ‖z‖ ^ (n - 1) := by simp; ring

theorem norm_polyQ_le (hq : ∀ k, ‖q k‖ ≤ s) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖polyQ n q z‖ ≤ ‖z‖ ^ n + n * s := by
  unfold polyQ
  calc _ ≤ ‖z ^ n‖ + ‖∑ k : Fin n, q k * z ^ (k : ℕ)‖ := norm_add_le _ _
    _ ≤ ‖z‖ ^ n + n * s := by rw [norm_pow]; gcongr; exact norm_sum_le_of_le_one hq hz

theorem norm_polyQ_ge (hn : 1 ≤ n) (hq : ∀ k, ‖q k‖ ≤ s) {z : ℂ} (hz : 1 ≤ ‖z‖) :
    ‖z‖ - n * s ≤ ‖polyQ n q z‖ := by
  have h1 := norm_sum_le_of_one_le hq hz
  have h2 : ‖z ^ n‖ - ‖∑ k : Fin n, q k * z ^ (k : ℕ)‖ ≤ ‖polyQ n q z‖ := by
    unfold polyQ
    have := norm_sub_norm_le (z ^ n) (-(∑ k : Fin n, q k * z ^ (k : ℕ)))
    rwa [norm_neg, sub_neg_eq_add] at this
  rw [norm_pow] at h2
  have hpow : ‖z‖ ^ n = ‖z‖ ^ (n - 1) * ‖z‖ := by
    rw [← pow_succ]; congr 1; omega
  have hp1 : 1 ≤ ‖z‖ ^ (n - 1) := one_le_pow₀ hz
  rcases le_or_gt (‖z‖ - n * s) 0 with h | h
  · exact h.trans (norm_nonneg _)
  · nlinarith

/-- **Root localization.** If `n s < ρⁿ` with `0 < ρ ≤ 1`, every root of `Q` lies in `B(0,ρ)`. -/
theorem polyQ_root_small (hn : 1 ≤ n) (hq : ∀ k, ‖q k‖ ≤ s) {ρ : ℝ} (hρ0 : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hs : n * s < ρ ^ n) {z : ℂ} (hz : polyQ n q z = 0) : ‖z‖ < ρ := by
  by_contra hcon
  push_neg at hcon
  rcases le_or_gt ‖z‖ 1 with h1 | h1
  · have heq : z ^ n = -∑ k : Fin n, q k * z ^ (k : ℕ) := by
      unfold polyQ at hz; linear_combination hz
    have := congrArg norm heq
    rw [norm_neg, norm_pow] at this
    have h2 := norm_sum_le_of_le_one hq h1
    have h3 : ρ ^ n ≤ ‖z‖ ^ n := pow_le_pow_left₀ hρ0.le hcon n
    linarith
  · have := norm_polyQ_ge hn hq h1.le
    rw [hz, norm_zero] at this
    have : ρ ^ n ≤ 1 := pow_le_one₀ hρ0.le hρ1
    linarith

/-- **Inner disk trapping.** -/
theorem ball_subset_component (hq : ∀ k, ‖q k‖ ≤ s) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hs : r ^ n + n * s < 1) :
    ball 0 r ⊆ connectedComponentIn (polyQ n q ⁻¹' ball 0 1) 0 := by
  refine (convex_ball (0 : ℂ) r).isPreconnected.subset_connectedComponentIn
    (mem_ball_self hr0) fun z hz => ?_
  have hz' := mem_ball_zero_iff.1 hz
  rw [mem_preimage, mem_ball_zero_iff]
  calc ‖polyQ n q z‖ ≤ ‖z‖ ^ n + n * s := norm_polyQ_le hq (by linarith)
    _ ≤ r ^ n + n * s := by gcongr
    _ < 1 := hs

/-- **Outer disk trapping.** -/
theorem preimage_subset_ball (hn : 1 ≤ n) (hq : ∀ k, ‖q k‖ ≤ s) {R : ℝ}
    (hR : 1 + n * s ≤ R) (hs : 0 ≤ s) :
    polyQ n q ⁻¹' ball 0 1 ⊆ ball 0 R := by
  intro z hz
  rw [mem_preimage, mem_ball_zero_iff] at hz
  rw [mem_ball_zero_iff]
  by_contra hcon
  push_neg at hcon
  have hns : 0 ≤ (n : ℝ) * s := by positivity
  have := norm_polyQ_ge hn hq (show 1 ≤ ‖z‖ by linarith)
  linarith

theorem component_subset_ball (hn : 1 ≤ n) (hq : ∀ k, ‖q k‖ ≤ s) {R : ℝ}
    (hR : 1 + n * s ≤ R) (hs : 0 ≤ s) :
    connectedComponentIn (polyQ n q ⁻¹' ball 0 1) 0 ⊆ ball 0 R :=
  (connectedComponentIn_subset _ _).trans (preimage_subset_ball hn hq hR hs)

end SteklovCoalescence
