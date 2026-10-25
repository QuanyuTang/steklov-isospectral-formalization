module

public import Mathlib
public import RequestProject.PolyTrapping

/-!
# The lemniscate domain `{|Q| < 1}` of a nearly monomial polynomial

For `Q(z) = zⁿ + ∑_{k<n} q_k z^k` with `|q_k| ≤ s`, `3 n s 16ⁿ < 1`:

* `polyQ_eq_prod`: `Q(z) = ∏_{l<n} (z - r_l)` for some roots `r_l` (listed with multiplicity);
* `re_polyQ_deriv_pos`: `Re(z Q'(z) \overline{Q(z)}) > 0` on `1/2 ≤ |z| ≤ 2`, so `|Q|` increases
  strictly along rays there;
* `starConvex_preimage`: `V = Q⁻¹(𝔻)` is star-shaped with respect to `0`;
* `nearDisk_preimage`: `V` is open, bounded, star-shaped, contains `0`, and it is the connected
  component of `Q⁻¹(𝔻)` containing `0`.
-/

@[expose] public section

open Set Filter Topology Metric Complex Polynomial

noncomputable section

namespace SteklovCoalescence

/-- **Factorization into linear factors** (with multiplicity). -/
theorem polyQ_eq_prod (n : ℕ) (q : Fin n → ℂ) :
    ∃ r : Fin n → ℂ, ∀ z : ℂ, polyQ n q z = ∏ l, (z - r l) := by
  set p : ℂ[X] := X ^ n + ∑ k : Fin n, C (q k) * X ^ (k : ℕ) with hp
  have hdeg : (∑ k : Fin n, C (q k) * X ^ (k : ℕ)).degree < (X ^ n : ℂ[X]).degree := by
    rw [degree_X_pow]
    refine lt_of_le_of_lt (degree_sum_le _ _) ?_
    rw [Finset.sup_lt_iff (WithBot.bot_lt_coe _)]
    intro k _
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le _ _) (by exact_mod_cast k.2)
  have hmon : p.Monic := (monic_X_pow n).add_of_left hdeg
  have hnat : p.natDegree = n := by
    rw [hp, natDegree_add_eq_left_of_degree_lt hdeg, natDegree_X_pow]
  have hcard : p.roots.card = n := by rw [IsAlgClosed.card_roots_eq_natDegree, hnat]
  have hprod := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon (by rw [hcard, hnat])
  have key : ∀ z, p.eval z = (p.roots.toList.map (fun a => z - a)).prod := by
    intro z
    conv_lhs => rw [← hprod]
    rw [eval_multiset_prod, ← Multiset.coe_toList p.roots, Multiset.map_coe, Multiset.map_coe,
      Multiset.prod_coe, List.map_map]
    simp [Function.comp_def]
  have h1 : ∀ z, p.eval z = polyQ n q z := by
    intro z; simp [hp, eval_finset_sum, polyQ]
  set L := p.roots.toList with hL
  have hLlen : L.length = n := by rw [hL, Multiset.length_toList, hcard]
  refine ⟨fun l => L.get ⟨l, by rw [hLlen]; exact l.2⟩, fun z => ?_⟩
  rw [← h1, key, ← Fin.prod_univ_fun_getElem]
  exact Fintype.prod_equiv (finCongr hLlen) _ _ (fun l => rfl)

/-- The derivative `Q'`. -/
def dpolyQ (n : ℕ) (q : Fin n → ℂ) (w : ℂ) : ℂ :=
  n * w ^ (n - 1) + ∑ k : Fin n, q k * ((k : ℕ) * w ^ ((k : ℕ) - 1))

lemma hasDerivAt_polyQ (n : ℕ) (q : Fin n → ℂ) (w : ℂ) :
    HasDerivAt (polyQ n q) (dpolyQ n q w) w := by
  have h1 := hasDerivAt_pow n w
  have h2 : HasDerivAt (fun z => ∑ k : Fin n, q k * z ^ (k : ℕ))
      (∑ k : Fin n, q k * ((k : ℕ) * w ^ ((k : ℕ) - 1))) w := by
    have := HasDerivAt.sum (u := Finset.univ) (A := fun (k : Fin n) (z : ℂ) => q k * z ^ (k : ℕ))
      (A' := fun k => q k * ((k : ℕ) * w ^ ((k : ℕ) - 1))) (x := w)
      (fun k _ => (hasDerivAt_pow (k : ℕ) w).const_mul (q k))
    convert this using 1
    ext z; simp
  exact h1.add h2

lemma mul_pow_pred (k : ℕ) (w : ℂ) : w * ((k : ℂ) * w ^ (k - 1)) = k * w ^ k := by
  cases k with
  | zero => simp
  | succ m => simp [pow_succ]; ring

lemma mul_dpolyQ (n : ℕ) (q : Fin n → ℂ) (w : ℂ) :
    w * dpolyQ n q w = n * w ^ n + ∑ k : Fin n, q k * ((k : ℕ) * w ^ (k : ℕ)) := by
  rw [dpolyQ, mul_add, Finset.mul_sum]
  congr 1
  · rw [mul_pow_pred]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_left_comm, mul_pow_pred]

variable {n : ℕ} {q : Fin n → ℂ} {s : ℝ}

/-- **Radial monotonicity of `|Q|`** in the annulus `1/2 ≤ |w| ≤ 2`. -/
theorem re_polyQ_deriv_pos (hq : ∀ k, ‖q k‖ ≤ s) (hs0 : 0 ≤ s)
    (hs : 3 * n * s * 16 ^ n < 1) {w : ℂ} (hw1 : 1 / 2 ≤ ‖w‖) (hw2 : ‖w‖ ≤ 2)
    (hn : 1 ≤ n) : 0 < (w * dpolyQ n q w * (starRingEnd ℂ) (polyQ n q w)).re := by
  set E := ∑ k : Fin n, q k * w ^ (k : ℕ) with hE
  set E2 := ∑ k : Fin n, q k * ((k : ℕ) * w ^ (k : ℕ)) with hE2
  set X : ℝ := 2 ^ n with hX
  set p : ℝ := ‖w‖ ^ n with hp
  have hX1 : 1 ≤ X := one_le_pow₀ (by norm_num)
  have hwk : ∀ k : Fin n, ‖w‖ ^ (k : ℕ) ≤ X := fun k =>
    (pow_le_pow_left₀ (norm_nonneg w) hw2 _).trans (pow_le_pow_right₀ (by norm_num) k.2.le)
  have hEn : ‖E‖ ≤ n * s * X := by
    calc ‖E‖ ≤ ∑ k : Fin n, ‖q k * w ^ (k : ℕ)‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin n, s * X := by
          gcongr with k
          rw [norm_mul, norm_pow]
          exact mul_le_mul (hq k) (hwk k) (by positivity) hs0
      _ = n * s * X := by simp; ring
  have hE2n : ‖E2‖ ≤ n * (n * s * X) := by
    calc ‖E2‖ ≤ ∑ k : Fin n, ‖q k * ((k : ℕ) * w ^ (k : ℕ))‖ := norm_sum_le _ _
      _ ≤ ∑ _k : Fin n, n * s * X := by
          gcongr with k
          rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
          have hk : ((k : ℕ) : ℝ) ≤ n := by exact_mod_cast k.2.le
          calc ‖q k‖ * ((k : ℕ) * ‖w‖ ^ (k : ℕ)) ≤ s * (n * X) := by
                gcongr
                · exact hq k
                · exact hwk k
            _ = n * s * X := by ring
      _ = n * (n * s * X) := by simp
  have hpX : p ≤ X := pow_le_pow_left₀ (norm_nonneg w) hw2 n
  have hpX1 : 1 ≤ p * X := by
    rw [hp, hX, ← mul_pow]
    exact one_le_pow₀ (by linarith)
  have hp0 : 0 ≤ p := by positivity
  have hQ : polyQ n q w = w ^ n + E := rfl
  have hD : w * dpolyQ n q w = n * w ^ n + E2 := mul_dpolyQ n q w
  rw [hD, hQ]
  have hexp : (n * w ^ n + E2) * (starRingEnd ℂ) (w ^ n + E) =
      ((n * p ^ 2 : ℝ) : ℂ) + (E2 * (starRingEnd ℂ) (w ^ n) + n * w ^ n * (starRingEnd ℂ) E +
        E2 * (starRingEnd ℂ) E) := by
    have : w ^ n * (starRingEnd ℂ) (w ^ n) = (p : ℂ) ^ 2 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hp]; push_cast; ring
    rw [map_add]
    push_cast
    rw [← this]
    ring
  rw [hexp, Complex.add_re, Complex.ofReal_re]
  set R := E2 * (starRingEnd ℂ) (w ^ n) + n * w ^ n * (starRingEnd ℂ) E +
    E2 * (starRingEnd ℂ) E with hR
  have hRn : ‖R‖ ≤ p * (n * (n * s * X)) + n * p * (n * s * X) +
      n * (n * s * X) * (n * s * X) := by
    rw [hR]
    refine (norm_add₃_le).trans ?_
    simp only [norm_mul, Complex.norm_conj, norm_pow, Complex.norm_natCast, ← hp]
    have hE0 : 0 ≤ ‖E‖ := norm_nonneg _
    have a1 : ‖E2‖ * p ≤ p * (n * (n * s * X)) := by
      rw [mul_comm]; exact mul_le_mul_of_nonneg_left hE2n hp0
    have a2 : n * p * ‖E‖ ≤ n * p * (n * s * X) :=
      mul_le_mul_of_nonneg_left hEn (by positivity)
    have a3 : ‖E2‖ * ‖E‖ ≤ n * (n * s * X) * (n * s * X) :=
      mul_le_mul hE2n hEn hE0 (by positivity)
    linarith
  have hre : -‖R‖ ≤ R.re := by
    have := Complex.abs_re_le_norm R
    linarith [neg_abs_le R.re]
  have hns : (n : ℝ) * s ≤ 1 := by
    have h16 : (1 : ℝ) ≤ 16 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hX4 : X ^ 4 = 16 ^ n := by rw [hX, ← pow_mul, mul_comm, pow_mul]; norm_num
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  -- `‖R‖ ≤ 3 n² s X²`
  have hRb : ‖R‖ ≤ 3 * n ^ 2 * s * X ^ 2 := by
    have h1 : p * (n * (n * s * X)) ≤ n ^ 2 * s * X ^ 2 := by
      have := mul_le_mul_of_nonneg_right hpX (by positivity : (0 : ℝ) ≤ n * (n * s * X))
      nlinarith
    have h2 : n * p * (n * s * X) ≤ n ^ 2 * s * X ^ 2 := by
      have := mul_le_mul_of_nonneg_right hpX (by positivity : (0 : ℝ) ≤ n * (n * s * X))
      nlinarith
    have h3 : n * (n * s * X) * (n * s * X) ≤ n ^ 2 * s * X ^ 2 := by
      have : n * (n * s * X) * (n * s * X) = (n * s) * (n ^ 2 * s * X ^ 2) := by ring
      rw [this]
      have : 0 ≤ n ^ 2 * s * X ^ 2 := by positivity
      nlinarith
    linarith
  -- `n p² ≥ n / X²` and `3 n² s X² < n / X²`
  have hmain : 3 * n ^ 2 * s * X ^ 2 < n * p ^ 2 := by
    have hpX2 : 1 ≤ (p * X) ^ 2 := one_le_pow₀ hpX1
    have hX2 : 0 < X ^ 2 := by positivity
    have : 3 * n ^ 2 * s * X ^ 2 * X ^ 2 < n := by
      have : 3 * n ^ 2 * s * X ^ 2 * X ^ 2 = n * (3 * n * s * X ^ 4) := by ring
      rw [this, hX4]
      nlinarith
    have : n ≤ n * p ^ 2 * X ^ 2 := by
      have : n * p ^ 2 * X ^ 2 = n * (p * X) ^ 2 := by ring
      rw [this]; nlinarith
    nlinarith
  linarith

/-- `|Q|` does not decrease along the ray from `t₀ z` to `z` when `t₀ |z| ≥ 1/2`, `|z| ≤ 2`. -/
theorem norm_polyQ_radial_le (hq : ∀ k, ‖q k‖ ≤ s) (hs0 : 0 ≤ s)
    (hs : 3 * n * s * 16 ^ n < 1) (hn : 1 ≤ n) {z : ℂ} (hz : ‖z‖ ≤ 2) {t₀ : ℝ}
    (ht₀ : 0 < t₀) (ht₁ : t₀ ≤ 1) (hhalf : 1 / 2 ≤ t₀ * ‖z‖) :
    ‖polyQ n q ((t₀ : ℂ) * z)‖ ≤ ‖polyQ n q z‖ := by
  set f : ℝ → ℝ := fun τ => ‖polyQ n q ((τ : ℂ) * z)‖ ^ 2 with hf
  have hderiv : ∀ τ : ℝ, HasDerivAt f
      (2 * inner ℝ (polyQ n q ((τ : ℂ) * z)) (dpolyQ n q ((τ : ℂ) * z) * z)) τ := by
    intro τ
    have h1 : HasDerivAt (fun u : ℂ => polyQ n q (u * z)) (dpolyQ n q ((τ : ℂ) * z) * z)
        (τ : ℂ) := (hasDerivAt_polyQ n q _).comp (τ : ℂ) (by simpa using (hasDerivAt_mul_const z))
    exact h1.comp_ofReal.norm_sq
  have hmono : MonotoneOn f (Icc t₀ 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t₀ 1) ?_
      (fun τ _ => (hderiv τ).hasDerivWithinAt) ?_
    · exact fun τ _ => (hderiv τ).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      have hτ0 : 0 < τ := ht₀.trans hτ.1
      set w := (τ : ℂ) * z with hw
      have hwn : ‖w‖ = τ * ‖z‖ := by
        rw [hw, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0]
      have hw1 : 1 / 2 ≤ ‖w‖ := by
        rw [hwn]; nlinarith [hτ.1, norm_nonneg z]
      have hw2 : ‖w‖ ≤ 2 := by
        rw [hwn]; nlinarith [hτ.2, norm_nonneg z]
      have hpos := re_polyQ_deriv_pos hq hs0 hs hw1 hw2 hn
      rw [Complex.inner]
      have : (dpolyQ n q w * z * (starRingEnd ℂ) (polyQ n q w)).re =
          τ⁻¹ * (w * dpolyQ n q w * (starRingEnd ℂ) (polyQ n q w)).re := by
        rw [← Complex.re_ofReal_mul]
        congr 1
        have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ0.ne'
        rw [hw]; push_cast; field_simp
      rw [this]
      have : 0 < τ⁻¹ := inv_pos.2 hτ0
      positivity
  have := hmono ⟨le_rfl, ht₁⟩ ⟨ht₁, le_rfl⟩ ht₁
  simp only [hf, Complex.ofReal_one, one_mul] at this
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

/-- **`Q⁻¹(𝔻)` is star-shaped** with respect to `0`. -/
theorem starConvex_preimage (hq : ∀ k, ‖q k‖ ≤ s) (hs0 : 0 ≤ s)
    (hs : 3 * n * s * 16 ^ n < 1) (hn : 1 ≤ n) :
    StarConvex ℝ 0 (polyQ n q ⁻¹' ball 0 1) := by
  have hns : (n : ℝ) * s < 1 / 3 := by
    have h16 : (1 : ℝ) ≤ 16 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  intro y hy a b ha hb hab
  rw [smul_zero, zero_add, Complex.real_smul, mem_preimage, mem_ball_zero_iff]
  have hy' : ‖polyQ n q y‖ < 1 := mem_ball_zero_iff.1 hy
  have hy2 : ‖y‖ ≤ 2 := by
    have := preimage_subset_ball hn hq (R := 2) (by linarith) hs0 hy
    exact (mem_ball_zero_iff.1 this).le
  have hb1 : b ≤ 1 := by linarith
  have hbyn : ‖(b : ℂ) * y‖ = b * ‖y‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb]
  rcases le_or_gt (b * ‖y‖) (1 / 2) with hsmall | hlarge
  · have hle1 : ‖(b : ℂ) * y‖ ≤ 1 := by rw [hbyn]; linarith
    calc ‖polyQ n q ((b : ℂ) * y)‖ ≤ ‖(b : ℂ) * y‖ ^ n + n * s := norm_polyQ_le hq hle1
      _ ≤ ‖(b : ℂ) * y‖ ^ 1 + n * s :=
          add_le_add_left (pow_le_pow_of_le_one (norm_nonneg _) hle1 hn) _
      _ < 1 := by rw [pow_one, hbyn]; linarith
  · have hb0 : 0 < b := by
      by_contra h; push_neg at h
      have : b = 0 := le_antisymm h hb
      rw [this, zero_mul] at hlarge; linarith
    exact (norm_polyQ_radial_le hq hs0 hs hn hy2 hb0 hb1 hlarge.le).trans_lt hy'

/-- **The lemniscate domain.** For small coefficients, `V = Q⁻¹(𝔻)` is open, bounded,
star-shaped with respect to `0`, contains `0`, and equals the connected component of `Q⁻¹(𝔻)`
containing `0`. -/
theorem nearDisk_preimage (hq : ∀ k, ‖q k‖ ≤ s) (hs0 : 0 ≤ s)
    (hs : 3 * n * s * 16 ^ n < 1) (hn : 1 ≤ n) :
    IsOpen (polyQ n q ⁻¹' ball 0 1) ∧ StarConvex ℝ 0 (polyQ n q ⁻¹' ball 0 1) ∧
      (0 : ℂ) ∈ polyQ n q ⁻¹' ball 0 1 ∧ polyQ n q ⁻¹' ball 0 1 ⊆ ball 0 2 ∧
      connectedComponentIn (polyQ n q ⁻¹' ball 0 1) 0 = polyQ n q ⁻¹' ball 0 1 := by
  have hns : (n : ℝ) * s < 1 / 3 := by
    have h16 : (1 : ℝ) ≤ 16 ^ n := one_le_pow₀ (by norm_num)
    nlinarith
  have hstar := starConvex_preimage hq hs0 hs hn
  have h0 : (0 : ℂ) ∈ polyQ n q ⁻¹' ball 0 1 := by
    rw [mem_preimage, mem_ball_zero_iff]
    have := norm_polyQ_le hq (z := 0) (by simp)
    rw [norm_zero, zero_pow (by omega), zero_add] at this
    linarith
  refine ⟨isOpen_ball.preimage (polyQ_continuous n q), hstar, h0,
    preimage_subset_ball hn hq (by linarith) hs0, ?_⟩
  exact (hstar.isPathConnected h0).isConnected.isPreconnected.connectedComponentIn h0

end SteklovCoalescence
