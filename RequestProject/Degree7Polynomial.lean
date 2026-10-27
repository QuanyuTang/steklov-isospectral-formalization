module

public import Mathlib

/-!
# A candidate degree-seven polynomial pair: algebraic certificates

**Status: candidate data only.**  This file verifies the *algebraic* properties of the explicit
polynomials suggested for Lemma 3.2.1.  It does **not** prove that their monodromy is the
point/line action of `GL(3, 𝔽₂)`; matching passports do not certify the monodromy, a common
regular cover, or isospectrality.

Let `s² = -7` (both choices `s = ±i√7` are covered), `c = (7+s)/4`,
`A_c(z) = (z²-1)³(z-c)`, `q_c(z) = 7z² - 6cz - 1`, `b_c = 27(637+87s)/9604`,
`p_c(z) = 1 - A_c(z)/b_c`.  We prove:

* `hasDerivAt_A`: `A_c' = (z²-1)² q_c` (for every `c`);
* `A_divmod`: `A_c = q_c S_c + a(c) z + b(c)` with the stated `a(c)`, `b(c)` (for every `c`);
* `quartic_cc`, `aRem_cc`, `bRem_cc`, `bconst_ne_zero`: `4c⁴ - 21c² + 49 = 0`, `a(c) = 0`,
  `b(c) = b_c ≠ 0` when `s² = -7`;
* `deriv_pfun_eq_zero_iff`, `pfun_critical_values`: the critical points of `p_c` are `±1` and the
  two roots of `q_c`; the critical values are exactly `1` (at `±1`) and `0` (at the roots of `q_c`);
* `one_sub_pfun`, `cc_ne_one`, `cc_ne_neg_one`: `1 - p_c = (z-1)³(z+1)³(z-c)/b_c` with `c ≠ ±1`
  (so `p_c` has the local degrees `3, 3, 1` over `1`);
* `q_roots_simple`: the roots of `q_c` are simple, distinct from `±1`, and simple zeros of `p_c'`
  (so they are double points of `p_c` over `0`; by degree count the fibre over `0` has local degrees
  `2, 2, 1, 1, 1`);
* `exists_monic_normalization`: there is `a ≠ 0` with `a⁷ = -b_c` such that `P(z) = p_c(az)` is
  given by a monic polynomial of degree `7`, with all critical values in `{0, 1}`;
* `cc_plus_ne_cc_minus`: the two choices `c₊ = (7+s)/4`, `c₋ = (7-s)/4` are neither equal nor
  negatives of each other;
* `not_affine_equivalent`: there is no affine `z ↦ αz + β` (`α ≠ 0`) with
  `p_{c₋}(αz + β) = p_{c₊}(z)` (such a map must send the triple points `±1` over `1` to `±1`,
  hence be `z ↦ ±z`, and then `c₋ = ±c₊`).  Post-composition with the swap `w ↦ 1 - w` is not
  considered (it would exchange the passports `(3,3,1)` and `(2,2,1,1,1)`).
-/

@[expose] public section

open Polynomial

noncomputable section

namespace Degree7

/-- `c = (7 + s)/4`. -/
def cc (s : ℂ) : ℂ := (7 + s) / 4

/-- `A_c(z) = (z² - 1)³ (z - c)`. -/
def Apoly (c z : ℂ) : ℂ := (z ^ 2 - 1) ^ 3 * (z - c)

/-- `q_c(z) = 7z² - 6cz - 1`. -/
def qpoly (c z : ℂ) : ℂ := 7 * z ^ 2 - 6 * c * z - 1

/-- `b_c = 27(637 + 87 s)/9604`. -/
def bconst (s : ℂ) : ℂ := 27 * (637 + 87 * s) / 9604

/-- `p_c(z) = 1 - A_c(z)/b_c`. -/
def pfun (s z : ℂ) : ℂ := 1 - Apoly (cc s) z / bconst s

/-- `a(c) = -216 (9c² + 7)(4c⁴ - 21c² + 49)/117649`. -/
def aRem (c : ℂ) : ℂ := -216 * (9 * c ^ 2 + 7) * (4 * c ^ 4 - 21 * c ^ 2 + 49) / 117649

/-- `b(c) = c (105840 + 6048c² - 1296c⁴)/117649`. -/
def bRem (c : ℂ) : ℂ := c * (105840 + 6048 * c ^ 2 - 1296 * c ^ 4) / 117649

/-- The quotient of `A_c` by `q_c`. -/
def Squot (c z : ℂ) : ℂ :=
  (1 / 7) * z ^ 5 + (-1 / 49) * c * z ^ 4 + (-20 / 49 - 6 / 343 * c ^ 2) * z ^ 3 +
    (26 / 343 * c - 36 / 2401 * c ^ 3) * z ^ 2 +
    (127 / 343 + 150 / 2401 * c ^ 2 - 216 / 16807 * c ^ 4) * z +
    (-241 / 2401 * c + 864 / 16807 * c ^ 3 - 1296 / 117649 * c ^ 5)

/-- `A_c' = (z² - 1)² q_c`. -/
theorem hasDerivAt_A (c z : ℂ) : HasDerivAt (Apoly c) ((z ^ 2 - 1) ^ 2 * qpoly c z) z := by
  have h1 : HasDerivAt (fun w : ℂ => (w ^ 2 - 1) ^ 3) (3 * (z ^ 2 - 1) ^ 2 * (2 * z)) z := by
    have := ((hasDerivAt_pow 2 z).sub_const (1 : ℂ)).pow 3
    convert! this using 1; push_cast; ring
  have := h1.mul ((hasDerivAt_id z).sub_const c)
  show HasDerivAt (fun w => (w ^ 2 - 1) ^ 3 * (w - c)) _ z
  convert! this using 1
  simp only [qpoly, id]; ring

/-- **Division certificate**: `A_c = q_c S_c + a(c) z + b(c)`. -/
theorem A_divmod (c z : ℂ) : Apoly c z = qpoly c z * Squot c z + aRem c * z + bRem c := by
  unfold Apoly qpoly Squot aRem bRem
  ring

variable {s : ℂ}

theorem quartic_cc (hs : s ^ 2 = -7) : 4 * cc s ^ 4 - 21 * cc s ^ 2 + 49 = 0 := by
  unfold cc
  linear_combination ((s ^ 2 + 28 * s + 203) / 64) * hs

theorem aRem_cc (hs : s ^ 2 = -7) : aRem (cc s) = 0 := by
  unfold aRem; rw [quartic_cc hs]; ring

theorem bRem_cc (hs : s ^ 2 = -7) : bRem (cc s) = bconst s := by
  unfold bRem bconst cc
  linear_combination (-2673 / 153664 - 675 / 153664 * s - 405 / 1075648 * s ^ 2 -
    81 / 7529536 * s ^ 3) * hs

theorem bconst_ne_zero (hs : s ^ 2 = -7) : bconst s ≠ 0 := by
  unfold bconst
  intro h
  have : s = -637 / 87 := by linear_combination (9604 / (27 * 87)) * h
  rw [this] at hs
  norm_num at hs

theorem cc_ne_one (hs : s ^ 2 = -7) : cc s ≠ 1 := by
  unfold cc; intro h
  have : s = -3 := by linear_combination 4 * h
  rw [this] at hs; norm_num at hs

theorem cc_ne_neg_one (hs : s ^ 2 = -7) : cc s ≠ -1 := by
  unfold cc; intro h
  have : s = -11 := by linear_combination 4 * h
  rw [this] at hs; norm_num at hs

/-- The derivative of `p_c`. -/
theorem hasDerivAt_pfun (s z : ℂ) :
    HasDerivAt (pfun s) (-((z ^ 2 - 1) ^ 2 * qpoly (cc s) z) / bconst s) z := by
  have := ((hasDerivAt_A (cc s) z).div_const (bconst s)).const_sub 1
  convert! this using 1
  ring

/-- **Critical points** of `p_c`: `±1` and the roots of `q_c`. -/
theorem deriv_pfun_eq_zero_iff (hs : s ^ 2 = -7) (z : ℂ) :
    deriv (pfun s) z = 0 ↔ z = 1 ∨ z = -1 ∨ qpoly (cc s) z = 0 := by
  rw [(hasDerivAt_pfun s z).deriv, neg_div, neg_eq_zero, div_eq_zero_iff,
    or_iff_left (bconst_ne_zero hs), mul_eq_zero, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
  constructor
  · rintro (h | h)
    · have : (z - 1) * (z + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h1 | h1
      · exact Or.inl (sub_eq_zero.1 h1)
      · exact Or.inr (Or.inl (eq_neg_of_add_eq_zero_left h1))
    · exact Or.inr (Or.inr h)
  · rintro (rfl | rfl | h)
    · left; norm_num
    · left; norm_num
    · right; exact h

/-- **Critical values**: `p_c(±1) = 1` and `p_c = 0` at the roots of `q_c`. -/
theorem pfun_critical_values (hs : s ^ 2 = -7) :
    pfun s 1 = 1 ∧ pfun s (-1) = 1 ∧ ∀ z, qpoly (cc s) z = 0 → pfun s z = 0 := by
  refine ⟨by simp [pfun, Apoly], by simp [pfun, Apoly], fun z hz => ?_⟩
  rw [pfun, A_divmod, hz, aRem_cc hs, bRem_cc hs, zero_mul, zero_mul, zero_add, zero_add,
    div_self (bconst_ne_zero hs), sub_self]

/-- Every critical value of `p_c` is `0` or `1`. -/
theorem pfun_critical_value_mem (hs : s ^ 2 = -7) {z : ℂ} (hz : deriv (pfun s) z = 0) :
    pfun s z = 0 ∨ pfun s z = 1 := by
  obtain ⟨h1, h2, h3⟩ := pfun_critical_values hs
  rcases (deriv_pfun_eq_zero_iff hs z).1 hz with rfl | rfl | h
  · exact Or.inr h1
  · exact Or.inr h2
  · exact Or.inl (h3 z h)

/-- The fibre over `1`: `1 - p_c(z) = (z-1)³ (z+1)³ (z-c) / b_c`. -/
theorem one_sub_pfun (s z : ℂ) :
    1 - pfun s z = (z - 1) ^ 3 * (z + 1) ^ 3 * (z - cc s) / bconst s := by
  unfold pfun Apoly; ring

/-- The roots of `q_c` are simple, differ from `±1`, and are simple zeros of `p_c'`
(`q_c'(z) = 14z - 6c ≠ 0`). -/
theorem q_roots_simple (hs : s ^ 2 = -7) {z : ℂ} (hz : qpoly (cc s) z = 0) :
    z ≠ 1 ∧ z ≠ -1 ∧ 14 * z - 6 * cc s ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · rintro rfl
    apply cc_ne_one hs
    unfold qpoly at hz; linear_combination -hz / 6
  · rintro rfl
    apply cc_ne_neg_one hs
    unfold qpoly at hz; linear_combination hz / 6
  · intro h
    have hz' : z = 3 * cc s / 7 := by linear_combination h / 14
    rw [hz'] at hz
    unfold qpoly at hz
    -- then `9c² = -7`, i.e. the discriminant `36c² + 28` vanishes
    have hc : 9 * cc s ^ 2 = -7 := by linear_combination -7 * hz
    unfold cc at hc
    have : s = -35 / 9 := by linear_combination (16 / 126) * hc - (1 / 14) * hs
    rw [this] at hs; norm_num at hs

/-- The discriminant of `q_c` is nonzero: `q_c` has two distinct roots. -/
theorem q_disc_ne_zero (hs : s ^ 2 = -7) : 36 * cc s ^ 2 + 28 ≠ 0 := by
  unfold cc; intro h
  have : s = -35 / 9 := by linear_combination (4 / 126) * h - (1 / 14) * hs
  rw [this] at hs; norm_num at hs

/-- The monic normalization `P(z) = p_c(a z)` written as an explicit polynomial. -/
def monicP (s a : ℂ) : ℂ[X] :=
  X ^ 7 + (C (cc s * a ^ 6 / bconst s) * X ^ 6 + C (3 * a ^ 5 / bconst s) * X ^ 5 +
    C (-(3 * cc s * a ^ 4) / bconst s) * X ^ 4 + C (-(3 * a ^ 3) / bconst s) * X ^ 3 +
    C (3 * cc s * a ^ 2 / bconst s) * X ^ 2 + C (a / bconst s) * X + C (1 - cc s / bconst s))

theorem monicP_monic (s a : ℂ) : (monicP s a).Monic := by
  apply Monic.add_of_left (monic_X_pow 7)
  rw [degree_X_pow]
  refine lt_of_le_of_lt (b := ((6 : ℕ) : WithBot ℕ)) ?_ (by exact_mod_cast (by norm_num : 6 < 7))
  compute_degree!

theorem monicP_natDegree (s a : ℂ) : (monicP s a).natDegree = 7 := by
  unfold monicP; compute_degree!

theorem monicP_eval (hs : s ^ 2 = -7) {a : ℂ} (ha : a ^ 7 = -bconst s) (z : ℂ) :
    (monicP s a).eval z = pfun s (a * z) := by
  have hb := bconst_ne_zero hs
  simp only [monicP, eval_add, eval_pow, eval_X, eval_mul, eval_C, pfun, Apoly]
  field_simp
  linear_combination z ^ 7 * ha

/-- **Monic normalization**: there is `a ≠ 0` with `a⁷ = -b_c` such that `P = p_c(a ·)` is a monic
polynomial of degree `7` whose critical values all lie in `{0, 1}`. -/
theorem exists_monic_normalization (hs : s ^ 2 = -7) :
    ∃ a : ℂ, a ≠ 0 ∧ a ^ 7 = -bconst s ∧ (monicP s a).Monic ∧ (monicP s a).natDegree = 7 ∧
      (∀ z, (monicP s a).eval z = pfun s (a * z)) ∧
      ∀ z, deriv (fun w => (monicP s a).eval w) z = 0 →
        (monicP s a).eval z = 0 ∨ (monicP s a).eval z = 1 := by
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (-bconst s) (by norm_num : 0 < 7)
  have hb := bconst_ne_zero hs
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [zero_pow (by norm_num)] at ha; exact hb (neg_eq_zero.1 ha.symm)
  refine ⟨a, ha0, ha, monicP_monic s a, monicP_natDegree s a, monicP_eval hs ha, fun z hz => ?_⟩
  have hfun : (fun w => (monicP s a).eval w) = fun w => pfun s (a * w) := by
    ext w; exact monicP_eval hs ha w
  rw [hfun] at hz
  have hd : HasDerivAt (fun w => pfun s (a * w))
      (-(((a * z) ^ 2 - 1) ^ 2 * qpoly (cc s) (a * z)) / bconst s * a) z :=
    (hasDerivAt_pfun s (a * z)).comp z (by simpa using (hasDerivAt_id z).const_mul a)
  rw [hd.deriv] at hz
  have hz' : deriv (pfun s) (a * z) = 0 := by
    rw [(hasDerivAt_pfun s (a * z)).deriv]
    exact (mul_eq_zero.1 hz).resolve_right ha0
  rw [monicP_eval hs ha]
  exact pfun_critical_value_mem hs hz'

/-- The two choices `c₊ = (7+s)/4`, `c₋ = (7-s)/4` are neither equal nor negatives. -/
theorem cc_plus_ne_cc_minus (hs : s ^ 2 = -7) : cc s ≠ cc (-s) ∧ cc s ≠ -cc (-s) := by
  unfold cc
  constructor
  · intro h
    have : s = 0 := by linear_combination 2 * h
    rw [this] at hs; norm_num at hs
  · intro h
    have : (14 : ℂ) = 0 := by linear_combination 4 * h
    norm_num at this

lemma Apoly_eq_zero_iff (c w : ℂ) : Apoly c w = 0 ↔ w = 1 ∨ w = -1 ∨ w = c := by
  unfold Apoly
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · have h := pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h
      have : (w - 1) * (w + 1) = 0 := by linear_combination h
      rcases mul_eq_zero.1 this with h | h
      · exact Or.inl (sub_eq_zero.1 h)
      · exact Or.inr (Or.inl (eq_neg_of_add_eq_zero_left h))
    · exact Or.inr (Or.inr (sub_eq_zero.1 h))
  · rintro (rfl | rfl | rfl) <;> ring

/-- **The two candidates are affinely inequivalent**: there is no affine change of variable
`z ↦ αz + β` with `p_{c₋}(αz + β) = p_{c₊}(z)`. -/
theorem not_affine_equivalent (hs : s ^ 2 = -7) :
    ¬ ∃ α β : ℂ, α ≠ 0 ∧ ∀ z, pfun (-s) (α * z + β) = pfun s z := by
  rintro ⟨α, β, hα, h⟩
  have hs' : (-s) ^ 2 = -7 := by rw [neg_sq]; exact hs
  set c := cc s
  set c' := cc (-s)
  have hb := bconst_ne_zero hs
  have hb' := bconst_ne_zero hs'
  set k := bconst (-s) / bconst s with hk
  have hA : ∀ z, Apoly c' (α * z + β) = k * Apoly c z := by
    intro z
    have := h z
    unfold pfun at this
    rw [hk]
    field_simp at this ⊢
    linear_combination -this
  have hfun : (fun z => Apoly c' (α * z + β)) = fun z => k * Apoly c z := funext hA
  have hd : ∀ z, α * ((α * z + β) ^ 2 - 1) ^ 2 * qpoly c' (α * z + β) =
      k * ((z ^ 2 - 1) ^ 2 * qpoly c z) := by
    intro z
    have h1 : HasDerivAt (fun z => Apoly c' (α * z + β))
        (((α * z + β) ^ 2 - 1) ^ 2 * qpoly c' (α * z + β) * α) z := by
      have := (hasDerivAt_A c' (α * z + β)).comp z
        (((hasDerivAt_id z).const_mul α).add_const β)
      convert! this using 1 <;> first | rfl | ring1 | simp
    have h2 : HasDerivAt (fun z => k * Apoly c z) (k * ((z ^ 2 - 1) ^ 2 * qpoly c z)) z :=
      (hasDerivAt_A c z).const_mul k
    rw [hfun] at h1
    have := h1.unique h2
    linear_combination this
  -- the images of `±1` are `±1`
  have hpm : ∀ z, (z = 1 ∨ z = -1) → (α * z + β = 1 ∨ α * z + β = -1) := by
    intro z hz
    have h0 : Apoly c' (α * z + β) = 0 := by
      rw [hA]; rcases hz with rfl | rfl <;> simp [Apoly]
    have h0' : α * ((α * z + β) ^ 2 - 1) ^ 2 * qpoly c' (α * z + β) = 0 := by
      rw [hd]; rcases hz with rfl | rfl <;> simp
    rcases (Apoly_eq_zero_iff c' _).1 h0 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rcases mul_eq_zero.1 h0' with h2 | h2
      · rcases mul_eq_zero.1 h2 with h3 | h3
        · exact hα h3
        · have h4 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h3
          have : (α * z + β - 1) * (α * z + β + 1) = 0 := by linear_combination h4
          rcases mul_eq_zero.1 this with h5 | h5
          · exact cc_ne_one hs' (show c' = 1 by linear_combination h5 - h)
          · exact cc_ne_neg_one hs' (show c' = -1 by linear_combination h5 - h)
      · rw [h] at h2
        unfold qpoly at h2
        have : (c' - 1) * (c' + 1) = 0 := by linear_combination h2
        rcases mul_eq_zero.1 this with h5 | h5
        · exact cc_ne_one hs' (sub_eq_zero.1 h5)
        · exact cc_ne_neg_one hs' (eq_neg_of_add_eq_zero_left h5)
  have hβ : β = 0 ∧ (α = 1 ∨ α = -1) := by
    rcases hpm 1 (Or.inl rfl) with h1 | h1 <;> rcases hpm (-1) (Or.inr rfl) with h2 | h2
    · exfalso; apply hα; linear_combination (h1 - h2) / 2
    · exact ⟨by linear_combination (h1 + h2) / 2, Or.inl (by linear_combination (h1 - h2) / 2)⟩
    · exact ⟨by linear_combination (h1 + h2) / 2, Or.inr (by linear_combination (h1 - h2) / 2)⟩
    · exfalso; apply hα; linear_combination (h1 - h2) / 2
  obtain ⟨rfl, hα1⟩ := hβ
  have h0 : Apoly c' (α * c) = 0 := by
    have := hA c; rw [add_zero] at this; rw [this]; simp [Apoly]
  have hne := cc_plus_ne_cc_minus hs
  rcases (Apoly_eq_zero_iff c' _).1 h0 with h | h | h <;> rcases hα1 with rfl | rfl
  · exact cc_ne_one hs (by linear_combination h)
  · exact cc_ne_neg_one hs (by linear_combination -h)
  · exact cc_ne_neg_one hs (by linear_combination h)
  · exact cc_ne_one hs (by linear_combination -h)
  · exact hne.1 (by linear_combination h)
  · exact hne.2 (by linear_combination -h)

/-- The concrete choices `s = ±i√7` satisfy `s² = -7`. -/
theorem i_sqrt7_sq : (Complex.I * (Real.sqrt 7 : ℂ)) ^ 2 = -7 ∧
    (-(Complex.I * (Real.sqrt 7 : ℂ))) ^ 2 = -7 := by
  have h : ((Real.sqrt 7 : ℝ) : ℂ) ^ 2 = 7 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  constructor
  · rw [mul_pow, Complex.I_sq, h]; ring
  · rw [neg_sq, mul_pow, Complex.I_sq, h]; ring

end Degree7
