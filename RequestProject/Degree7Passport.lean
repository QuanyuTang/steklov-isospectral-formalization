module

public import RequestProject.Degree7Polynomial

/-!
# Exact ramification passports of the degree-seven candidates

For `s² = -7` let `p_s = 1 - A_c/b_s` (`Degree7.pfun`), now packaged as a genuine polynomial
`Degree7.pPoly s : ℂ[X]`.  We prove the *exact* passports, with the degree count included and
no nondegeneracy assumption beyond `s² = -7`:

* `passport_zero`: the multiset of local degrees (root multiplicities) of `p_s` over the value `0`
  is exactly `{2, 2, 1, 1, 1}`; in particular the fibre over `0` has exactly `5` points;
* `passport_one`: the multiset of local degrees of `p_s` over `1` is exactly `{3, 3, 1}`
  (the fibre is `{1, -1, c}`);
* `passport_infinity`: `p_s` has degree `7` (nonzero leading coefficient `-1/b_s`), so the
  local degree at `∞` is `7`;
* `card_fibre_regular`: every value `w ∉ {0,1}` has exactly `7` distinct preimages, all of them
  simple (the derivative does not vanish there).

The degree count (sum of local degrees `= 7` over every value) is `card_roots_sub`.
-/

@[expose] public section

open Polynomial

noncomputable section

namespace Degree7

/-- `(z-1)³ (z+1)³ (z-c)` as a polynomial. -/
def onePoly (c : ℂ) : ℂ[X] := (X - C 1) ^ 3 * (X - C (-1)) ^ 3 * (X - C c)

/-- `p_s` as a polynomial: `p_s = 1 - b_s⁻¹ (z-1)³(z+1)³(z-c)`. -/
def pPoly (s : ℂ) : ℂ[X] := 1 - C (bconst s)⁻¹ * onePoly (cc s)

/-- `q_c` as a polynomial. -/
def qPoly (c : ℂ) : ℂ[X] := C 7 * X ^ 2 - C (6 * c) * X - 1

variable {s : ℂ}

theorem pPoly_eval (s z : ℂ) : (pPoly s).eval z = pfun s z := by
  simp only [pPoly, onePoly, eval_sub, eval_one, eval_mul, eval_C, eval_pow, eval_X, pfun, Apoly]
  ring

theorem qPoly_eval (c z : ℂ) : (qPoly c).eval z = qpoly c z := by
  simp [qPoly, qpoly]

theorem onePoly_natDegree (c : ℂ) : (onePoly c).natDegree = 7 := by
  unfold onePoly
  compute_degree!

theorem onePoly_monic (c : ℂ) : (onePoly c).Monic := by
  unfold onePoly
  exact (((monic_X_sub_C _).pow _).mul ((monic_X_sub_C _).pow _)).mul (monic_X_sub_C _)

theorem pPoly_natDegree (hs : s ^ 2 = -7) : (pPoly s).natDegree = 7 := by
  have hb := inv_ne_zero (bconst_ne_zero hs)
  unfold pPoly
  rw [sub_eq_add_neg, ← neg_mul, ← C_neg, add_comm, natDegree_add_eq_left_of_natDegree_lt]
  · rw [natDegree_C_mul (neg_ne_zero.2 hb), onePoly_natDegree]
  · rw [natDegree_C_mul (neg_ne_zero.2 hb), onePoly_natDegree]; simp

theorem pPoly_leadingCoeff (hs : s ^ 2 = -7) : (pPoly s).leadingCoeff = -(bconst s)⁻¹ := by
  have hb := inv_ne_zero (bconst_ne_zero hs)
  unfold pPoly
  have hdeg : degree (1 : ℂ[X]) < degree (C (-(bconst s)⁻¹) * onePoly (cc s)) := by
    rw [degree_C_mul (neg_ne_zero.2 hb), degree_eq_natDegree (onePoly_monic _).ne_zero,
      onePoly_natDegree]
    simp
  rw [sub_eq_add_neg, ← neg_mul, ← C_neg, leadingCoeff_add_of_degree_lt hdeg,
    leadingCoeff_C_mul_of_isUnit (isUnit_iff_ne_zero.2 (neg_ne_zero.2 hb)),
    (onePoly_monic _).leadingCoeff, mul_one]

theorem pPoly_ne_zero (hs : s ^ 2 = -7) : pPoly s ≠ 0 := by
  intro h; have := pPoly_natDegree hs; rw [h] at this; simp at this

/-- **Local degree at infinity**: `p_s` has degree `7` and leading coefficient `-1/b_s ≠ 0`. -/
theorem passport_infinity (hs : s ^ 2 = -7) :
    (pPoly s).natDegree = 7 ∧ (pPoly s).leadingCoeff = -(bconst s)⁻¹ ∧ -(bconst s)⁻¹ ≠ 0 :=
  ⟨pPoly_natDegree hs, pPoly_leadingCoeff hs, neg_ne_zero.2 (inv_ne_zero (bconst_ne_zero hs))⟩

theorem derivative_pPoly_eval (s z : ℂ) :
    (derivative (pPoly s)).eval z = -((z ^ 2 - 1) ^ 2 * qpoly (cc s) z) / bconst s := by
  have h1 := Polynomial.hasDerivAt (pPoly s) z
  have h2 := hasDerivAt_pfun s z
  have hf : (fun x => (pPoly s).eval x) = pfun s := funext (pPoly_eval s)
  rw [hf] at h1
  exact h1.unique h2

/-- `p_s' = -b_s⁻¹ (z-1)² (z+1)² q_c`. -/
theorem derivative_pPoly (s : ℂ) :
    derivative (pPoly s) =
      C (-(bconst s)⁻¹) * ((X - C 1) ^ 2 * (X - C (-1)) ^ 2 * qPoly (cc s)) := by
  apply Polynomial.funext
  intro z
  rw [derivative_pPoly_eval]
  simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, qPoly_eval]
  ring

theorem qPoly_ne_zero (c : ℂ) : qPoly c ≠ 0 := by
  intro h
  have := congrArg (fun p => p.coeff 2) h
  simp [qPoly, coeff_one] at this

theorem qPoly_natDegree (c : ℂ) : (qPoly c).natDegree = 2 := by
  unfold qPoly; compute_degree!

/-- The roots of `q_c` are simple. -/
theorem qPoly_rootMultiplicity (hs : s ^ 2 = -7) (z : ℂ) :
    (qPoly (cc s)).rootMultiplicity z = if (qPoly (cc s)).IsRoot z then 1 else 0 := by
  split_ifs with h
  · apply le_antisymm
    · by_contra hlt
      push_neg at hlt
      have := (one_lt_rootMultiplicity_iff_isRoot (qPoly_ne_zero _)).1 hlt
      have hd : (derivative (qPoly (cc s))).eval z = 14 * z - 6 * cc s := by
        simp [qPoly]; ring
      have h2 : (derivative (qPoly (cc s))).eval z = 0 := this.2
      rw [hd] at h2
      exact (q_roots_simple hs (by rw [← qPoly_eval]; exact h)).2.2 h2
    · exact (rootMultiplicity_pos (qPoly_ne_zero _)).2 h
  · exact rootMultiplicity_eq_zero h

theorem qPoly_roots_nodup (hs : s ^ 2 = -7) : (qPoly (cc s)).roots.Nodup := by
  classical
  rw [Multiset.nodup_iff_count_le_one]
  intro z
  rw [count_roots, qPoly_rootMultiplicity hs]
  split_ifs <;> norm_num

theorem qPoly_roots_card (s : ℂ) : (qPoly (cc s)).roots.card = 2 := by
  rw [IsAlgClosed.card_roots_eq_natDegree, qPoly_natDegree]

/-- At a zero of `p_s` the multiplicity is `1 + [q_c(z) = 0]`. -/
theorem pPoly_rootMultiplicity (hs : s ^ 2 = -7) {z : ℂ} (hz : (pPoly s).IsRoot z) :
    (pPoly s).rootMultiplicity z = if (qPoly (cc s)).IsRoot z then 2 else 1 := by
  have hb := neg_ne_zero.2 (inv_ne_zero (bconst_ne_zero hs))
  have hpos : 0 < (pPoly s).rootMultiplicity z := (rootMultiplicity_pos (pPoly_ne_zero hs)).2 hz
  have hd := derivative_rootMultiplicity_of_root hz
  have hz1 : z ≠ 1 := by
    rintro rfl; have := hz; simp [IsRoot, pPoly_eval, (pfun_critical_values hs).1] at this
  have hz2 : z ≠ -1 := by
    rintro rfl; have := hz; simp [IsRoot, pPoly_eval, (pfun_critical_values hs).2.1] at this
  have hm : (derivative (pPoly s)).rootMultiplicity z = (qPoly (cc s)).rootMultiplicity z := by
    rw [derivative_pPoly, rootMultiplicity_mul, rootMultiplicity_C, zero_add,
      rootMultiplicity_mul, rootMultiplicity_mul, rootMultiplicity_eq_zero, rootMultiplicity_eq_zero]
    · simp
    · simp only [IsRoot.def, eval_pow, eval_sub, eval_X, eval_C]
      intro h; apply hz2
      have := (pow_eq_zero_iff two_ne_zero).1 h
      linear_combination this
    · simp only [IsRoot.def, eval_pow, eval_sub, eval_X, eval_C]
      intro h; apply hz1
      have := (pow_eq_zero_iff two_ne_zero).1 h
      linear_combination this
    · exact mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) (pow_ne_zero _ (X_sub_C_ne_zero _))
    · exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _))
        (pow_ne_zero _ (X_sub_C_ne_zero _))) (qPoly_ne_zero _)
    · exact mul_ne_zero (C_ne_zero.2 hb) (mul_ne_zero (mul_ne_zero
        (pow_ne_zero _ (X_sub_C_ne_zero _)) (pow_ne_zero _ (X_sub_C_ne_zero _))) (qPoly_ne_zero _))
  rw [hm, qPoly_rootMultiplicity hs] at hd
  split_ifs at hd ⊢ <;> omega

/-- Roots of `q_c` are roots of `p_s` (critical value `0`). -/
theorem pPoly_isRoot_of_qPoly (hs : s ^ 2 = -7) {z : ℂ} (hz : (qPoly (cc s)).IsRoot z) :
    (pPoly s).IsRoot z := by
  simp only [IsRoot, pPoly_eval]
  exact (pfun_critical_values hs).2.2 z (by rw [← qPoly_eval]; exact hz)

/-- **Degree count**: for every value `w`, the local degrees of `p_s` over `w` add up to `7`. -/
theorem card_roots_sub (hs : s ^ 2 = -7) (w : ℂ) : (pPoly s - C w).roots.card = 7 := by
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_sub_C, pPoly_natDegree hs]

/-- **Passport over `0`**: the multiset of local degrees of `p_s` over `0` is `{2,2,1,1,1}`. -/
theorem passport_zero (hs : s ^ 2 = -7) :
    (pPoly s).roots.toFinset.val.map (fun z => (pPoly s).rootMultiplicity z) = {2, 2, 1, 1, 1} := by
  classical
  set p := pPoly s
  set T := p.roots.toFinset
  set R := (qPoly (cc s)).roots.toFinset
  have hR : R.card = 2 := by
    rw [Multiset.toFinset_card_of_nodup (qPoly_roots_nodup hs), qPoly_roots_card]
  have hRT : R ⊆ T := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots (qPoly_ne_zero _)] at hz
    rw [Multiset.mem_toFinset, mem_roots (pPoly_ne_zero hs)]
    exact pPoly_isRoot_of_qPoly hs hz
  have hmult : ∀ z ∈ T, p.rootMultiplicity z = if z ∈ R then 2 else 1 := by
    intro z hz
    rw [Multiset.mem_toFinset, mem_roots (pPoly_ne_zero hs)] at hz
    have hiff : z ∈ R ↔ (qPoly (cc s)).IsRoot z := by
      simp [R, mem_roots (qPoly_ne_zero _)]
    rw [pPoly_rootMultiplicity hs hz]
    split_ifs <;> tauto
  -- the degree count
  have hsum : ∑ z ∈ T, p.rootMultiplicity z = 7 := by
    have := Multiset.toFinset_sum_count_eq p.roots
    simp only [count_roots] at this
    rw [this, IsAlgClosed.card_roots_eq_natDegree, pPoly_natDegree hs]
  have hsum2 : ∑ z ∈ T, p.rootMultiplicity z = 2 * R.card + (T \ R).card := by
    rw [← Finset.sum_sdiff hRT]
    have e1 : ∑ z ∈ T \ R, p.rootMultiplicity z = ∑ z ∈ T \ R, 1 :=
      Finset.sum_congr rfl (fun z hz => by
        rw [Finset.mem_sdiff] at hz; rw [hmult z hz.1, if_neg hz.2])
    have e2 : ∑ z ∈ R, p.rootMultiplicity z = ∑ z ∈ R, 2 :=
      Finset.sum_congr rfl (fun z hz => by rw [hmult z (hRT hz), if_pos hz])
    rw [e1, e2]
    simp [mul_comm]; ring
  have hTR : (T \ R).card = 3 := by omega
  have hmap : T.val.map (fun z => p.rootMultiplicity z) =
      (T.val.filter (· ∈ R)).map (fun _ => 2) + (T.val.filter (· ∉ R)).map (fun _ => 1) := by
    conv_lhs => rw [← Multiset.filter_add_not (· ∈ R) T.val]
    rw [Multiset.map_add]
    congr 1
    · exact Multiset.map_congr rfl fun z hz => by
        rw [Multiset.mem_filter] at hz; rw [hmult z hz.1, if_pos hz.2]
    · exact Multiset.map_congr rfl fun z hz => by
        rw [Multiset.mem_filter] at hz; rw [hmult z hz.1, if_neg hz.2]
  have hf1 : (T.val.filter (· ∈ R)).card = 2 := by
    rw [← Finset.filter_val, Finset.card_val, Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.2 hRT, hR]
  have hf2 : (T.val.filter (· ∉ R)).card = 3 := by
    rw [← Finset.filter_val, Finset.card_val, Finset.filter_notMem_eq_sdiff, hTR]
  rw [hmap, Multiset.map_const', Multiset.map_const', hf1, hf2]
  rfl

/-- **Passport over `1`**: the multiset of local degrees of `p_s` over `1` is `{3,3,1}`;
the fibre over `1` is `{1, -1, c}`. -/
theorem passport_one (hs : s ^ 2 = -7) :
    (pPoly s - C 1).roots.toFinset.val.map (fun z => (pPoly s - C 1).rootMultiplicity z) =
      {3, 3, 1} := by
  classical
  have hb := neg_ne_zero.2 (inv_ne_zero (bconst_ne_zero hs))
  have heq : pPoly s - C 1 = C (-(bconst s)⁻¹) * onePoly (cc s) := by
    unfold pPoly; simp only [C_neg, map_one]; ring
  have hroots : (pPoly s - C 1).roots =
      3 • ({1} : Multiset ℂ) + 3 • ({-1} : Multiset ℂ) + {cc s} := by
    have h1 : ((X - C (1 : ℂ)) ^ 3 * (X - C (-1)) ^ 3) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (X_sub_C_ne_zero _)) (pow_ne_zero _ (X_sub_C_ne_zero _))
    have h2 : ((X - C (1 : ℂ)) ^ 3 * (X - C (-1)) ^ 3) * (X - C (cc s)) ≠ 0 :=
      mul_ne_zero h1 (X_sub_C_ne_zero _)
    rw [heq, roots_C_mul _ hb, onePoly, roots_mul h2, roots_mul h1, roots_pow, roots_pow,
      roots_X_sub_C, roots_X_sub_C, roots_X_sub_C]
  have h1 := cc_ne_one hs
  have h2 := cc_ne_neg_one hs
  have hT : (pPoly s - C 1).roots.toFinset = {1, -1, cc s} := by
    rw [hroots]; ext z; simp
  simp only [← count_roots, hroots]
  have h3 : (1 : ℂ) ≠ -1 := by norm_num
  simp [Finset.insert_val, Multiset.ndinsert_of_notMem, h1, h2, h3, h1.symm, h2.symm, h3.symm,
    Multiset.count_nsmul, Multiset.count_singleton]

/-- **Regular fibres**: every value `w ∉ {0, 1}` has exactly `7` distinct preimages under `p_s`,
and `p_s'` does not vanish at any of them. -/
theorem card_fibre_regular (hs : s ^ 2 = -7) {w : ℂ} (hw0 : w ≠ 0) (hw1 : w ≠ 1) :
    (pPoly s - C w).roots.Nodup ∧ (pPoly s - C w).roots.toFinset.card = 7 ∧
      ∀ z, pfun s z = w → deriv (pfun s) z ≠ 0 := by
  classical
  have hder : ∀ z, pfun s z = w → deriv (pfun s) z ≠ 0 := by
    intro z hz hd
    rcases pfun_critical_value_mem hs hd with h | h <;> [exact hw0 (hz ▸ h); exact hw1 (hz ▸ h)]
  have hne : pPoly s - C w ≠ 0 := by
    intro h; have := card_roots_sub hs w; rw [h] at this; simp at this
  have hnd : (pPoly s - C w).roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro z
    rw [count_roots]
    by_contra hlt
    push_neg at hlt
    have := (one_lt_rootMultiplicity_iff_isRoot hne).1 hlt
    simp only [IsRoot, eval_sub, eval_C, derivative_sub, derivative_C, sub_zero,
      pPoly_eval, sub_eq_zero] at this
    apply hder z this.1
    rw [(hasDerivAt_pfun s z).deriv, ← derivative_pPoly_eval]
    exact this.2
  exact ⟨hnd, by rw [Multiset.toFinset_card_of_nodup hnd, card_roots_sub hs], hder⟩

end Degree7
