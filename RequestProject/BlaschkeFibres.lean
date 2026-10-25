module

public import RequestProject.Blaschke

/-!
# Fibres of finite Blaschke products

For `B(z) = η ∏ (z - a_l)/(1 - ā_l z)` of degree `n ≥ 1`:
* away from the poles, `B(p) = w` iff `p` is a root of the polynomial
  `η ∏ (X - a_l) - w ∏ (1 - ā_l X)`, which is nonzero of degree `≤ n`; hence every fibre in a
  pole-free set is finite with at most `n` points (`fibre_finite`, `fibre_card_le`);
* `|B(p)| > 1` for `1 < |p|` in the pole-free region, with an explicit lower bound
  (`one_lt_norm_of_one_lt`, `norm_sq_ge`).
-/

@[expose] public section

open Complex Metric Set Polynomial

noncomputable section

namespace SteklovBlaschke

/-- The numerator polynomial of `B - w`. -/
def numPoly {n : ℕ} (η : ℂ) (a : Fin n → ℂ) (w : ℂ) : ℂ[X] :=
  C η * ∏ l, (X - C (a l)) - C w * ∏ l, (1 - C ((starRingEnd ℂ) (a l)) * X)

lemma eval_numPoly {n : ℕ} (η : ℂ) (a : Fin n → ℂ) (w p : ℂ) :
    (numPoly η a w).eval p =
      η * ∏ l, (p - a l) - w * ∏ l, (1 - (starRingEnd ℂ) (a l) * p) := by
  simp [numPoly, eval_prod]

lemma blaschke_eq_iff {n : ℕ} (η : ℂ) (a : Fin n → ℂ) {w p : ℂ}
    (hp : ∀ l, 1 - (starRingEnd ℂ) (a l) * p ≠ 0) :
    η * ∏ l, bfac (a l) p = w ↔ (numPoly η a w).eval p = 0 := by
  rw [eval_numPoly, sub_eq_zero]
  have hD : ∏ l, (1 - (starRingEnd ℂ) (a l) * p) ≠ 0 := Finset.prod_ne_zero_iff.2 fun l _ => hp l
  simp only [bfac]
  rw [Finset.prod_div_distrib, ← mul_div_assoc, div_eq_iff hD]

lemma numPoly_ne_zero {n : ℕ} (hn : 0 < n) {η : ℂ} (hη : η ≠ 0) {a : Fin n → ℂ}
    (ha : ∀ l, ‖a l‖ < 1) (w : ℂ) : numPoly η a w ≠ 0 := by
  intro h0
  by_cases hw : w = 0
  · subst hw
    have : numPoly η a 0 = C η * ∏ l, (X - C (a l)) := by simp [numPoly]
    rw [this] at h0
    have hm : (∏ l, (X - C (a l))).Monic := monic_prod_of_monic _ _ fun l _ => monic_X_sub_C _
    exact mul_ne_zero (C_ne_zero.2 hη) hm.ne_zero h0
  · have he := congrArg (eval (a ⟨0, hn⟩)) h0
    rw [eval_numPoly, eval_zero] at he
    have h1 : ∏ l, (a ⟨0, hn⟩ - a l) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ ⟨0, hn⟩) (sub_self _)
    have h2 : ∏ l, (1 - (starRingEnd ℂ) (a l) * a ⟨0, hn⟩) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun l _ => denom_ne_zero (ha l) (ha _).le
    rw [h1, mul_zero, zero_sub, neg_eq_zero] at he
    exact mul_ne_zero hw h2 he

lemma natDegree_numPoly_le {n : ℕ} (η : ℂ) (a : Fin n → ℂ) (w : ℂ) :
    (numPoly η a w).natDegree ≤ n := by
  unfold numPoly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
    refine (Finset.sum_le_sum fun l _ => natDegree_X_sub_C_le (a l)).trans ?_
    simp
  · refine (natDegree_C_mul_le _ _).trans ((natDegree_prod_le _ _).trans ?_)
    refine (Finset.sum_le_sum fun l _ => ?_).trans (by simp : ∑ _l : Fin n, 1 ≤ n)
    refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
    exact (natDegree_C_mul_le _ _).trans (by simp)

/-- Fibres in a pole-free set lie among the roots of the numerator polynomial. -/
lemma fibre_subset_roots {n : ℕ} (hn : 0 < n) {η : ℂ} (hη : η ≠ 0) {a : Fin n → ℂ}
    (ha : ∀ l, ‖a l‖ < 1) {W : Set ℂ} (hW : ∀ p ∈ W, ∀ l, 1 - (starRingEnd ℂ) (a l) * p ≠ 0)
    (w : ℂ) :
    {p | p ∈ W ∧ η * ∏ l, bfac (a l) p = w} ⊆ ↑(numPoly η a w).roots.toFinset := by
  rintro p ⟨hpW, hp⟩
  rw [Finset.mem_coe, Multiset.mem_toFinset, mem_roots (numPoly_ne_zero hn hη ha w), IsRoot.def]
  exact (blaschke_eq_iff η a (hW p hpW)).1 hp

theorem fibre_finite {n : ℕ} (hn : 0 < n) {η : ℂ} (hη : η ≠ 0) {a : Fin n → ℂ}
    (ha : ∀ l, ‖a l‖ < 1) {W : Set ℂ} (hW : ∀ p ∈ W, ∀ l, 1 - (starRingEnd ℂ) (a l) * p ≠ 0)
    (w : ℂ) : {p | p ∈ W ∧ η * ∏ l, bfac (a l) p = w}.Finite :=
  (Finset.finite_toSet _).subset (fibre_subset_roots hn hη ha hW w)

theorem fibre_card_le {n : ℕ} (hn : 0 < n) {η : ℂ} (hη : η ≠ 0) {a : Fin n → ℂ}
    (ha : ∀ l, ‖a l‖ < 1) {W : Set ℂ} (hW : ∀ p ∈ W, ∀ l, 1 - (starRingEnd ℂ) (a l) * p ≠ 0)
    (w : ℂ) : (fibre_finite hn hη ha hW w).toFinset.card ≤ n := by
  classical
  calc (fibre_finite hn hη ha hW w).toFinset.card ≤ (numPoly η a w).roots.toFinset.card := by
        refine Finset.card_le_card fun p hp => ?_
        rw [Set.Finite.mem_toFinset] at hp
        exact fibre_subset_roots hn hη ha hW w hp
    _ ≤ (numPoly η a w).roots.card := Multiset.toFinset_card_le _
    _ ≤ (numPoly η a w).natDegree := card_roots' _
    _ ≤ n := natDegree_numPoly_le η a w

/-! ### Outside the closed disk -/

lemma norm_bfac_sq_eq {a p : ℂ} (hd : 1 - (starRingEnd ℂ) a * p ≠ 0) :
    ‖bfac a p‖ ^ 2 = 1 + (1 - ‖a‖ ^ 2) * (‖p‖ ^ 2 - 1) / ‖1 - (starRingEnd ℂ) a * p‖ ^ 2 := by
  have h := normSq_denom_sub a p
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq, normSq_eq_norm_sq, normSq_eq_norm_sq] at h
  have hpos : 0 < ‖1 - (starRingEnd ℂ) a * p‖ ^ 2 := by positivity
  have hp2 : ‖p - a‖ ^ 2 = ‖1 - (starRingEnd ℂ) a * p‖ ^ 2 + (1 - ‖a‖ ^ 2) * (‖p‖ ^ 2 - 1) := by
    linarith
  rw [bfac, norm_div, div_pow, hp2, add_div, div_self hpos.ne']

lemma norm_denom_le {a p : ℂ} : ‖1 - (starRingEnd ℂ) a * p‖ ≤ 1 + ‖a‖ * ‖p‖ := by
  calc ‖1 - (starRingEnd ℂ) a * p‖ ≤ ‖(1:ℂ)‖ + ‖(starRingEnd ℂ) a * p‖ := norm_sub_le _ _
    _ = 1 + ‖a‖ * ‖p‖ := by rw [norm_one, norm_mul, Complex.norm_conj]

lemma one_le_norm_bfac {a p : ℂ} (ha : ‖a‖ < 1) (hp : 1 ≤ ‖p‖)
    (hd : 1 - (starRingEnd ℂ) a * p ≠ 0) : 1 ≤ ‖bfac a p‖ := by
  have h := norm_bfac_sq_eq hd
  have h1 : 0 ≤ (1 - ‖a‖ ^ 2) * (‖p‖ ^ 2 - 1) / ‖1 - (starRingEnd ℂ) a * p‖ ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    apply mul_nonneg <;> nlinarith [norm_nonneg a]
  nlinarith [norm_nonneg (bfac a p)]

lemma norm_bfac_sq_ge {a p : ℂ} {m R' R : ℝ} (ham : ‖a‖ ≤ m) (hm : m < 1) (hR' : 1 ≤ R')
    (hp : R' ≤ ‖p‖) (hpR : ‖p‖ ≤ R) (hd : 1 - (starRingEnd ℂ) a * p ≠ 0) :
    1 + (1 - m ^ 2) * (R' ^ 2 - 1) / (1 + R) ^ 2 ≤ ‖bfac a p‖ ^ 2 := by
  rw [norm_bfac_sq_eq hd]
  have ha0 := norm_nonneg a
  have hm0 : 0 ≤ m := ha0.trans ham
  have hR : 1 ≤ R := hR'.trans (hp.trans hpR)
  have hD : 0 < ‖1 - (starRingEnd ℂ) a * p‖ := norm_pos_iff.2 hd
  have hDle : ‖1 - (starRingEnd ℂ) a * p‖ ≤ 1 + R := by
    refine norm_denom_le.trans ?_
    nlinarith [norm_nonneg p]
  have hX : (1 - m ^ 2) * (R' ^ 2 - 1) ≤ (1 - ‖a‖ ^ 2) * (‖p‖ ^ 2 - 1) := by
    apply mul_le_mul <;> nlinarith
  have hY : 0 ≤ (1 - ‖a‖ ^ 2) * (‖p‖ ^ 2 - 1) := by
    apply mul_nonneg <;> nlinarith
  have h1 : (1 - m ^ 2) * (R' ^ 2 - 1) / (1 + R) ^ 2 ≤
      (1 - ‖a‖ ^ 2) * (‖p‖ ^ 2 - 1) / (1 + R) ^ 2 :=
    div_le_div_of_nonneg_right hX (by positivity)
  have h2 : (1 - ‖a‖ ^ 2) * (‖p‖ ^ 2 - 1) / (1 + R) ^ 2 ≤
      (1 - ‖a‖ ^ 2) * (‖p‖ ^ 2 - 1) / ‖1 - (starRingEnd ℂ) a * p‖ ^ 2 :=
    div_le_div_of_nonneg_left hY (by positivity) (pow_le_pow_left₀ hD.le hDle 2)
  linarith

/-- The pole-free radius and the outside estimates for a finite Blaschke product. -/
theorem IsFiniteBlaschke.exists_nbhd {B : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n)
    (hn : 0 < n) : ∃ R > 1, DifferentiableOn ℂ B (ball 0 R) ∧
      (∀ w, {p | p ∈ ball (0:ℂ) R ∧ B p = w}.Finite) ∧
      (∀ w, {p | p ∈ ball (0:ℂ) R ∧ B p = w}.ncard ≤ n) ∧
      (∀ R', 1 < R' → R' < R → ∃ c > 1, ∀ p ∈ ball (0:ℂ) R, R' ≤ ‖p‖ → c ≤ ‖B p‖) := by
  classical
  obtain ⟨η, a, hη, ha, rfl⟩ := hB
  have hη0 : η ≠ 0 := by rintro rfl; simp at hη
  obtain ⟨m, hm0, hm1, ham⟩ : ∃ m : ℝ, 0 ≤ m ∧ m < 1 ∧ ∀ l, ‖a l‖ ≤ m := by
    refine ⟨Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun l => ‖a l‖, ?_, ?_, fun l =>
      Finset.le_sup' (fun l => ‖a l‖) (Finset.mem_univ l)⟩
    · exact (norm_nonneg _).trans (Finset.le_sup' (fun l => ‖a l‖) (Finset.mem_univ ⟨0, hn⟩))
    · exact (Finset.sup'_lt_iff _).2 fun l _ => ha l
  set R : ℝ := 2 / (1 + m) with hRdef
  have hR1 : 1 < R := by rw [hRdef, lt_div_iff₀ (by linarith)]; linarith
  have hmR : m * R < 1 := by
    rw [hRdef, mul_div_assoc', div_lt_one (by linarith)]; linarith
  have hpole : ∀ p ∈ ball (0:ℂ) R, ∀ l, 1 - (starRingEnd ℂ) (a l) * p ≠ 0 := by
    intro p hp l h
    have h1 : (starRingEnd ℂ) (a l) * p = 1 := by linear_combination -h
    have : ‖(starRingEnd ℂ) (a l) * p‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      rw [mem_ball_zero_iff] at hp
      calc ‖a l‖ * ‖p‖ ≤ m * R := mul_le_mul (ham l) hp.le (norm_nonneg _) hm0
        _ < 1 := hmR
    rw [h1, norm_one] at this
    exact lt_irrefl _ this
  refine ⟨R, hR1, ?_, fun w => fibre_finite hn hη0 ha hpole w, fun w => ?_, ?_⟩
  · intro p hp
    have : DifferentiableAt ℂ (fun z => ∏ l, bfac (a l) z) p := by
      refine DifferentiableAt.fun_finset_prod fun l _ => ?_
      exact (differentiableAt_id.sub_const _).div
        ((differentiableAt_const _).sub (differentiableAt_const _ |>.mul differentiableAt_id))
        (hpole p hp l)
    exact (this.const_mul η).differentiableWithinAt
  · rw [Set.ncard_eq_toFinset_card _ (fibre_finite hn hη0 ha hpole w)]
    exact fibre_card_le hn hη0 ha hpole w
  · intro R' hR' hR'R
    set δ := (1 - m ^ 2) * (R' ^ 2 - 1) / (1 + R) ^ 2 with hδ
    have hδpos : 0 < δ := by
      apply div_pos _ (by positivity)
      apply mul_pos <;> nlinarith
    refine ⟨Real.sqrt (1 + δ), ?_, fun p hp hpR' => ?_⟩
    · calc (1:ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
        _ < Real.sqrt (1 + δ) := Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have hpR := (mem_ball_zero_iff.1 hp).le
    have hfac : ∀ l, 1 ≤ ‖bfac (a l) p‖ := fun l =>
      one_le_norm_bfac (ha l) (by linarith) (hpole p hp l)
    have hfac0 : Real.sqrt (1 + δ) ≤ ‖bfac (a ⟨0, hn⟩) p‖ := by
      rw [Real.sqrt_le_left (by positivity)]
      exact norm_bfac_sq_ge (ham _) hm1 hR'.le hpR' hpR (hpole p hp _)
    simp only [norm_mul, hη, one_mul, norm_prod]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ⟨0, hn⟩)]
    calc Real.sqrt (1 + δ) = Real.sqrt (1 + δ) * 1 := (mul_one _).symm
      _ ≤ ‖bfac (a ⟨0, hn⟩) p‖ * ∏ l ∈ Finset.univ.erase ⟨0, hn⟩, ‖bfac (a l) p‖ := by
          refine mul_le_mul hfac0 ?_ zero_le_one (norm_nonneg _)
          have := Finset.prod_le_prod (s := Finset.univ.erase ⟨0, hn⟩)
            (fun _ _ => zero_le_one) (fun l _ => hfac l)
          simpa using this

end SteklovBlaschke

end
