module

public import Mathlib

/-!
# Fourier coefficients on `(0, 2π]` and an exponential-decay bootstrap

* `SteklovFourier.fc g n = (2π)⁻¹ ∫_{(0,2π]} e^{-int} g(t) dt`;
* `SteklovFourier.ae_eq_zero_of_fc`: an `L²` function on `(0, 2π]` all of whose Fourier
  coefficients vanish is zero a.e. (Parseval);
* `SteklovFourier.exp_decay_of_relation`: if a bounded sequence `F : ℤ → ℂ` satisfies
  `|n| F(n) = τ ∑ₖ R(k) F(n - k)` with exponentially decaying `R`, then `F` decays exponentially.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ComplexConjugate

noncomputable section

namespace SteklovFourier

/-- Fourier coefficient on `(0, 2π]`. -/
def fc (g : ℝ → ℂ) (n : ℤ) : ℂ :=
  ((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in Ioc 0 (2 * π), Complex.exp (-(n * t * Complex.I)) * g t

lemma fc_eq_fourierCoeffOn (g : ℝ → ℂ) (n : ℤ) :
    fc g n = fourierCoeffOn Real.two_pi_pos g n := by
  rw [fc, fourierCoeffOn_eq_integral, intervalIntegral.integral_of_le (by positivity)]
  rw [Complex.real_smul]
  congr 1
  · simp
  refine setIntegral_congr_fun measurableSet_Ioc fun t _ => ?_
  rw [fourier_coe_apply, smul_eq_mul]
  congr 2
  push_cast
  field_simp
  ring

/-- **Uniqueness of Fourier coefficients** on `(0, 2π]` for `L²` functions. -/
theorem ae_eq_zero_of_fc {g : ℝ → ℂ} (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * π))))
    (h : ∀ n : ℤ, fc g n = 0) : g =ᵐ[volume.restrict (Ioc 0 (2 * π))] 0 := by
  have hs := hasSum_sq_fourierCoeffOn Real.two_pi_pos (by simpa using hg)
  simp only [← fc_eq_fourierCoeffOn, h, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at hs
  have h0 := hs.unique hasSum_zero
  rw [intervalIntegral.integral_of_le (by positivity), smul_eq_mul] at h0
  have h1 : ∫ x in Ioc 0 (2 * π), ‖g x‖ ^ 2 = 0 := by
    rcases mul_eq_zero.1 h0 with h2 | h2
    · exfalso; simp at h2
    · exact h2
  have hint : Integrable (fun x => ‖g x‖ ^ 2) (volume.restrict (Ioc 0 (2 * π))) :=
    (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).1 hg
  have := (integral_eq_zero_iff_of_nonneg (fun _ => by positivity) hint).1 h1
  filter_upwards [this] with x hx
  simpa using hx

/-- Submultiplicativity of truncated exponential weights. -/
lemma weight_le {lam : ℝ} (hlam : 1 ≤ lam) (K : ℕ) (n k : ℤ) :
    lam ^ min n.natAbs K ≤ lam ^ k.natAbs * lam ^ min (n - k).natAbs K := by
  rw [← pow_add]
  refine pow_le_pow_right₀ hlam ?_
  have : n.natAbs ≤ k.natAbs + (n - k).natAbs := by
    have := Int.natAbs_add_le k (n - k); simpa using this
  omega

/-- Summability of a two-sided geometric sequence. -/
lemma summable_geom_int {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun k : ℤ => q ^ k.natAbs := by
  apply Summable.of_nat_of_neg
  · simpa using summable_geometric_of_lt_one hq0 hq1
  · simpa using summable_geometric_of_lt_one hq0 hq1

/-- **Exponential-decay bootstrap.** If `F : ℤ → ℂ` is bounded and
`|n| F(n) = τ ∑ₖ R(k) F(n - k)` for all `n`, where `|R(k)| ≤ C q^{|k|}` with `0 ≤ q < 1`, then
`|F(n)| ≤ D λ^{-|n|}` for some `λ > 1`. (Proof: a weighted sup-norm estimate with truncated,
submultiplicative weights `λ^{min(|n|, K)}`, uniform in `K`.) -/
theorem exp_decay_of_relation {F R : ℤ → ℂ} {B C q τ : ℝ} (hF : ∀ n, ‖F n‖ ≤ B)
    (hq0 : 0 ≤ q) (hq1 : q < 1) (hR : ∀ k, ‖R k‖ ≤ C * q ^ k.natAbs)
    (hrel : ∀ n, (n.natAbs : ℂ) * F n = τ * ∑' k, R k * F (n - k)) :
    ∃ lam > (1 : ℝ), ∃ D, ∀ n, ‖F n‖ * lam ^ n.natAbs ≤ D := by
  have hB : 0 ≤ B := (norm_nonneg _).trans (hF 0)
  set lam : ℝ := 2 / (1 + q) with hlam_def
  have hlam : 1 < lam := by rw [hlam_def, lt_div_iff₀ (by linarith)]; linarith
  have hql : q * lam < 1 := by
    rw [hlam_def, mul_div_assoc', div_lt_one (by linarith)]; linarith
  have hql0 : 0 ≤ q * lam := mul_nonneg hq0 (by linarith)
  have hRs : Summable fun k : ℤ => ‖R k‖ * lam ^ k.natAbs := by
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((summable_geom_int hql0 hql).mul_left C)
    calc ‖R k‖ * lam ^ k.natAbs ≤ C * q ^ k.natAbs * lam ^ k.natAbs :=
          mul_le_mul_of_nonneg_right (hR k) (by positivity)
      _ = C * (q * lam) ^ k.natAbs := by rw [mul_pow]; ring
  have hRs0 : Summable fun k : ℤ => ‖R k‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) hRs
    exact le_mul_of_one_le_right (norm_nonneg _) (one_le_pow₀ hlam.le)
  set S := ∑' k, ‖R k‖ * lam ^ k.natAbs with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun k => by positivity
  obtain ⟨N, hN⟩ := exists_nat_ge (|τ| * S * 2)
  refine ⟨lam, hlam, B * lam ^ N, fun n => ?_⟩
  set K := n.natAbs
  set w : ℤ → ℝ := fun m => lam ^ min m.natAbs K with hw
  have hw0 : ∀ m, 0 ≤ w m := fun m => by positivity
  have hbdd : BddAbove (Set.range fun m => ‖F m‖ * w m) := by
    refine ⟨B * lam ^ K, ?_⟩
    rintro _ ⟨m, rfl⟩
    exact mul_le_mul (hF m) (pow_le_pow_right₀ hlam.le (min_le_right _ _)) (hw0 m) hB
  set M := ⨆ m, ‖F m‖ * w m with hM
  have hle : ∀ m, ‖F m‖ * w m ≤ M := fun m => le_ciSup hbdd m
  have hM0 : 0 ≤ M := (mul_nonneg (norm_nonneg _) (hw0 0)).trans (hle 0)
  have key : ∀ m, ‖F m‖ * w m ≤ max (B * lam ^ N) (M / 2) := by
    intro m
    by_cases hm : m.natAbs ≤ N
    · refine le_max_of_le_left (mul_le_mul (hF m) ?_ (hw0 m) hB)
      exact pow_le_pow_right₀ hlam.le ((min_le_left _ _).trans hm)
    · push_neg at hm
      refine le_max_of_le_right ?_
      have hsum0 : Summable fun k => ‖R k‖ * ‖F (m - k)‖ :=
        Summable.of_nonneg_of_le (fun k => by positivity)
          (fun k => mul_le_mul_of_nonneg_left (hF _) (norm_nonneg _))
          (hRs0.mul_right B)
      have hsum1 : Summable fun k => ‖R k * F (m - k)‖ := hsum0.congr fun k => by simp
      have h1 : (m.natAbs : ℝ) * ‖F m‖ ≤ |τ| * ∑' k, ‖R k‖ * ‖F (m - k)‖ := by
        have := congrArg norm (hrel m)
        rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs] at this
        rw [this]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        refine (norm_tsum_le_tsum_norm hsum1).trans (le_of_eq ?_)
        simp
      have hsum2 : Summable fun k => ‖R k‖ * lam ^ k.natAbs * (‖F (m - k)‖ * w (m - k)) :=
        Summable.of_nonneg_of_le (fun k => by positivity)
          (fun k => mul_le_mul_of_nonneg_left (hle _) (by positivity)) (hRs.mul_right M)
      have h2 : (∑' k, ‖R k‖ * ‖F (m - k)‖) * w m ≤
          ∑' k, ‖R k‖ * lam ^ k.natAbs * (‖F (m - k)‖ * w (m - k)) := by
        rw [← tsum_mul_right]
        refine Summable.tsum_le_tsum (fun k => ?_) (hsum0.mul_right _) hsum2
        calc ‖R k‖ * ‖F (m - k)‖ * w m ≤ ‖R k‖ * ‖F (m - k)‖ * (lam ^ k.natAbs * w (m - k)) :=
              mul_le_mul_of_nonneg_left (weight_le hlam.le K m k) (by positivity)
          _ = _ := by ring
      have h3 : ∑' k, ‖R k‖ * lam ^ k.natAbs * (‖F (m - k)‖ * w (m - k)) ≤ S * M := by
        rw [hS, ← tsum_mul_right]
        exact Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hle _) (by positivity))
          hsum2 (hRs.mul_right M)
      have hmpos : (0 : ℝ) < m.natAbs := by exact_mod_cast (Nat.zero_le N).trans_lt hm
      have hNm : (N : ℝ) < m.natAbs := by exact_mod_cast hm
      have h4 : (m.natAbs : ℝ) * (‖F m‖ * w m) ≤ |τ| * (S * M) := by
        calc (m.natAbs : ℝ) * (‖F m‖ * w m) = ((m.natAbs : ℝ) * ‖F m‖) * w m := by ring
          _ ≤ (|τ| * ∑' k, ‖R k‖ * ‖F (m - k)‖) * w m := mul_le_mul_of_nonneg_right h1 (hw0 m)
          _ = |τ| * ((∑' k, ‖R k‖ * ‖F (m - k)‖) * w m) := by ring
          _ ≤ |τ| * (S * M) := mul_le_mul_of_nonneg_left (h2.trans h3) (abs_nonneg _)
      have h5 : |τ| * (S * M) ≤ (m.natAbs : ℝ) * (M / 2) := by
        nlinarith [abs_nonneg τ]
      exact le_of_mul_le_mul_left (h4.trans h5) hmpos
  have hMle : M ≤ max (B * lam ^ N) (M / 2) := ciSup_le key
  have hMle' : M ≤ B * lam ^ N := by
    rcases le_max_iff.1 hMle with h | h
    · exact h
    · have : M ≤ 0 := by linarith
      exact this.trans (by positivity)
  have := (hle n).trans hMle'
  simpa [w, K] using this

/-! ### Elementary computations -/

lemma norm_exp_int (n : ℤ) (t : ℝ) : ‖Complex.exp (n * t * Complex.I)‖ = 1 := by
  rw [show (n:ℂ) * t * Complex.I = ((n * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma norm_exp_neg_int (n : ℤ) (t : ℝ) : ‖Complex.exp (-(n * t * Complex.I))‖ = 1 := by
  rw [show -((n:ℂ) * t * Complex.I) = ((-(n * t) : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma integral_exp_int (k : ℤ) :
    ∫ t in Ioc 0 (2 * π), Complex.exp (k * t * Complex.I) =
      if k = 0 then ((2 * π : ℝ) : ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp [Real.pi_pos.le]
  · rw [← intervalIntegral.integral_of_le (by positivity)]
    have hc : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
    have := integral_exp_mul_complex (a := 0) (b := 2 * π) hc
    simp only [mul_comm _ (Complex.I), ← mul_assoc] at this ⊢
    rw [this]
    have h1 : Complex.exp (Complex.I * k * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [show Complex.I * k * ((2 * π : ℝ) : ℂ) = k * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h1]; simp

lemma exp_mul_exp_int (a b : ℤ) (t : ℝ) :
    Complex.exp (-(a * t * Complex.I)) * Complex.exp (b * t * Complex.I) =
      Complex.exp (((b - a : ℤ) : ℂ) * t * Complex.I) := by
  rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma exp_neg_int_mul (n : ℤ) (t : ℝ) : Complex.exp (-(n * t * Complex.I)) =
    (Real.cos (n * t) : ℂ) - (Real.sin (n * t) : ℂ) * Complex.I := by
  rw [show -((n:ℂ) * t * Complex.I) = ((-(n * t) : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]; ring

lemma integrableOn_mul_bdd {h : ℝ → ℝ} (hi : IntegrableOn h (Ioc 0 (2 * π))) (c : ℝ → ℝ)
    (hc : Continuous c) (hb : ∀ t, |c t| ≤ 1) :
    IntegrableOn (fun t => h t * c t) (Ioc 0 (2 * π)) := by
  refine hi.mul_bdd (c := 1) hc.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun t => by simpa using hb t

/-! ### Fourier coefficients of real functions, bounds, series -/

lemma fc_real {h : ℝ → ℝ} (hi : IntegrableOn h (Ioc 0 (2 * π))) (n : ℤ) :
    fc (fun t => (h t : ℂ)) n = ((2 * π : ℝ) : ℂ)⁻¹ *
      ((∫ t in Ioc 0 (2 * π), h t * Real.cos (n * t) : ℝ) -
        (∫ t in Ioc 0 (2 * π), h t * Real.sin (n * t) : ℝ) * Complex.I) := by
  rw [fc]
  congr 1
  have h1 := integrableOn_mul_bdd hi (fun t => Real.cos (n * t)) (by fun_prop)
    (fun t => abs_cos_le_one _)
  have h2 := integrableOn_mul_bdd hi (fun t => Real.sin (n * t)) (by fun_prop)
    (fun t => abs_sin_le_one _)
  rw [integral_complex_ofReal.symm, integral_complex_ofReal.symm, ← integral_mul_const,
    ← integral_sub]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [exp_neg_int_mul]; push_cast; ring
  · exact h1.ofReal
  · exact h2.ofReal.mul_const _

lemma fc_real_neg {h : ℝ → ℝ} (hi : IntegrableOn h (Ioc 0 (2 * π))) (n : ℤ) :
    fc (fun t => (h t : ℂ)) (-n) = conj (fc (fun t => (h t : ℂ)) n) := by
  rw [fc_real hi, fc_real hi]
  simp only [Int.cast_neg, neg_mul, Real.cos_neg, Real.sin_neg, map_mul, map_inv₀, map_sub,
    Complex.conj_ofReal, Complex.conj_I]
  simp only [mul_neg, integral_neg]; push_cast; ring

lemma norm_fc_le (g : ℝ → ℂ) (n : ℤ) :
    ‖fc g n‖ ≤ (2 * π)⁻¹ * ∫ t in Ioc 0 (2 * π), ‖g t‖ := by
  rw [fc, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (le_of_eq ?_))
    (by positivity)
  congr 1; funext t; rw [norm_mul, norm_exp_neg_int, one_mul]

/-- If `∑ ‖F n‖ < ∞` and `g(t) = ∑ F(n) e^{int}` for all `t`, then `ĝ(m) = F(m)`. -/
lemma fc_of_hasSum {F : ℤ → ℂ} (hF : Summable fun n => ‖F n‖) {g : ℝ → ℂ}
    (hg : ∀ t : ℝ, HasSum (fun n : ℤ => F n * Complex.exp (n * t * Complex.I)) (g t)) (m : ℤ) :
    fc g m = F m := by
  have hint : ∀ n : ℤ, Integrable (fun t : ℝ => Complex.exp (-(m * t * Complex.I)) *
      (F n * Complex.exp (n * t * Complex.I))) (volume.restrict (Ioc 0 (2 * π))) := by
    intro n
    refine Integrable.of_bound (C := ‖F n‖) (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun t => by
      rw [norm_mul, norm_mul, norm_exp_int, norm_exp_neg_int]; simp
  have hsum : Summable fun n : ℤ => ∫ t in Ioc 0 (2 * π),
      ‖Complex.exp (-(m * t * Complex.I)) * (F n * Complex.exp (n * t * Complex.I))‖ := by
    refine (hF.mul_left (2 * π)).congr fun n => ?_
    simp only [norm_mul, norm_exp_int, norm_exp_neg_int, one_mul, mul_one]
    rw [setIntegral_const]; simp [Real.pi_pos.le, mul_comm]
  have h1 := integral_tsum_of_summable_integral_norm hint hsum
  have h2 : ∀ t : ℝ, ∑' n : ℤ, Complex.exp (-(m * t * Complex.I)) *
      (F n * Complex.exp (n * t * Complex.I)) = Complex.exp (-(m * t * Complex.I)) * g t :=
    fun t => by rw [tsum_mul_left, (hg t).tsum_eq]
  simp only [h2] at h1
  rw [fc, ← h1]
  have h3 : ∀ n : ℤ, ∫ t in Ioc 0 (2 * π), Complex.exp (-(m * t * Complex.I)) *
      (F n * Complex.exp (n * t * Complex.I)) =
      if n = m then ((2 * π : ℝ) : ℂ) * F m else 0 := by
    intro n
    have : (fun t : ℝ => Complex.exp (-(m * t * Complex.I)) *
        (F n * Complex.exp (n * t * Complex.I))) =
        fun t : ℝ => F n * Complex.exp (((n - m : ℤ) : ℂ) * t * Complex.I) := by
      funext t; rw [← exp_mul_exp_int]; ring
    rw [this, integral_const_mul, integral_exp_int]
    by_cases h : n = m
    · subst h; simp; ring
    · simp [h, sub_eq_zero]
  simp only [h3]
  rw [tsum_ite_eq]
  field_simp

/-- **Convolution identity**: if `r(t) = ∑ₖ R(k) e^{ikt}` with `∑ ‖R k‖ < ∞` and `f` is
integrable on `(0, 2π]`, then `(r f)^(n) = ∑ₖ R(k) f̂(n - k)`. -/
lemma fc_mul_eq_tsum {R : ℤ → ℂ} (hR : Summable fun k => ‖R k‖) {r f : ℝ → ℂ}
    (hr : ∀ t : ℝ, HasSum (fun k : ℤ => R k * Complex.exp (k * t * Complex.I)) (r t))
    (hf : IntegrableOn f (Ioc 0 (2 * π))) (n : ℤ) :
    fc (fun t => r t * f t) n = ∑' k, R k * fc f (n - k) := by
  set G : ℤ → ℝ → ℂ := fun k t =>
    R k * (Complex.exp (-(((n - k : ℤ) : ℂ) * t * Complex.I)) * f t)
  have hint : ∀ k, Integrable (G k) (volume.restrict (Ioc 0 (2 * π))) := by
    intro k
    refine (Integrable.bdd_mul (c := 1) hf (by fun_prop) ?_).const_mul (R k)
    exact Filter.Eventually.of_forall fun t => by rw [norm_exp_neg_int]
  have hsum : Summable fun k => ∫ t in Ioc 0 (2 * π), ‖G k t‖ := by
    refine (hR.mul_right (∫ t in Ioc 0 (2 * π), ‖f t‖)).congr fun k => ?_
    simp only [G, norm_mul, norm_exp_neg_int, one_mul]
    rw [integral_const_mul]
  have h1 := integral_tsum_of_summable_integral_norm hint hsum
  have h2 : ∀ t : ℝ, ∑' k, G k t = Complex.exp (-(n * t * Complex.I)) * (r t * f t) := by
    intro t
    have : ∀ k, G k t = (R k * Complex.exp (k * t * Complex.I)) *
        (Complex.exp (-(n * t * Complex.I)) * f t) := by
      intro k; simp only [G]
      rw [show Complex.exp (-(((n - k : ℤ) : ℂ) * t * Complex.I)) =
          Complex.exp (k * t * Complex.I) * Complex.exp (-(n * t * Complex.I)) by
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
      ring
    simp only [this]
    rw [tsum_mul_right, (hr t).tsum_eq]; ring
  simp only [h2] at h1
  rw [fc, ← h1, ← tsum_mul_left]
  congr 1; funext k
  simp only [G, fc]
  rw [integral_const_mul]; ring

lemma fc_sub {g h : ℝ → ℂ} (hg : IntegrableOn g (Ioc 0 (2 * π)))
    (hh : IntegrableOn h (Ioc 0 (2 * π))) (n : ℤ) :
    fc (fun t => g t - h t) n = fc g n - fc h n := by
  have hb : ∀ k : ℤ, ∀ {u : ℝ → ℂ}, IntegrableOn u (Ioc 0 (2 * π)) →
      IntegrableOn (fun t : ℝ => Complex.exp (-(k * t * Complex.I)) * u t) (Ioc 0 (2 * π)) := by
    intro k u hu
    refine hu.bdd_mul (c := 1) (by fun_prop) ?_
    exact Filter.Eventually.of_forall fun t => by rw [norm_exp_neg_int]
  simp only [fc, mul_sub]
  rw [integral_sub (hb n hg) (hb n hh), mul_sub]

/-- Two real `L²` functions on `(0, 2π]` with the same Fourier coefficients agree a.e. -/
theorem ae_eq_of_fc_eq {f g : ℝ → ℝ} (hf : MemLp f 2 (volume.restrict (Ioc 0 (2 * π))))
    (hg : MemLp g 2 (volume.restrict (Ioc 0 (2 * π))))
    (h : ∀ n : ℤ, fc (fun t => (f t : ℂ)) n = fc (fun t => (g t : ℂ)) n) :
    f =ᵐ[volume.restrict (Ioc 0 (2 * π))] g := by
  have hf' : MemLp (fun t => (f t : ℂ)) 2 (volume.restrict (Ioc 0 (2 * π))) := hf.ofReal
  have hg' : MemLp (fun t => (g t : ℂ)) 2 (volume.restrict (Ioc 0 (2 * π))) := hg.ofReal
  have h0 := ae_eq_zero_of_fc (hf'.sub hg') (fun n => by
    have := fc_sub (hf'.integrable one_le_two) (hg'.integrable one_le_two) n
    rw [show ((fun t => (f t : ℂ)) - fun t => (g t : ℂ)) = fun t => (f t : ℂ) - (g t : ℂ) from rfl,
      this, h n, sub_self])
  filter_upwards [h0] with t ht
  simpa [sub_eq_zero] using ht

instance fact_two_pi_pos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

lemma liftIoc_coe_eq {f : ℝ → ℂ} (hper : Function.Periodic f (2 * π)) (t : ℝ) :
    AddCircle.liftIoc (2 * π) 0 f (t : AddCircle (2 * π)) = f t := by
  have hmem := toIocMod_mem_Ioc Real.two_pi_pos 0 t
  have hsub := self_sub_toIocDiv_zsmul Real.two_pi_pos 0 t
  simp only [zsmul_eq_mul] at hsub
  have he : ((toIocMod Real.two_pi_pos 0 t : ℝ) : AddCircle (2 * π)) = (t : AddCircle (2 * π)) := by
    rw [QuotientAddGroup.eq]
    exact ⟨(toIocDiv Real.two_pi_pos 0 t), by simp only [zsmul_eq_mul]; linarith⟩
  rw [← he, AddCircle.liftIoc_coe_apply (by simpa using hmem), ← hsub]
  exact hper.sub_int_mul_eq _

/-- **Pointwise Fourier inversion** for a continuous `2π`-periodic function with absolutely
summable Fourier coefficients. -/
theorem hasSum_fc {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f (2 * π))
    (hs : Summable fun n => ‖fc f n‖) (t : ℝ) :
    HasSum (fun n : ℤ => fc f n * Complex.exp (n * t * Complex.I)) (f t) := by
  have hcont : Continuous (AddCircle.liftIoc (2 * π) 0 f) :=
    AddCircle.liftIoc_continuous (by simpa using (hper 0).symm) hf.continuousOn
  set Fc : C(AddCircle (2 * π), ℂ) := ⟨_, hcont⟩
  have hcoef : ∀ n, fourierCoeff Fc n = fc f n := by
    intro n
    rw [fc_eq_fourierCoeffOn]
    have := fourierCoeff_liftIoc_eq (T := 2 * π) (a := 0) f n
    convert this using 2
    simp
  have hcoef' : (fourierCoeff Fc : ℤ → ℂ) = fc f := funext hcoef
  have h := has_pointwise_sum_fourier_series_of_summable (f := Fc)
    (by rw [hcoef']; exact hs.of_norm) (t : AddCircle (2 * π))
  have hval : Fc (t : AddCircle (2 * π)) = f t := liftIoc_coe_eq hper t
  convert h using 1
  · funext n
    rw [hcoef, fourier_coe_apply, smul_eq_mul]
    congr 2
    push_cast
    field_simp
  · exact hval.symm

end SteklovFourier
