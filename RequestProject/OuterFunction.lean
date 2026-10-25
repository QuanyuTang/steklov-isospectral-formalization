module

public import RequestProject.OuterFourier
public import RequestProject.RealAnalyticBounds

/-!
# The Schwarz series `H` of a real periodic function

For a smooth `2π`-periodic `h : ℝ → ℝ` with Fourier coefficients `ĥ(k) = fc h k` we define
`H(z) = ĥ(0) + 2 ∑_{k ≥ 1} ĥ(k) z^k` (`OuterFunction.H`) and its formal `j`-th derivative
`H_j(z) = ∑_k b_k · k(k-1)⋯(k-j+1) · z^{k-j}` (`OuterFunction.Hj`).

Proved here:
* `norm_Hj_le` — on the closed unit disk, `‖H_j(z)‖ ≤ |ĥ(0)| + 4·‖h^{(j+2)}‖_∞`
  (from `|ĥ(k)| ≤ ‖h^{(j+2)}‖_∞ / k^{j+2}`, and `∑ 1/k² = π²/6 < 2`);
* `re_H_exp` — `Re H(e^{it}) = h(t)` (Fourier inversion and conjugate symmetry);
* `H_zero` — `H(0) = ĥ(0)`, which is real;
* `exists_decay` — if `h` is real-analytic, `|b_k| ≤ A q^k` with `q < 1`;
* `hasDerivAt_Hj`, `iteratedDeriv_H` — under geometric decay, `H` is holomorphic on a disk of
  radius `R > 1` and `H^{(j)} = H_j` there.
-/

@[expose] public section

open Real Complex Set Metric Filter Topology OuterFourier
open scoped Nat ContDiff

noncomputable section

namespace OuterFunction

/-- The complexification `t ↦ (h t : ℂ)`. -/
def hc (h : ℝ → ℝ) : ℝ → ℂ := fun t => (h t : ℂ)

/-- Fourier coefficients of `h`. -/
def coef (h : ℝ → ℝ) (n : ℤ) : ℂ := fc (hc h) n

/-- Coefficients of the Schwarz series: `b 0 = ĥ(0)`, `b k = 2 ĥ(k)` for `k ≥ 1`. -/
def b (h : ℝ → ℝ) (k : ℕ) : ℂ := if k = 0 then coef h 0 else 2 * coef h k

/-- The formal `j`-th derivative of the Schwarz series. -/
def Hj (h : ℝ → ℝ) (j : ℕ) (z : ℂ) : ℂ := ∑' k : ℕ, b h k * (k.descFactorial j : ℂ) * z ^ (k - j)

/-- The Schwarz series `H(z) = ĥ(0) + 2 ∑_{k ≥ 1} ĥ(k) z^k`, i.e. the holomorphic function with
`Re H = h` on the unit circle and `Im H(0) = 0`. -/
def H (h : ℝ → ℝ) (z : ℂ) : ℂ := Hj h 0 z

lemma H_eq (h : ℝ → ℝ) (z : ℂ) : H h z = ∑' k : ℕ, b h k * z ^ k := by
  simp [H, Hj]

lemma iteratedDeriv_hc {h : ℝ → ℝ} (hsm : ContDiff ℝ ∞ h) (m : ℕ) :
    iteratedDeriv m (hc h) = fun t => (((iteratedDeriv m h t : ℝ)) : ℂ) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext t
    rw [iteratedDeriv_succ, ih, iteratedDeriv_succ]
    have hd : DifferentiableAt ℝ (iteratedDeriv m h) t :=
      hsm.differentiable_iteratedDeriv m (by exact_mod_cast WithTop.coe_lt_top _) t
    exact hd.hasDerivAt.ofReal_comp.deriv

lemma contDiff_hc {h : ℝ → ℝ} (hsm : ContDiff ℝ ∞ h) : ContDiff ℝ ∞ (hc h) :=
  Complex.ofRealCLM.contDiff.comp hsm

lemma periodic_hc {h : ℝ → ℝ} (hper : Function.Periodic h (2 * π)) :
    Function.Periodic (hc h) (2 * π) := fun t => by simp [hc, hper t]

/-- A continuous periodic function is bounded. -/
lemma exists_bound_periodic {u : ℝ → ℝ} (hu : Continuous u) {T : ℝ} (hT : 0 < T)
    (hper : Function.Periodic u T) : ∃ M, ∀ x, |u x| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := 0) (b := T)).exists_bound_of_continuousOn
    hu.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ico₀ hT x
  rw [hxy]; simpa [Real.norm_eq_abs] using hM y (Ico_subset_Icc_self hy)

lemma norm_coef_le {h : ℝ → ℝ} (hsm : ContDiff ℝ ∞ h) (hper : Function.Periodic h (2 * π))
    (j : ℕ) {M : ℝ} (hM : ∀ x, |iteratedDeriv j h x| ≤ M) {n : ℤ} (hn : n ≠ 0) :
    ‖coef h n‖ ≤ M / |(n : ℝ)| ^ j := by
  refine norm_fc_le_of_iteratedDeriv (contDiff_hc hsm) (periodic_hc hper) hn j fun x => ?_
  rw [iteratedDeriv_hc hsm, Complex.norm_real, Real.norm_eq_abs]; exact hM x

lemma norm_coef_zero_le (h : ℝ → ℝ) {M : ℝ} (hM : ∀ x, |h x| ≤ M) : ‖coef h 0‖ ≤ M :=
  norm_fc_le _ _ fun x => by simpa [hc, Complex.norm_real] using hM x

lemma coef_neg (h : ℝ → ℝ) (n : ℤ) : coef h (-n) = (starRingEnd ℂ) (coef h n) :=
  fc_neg_ofReal h n

lemma coef_zero_im (h : ℝ → ℝ) : (coef h 0).im = 0 := by
  have := coef_neg h 0
  rw [neg_zero] at this
  exact Complex.conj_eq_iff_im.1 this.symm

/-- The termwise bound on the closed unit disk. -/
lemma norm_term_le {h : ℝ → ℝ} (hsm : ContDiff ℝ ∞ h) (hper : Function.Periodic h (2 * π))
    (j : ℕ) {M : ℝ} (hM : ∀ x, |iteratedDeriv (j + 2) h x| ≤ M) {z : ℂ} (hz : ‖z‖ ≤ 1)
    (k : ℕ) :
    ‖b h k * (k.descFactorial j : ℂ) * z ^ (k - j)‖ ≤
      (if k = 0 then ‖coef h 0‖ else 0) + 2 * M * (1 / (k : ℝ) ^ 2) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hzk : ‖z ^ (k - j)‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [b, if_true, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, div_zero, mul_zero, add_zero]
    rw [norm_mul, norm_mul]
    have hd : ‖((Nat.descFactorial 0 j : ℕ) : ℂ)‖ ≤ 1 := by
      rcases j with _ | j <;> simp
    calc ‖coef h 0‖ * ‖((Nat.descFactorial 0 j : ℕ) : ℂ)‖ * ‖z ^ (0 - j)‖
        ≤ ‖coef h 0‖ * 1 * 1 := by gcongr
      _ = ‖coef h 0‖ := by ring
  · have hk0 : k ≠ 0 := hk.ne'
    simp only [b, hk0, if_false, zero_add]
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hc := norm_coef_le hsm hper (j + 2) hM (n := (k : ℤ)) (by exact_mod_cast hk0)
    rw [show |((k : ℤ) : ℝ)| = (k : ℝ) by push_cast; exact abs_of_pos hkpos] at hc
    have hd : ‖((Nat.descFactorial k j : ℕ) : ℂ)‖ ≤ (k : ℝ) ^ j := by
      rw [Complex.norm_natCast]; exact_mod_cast Nat.descFactorial_le_pow k j
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_ofNat]
    calc 2 * ‖coef h k‖ * ‖((Nat.descFactorial k j : ℕ) : ℂ)‖ * ‖z ^ (k - j)‖
        ≤ 2 * (M / (k : ℝ) ^ (j + 2)) * (k : ℝ) ^ j * 1 := by gcongr
      _ = 2 * M * (1 / (k : ℝ) ^ 2) := by
        field_simp
        ring

lemma summable_bound (h : ℝ → ℝ) (M : ℝ) :
    HasSum (fun k : ℕ => (if k = 0 then ‖coef h 0‖ else 0) + 2 * M * (1 / (k : ℝ) ^ 2))
      (‖coef h 0‖ + 2 * M * (π ^ 2 / 6)) := by
  refine HasSum.add ?_ (hasSum_zeta_two.mul_left (2 * M))
  convert hasSum_ite_eq 0 ‖coef h 0‖ using 1

lemma summable_Hj_term {h : ℝ → ℝ} (hsm : ContDiff ℝ ∞ h) (hper : Function.Periodic h (2 * π))
    (j : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun k : ℕ => b h k * (k.descFactorial j : ℂ) * z ^ (k - j)) := by
  obtain ⟨M, hM⟩ := exists_bound_periodic
    (hsm.continuous_iteratedDeriv (j + 2) (WithTop.coe_le_coe.2 le_top)) Real.two_pi_pos
    (RealAnalyticBounds.periodic_iteratedDeriv hper (j + 2))
  exact Summable.of_norm_bounded (summable_bound h M).summable
    (norm_term_le hsm hper j hM hz)

/-- **`C^j` bound for the Schwarz series on the closed unit disk.** -/
theorem norm_Hj_le {h : ℝ → ℝ} (hsm : ContDiff ℝ ∞ h) (hper : Function.Periodic h (2 * π))
    (j : ℕ) {M : ℝ} (hM : ∀ x, |iteratedDeriv (j + 2) h x| ≤ M) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Hj h j z‖ ≤ ‖coef h 0‖ + 4 * M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hs := summable_bound h M
  calc ‖Hj h j z‖ ≤ ‖coef h 0‖ + 2 * M * (π ^ 2 / 6) :=
        tsum_of_norm_bounded hs (norm_term_le hsm hper j hM hz)
    _ ≤ ‖coef h 0‖ + 4 * M := by
        have : π ^ 2 / 6 ≤ 2 := by
          have := Real.pi_lt_d2
          nlinarith [Real.pi_pos]
        nlinarith

lemma H_zero (h : ℝ → ℝ) : H h 0 = coef h 0 := by
  rw [H_eq, tsum_eq_single 0]
  · simp [b]
  · intro k hk; simp [hk]

/-- **Boundary values**: `Re H(e^{it}) = h(t)`. -/
theorem re_H_exp {h : ℝ → ℝ} (hsm : ContDiff ℝ ∞ h) (hper : Function.Periodic h (2 * π))
    (t : ℝ) : (H h (exp (t * I))).re = h t := by
  -- summability of the Fourier coefficients
  obtain ⟨M, hM⟩ := exists_bound_periodic
    (hsm.continuous_iteratedDeriv 2 (WithTop.coe_le_coe.2 le_top)) Real.two_pi_pos
    (RealAnalyticBounds.periodic_iteratedDeriv hper 2)
  have hsumZ : Summable (coef h) := by
    refine Summable.of_norm_bounded (g := fun n : ℤ =>
      (if n = 0 then ‖coef h 0‖ else 0) + M * (1 / (n : ℝ) ^ 2)) ?_ ?_
    · exact (hasSum_ite_eq (0 : ℤ) ‖coef h 0‖).summable.add
        ((Real.summable_one_div_int_pow.2 one_lt_two).mul_left M)
    · intro n
      rcases eq_or_ne n 0 with rfl | hn
      · dsimp only
        rw [if_pos rfl]
        simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
          div_zero, mul_zero, add_zero, le_refl]
      · have := norm_coef_le hsm hper 2 hM hn
        dsimp only
        rw [if_neg hn, zero_add, mul_one_div]
        rw [sq_abs] at this
        exact this
  have hF := hasSum_fc (f := hc h) (Complex.continuous_ofReal.comp hsm.continuous)
    (periodic_hc hper) hsumZ t
  have h2 := hF.nat_add_neg
  -- real parts
  have h3 := Complex.hasSum_re h2
  simp only [hc, Complex.ofReal_re, Complex.add_re] at h3
  -- the series for `H(e^{it})`
  have hz : ‖exp (t * I)‖ ≤ 1 := by rw [Complex.norm_exp_ofReal_mul_I]
  have hsH := summable_Hj_term hsm hper 0 hz
  have hH := Complex.hasSum_re hsH.hasSum
  rw [← Hj, ← H] at hH
  refine hH.unique ?_
  have key : ∀ k : ℕ, (b h k * ((k.descFactorial 0 : ℕ) : ℂ) * exp (t * I) ^ (k - 0)).re =
      ((coef h k * exp (k * t * I)).re + (coef h (-(k : ℤ)) * exp ((-(k : ℤ) : ℤ) * t * I)).re) -
        (if k = 0 then (coef h 0).re else 0) := by
    intro k
    have he : exp (t * I) ^ k = exp (k * t * I) := by
      rw [← Complex.exp_nat_mul]; ring_nf
    have hconj : (coef h (-(k : ℤ)) * exp ((-(k : ℤ) : ℤ) * t * I)).re =
        (coef h k * exp (k * t * I)).re := by
      rw [coef_neg]
      have : exp ((-(k : ℤ) : ℤ) * t * I) = (starRingEnd ℂ) (exp (k * t * I)) := by
        rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]
      rw [this, ← map_mul, Complex.conj_re]
    rw [hconj, Nat.descFactorial_zero, Nat.cast_one, mul_one, Nat.sub_zero, he]
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [b]
    · simp only [b, hk.ne', if_false, sub_zero]
      rw [show (2 : ℂ) * coef h k * exp (k * t * I) = 2 * (coef h k * exp (k * t * I)) by ring]
      simp only [Complex.mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
      ring
  simp_rw [key]
  have h4 : HasSum (fun k : ℕ => if k = 0 then (coef h 0).re else 0) (coef h 0).re := by
    convert hasSum_ite_eq 0 (coef h 0).re using 1
  convert h3.sub h4 using 1
  simp [coef]

/-! ## Holomorphy under geometric decay -/

section Decay

variable {h : ℝ → ℝ} {A q : ℝ}

/-- The radius `R = 2/(1+q) > 1` used under geometric decay with ratio `q < 1`. -/
def radius (q : ℝ) : ℝ := 2 / (1 + q)

lemma one_lt_radius (hq0 : 0 ≤ q) (hq1 : q < 1) : 1 < radius q := by
  rw [radius, lt_div_iff₀ (by linarith)]; linarith

lemma q_mul_radius_lt_one (hq0 : 0 ≤ q) (hq1 : q < 1) : q * radius q < 1 := by
  rw [radius, mul_div_assoc', div_lt_one (by linarith)]; linarith

lemma norm_term_le_decay (hdec : ∀ k, ‖b h k‖ ≤ A * q ^ k) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j k : ℕ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (radius q)) :
    ‖b h k * (k.descFactorial j : ℂ) * z ^ (k - j)‖ ≤ A * ((k : ℝ) ^ j * (q * radius q) ^ k) := by
  have hR : 1 ≤ radius q := (one_lt_radius hq0 hq1).le
  have hz' : ‖z‖ ≤ radius q := by
    rw [mem_ball, dist_zero_right] at hz; exact hz.le
  have hA : 0 ≤ A := by
    have := (norm_nonneg _).trans (hdec 0); simpa using this
  rw [norm_mul, norm_mul, norm_pow, Complex.norm_natCast]
  have h1 : (k.descFactorial j : ℝ) ≤ (k : ℝ) ^ j := by
    exact_mod_cast Nat.descFactorial_le_pow k j
  have h2 : ‖z‖ ^ (k - j) ≤ radius q ^ k := by
    calc ‖z‖ ^ (k - j) ≤ radius q ^ (k - j) := by gcongr
      _ ≤ radius q ^ k := pow_le_pow_right₀ hR (Nat.sub_le k j)
  calc ‖b h k‖ * (k.descFactorial j : ℝ) * ‖z‖ ^ (k - j)
      ≤ (A * q ^ k) * (k : ℝ) ^ j * radius q ^ k := by gcongr; exact hdec k
    _ = A * ((k : ℝ) ^ j * (q * radius q) ^ k) := by rw [mul_pow]; ring

lemma summable_decay_bound (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) :
    Summable (fun k : ℕ => A * ((k : ℝ) ^ j * (q * radius q) ^ k)) := by
  refine (summable_pow_mul_geometric_of_norm_lt_one j ?_).mul_left A
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hq0 (by
    have := one_lt_radius hq0 hq1; linarith))]
  exact q_mul_radius_lt_one hq0 hq1

lemma differentiableOn_Hj (hdec : ∀ k, ‖b h k‖ ≤ A * q ^ k) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) : DifferentiableOn ℂ (Hj h j) (ball 0 (radius q)) := by
  refine Complex.differentiableOn_tsum_of_summable_norm (summable_decay_bound hq0 hq1 j)
    (fun k => ?_) isOpen_ball (fun k z hz => norm_term_le_decay hdec hq0 hq1 j k hz)
  fun_prop

lemma hasDerivAt_Hj (hdec : ∀ k, ‖b h k‖ ≤ A * q ^ k) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (j : ℕ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) (radius q)) :
    HasDerivAt (Hj h j) (Hj h (j + 1) z) z := by
  have hd := (differentiableOn_Hj hdec hq0 hq1 j).differentiableAt (isOpen_ball.mem_nhds hz)
  have hs := Complex.hasSum_deriv_of_summable_norm (summable_decay_bound hq0 hq1 j)
    (F := fun k (w : ℂ) => b h k * (k.descFactorial j : ℂ) * w ^ (k - j))
    (fun k => by fun_prop) isOpen_ball
    (fun k w hw => norm_term_le_decay hdec hq0 hq1 j k hw) hz
  have hval : deriv (Hj h j) z = Hj h (j + 1) z := by
    refine (hs.tsum_eq.symm.trans ?_).symm.symm
    unfold Hj
    congr 1
    funext k
    rw [deriv_const_mul _ (by fun_prop), deriv_pow_field, Nat.descFactorial_succ]
    push_cast
    rw [show k - (j + 1) = k - j - 1 by omega]
    rcases Nat.lt_or_ge k j with hkj | hkj
    · simp [Nat.descFactorial_eq_zero_iff_lt.2 hkj]
    · rw [Nat.cast_sub hkj]; ring
  rw [← hval]
  exact hd.hasDerivAt

theorem iteratedDeriv_H (hdec : ∀ k, ‖b h k‖ ≤ A * q ^ k) (hq0 : 0 ≤ q) (hq1 : q < 1) (j : ℕ) :
    ∀ z ∈ ball (0 : ℂ) (radius q), iteratedDeriv j (H h) z = Hj h j z := by
  induction j with
  | zero => intro z _; simp [H]
  | succ j ih =>
    intro z hz
    rw [iteratedDeriv_succ]
    have hev : iteratedDeriv j (H h) =ᶠ[𝓝 z] Hj h j :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) ih
    rw [hev.deriv_eq]
    exact (hasDerivAt_Hj hdec hq0 hq1 j hz).deriv

lemma differentiableOn_H (hdec : ∀ k, ‖b h k‖ ≤ A * q ^ k) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    DifferentiableOn ℂ (H h) (ball 0 (radius q)) :=
  differentiableOn_Hj hdec hq0 hq1 0

end Decay

/-- **Geometric decay of the Schwarz coefficients of a real-analytic periodic function.** -/
theorem exists_decay {h : ℝ → ℝ} (hA : AnalyticOnNhd ℝ h univ)
    (hper : Function.Periodic h (2 * π)) :
    ∃ A q : ℝ, 0 < q ∧ q < 1 ∧ ∀ k, ‖b h k‖ ≤ A * q ^ k := by
  have hsm : ContDiff ℝ ∞ h := hA.contDiff
  have hAc : AnalyticOnNhd ℝ (hc h) univ := fun x _ =>
    (Complex.ofRealCLM.analyticAt _).comp (hA x (mem_univ x))
  obtain ⟨C, hC, r, hr, hbd⟩ :=
    RealAnalyticBounds.exists_iteratedDeriv_bound_periodic hAc Real.two_pi_pos (periodic_hc hper)
  set s := r * Real.exp (-1) with hs
  have hs0 : 0 < s := by positivity
  refine ⟨2 * C * Real.exp 1, Real.exp (-s), Real.exp_pos _, by
    rw [Real.exp_lt_one_iff]; linarith, fun k => ?_⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [b, if_true, pow_zero, mul_one]
    have := norm_fc_le (hc h) 0 (M := C) (fun x => by simpa using hbd x 0)
    have h1 : 1 ≤ Real.exp 1 := by
      rw [Real.one_le_exp_iff]; norm_num
    calc ‖coef h 0‖ ≤ C := this
      _ ≤ 2 * C * Real.exp 1 := by nlinarith
  · simp only [b, hk.ne', if_false]
    set m := ⌊s * k⌋₊ with hm
    have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
    have hfc := norm_fc_le_of_iteratedDeriv (contDiff_hc hsm) (periodic_hc hper)
      (n := (k : ℤ)) (by exact_mod_cast hk.ne') m (fun x => hbd x m)
    rw [show |((k : ℤ) : ℝ)| = (k : ℝ) by push_cast; exact abs_of_pos hkpos] at hfc
    have hm_le : (m : ℝ) ≤ s * k := Nat.floor_le (by positivity)
    have hm_gt : s * k < m + 1 := Nat.lt_floor_add_one _
    have hfact : (m ! : ℝ) ≤ (m : ℝ) ^ m := by exact_mod_cast Nat.factorial_le_pow m
    have key : C * m ! / r ^ m / (k : ℝ) ^ m ≤ C * Real.exp 1 * Real.exp (-s) ^ k := by
      have h1 : C * m ! / r ^ m / (k : ℝ) ^ m ≤ C * (s * k) ^ m / (r * k) ^ m := by
        rw [div_div, ← mul_pow]
        gcongr
        exact hfact.trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hm_le m)
      have h2 : C * (s * k) ^ m / (r * k) ^ m = C * Real.exp (-(m : ℝ)) := by
        rw [mul_div_assoc, ← div_pow, show s * k / (r * k) = Real.exp (-1) by
          rw [hs]; field_simp]
        rw [← Real.exp_nat_mul]; ring_nf
      have h3 : Real.exp (-(m : ℝ)) ≤ Real.exp 1 * Real.exp (-s) ^ k := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith)
      calc C * m ! / r ^ m / (k : ℝ) ^ m ≤ C * Real.exp (-(m : ℝ)) := h1.trans h2.le
        _ ≤ C * (Real.exp 1 * Real.exp (-s) ^ k) := by gcongr
        _ = C * Real.exp 1 * Real.exp (-s) ^ k := by ring
    rw [norm_mul, Complex.norm_ofNat]
    calc 2 * ‖coef h k‖ ≤ 2 * (C * Real.exp 1 * Real.exp (-s) ^ k) := by
          gcongr; exact hfc.trans key
      _ = 2 * C * Real.exp 1 * Real.exp (-s) ^ k := by ring

end OuterFunction

end
