module

public import Mathlib

/-!
# Fourier coefficients on `[0, 2π]`: integration by parts, decay and inversion

Tools for the construction of the normalized outer function in Proposition 2.3.1.

* `OuterFourier.fc f n` — the normalized Fourier coefficient
  `(1/2π) ∫_0^{2π} f(t) e^{-int} dt` (Mathlib's `fourierCoeffOn` on `[0, 2π]`).
* `OuterFourier.fc_iteratedDeriv` — for smooth `2π`-periodic `f` and `n ≠ 0`,
  `fc f n = fc f^{(m)} n / (i n)^m` (repeated integration by parts).
* `OuterFourier.norm_fc_le_of_iteratedDeriv` — `|fc f n| ≤ ‖f^{(m)}‖_∞ / |n|^m`.
* `OuterFourier.fc_neg_ofReal` — conjugate symmetry for real-valued functions.
* `OuterFourier.hasSum_fc` — pointwise Fourier inversion for continuous periodic functions with
  summable coefficients.
-/

@[expose] public section

open Real Complex MeasureTheory intervalIntegral Set Filter Topology
open scoped ContDiff

noncomputable section

namespace OuterFourier

/-- The normalized Fourier coefficient `(1/2π) ∫_0^{2π} f(t) e^{-int} dt`. -/
def fc (f : ℝ → ℂ) (n : ℤ) : ℂ := fourierCoeffOn Real.two_pi_pos f n

lemma fourier_coe_eq {T : ℝ} (hT : T = 2 * π) (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle T) = exp (n * x * I) := by
  rw [fourier_coe_apply, hT]
  congr 1
  push_cast
  field_simp [Real.pi_pos.ne']

lemma fc_eq_integral (f : ℝ → ℂ) (n : ℤ) :
    fc f n = ((1 / (2 * π) : ℝ) : ℂ) * ∫ x in (0 : ℝ)..2 * π, exp (-(n * x * I)) * f x := by
  rw [fc, fourierCoeffOn_eq_integral, sub_zero, Complex.real_smul]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [smul_eq_mul, fourier_coe_eq (by ring) (-n) x]
  push_cast; ring_nf

lemma norm_fc_le (f : ℝ → ℂ) (n : ℤ) {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) : ‖fc f n‖ ≤ M := by
  rw [fc_eq_integral, norm_mul]
  have h1 : ‖∫ x in (0 : ℝ)..2 * π, exp (-(n * x * I)) * f x‖ ≤ M * |2 * π - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => ?_
    rw [norm_mul]
    have : ‖exp (-(n * x * I))‖ = 1 := by
      rw [Complex.norm_exp]; simp
    rw [this, one_mul]; exact hM x
  have hpi : 0 < 2 * π := Real.two_pi_pos
  rw [sub_zero, abs_of_pos hpi] at h1
  have : ‖(((1 / (2 * π) : ℝ)) : ℂ)‖ = 1 / (2 * π) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [this]
  calc 1 / (2 * π) * ‖∫ x in (0 : ℝ)..2 * π, exp (-(n * x * I)) * f x‖
      ≤ 1 / (2 * π) * (M * (2 * π)) := by gcongr
    _ = M := by field_simp

/-- One integration by parts for a periodic function. -/
lemma fc_deriv {f f' : ℝ → ℂ} (hper : Function.Periodic f (2 * π))
    (hd : ∀ x, HasDerivAt f (f' x) x) (hint : IntervalIntegrable f' volume 0 (2 * π))
    {n : ℤ} (hn : n ≠ 0) : fc f n = fc f' n / (n * I) := by
  unfold fc
  rw [fourierCoeffOn_of_hasDerivAt Real.two_pi_pos hn (fun x _ => hd x) hint]
  have h2 : f (2 * π) = f 0 := by simpa using hper 0
  rw [h2, sub_self, mul_zero, zero_sub]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  field_simp
  push_cast
  ring

lemma periodic_deriv {f : ℝ → ℂ} {T : ℝ} (hper : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  rw [← deriv_comp_add_const]
  congr 1
  funext y; exact hper y

lemma periodic_iteratedDeriv {f : ℝ → ℂ} {T : ℝ} (hper : Function.Periodic f T) (m : ℕ) :
    Function.Periodic (iteratedDeriv m f) T := by
  induction m with
  | zero => simpa using hper
  | succ m ih => rw [iteratedDeriv_succ]; exact periodic_deriv ih

/-- Repeated integration by parts: `fc f n = fc f^{(m)} n / (i n)^m` for smooth periodic `f`. -/
lemma fc_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hper : Function.Periodic f (2 * π))
    {n : ℤ} (hn : n ≠ 0) (m : ℕ) : fc f n = fc (iteratedDeriv m f) n / (n * I) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hd : ∀ x, HasDerivAt (iteratedDeriv m f) (iteratedDeriv (m + 1) f x) x := by
      intro x
      rw [iteratedDeriv_succ]
      exact ((hf.differentiable_iteratedDeriv m (by exact_mod_cast WithTop.coe_lt_top _))
        x).hasDerivAt
    have hc : Continuous (iteratedDeriv (m + 1) f) :=
      hf.continuous_iteratedDeriv (m + 1) (by exact_mod_cast le_top)
    rw [ih, fc_deriv (periodic_iteratedDeriv hper m) hd (hc.intervalIntegrable _ _) hn, pow_succ,
      div_div, mul_comm (n * I)]

/-- **Fourier coefficient estimate**: `|fc f n| ≤ M / |n|^m` if `|f^{(m)}| ≤ M`. -/
lemma norm_fc_le_of_iteratedDeriv {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hper : Function.Periodic f (2 * π)) {n : ℤ} (hn : n ≠ 0) (m : ℕ) {M : ℝ}
    (hM : ∀ x, ‖iteratedDeriv m f x‖ ≤ M) : ‖fc f n‖ ≤ M / |(n : ℝ)| ^ m := by
  rw [fc_iteratedDeriv hf hper hn m, norm_div, norm_pow, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_intCast]
  have : 0 < |(n : ℝ)| := by positivity
  gcongr
  exact norm_fc_le _ _ hM

/-- Conjugate symmetry of the Fourier coefficients of a real function. -/
lemma fc_neg_ofReal (h : ℝ → ℝ) (n : ℤ) :
    fc (fun x => (h x : ℂ)) (-n) = (starRingEnd ℂ) (fc (fun x => (h x : ℂ)) n) := by
  rw [fc_eq_integral, fc_eq_integral, map_mul, Complex.conj_ofReal]
  congr 1
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, map_intCast,
    Complex.conj_I]
  push_cast; ring_nf

/-- **Fourier inversion** for a continuous `2π`-periodic function with summable coefficients. -/
lemma hasSum_fc {f : ℝ → ℂ} (hf : Continuous f) (hper : Function.Periodic f (2 * π))
    (hs : Summable (fc f)) (t : ℝ) :
    HasSum (fun n : ℤ => fc f n * exp (n * t * I)) (f t) := by
  haveI : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
  have hlift : AddCircle.liftIoc (2 * π) 0 f = hper.lift := by
    funext x
    induction x using QuotientAddGroup.induction_on with
    | H z =>
      obtain ⟨y, hy, hyz⟩ : ∃ y ∈ Ioc (0 : ℝ) (0 + 2 * π), ((y : ℝ) : AddCircle (2 * π)) = z := by
        refine ⟨AddCircle.equivIoc (2 * π) 0 z, Subtype.prop _, ?_⟩
        exact (AddCircle.equivIoc (2 * π) 0).symm_apply_apply z
      rw [← hyz]
      change AddCircle.liftIoc (2 * π) 0 f (y : AddCircle (2 * π)) = f y
      exact AddCircle.liftIoc_coe_apply hy
  let F : C(AddCircle (2 * π), ℂ) :=
    ⟨AddCircle.liftIoc (2 * π) 0 f, by
      rw [hlift]; exact continuous_quot_lift _ hf⟩
  have hcoef : ∀ n, fourierCoeff F n = fc f n := by
    intro n
    change fourierCoeff (AddCircle.liftIoc (2 * π) 0 f) n = _
    rw [fourierCoeff_liftIoc_eq, fourierCoeffOn_eq_integral, fc, fourierCoeffOn_eq_integral]
    simp only [zero_add, sub_zero]
    congr 1
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [smul_eq_mul]
    rw [fourier_coe_eq (by ring) (-n) x, fourier_coe_eq (by ring) (-n) x]
  have hsF : Summable (fourierCoeff F) := by
    rw [show fourierCoeff F = fc f from funext hcoef]; exact hs
  have := has_pointwise_sum_fourier_series_of_summable hsF (t : AddCircle (2 * π))
  have hFt : F (t : AddCircle (2 * π)) = f t := by
    change AddCircle.liftIoc (2 * π) 0 f (t : AddCircle (2 * π)) = f t
    rw [hlift]; rfl
  rw [hFt] at this
  convert this using 2 with n
  rw [hcoef, smul_eq_mul, fourier_coe_eq rfl]

end OuterFourier

end
