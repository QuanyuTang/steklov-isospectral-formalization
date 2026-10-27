module

public import Mathlib
public import RequestProject.SteklovRegularity
public import RequestProject.FourierCircle

/-!
# Harmonic functions from exponentially decaying Fourier coefficients

If `F : ℤ → ℂ` satisfies `F(-n) = conj F(n)` and `|F(n)| λ^{|n|} ≤ D` with `λ > 1`, the series
`∑ F(n) r^{|n|} e^{inθ} = Re(2 ∑_{n ≥ 0} F(n) zⁿ - F(0))` defines a function harmonic on the
disk `|z| < λ`; after a smooth cut-off it is a globally smooth function that is harmonic on a
disk of radius `> 1` and has boundary values `∑ F(n) e^{int}` on the unit circle
(`SteklovBoundary.exists_harmonic_of_decay`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Real InnerProductSpace Laplacian
open scoped ENNReal ContDiff ComplexConjugate

noncomputable section

namespace SteklovBoundary

open SteklovH1 SteklovFourier

/-- The point `e^{it}` of the unit circle. -/
abbrev ee (t : ℝ) : ℂ := Complex.exp (t * Complex.I)

/-- Coefficients of `Φ(z) = 2 ∑_{n ≥ 0} F(n) zⁿ - F(0)`. -/
def phiCoeff (F : ℤ → ℂ) (n : ℕ) : ℂ := 2 * F n - if n = 0 then F 0 else 0

/-- The power series `Φ(z) = ∑ phiCoeff F n zⁿ`. -/
def seriesPhi (F : ℤ → ℂ) (z : ℂ) : ℂ := ∑' n : ℕ, phiCoeff F n * z ^ n

variable {F : ℤ → ℂ} {lam D : ℝ}

lemma norm_F_le (hlam : 1 < lam) (hD : ∀ n, ‖F n‖ * lam ^ n.natAbs ≤ D) (n : ℕ) :
    ‖F n‖ ≤ D * lam⁻¹ ^ n := by
  have hp : 0 < lam ^ n := pow_pos (by linarith) _
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hp]
  simpa using hD n

lemma norm_phiCoeff_le (hlam : 1 < lam) (hD : ∀ n, ‖F n‖ * lam ^ n.natAbs ≤ D) (n : ℕ) :
    ‖phiCoeff F n‖ ≤ 3 * D * lam⁻¹ ^ n := by
  have h1 := norm_F_le hlam hD n
  have hD0 : 0 ≤ D := (by simpa using (norm_nonneg (F 0)).trans (by simpa using hD 0) : (0:ℝ) ≤ D)
  have hq : 0 ≤ lam⁻¹ ^ n := pow_nonneg (inv_nonneg.2 (by linarith)) _
  have h2 : ‖(if n = 0 then F 0 else 0 : ℂ)‖ ≤ D * lam⁻¹ ^ n := by
    split_ifs with h
    · subst h; simpa using h1
    · simp; positivity
  calc ‖phiCoeff F n‖ ≤ ‖2 * F n‖ + ‖(if n = 0 then F 0 else 0 : ℂ)‖ := norm_sub_le _ _
    _ ≤ 2 * (D * lam⁻¹ ^ n) + D * lam⁻¹ ^ n := by
        rw [norm_mul]; simp only [Complex.norm_ofNat]; linarith
    _ = 3 * D * lam⁻¹ ^ n := by ring

lemma differentiableOn_seriesPhi (hlam : 1 < lam) (hD : ∀ n, ‖F n‖ * lam ^ n.natAbs ≤ D)
    {s : ℝ} (hs : s < lam) : DifferentiableOn ℂ (seriesPhi F) (ball 0 s) := by
  rcases le_or_gt s 0 with hs0 | hs0
  · rw [ball_eq_empty.2 hs0]; exact differentiableOn_empty
  have hq0 : 0 ≤ s * lam⁻¹ := by positivity
  have hq1 : s * lam⁻¹ < 1 := by rw [← div_eq_mul_inv, div_lt_one (by linarith)]; exact hs
  refine Complex.differentiableOn_tsum_of_summable_norm (u := fun n => 3 * D * (s * lam⁻¹) ^ n)
    ((summable_geometric_of_lt_one hq0 hq1).mul_left _) (fun n => by fun_prop) isOpen_ball ?_
  intro n z hz
  simp only [norm_mul, norm_pow, mul_pow]
  have hz' : ‖z‖ ≤ s := (mem_ball_zero_iff.1 hz).le
  calc ‖phiCoeff F n‖ * ‖z‖ ^ n ≤ (3 * D * lam⁻¹ ^ n) * s ^ n :=
        mul_le_mul (norm_phiCoeff_le hlam hD n) (pow_le_pow_left₀ (norm_nonneg _) hz' n)
          (by positivity) (le_trans (norm_nonneg _) (norm_phiCoeff_le hlam hD n))
    _ = 3 * D * (s ^ n * lam⁻¹ ^ n) := by ring

lemma hasSum_seriesPhi_circle (hconj : ∀ n, F (-n) = conj (F n)) (hlam : 1 < lam)
    (hD : ∀ n, ‖F n‖ * lam ^ n.natAbs ≤ D) (t : ℝ) :
    HasSum (fun n : ℤ => F n * Complex.exp (n * t * Complex.I)) ((seriesPhi F (ee t)).re : ℂ) := by
  set b : ℤ → ℂ := fun n => F n * Complex.exp (n * t * Complex.I) with hb
  have hq0 : 0 ≤ lam⁻¹ := inv_nonneg.2 (by linarith)
  have hq1 : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam
  have hbs : Summable fun n : ℤ => ‖b n‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geom_int hq0 hq1).mul_left D)
    rw [hb, norm_mul, norm_exp_int, mul_one]
    have hp : 0 < lam ^ n.natAbs := pow_pos (by linarith) _
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hp]
    exact hD n
  have hbs' : Summable b := hbs.of_norm
  have hnat : Summable fun n : ℕ => b n := hbs'.comp_injective Nat.cast_injective
  have hnat1 : Summable fun n : ℕ => b (n + 1 : ℕ) := (summable_nat_add_iff 1).2 hnat
  set A := ∑' n : ℕ, b n with hA
  have hneg : ∀ n : ℕ, b (-((n : ℤ) + 1)) = conj (b (n + 1 : ℕ)) := by
    intro n
    simp only [hb, map_mul]
    rw [show (-((n : ℤ) + 1)) = -((n + 1 : ℕ) : ℤ) by push_cast; ring, hconj, ← Complex.exp_conj]
    congr 2
    simp [Complex.conj_ofReal]
    ring
  have h2 : HasSum (fun n : ℕ => b (-((n : ℤ) + 1))) (conj (A - b 0)) := by
    have : HasSum (fun n : ℕ => b (n + 1 : ℕ)) (A - b 0) := by
      have := hnat.tsum_eq_zero_add
      rw [← hA] at this
      have h' : A - b 0 = ∑' n : ℕ, b (n + 1 : ℕ) := by
        rw [this]; simp
      rw [h']; exact hnat1.hasSum
    simp only [hneg]
    exact (Complex.hasSum_conj').2 this
  have htot := HasSum.of_nat_of_neg_add_one hnat.hasSum h2
  convert htot using 1
  have hw : ∀ n : ℕ, phiCoeff F n * ee t ^ n = 2 * b n - if n = 0 then F 0 else 0 := by
    intro n
    simp only [phiCoeff, hb]
    rw [← Complex.exp_nat_mul]
    split_ifs with h
    · subst h; simp
    · simp only [sub_zero, Int.cast_natCast]; ring_nf
  have hPhi : seriesPhi F (ee t) = 2 * A - F 0 := by
    rw [seriesPhi]
    simp only [hw]
    rw [Summable.tsum_sub (hnat.mul_left 2) ⟨_, hasSum_ite_eq 0 (F 0)⟩, tsum_mul_left,
      tsum_ite_eq]
  have hF0 : conj (F 0) = F 0 := by have := hconj 0; simp at this; exact this.symm
  have hb0 : b 0 = F 0 := by simp [hb]
  rw [hPhi, hb0, map_sub, hF0]
  apply Complex.ext
  · simp; ring
  · simp
    have := Complex.conj_eq_iff_im.1 hF0
    linarith

/-- If `F(-n) = conj F(n)` and `|F(n)| λ^{|n|} ≤ D` with `λ > 1`, then `∑ F(n) r^{|n|} e^{inθ}`
is (the restriction of) a globally smooth function harmonic on a disk of radius `> 1`. -/
theorem exists_harmonic_of_decay (hconj : ∀ n, F (-n) = conj (F n))
    (hlam : 1 < lam) (hD : ∀ n, ‖F n‖ * lam ^ n.natAbs ≤ D) :
    ∃ r > (1 : ℝ), ∃ U : smoothFns, HarmonicOnNhd (U : ℂ → ℝ) (ball 0 r) ∧
      ∀ t : ℝ, HasSum (fun n : ℤ => F n * Complex.exp (n * t * Complex.I))
        ((U : ℂ → ℝ) (ee t) : ℂ) := by
  set δ := lam - 1 with hδdef
  have hδ : 0 < δ := by linarith
  set r1 := 1 + δ / 4 with hr1
  set r2 := 1 + δ / 2 with hr2
  set s := 1 + 3 * δ / 4 with hsdef
  have hs : s < lam := by linarith
  have hΦ := differentiableOn_seriesPhi hlam hD hs
  set P : ℂ → ℝ := fun z => (seriesPhi F z).re with hP
  have hPc : ContDiffOn ℝ ∞ P (ball 0 s) :=
    Complex.reCLM.contDiff.comp_contDiffOn ((hΦ.contDiffOn isOpen_ball).restrict_scalars ℝ)
  obtain ⟨χ, hχ, hχ1, hχ0⟩ := SteklovWeyl.exists_cutoff (K := closedBall (0:ℂ) r1)
    (V := ball 0 r2) isClosed_closedBall
    (by rw [isOpen_ball.interior_eq]; exact closedBall_subset_ball (by linarith))
  set U : ℂ → ℝ := fun z => χ z * P z with hUdef
  have hU : ContDiff ℝ ∞ U := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : ‖z‖ < s
    · exact hχ.contDiffAt.mul (hPc.contDiffAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)))
    · push_neg at hz
      have hopen : IsOpen {w : ℂ | r2 < ‖w‖} := isOpen_lt continuous_const continuous_norm
      have : U =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [hopen.mem_nhds (show r2 < ‖z‖ by linarith)]
          with w hw
        have hw' : w ∉ ball (0:ℂ) r2 := by
          rw [mem_ball_zero_iff]; exact not_lt.2 (le_of_lt hw)
        simp [U, hχ0 w hw']
      exact contDiffAt_const.congr_of_eventuallyEq this
  have hK : ∀ x ∈ closedBall (0:ℂ) r1, ∀ᶠ y in 𝓝 x, χ y = 1 :=
    (eventually_nhdsSet_iff_forall.1 hχ1)
  refine ⟨r1, by linarith, ⟨U, hU⟩, ?_, ?_⟩
  · intro z hz
    have hzK : z ∈ closedBall (0:ℂ) r1 := ball_subset_closedBall hz
    have h1 : U =ᶠ[𝓝 z] P := by
      filter_upwards [hK z hzK] with w hw
      simp [U, hw]
    have hzs : z ∈ ball (0:ℂ) s := ball_subset_ball (by linarith) hz
    have hPh : HarmonicAt P z :=
      (hΦ.analyticAt (isOpen_ball.mem_nhds hzs)).harmonicAt_re
    exact (harmonicAt_congr_nhds h1).2 hPh
  · intro t
    have hKt : ee t ∈ closedBall (0:ℂ) r1 := by
      rw [mem_closedBall_zero_iff, Complex.norm_exp_ofReal_mul_I]; linarith
    have hUt : U (ee t) = P (ee t) := by
      have := (hK _ hKt).self_of_nhds
      simp [U, this]
    show HasSum _ ((U (ee t) : ℝ) : ℂ)
    rw [hUt]
    exact hasSum_seriesPhi_circle hconj hlam hD t

end SteklovBoundary
