module

public import Mathlib
public import RequestProject.BoundaryRegularity

/-!
# `|g|` is a real-analytic weight for `g` holomorphic and nonvanishing near the circle

`SteklovBoundary.isAnalyticWeight_norm`: if `g` is holomorphic on an open set containing the
unit circle and has no zeros on the circle, then `ρ = |g|` satisfies
`SteklovBoundary.IsAnalyticWeight`: its Fourier coefficients decay exponentially and its Fourier
series converges to it pointwise.

Proof: `|g(w)|² = Q(w) := g(w) · conj(g(conj(w⁻¹)))` on the circle, `Q` is holomorphic near the
circle with positive real part, so `S = Q^{1/2}` is holomorphic on a closed annulus
`1 - ε ≤ |w| ≤ 1 + ε` and equals `|g|` on the circle. The Fourier coefficients of `S(e^{it})`
are contour integrals `(2πi)⁻¹ ∮ S(w) w^{-k-1} dw`, which may be computed on the circles
`|w| = 1 ± ε` (Cauchy's theorem on an annulus), giving `|ρ̂(k)| ≤ M q^{|k|}` with `q < 1`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Real
open scoped ComplexConjugate

noncomputable section

namespace SteklovBoundary

open SteklovFourier

/-- The reflected product `Q(w) = g(w) · conj(g(conj(w⁻¹)))`. -/
def reflQ (g : ℂ → ℂ) (w : ℂ) : ℂ := g w * conj (g (conj w⁻¹))

lemma conj_inv_of_norm_one {w : ℂ} (hw : ‖w‖ = 1) : conj w⁻¹ = w := by
  have hw0 : w ≠ 0 := by rintro rfl; simp at hw
  rw [map_inv₀, Complex.inv_def, Complex.conj_conj, Complex.normSq_eq_norm_sq]
  simp [hw]

lemma reflQ_of_norm_one (g : ℂ → ℂ) {w : ℂ} (hw : ‖w‖ = 1) :
    reflQ g w = ((‖g w‖ ^ 2 : ℝ) : ℂ) := by
  rw [reflQ, conj_inv_of_norm_one hw, Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma differentiableAt_reflQ {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) {w : ℂ} (hw0 : w ≠ 0) (hw : w ∈ U) (hw' : conj w⁻¹ ∈ U) :
    DifferentiableAt ℂ (reflQ g) w := by
  have h1 : DifferentiableAt ℂ g w := hg.differentiableAt (hU.mem_nhds hw)
  have h2 : DifferentiableAt ℂ g (conj w⁻¹) := hg.differentiableAt (hU.mem_nhds hw')
  have h3 := h2.conj_conj
  rw [Complex.conj_conj] at h3
  have h4 : DifferentiableAt ℂ (fun z : ℂ => z⁻¹) w := differentiableAt_inv hw0
  exact h1.mul (h3.comp w h4)

/-- A thin open neighbourhood of the circle on which `Q` is holomorphic with positive real
part. -/
lemma exists_thickening {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hcb : sphere (0:ℂ) 1 ⊆ U)
    (hg : DifferentiableOn ℂ g U) (hne : ∀ z ∈ sphere (0:ℂ) 1, g z ≠ 0) :
    ∃ δ > 0, ∀ w ∈ thickening δ (sphere (0:ℂ) 1),
      DifferentiableAt ℂ (reflQ g) w ∧ 0 < (reflQ g w).re := by
  have hc : ContinuousOn (fun w : ℂ => conj w⁻¹) {w | w ≠ 0} :=
    (Complex.continuous_conj.comp_continuousOn (continuousOn_inv₀))
  have hW : IsOpen ({w : ℂ | w ≠ 0} ∩ (fun w : ℂ => conj w⁻¹) ⁻¹' U ∩ U) :=
    (hc.isOpen_inter_preimage isOpen_ne hU).inter hU
  set W := {w : ℂ | w ≠ 0} ∩ (fun w : ℂ => conj w⁻¹) ⁻¹' U ∩ U with hWdef
  have hdiff : ∀ w ∈ W, DifferentiableAt ℂ (reflQ g) w := fun w hw =>
    differentiableAt_reflQ hU hg hw.1.1 hw.2 hw.1.2
  have hcont : ContinuousOn (fun w => (reflQ g w).re) W := fun w hw =>
    (Complex.continuous_re.continuousAt.comp (hdiff w hw).continuousAt).continuousWithinAt
  have hW' := hcont.isOpen_inter_preimage hW (isOpen_Ioi (a := (0:ℝ)))
  have hsub : sphere (0:ℂ) 1 ⊆ W ∩ (fun w => (reflQ g w).re) ⁻¹' Ioi 0 := by
    intro w hw
    have hw1 : ‖w‖ = 1 := by simpa using hw
    refine ⟨⟨⟨?_, ?_⟩, hcb hw⟩, ?_⟩
    · rintro rfl; simp at hw1
    · show conj w⁻¹ ∈ U; rw [conj_inv_of_norm_one hw1]; exact hcb hw
    · show 0 < (reflQ g w).re
      rw [reflQ_of_norm_one g hw1, Complex.ofReal_re]
      exact pow_pos (norm_pos_iff.2 (hne w hw)) 2
  obtain ⟨δ, hδ, hth⟩ := (isCompact_sphere (0:ℂ) 1).exists_thickening_subset_open hW' hsub
  exact ⟨δ, hδ, fun w hw => ⟨hdiff w (hth hw).1, (hth hw).2⟩⟩

lemma mem_thickening_of_annulus {δ ε : ℝ} (hεδ : ε < δ) (hε1 : ε < 1) {w : ℂ}
    (h1 : 1 - ε ≤ ‖w‖) (h2 : ‖w‖ ≤ 1 + ε) : w ∈ thickening δ (sphere (0:ℂ) 1) := by
  rw [mem_thickening_iff]
  have hn : 0 < ‖w‖ := by linarith
  have hw0 : w ≠ 0 := norm_pos_iff.1 hn
  refine ⟨w / ‖w‖, by simp [hw0], ?_⟩
  rw [dist_eq_norm]
  have : w - w / ‖w‖ = ((1 - ‖w‖⁻¹ : ℝ) : ℂ) * w := by
    push_cast; field_simp
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have : |1 - ‖w‖⁻¹| * ‖w‖ = |‖w‖ - 1| := by
    rw [← abs_of_pos hn, ← abs_mul, abs_of_pos hn]; congr 1; field_simp
  rw [this]
  exact lt_of_le_of_lt (abs_le.2 ⟨by linarith, by linarith⟩) hεδ

/-- The Fourier coefficient of `S(e^{it})` as a contour integral over the unit circle. -/
lemma circleIntegral_eq_fc (S : ℂ → ℂ) (k : ℤ) :
    (∮ w in C(0, 1), S w * w ^ (-(k + 1))) =
      (2 * π * Complex.I) * fc (fun t => S (ee t)) k := by
  rw [circleIntegral, fc, intervalIntegral.integral_of_le (by positivity)]
  rw [show (2 * π * Complex.I) * (((2 * π : ℝ) : ℂ)⁻¹ * ∫ t in Ioc 0 (2 * π),
      Complex.exp (-(k * t * Complex.I)) * S (ee t)) = ∫ t in Ioc 0 (2 * π),
      Complex.I * (Complex.exp (-(k * t * Complex.I)) * S (ee t)) by
    rw [integral_const_mul]; push_cast; field_simp]
  refine setIntegral_congr_fun measurableSet_Ioc fun θ _ => ?_
  simp only [deriv_circleMap, circleMap_zero, Complex.ofReal_one, one_mul, smul_eq_mul]
  rw [← Complex.exp_int_mul]
  have : Complex.exp (θ * Complex.I) * Complex.exp (((-(k + 1) : ℤ) : ℂ) * (θ * Complex.I)) =
      Complex.exp (-(k * θ * Complex.I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  calc Complex.exp (θ * Complex.I) * Complex.I * (S (Complex.exp (θ * Complex.I)) *
        Complex.exp (((-(k + 1) : ℤ) : ℂ) * (θ * Complex.I)))
      = Complex.I * ((Complex.exp (θ * Complex.I) *
          Complex.exp (((-(k + 1) : ℤ) : ℂ) * (θ * Complex.I))) * S (ee θ)) := by ring
    _ = _ := by rw [this]

/-- **Coefficient decay from holomorphy on an annulus.** -/
lemma norm_fc_le_of_annulus {S : ℂ → ℂ} {ε M : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hSd : ∀ w : ℂ, 1 - ε ≤ ‖w‖ → ‖w‖ ≤ 1 + ε → DifferentiableAt ℂ S w)
    (hM : ∀ w : ℂ, 1 - ε ≤ ‖w‖ → ‖w‖ ≤ 1 + ε → ‖S w‖ ≤ M) (k : ℤ) :
    ‖fc (fun t => S (ee t)) k‖ ≤ M * (max (1 + ε)⁻¹ (1 - ε)) ^ k.natAbs := by
  set F : ℂ → ℂ := fun w => S w * w ^ (-(k + 1)) with hF
  have hFd : ∀ w : ℂ, 1 - ε ≤ ‖w‖ → ‖w‖ ≤ 1 + ε → DifferentiableAt ℂ F w := by
    intro w h1 h2
    have hw0 : w ≠ 0 := norm_pos_iff.1 (by linarith)
    exact (hSd w h1 h2).mul (differentiableAt_zpow.2 (Or.inl hw0))
  have hFb : ∀ R : ℝ, 1 - ε ≤ R → R ≤ 1 + ε → ∀ z ∈ sphere (0:ℂ) R,
      ‖F z‖ ≤ M * R ^ (-(k + 1)) := by
    intro R h1 h2 z hz
    have hzR : ‖z‖ = R := by simpa using hz
    rw [hF, norm_mul, norm_zpow, hzR]
    exact mul_le_mul_of_nonneg_right (hM z (hzR ▸ h1) (hzR ▸ h2)) (zpow_nonneg (by linarith) _)
  have hc := circleIntegral_eq_fc S k
  have hnorm : ‖(∮ w in C(0, 1), F w)‖ = 2 * π * ‖fc (fun t => S (ee t)) k‖ := by
    rw [hc, norm_mul]; simp [abs_of_pos Real.pi_pos]
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 1 (by simp; linarith) (by simp; linarith))
  have hq1 : (1 + ε)⁻¹ ≤ max (1 + ε)⁻¹ (1 - ε) := le_max_left _ _
  have hq2 : 1 - ε ≤ max (1 + ε)⁻¹ (1 - ε) := le_max_right _ _
  rcases le_or_gt 0 k with hk | hk
  · -- outer circle `|w| = 1 + ε`
    obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hk
    have heq := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (c := 0) (r := 1) (R := 1 + ε) (f := F) one_pos (by linarith) countable_empty
      (fun w hw => (hFd w (by
          have := hw.2; simp only [mem_ball, dist_zero_right, not_lt] at this; linarith)
        (by have := hw.1; simpa using this)).continuousAt.continuousWithinAt)
      (fun w hw => hFd w (by
          have := hw.1.2; simp only [mem_closedBall, dist_zero_right, not_le] at this; linarith)
        (by have := hw.1.1; simp only [mem_ball, dist_zero_right] at this; linarith))
    have hb := circleIntegral.norm_integral_le_of_norm_le_const (by linarith)
      (hFb (1 + ε) (by linarith) le_rfl)
    rw [heq, hnorm] at hb
    have hpos : 0 < 1 + ε := by linarith
    have e1 : (1 + ε) * (1 + ε) ^ (-((m : ℤ) + 1)) = (1 + ε)⁻¹ ^ m := by
      rw [show -((m : ℤ) + 1) = -((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast,
        inv_pow, pow_succ]
      field_simp
    have h3 : ‖fc (fun t => S (ee t)) (m : ℤ)‖ ≤ M * (1 + ε)⁻¹ ^ m := by
      have : 2 * π * ‖fc (fun t => S (ee t)) (m : ℤ)‖ ≤ 2 * π * (M * (1 + ε)⁻¹ ^ m) := by
        calc _ ≤ 2 * π * (1 + ε) * (M * (1 + ε) ^ (-((m : ℤ) + 1))) := hb
          _ = 2 * π * (M * ((1 + ε) * (1 + ε) ^ (-((m : ℤ) + 1)))) := by ring
          _ = _ := by rw [e1]
      exact le_of_mul_le_mul_left this (by positivity)
    refine h3.trans (mul_le_mul_of_nonneg_left ?_ hM0)
    simp only [Int.natAbs_natCast]
    exact pow_le_pow_left₀ (by positivity) hq1 m
  · -- inner circle `|w| = 1 - ε`
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -((m : ℤ) + 1) := ⟨(-k - 1).toNat, by omega⟩
    subst hm
    have heq := Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable
      (c := 0) (r := 1 - ε) (R := 1) (f := F) (by linarith) (by linarith) countable_empty
      (fun w hw => (hFd w (by
          have := hw.2; simp only [mem_ball, dist_zero_right, not_lt] at this; linarith)
        (by have := hw.1; simp only [mem_closedBall, dist_zero_right] at this; linarith)).continuousAt.continuousWithinAt)
      (fun w hw => hFd w (by
          have := hw.1.2; simp only [mem_closedBall, dist_zero_right, not_le] at this; linarith)
        (by have := hw.1.1; simp only [mem_ball, dist_zero_right] at this; linarith))
    have hb := circleIntegral.norm_integral_le_of_norm_le_const (by linarith)
      (hFb (1 - ε) le_rfl (by linarith))
    rw [← heq, hnorm] at hb
    have e1 : (1 - ε) * (1 - ε) ^ (-(-((m : ℤ) + 1) + 1)) = (1 - ε) ^ (m + 1) := by
      rw [show -(-((m : ℤ) + 1) + 1) = ((m : ℕ) : ℤ) by ring, zpow_natCast, pow_succ]; ring
    have h3 : ‖fc (fun t => S (ee t)) (-((m : ℤ) + 1))‖ ≤ M * (1 - ε) ^ (m + 1) := by
      have : 2 * π * ‖fc (fun t => S (ee t)) (-((m : ℤ) + 1))‖ ≤
          2 * π * (M * (1 - ε) ^ (m + 1)) := by
        calc _ ≤ 2 * π * (1 - ε) * (M * (1 - ε) ^ (-(-((m : ℤ) + 1) + 1))) := hb
          _ = 2 * π * (M * ((1 - ε) * (1 - ε) ^ (-(-((m : ℤ) + 1) + 1)))) := by ring
          _ = _ := by rw [e1]
      exact le_of_mul_le_mul_left this (by positivity)
    refine h3.trans (mul_le_mul_of_nonneg_left ?_ hM0)
    have : (-((m : ℤ) + 1)).natAbs = m + 1 := by omega
    rw [this]
    exact pow_le_pow_left₀ (by linarith) hq2 _

/-- **`|g|` is a real-analytic weight.** -/
theorem isAnalyticWeight_norm {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hcb : sphere (0:ℂ) 1 ⊆ U) (hg : DifferentiableOn ℂ g U)
    (hne : ∀ z ∈ sphere (0:ℂ) 1, g z ≠ 0) : IsAnalyticWeight fun z => ‖g z‖ := by
  obtain ⟨δ, hδ, hth⟩ := exists_thickening hU hcb hg hne
  set ε := min (δ / 2) (1 / 2) with hεdef
  have hε0 : 0 < ε := lt_min (by linarith) (by norm_num)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  set S : ℂ → ℂ := fun w => reflQ g w ^ (1 / 2 : ℂ) with hS
  have hA : ∀ w : ℂ, 1 - ε ≤ ‖w‖ → ‖w‖ ≤ 1 + ε → w ∈ thickening δ (sphere (0:ℂ) 1) :=
    fun w h1 h2 => mem_thickening_of_annulus hεδ hε1 h1 h2
  have hSd : ∀ w : ℂ, 1 - ε ≤ ‖w‖ → ‖w‖ ≤ 1 + ε → DifferentiableAt ℂ S w := by
    intro w h1 h2
    have h := hth w (hA w h1 h2)
    exact h.1.cpow_const (Complex.mem_slitPlane_iff.2 (Or.inl h.2))
  have hScirc : ∀ t : ℝ, S (ee t) = ((‖g (ee t)‖ : ℝ) : ℂ) := by
    intro t
    have hn : ‖ee t‖ = 1 := Complex.norm_exp_ofReal_mul_I t
    simp only [hS]
    rw [reflQ_of_norm_one g hn, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  set K := {w : ℂ | 1 - ε ≤ ‖w‖ ∧ ‖w‖ ≤ 1 + ε} with hKdef
  have hKc : IsCompact K := by
    refine (isCompact_closedBall (0:ℂ) (1 + ε)).of_isClosed_subset ?_ ?_
    · exact (isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)
    · intro w hw; simpa using hw.2
  obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn
    (fun w hw => (hSd w hw.1 hw.2).continuousAt.continuousWithinAt)
  set q := max (1 + ε)⁻¹ (1 - ε) with hq
  have hq0 : 0 ≤ q := (show (0:ℝ) ≤ 1 - ε by linarith).trans (le_max_right _ _)
  have hq1 : q < 1 := max_lt (inv_lt_one_of_one_lt₀ (by linarith)) (by linarith)
  set f : ℝ → ℂ := fun t => ((‖g (ee t)‖ : ℝ) : ℂ) with hf
  have hfS : (fun t => S (ee t)) = f := funext hScirc
  have hbound : ∀ k, ‖fc f k‖ ≤ M * q ^ k.natAbs := by
    intro k
    rw [← hfS]
    exact norm_fc_le_of_annulus hε0 hε1 hSd (fun w h1 h2 => hM w ⟨h1, h2⟩) k
  have hgc : ContinuousOn g (sphere (0:ℂ) 1) := hg.continuousOn.mono hcb
  have hee : Continuous ee := by fun_prop
  have hfc : Continuous f := by
    refine Complex.continuous_ofReal.comp (continuous_norm.comp ?_)
    exact hgc.comp_continuous hee (fun t => by simp [Complex.norm_exp_ofReal_mul_I])
  have hfper : Function.Periodic f (2 * π) := by
    intro t
    simp only [hf, ee]
    congr 3
    rw [show ((t + 2 * π : ℝ) : ℂ) * Complex.I = t * Complex.I + 2 * π * Complex.I by
      push_cast; ring, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
  have hsum : Summable fun n => ‖fc f n‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
      ((summable_geom_int hq0 hq1).mul_left M)
  exact ⟨fc f, M, q, hq0, hq1, hbound, fun t => hasSum_fc hfc hfper hsum t⟩

end SteklovBoundary
