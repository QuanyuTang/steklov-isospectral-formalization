module

public import Mathlib
public import RequestProject.DomainH1
public import RequestProject.ConformalPullback
public import RequestProject.BoundaryLength

/-!
# Trace inequality and the `H¹` bridge for conformal images of the disk

Let `G` be holomorphic on a neighbourhood of `𝔻̄`, injective on `𝔻̄`, with `G' ≠ 0` on `𝕋`, and
`Ω = G(𝔻)`. We prove:

* `SteklovH1.bddDomain_image`: `Ω` is a bounded open set with boundary of finite length;
* `SteklovH1.traceIneq_image`: the trace inequality
  `∫_{∂Ω} u² dH¹ ≤ C (∫_Ω u² + ∫_Ω |∇u|²)` for all globally smooth `u`. Proof: pull back by
  `G` (arc-length change of variables on `𝕋`, area change of variables with Jacobian `|G'|²`,
  conformal invariance of the energy), and apply the disk trace inequality
  `SteklovH1.trace_ineq_lintegral` to the smooth cut-off of `u ∘ G`;
* `SteklovH1.steklovSpectrum_image_eq_h1`: `Steklov.steklovSpectrum Ω` equals the `H¹(Ω)`
  min–max spectrum `SteklovH1.h1SteklovSpectrum Ω`, for every index.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Real

noncomputable section

namespace SteklovH1

open Classical in
/-- The `H¹(Ω)` variational Steklov spectrum of a set `Ω ⊆ ℂ`: defined (as the min–max values
over subspaces of `H¹(Ω)`) when `Ω` is a bounded open set whose boundary has finite length,
and `⊤` otherwise. -/
def h1SteklovSpectrum (Ω : Set ℂ) : ℕ → ℝ≥0∞ :=
  if h : IsOpen Ω ∧ Bornology.IsBounded Ω ∧ Measure.hausdorffMeasure 1 (frontier Ω) ≠ ⊤ then
    (BddDomain.mk Ω h.1 h.2.1 h.2.2).h1SteklovEigenvalue
  else fun _ => ⊤

variable {G : ℂ → ℂ} {U : Set ℂ}

open ConformalPullback in
/-- `G(𝔻)` is a bounded open set whose boundary has finite length. -/
theorem bddDomain_image (hU : IsOpen U) (hcb : closedBall (0 : ℂ) 1 ⊆ U)
    (hG : DifferentiableOn ℂ G U) (hinj : InjOn G (closedBall 0 1))
    (hG' : ∀ z ∈ sphere (0 : ℂ) 1, deriv G z ≠ 0) :
    IsOpen (G '' ball 0 1) ∧ Bornology.IsBounded (G '' ball 0 1) ∧
      Measure.hausdorffMeasure 1 (frontier (G '' ball 0 1)) ≠ ⊤ := by
  obtain ⟨U', hU', hcb', hU'U, hinj', hd'⟩ :=
    HolInv.exists_open_nbhd_injOn_deriv_ne_zero hU hcb hG hinj hG'
  have hG₁ : DifferentiableOn ℂ G U' := hG.mono hU'U
  refine ⟨HolInv.isOpen_image hG₁ hinj' (ball_subset_closedBall.trans hcb') isOpen_ball, ?_, ?_⟩
  · exact ((isCompact_closedBall (0:ℂ) 1).image_of_continuousOn
      (hG₁.continuousOn.mono hcb')).isBounded.subset (image_mono ball_subset_closedBall)
  · have hlen := BoundaryLength.boundaryLength_image_ball hU' hcb' hG₁ (hinj'.mono hcb')
    unfold PlaneDomain.boundaryLength at hlen
    rw [hlen]
    have hdc : ContinuousOn (fun z => ‖deriv G z‖) U' := ((hG₁.deriv hU').continuousOn).norm
    obtain ⟨M, hM⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn
      (hdc.mono hcb')
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in Ioc 0 (2 * π), ENNReal.ofReal M) ?_ ?_
    · rw [setLIntegral_const, Real.volume_Ioc]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        ENNReal.ofReal_ne_top
    · refine lintegral_mono (fun t => ENNReal.ofReal_le_ofReal ?_)
      have := hM _ (sphere_subset_closedBall (exp_mem_sphere t))
      simpa using this

open ConformalPullback in
/-- **Trace inequality on `G(𝔻)`.** -/
theorem traceIneq_image (hU : IsOpen U) (hcb : closedBall (0 : ℂ) 1 ⊆ U)
    (hG : DifferentiableOn ℂ G U) (hinj : InjOn G (closedBall 0 1))
    (hG' : ∀ z ∈ sphere (0 : ℂ) 1, deriv G z ≠ 0) :
    ∃ C : ℝ, ∀ u : ℂ → ℝ, ContDiff ℝ ∞ u →
      Steklov.boundaryMass (G '' ball 0 1) u ≤
        ENNReal.ofReal C * ((∫⁻ z in G '' ball 0 1, ‖u z‖ₑ ^ 2) +
          Steklov.dirichletEnergy (G '' ball 0 1) u) := by
  obtain ⟨U', hU', hcb', hU'U, hinj', hd'⟩ :=
    HolInv.exists_open_nbhd_injOn_deriv_ne_zero hU hcb hG hinj hG'
  have hG₁ : DifferentiableOn ℂ G U' := hG.mono hU'U
  have hGs : ContDiffOn ℝ ∞ G U' := contDiffOn_of_differentiableOn hU' hG₁
  have hdc : ContinuousOn (fun z => ‖deriv G z‖) U' := ((hG₁.deriv hU').continuousOn).norm
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn (hdc.mono hcb')
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall (0:ℂ) 1).exists_isMinOn
    ⟨0, mem_closedBall_self zero_le_one⟩ (hdc.mono hcb')
  set m := ‖deriv G z₀‖ with hm_def
  have hm : 0 < m := norm_pos_iff.2 (hd' z₀ (hcb' hz₀))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (mem_closedBall_self zero_le_one))
  obtain ⟨χ, hχ, ⟨W, hW, hKW, hχone⟩, hsupp⟩ :=
    exists_cutoff (isCompact_closedBall (0 : ℂ) 1) hU' hcb'
  refine ⟨M * (3 / m ^ 2 + 1), fun u hu => ?_⟩
  set w : ℂ → ℝ := cutoffComp χ G u with hw_def
  have hw : ContDiff ℝ ∞ w := contDiff_mul_comp hU' hχ hsupp hGs hu
  have hwe : EqOn w (u ∘ G) (closedBall 0 1) := by
    intro z hz
    simp only [hw_def, Function.comp, cutoffComp_apply]
    rw [hχone z (hKW hz), one_mul]
  have hball : ball (0:ℂ) 1 ⊆ U' := ball_subset_closedBall.trans hcb'
  -- boundary term
  have h1 : Steklov.boundaryMass (G '' ball 0 1) u =
      Steklov.weightedBoundaryMass (fun z => ‖deriv G z‖) w := by
    rw [boundaryMass_image hU' hcb' hG₁ (hinj'.mono hcb') hu.continuous]
    exact weightedBoundaryMass_congr _ (hwe.symm.mono sphere_subset_closedBall)
  have h2 : Steklov.weightedBoundaryMass (fun z => ‖deriv G z‖) w ≤
      ENNReal.ofReal M * ∫⁻ t in Ioc 0 (2 * π), ‖w (Complex.exp (t * Complex.I))‖ₑ ^ 2 := by
    unfold Steklov.weightedBoundaryMass
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono (fun t => ?_)
    rw [mul_comm (‖w _‖ₑ ^ 2)]
    refine mul_le_mul' ?_ le_rfl
    refine ENNReal.ofReal_le_ofReal ?_
    have := hM _ (sphere_subset_closedBall (exp_mem_sphere t))
    simpa using this
  have h3 := trace_ineq_lintegral (hw.of_le (by exact_mod_cast le_top) : ContDiff ℝ 1 w)
  -- energy term
  have h4 : ∫⁻ z in ball (0:ℂ) 1, ‖fderiv ℝ w z‖ₑ ^ 2 =
      Steklov.dirichletEnergy (G '' ball 0 1) u := by
    rw [dirichletEnergy_image hU' hG₁ hball measurableSet_ball (hinj'.mono hball)
      (hu.differentiable (by simp))]
    exact dirichletEnergy_ball_congr (hwe.mono ball_subset_closedBall)
  -- mass term
  have hFd : ∀ x ∈ ball (0:ℂ) 1, HasFDerivAt G (mulR (deriv G x)) x := fun x hx =>
    ((hG₁.differentiableAt (hU'.mem_nhds (hball hx))).hasDerivAt.hasFDerivAt).restrictScalars ℝ
  have h5 : ∫⁻ z in ball (0:ℂ) 1, ‖w z‖ₑ ^ 2 ≤
      ENNReal.ofReal (1 / m ^ 2) * ∫⁻ z in G '' ball 0 1, ‖u z‖ₑ ^ 2 := by
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball
      (fun x hx => (hFd x hx).hasFDerivWithinAt) (hinj'.mono hball)]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball (fun z hz => ?_)
    rw [hwe (ball_subset_closedBall hz), det_mulR, Function.comp_apply, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity)]
    have hmz : m ≤ ‖deriv G z‖ := hmin (ball_subset_closedBall hz)
    have : 1 ≤ 1 / m ^ 2 * |‖deriv G z‖ ^ 2| := by
      rw [abs_of_nonneg (by positivity), one_div, inv_mul_eq_div, one_le_div (by positivity)]
      exact pow_le_pow_left₀ hm.le hmz 2
    calc ‖u (G z)‖ₑ ^ 2 = 1 * ‖u (G z)‖ₑ ^ 2 := (one_mul _).symm
      _ ≤ ENNReal.ofReal (1 / m ^ 2 * |‖deriv G z‖ ^ 2|) * ‖u (G z)‖ₑ ^ 2 := by
        refine mul_le_mul' ?_ le_rfl
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal this
  -- combine
  set A := ∫⁻ z in G '' ball 0 1, ‖u z‖ₑ ^ 2
  set E := Steklov.dirichletEnergy (G '' ball 0 1) u
  rw [h1]
  refine h2.trans ?_
  rw [ENNReal.ofReal_mul hM0]
  rw [mul_assoc]
  refine mul_le_mul' le_rfl ?_
  refine h3.trans ?_
  rw [h4]
  have hc : ENNReal.ofReal (3 / m ^ 2 + 1) = 3 * ENNReal.ofReal (1 / m ^ 2) + 1 := by
    rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_one,
      show 3 / m ^ 2 = 3 * (1 / m ^ 2) by ring, ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_ofNat]
  rw [hc]
  calc 3 * (∫⁻ z in ball (0:ℂ) 1, ‖w z‖ₑ ^ 2) + E
      ≤ 3 * (ENNReal.ofReal (1 / m ^ 2) * A) + E := by gcongr
    _ ≤ (3 * ENNReal.ofReal (1 / m ^ 2) + 1) * (A + E) := by
      rw [add_mul, one_mul, mul_add, ← mul_assoc]
      calc 3 * ENNReal.ofReal (1 / m ^ 2) * A + E
          ≤ 3 * ENNReal.ofReal (1 / m ^ 2) * A + 3 * ENNReal.ofReal (1 / m ^ 2) * E + (A + E) :=
            add_le_add (le_self_add) le_add_self
        _ = _ := by ring

/-- **`H¹` bridge for `G(𝔻)`**: the smooth-test Steklov spectrum of `G(𝔻)` equals its `H¹`
min–max spectrum, index by index (i.e. including multiplicities). -/
theorem steklovSpectrum_image_eq_h1 (hU : IsOpen U) (hcb : closedBall (0 : ℂ) 1 ⊆ U)
    (hG : DifferentiableOn ℂ G U) (hinj : InjOn G (closedBall 0 1))
    (hG' : ∀ z ∈ sphere (0 : ℂ) 1, deriv G z ≠ 0) :
    Steklov.steklovSpectrum (G '' ball 0 1) = h1SteklovSpectrum (G '' ball 0 1) := by
  have hD := bddDomain_image hU hcb hG hinj hG'
  obtain ⟨C, hC⟩ := traceIneq_image hU hcb hG hinj hG'
  unfold h1SteklovSpectrum
  rw [dif_pos hD]
  funext k
  exact (BddDomain.mk _ hD.1 hD.2.1 hD.2.2).steklovEigenvalue_eq_h1 (C := C) hC k

end SteklovH1
