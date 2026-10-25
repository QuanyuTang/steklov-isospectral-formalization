module

public import Mathlib
public import RequestProject.DiskGreen
public import RequestProject.SteklovRegularity

/-!
# Classical Steklov eigenfunctions are weak eigenfunctions

If a smooth `u` is harmonic in the unit disk and satisfies the weighted Steklov boundary
condition `∂_r u = τ ρ u` pointwise on the unit circle, then its `H¹(𝔻)` class is a weak weighted
Steklov eigenfunction. Transporting by a conformal map, a smooth `u` harmonic in `Ω = G(𝔻)` with
`∂_ν u = τ u` on `∂Ω = G(∂𝔻)` (outer unit normal `ν`) defines a weak Steklov eigenfunction on `Ω`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Real InnerProductSpace Laplacian
open scoped ENNReal ContDiff RealInnerProductSpace

noncomputable section

namespace SteklovH1

/-- **Classical ⇒ weak (weighted disk problem).** Let `ρ` be continuous and positive on the unit
circle. If `u ∈ C^∞(ℂ)` satisfies `Δu = 0` on `𝔻` and `Du(e^{iθ})[e^{iθ}] = τ ρ(e^{iθ}) u(e^{iθ})`
for all `θ`, then `u` (as an element of `H¹(𝔻)`) is a weak weighted Steklov eigenfunction. -/
theorem isWeakSteklovEigen_of_classical {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ (sphere 0 1))
    (hpos : ∀ z ∈ sphere (0:ℂ) 1, 0 < ρ z) {τ : ℝ} (u : smoothFns)
    (hharm : ∀ z ∈ ball (0:ℂ) 1, Δ (u : ℂ → ℝ) z = 0)
    (hbdry : ∀ θ : ℝ, fderiv ℝ (u : ℂ → ℝ) (Complex.exp (θ * Complex.I))
      (Complex.exp (θ * Complex.I)) =
        τ * ρ (Complex.exp (θ * Complex.I)) * (u : ℂ → ℝ) (Complex.exp (θ * Complex.I))) :
    IsWeakSteklovEigen ρ τ (embedH u) := by
  rw [← mem_weakEigenspace hρ hpos, weakEigenspace, SteklovSpectral.mem_eigenspace]
  -- both sides are continuous in `y`; check on the dense smooth range
  set x := embedH u
  have hcl : IsClosed {y : H1 | ⟪gradOpD x, gradOpD y⟫ = τ * ⟪weightOp hρ x, weightOp hρ y⟫} :=
    isClosed_eq (continuous_const.inner (gradOpD.continuous))
      (continuous_const.mul (continuous_const.inner (weightOp hρ).continuous))
  intro y
  refine denseRange_embedH.induction_on y hcl ?_
  intro v
  have hu2 : ContDiff ℝ 2 (u : ℂ → ℝ) := (mem_smoothFns.1 u.2).of_le (by norm_cast)
  have hv1 : ContDiff ℝ 1 (v : ℂ → ℝ) := contDiff_one_of_mem v.2
  have hG := SteklovGreen.green_disk hu2 hv1
  have hzero : ∫ z in ball (0:ℂ) 1, (v : ℂ → ℝ) z * Δ (u : ℂ → ℝ) z = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun z hz => by rw [hharm z hz, mul_zero]
  rw [hzero, add_zero] at hG
  rw [inner_weightOp hρ hpos, gradOpD_apply, gradOpD_apply, L2.inner_def]
  have eL : ∫ z, ⟪((x : Amb).snd : ℂ → ℂ) z, (((embedH v : H1) : Amb).snd : ℂ → ℂ) z⟫ ∂μD =
      ∫ z in ball (0:ℂ) 1, ⟪grad (u : ℂ → ℝ) z, grad (v : ℂ → ℝ) z⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [gradL2_ae u, gradL2_ae v] with z hz1 hz2
    simp only [x, coe_embedH, embed_snd]
    rw [hz1, hz2]
  have eR : ∫ t in Ioc 0 (2 * π), ρ (Complex.exp (t * Complex.I)) *
      ((trace x : ℝ → ℝ) t * (trace (embedH v) : ℝ → ℝ) t) =
      ∫ t in Ioc 0 (2 * π), ρ (Complex.exp (t * Complex.I)) *
        ((u : ℂ → ℝ) (Complex.exp (t * Complex.I)) * (v : ℂ → ℝ) (Complex.exp (t * Complex.I))) := by
    refine integral_congr_ae ?_
    filter_upwards [trace_embed_ae u, trace_embed_ae v] with t h1 h2
    rw [h1, h2]
  rw [eL, eR, hG, intervalIntegral.integral_of_le (by positivity), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [hbdry t]; ring

/-- **Harmonic functions composed with holomorphic maps are harmonic.** -/
theorem harmonicAt_comp_analyticAt {u : ℂ → ℝ} {G : ℂ → ℂ} {z : ℂ} (hu : HarmonicAt u (G z))
    (hG : AnalyticAt ℂ G z) : HarmonicAt (fun w => u (G w)) z := by
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.1 (isOpen_setOf_harmonicAt (f := u)) (G z) hu
  obtain ⟨F, hF, hFu⟩ := harmonic_is_realOfHolomorphic (f := u) (z := G z) (R := R)
    (fun w hw => hball hw)
  have hev : (fun w => u (G w)) =ᶠ[𝓝 z] fun w => (F (G w)).re := by
    have hc : ContinuousAt G z := hG.continuousAt
    filter_upwards [hc.preimage_mem_nhds (ball_mem_nhds (G z) hR)] with w hw
    exact (hFu hw).symm
  rw [harmonicAt_congr_nhds hev]
  exact ((hF (G z) (mem_ball_self hR)).comp hG).harmonicAt_re

namespace ConfMap

variable (c : ConfMap)

/-- The outward unit normal to `∂Ω = G(∂𝔻)` at `G(e^{iθ})`:
`ν(θ) = e^{iθ} G'(e^{iθ}) / |G'(e^{iθ})|` (the boundary tangent `i e^{iθ} G'(e^{iθ})` rotated by
`-π/2` and normalized). -/
def nrm (θ : ℝ) : ℂ :=
  Complex.exp (θ * Complex.I) * deriv c.G (Complex.exp (θ * Complex.I)) /
    (‖deriv c.G (Complex.exp (θ * Complex.I))‖ : ℂ)

lemma norm_nrm (θ : ℝ) : ‖c.nrm θ‖ = 1 := by
  have hz : Complex.exp (θ * Complex.I) ∈ sphere (0:ℂ) 1 := by
    simp [Complex.norm_exp_ofReal_mul_I]
  have h0 := c.ρ_pos _ hz
  simp only [nrm, norm_div, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    norm_norm]
  exact div_self h0.ne'

/-- The boundary parametrization `θ ↦ G(e^{iθ})` has velocity `T(θ) = i e^{iθ} G'(e^{iθ})`. -/
lemma hasDerivAt_boundary (θ : ℝ) :
    HasDerivAt (fun t : ℝ => c.G (Complex.exp (t * Complex.I)))
      (Complex.I * Complex.exp (θ * Complex.I) * deriv c.G (Complex.exp (θ * Complex.I))) θ := by
  have hes : Complex.exp (θ * Complex.I) ∈ c.U := c.cb (by simp [Complex.norm_exp_ofReal_mul_I])
  have hGd : HasDerivAt c.G (deriv c.G (Complex.exp (θ * Complex.I)))
      (Complex.exp (θ * Complex.I)) :=
    ((c.diff.analyticAt (c.isOpen.mem_nhds hes)).differentiableAt).hasDerivAt
  have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * Complex.I) Complex.I θ := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
  have := hGd.comp θ h1.cexp
  convert this using 1; ring

/-- `ν(θ)` is the velocity of the boundary parametrization rotated by `-π/2` and normalized,
i.e. the outward unit normal of the positively oriented boundary curve. -/
lemma nrm_eq_neg_I_mul_tangent (θ : ℝ) :
    c.nrm θ = -Complex.I *
      (Complex.I * Complex.exp (θ * Complex.I) * deriv c.G (Complex.exp (θ * Complex.I))) /
      (‖Complex.I * Complex.exp (θ * Complex.I) * deriv c.G (Complex.exp (θ * Complex.I))‖ : ℂ) := by
  simp only [nrm, norm_mul, Complex.norm_I, Complex.norm_exp_ofReal_mul_I, one_mul]
  congr 1
  ring_nf; rw [Complex.I_sq]; ring

/-- **Classical ⇒ weak on `Ω = G(𝔻)`.** If `u ∈ C^∞(ℂ)` is harmonic on `Ω` and satisfies the
Steklov condition `∂_ν u = τ u` at every boundary point `G(e^{iθ})` (with `ν = c.nrm θ` the outward
unit normal), then the `H¹(Ω)` class of `u` is a weak Steklov eigenfunction on `Ω`. -/
theorem isWeakSteklovEigenDom_of_classical {τ : ℝ} (u : smoothFns)
    (hharm : HarmonicOnNhd (u : ℂ → ℝ) c.dom.carrier)
    (hbdry : ∀ θ : ℝ, fderiv ℝ (u : ℂ → ℝ) (c.G (Complex.exp (θ * Complex.I))) (c.nrm θ) =
      τ * (u : ℂ → ℝ) (c.G (Complex.exp (θ * Complex.I)))) :
    IsWeakSteklovEigenDom c.dom τ (c.dom.embedH u) := by
  rw [c.isWeakSteklovEigenDom_iff, c.sobolevPullback_embedH]
  have hGa : ∀ z ∈ c.U, AnalyticAt ℂ c.G z := fun z hz =>
    (c.diff.analyticAt (c.isOpen.mem_nhds hz))
  refine isWeakSteklovEigen_of_classical c.continuousOn_ρ c.ρ_pos _ ?_ ?_
  · intro z hz
    have hev := c.pullSmooth_eventually u (ball_subset_closedBall hz)
    rw [(laplacian_congr_nhds hev).self_of_nhds]
    have hGz : c.G z ∈ c.dom.carrier := ⟨z, hz, rfl⟩
    exact (harmonicAt_comp_analyticAt (hharm _ hGz) (hGa z (c.ball_sub hz))).2.self_of_nhds
  · intro θ
    set e := Complex.exp (θ * Complex.I) with he
    have hes : e ∈ closedBall (0:ℂ) 1 := by
      simp [he, Complex.norm_exp_ofReal_mul_I]
    have hev := c.pullSmooth_eventually u hes
    rw [hev.fderiv_eq, hev.self_of_nhds]
    have hud : DifferentiableAt ℝ (u : ℂ → ℝ) (c.G e) :=
      ((contDiff_one_of_mem u.2).differentiable one_ne_zero) _
    have hGd : HasDerivAt c.G (deriv c.G e) e :=
      ((hGa e (c.cb hes)).differentiableAt).hasDerivAt
    have hcomp : HasFDerivAt (fun z => (u : ℂ → ℝ) (c.G z))
        ((fderiv ℝ (u : ℂ → ℝ) (c.G e)).comp ((deriv c.G e) • (1 : ℂ →L[ℝ] ℂ))) e := by
      have := hud.hasFDerivAt.comp e (hGd.hasFDerivAt.restrictScalars ℝ)
      convert this using 2
      ext1 w; simp [mul_comm]
    rw [hcomp.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply, smul_eq_mul]
    have hsph : e ∈ sphere (0:ℂ) 1 := by simp [he, Complex.norm_exp_ofReal_mul_I]
    have hρ0 := c.ρ_pos e hsph
    have hkey : deriv c.G e * e = (c.ρ e : ℝ) • c.nrm θ := by
      simp only [nrm, ← he, ρ]
      rw [Complex.real_smul, mul_div_assoc']
      field_simp [show ((‖deriv c.G e‖ : ℝ) : ℂ) ≠ 0 from by
        exact_mod_cast (show ‖deriv c.G e‖ ≠ 0 from hρ0.ne')]
    rw [hkey, map_smul, hbdry θ, smul_eq_mul]
    ring

end ConfMap

end SteklovH1
