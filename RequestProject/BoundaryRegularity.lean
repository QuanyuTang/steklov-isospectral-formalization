module

public import Mathlib
public import RequestProject.FourierCircle
public import RequestProject.ClassicalSteklov
public import RequestProject.HarmonicSeries

/-!
# Boundary regularity of weak weighted Steklov eigenfunctions on the disk

Let `ρ` be a real-analytic weight on the unit circle, in the Fourier form
`SteklovBoundary.IsAnalyticWeight ρ`: `ρ(e^{it}) = ∑ₖ R(k) e^{ikt}` with `|R(k)| ≤ C q^{|k|}`,
`q < 1`. If `x ∈ H¹(𝔻)` is a weak weighted Steklov eigenfunction,
`∫_𝔻 ⟨∇x, ∇y⟩ = τ ∫_0^{2π} ρ Tx Ty` for all `y ∈ H¹(𝔻)`, then `x` is (the class of) a smooth
function `u` that is harmonic on a disk `|z| < r` with `r > 1` and satisfies the Steklov boundary
condition `∂_r u = τ ρ u` pointwise on the unit circle (`SteklovBoundary.weak_eigen_classical`).

Proof: Green's identity against the harmonic polynomials `Re zⁿ`, `Im zⁿ` gives
`|n| f̂(n) = τ (ρ f)^(n)` for the trace `f = Tx`; with the Fourier expansion of `ρ` this is a
convolution relation, and the bootstrap `SteklovFourier.exp_decay_of_relation` gives exponential
decay of `f̂`. Hence `∑ f̂(n) r^{|n|} e^{inθ}` is harmonic on a larger disk; its `H¹` class has the
same trace as `x`, and the difference has zero trace and zero energy, so it vanishes.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Real InnerProductSpace Laplacian
open scoped ENNReal ContDiff RealInnerProductSpace ComplexConjugate

noncomputable section

namespace SteklovBoundary

open SteklovH1 SteklovFourier

/-- **Real-analytic weight on the circle** (Fourier form): `ρ(e^{it}) = ∑ₖ R(k) e^{ikt}` for all
`t`, with `|R(k)| ≤ C q^{|k|}` for some `0 ≤ q < 1`. -/
def IsAnalyticWeight (ρ : ℂ → ℝ) : Prop :=
  ∃ R : ℤ → ℂ, ∃ C q : ℝ, 0 ≤ q ∧ q < 1 ∧ (∀ k, ‖R k‖ ≤ C * q ^ k.natAbs) ∧
    ∀ t : ℝ, HasSum (fun k : ℤ => R k * Complex.exp (k * t * Complex.I)) (ρ (ee t) : ℂ)

/-! ### Harmonic polynomials -/

/-- `Re zⁿ`. -/
def rePowZ (n : ℕ) : smoothFns :=
  ⟨fun z : ℂ => (z ^ n).re,
    (Complex.reCLM.contDiff.comp (contDiff_id.pow n) : ContDiff ℝ ∞ fun z : ℂ => (z ^ n).re)⟩

/-- `Im zⁿ`. -/
def imPowZ (n : ℕ) : smoothFns :=
  ⟨fun z : ℂ => (z ^ n).im,
    (Complex.imCLM.contDiff.comp (contDiff_id.pow n) : ContDiff ℝ ∞ fun z : ℂ => (z ^ n).im)⟩

lemma laplacian_rePowZ (n : ℕ) (z : ℂ) : Δ (rePowZ n : ℂ → ℝ) z = 0 := by
  have : AnalyticAt ℂ (fun z : ℂ => z ^ n) z := analyticAt_id.pow n
  exact (this.harmonicAt_re).2.self_of_nhds

lemma laplacian_imPowZ (n : ℕ) (z : ℂ) : Δ (imPowZ n : ℂ → ℝ) z = 0 := by
  have : AnalyticAt ℂ (fun z : ℂ => -Complex.I * z ^ n) z :=
    analyticAt_const.mul (analyticAt_id.pow n)
  have h := (this.harmonicAt_re).2.self_of_nhds
  simpa [imPowZ] using h

lemma ee_pow (n : ℕ) (t : ℝ) : ee t ^ n = Complex.exp (((n * t : ℝ) : ℂ) * Complex.I) := by
  rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma rePowZ_ee (n : ℕ) (t : ℝ) : (rePowZ n : ℂ → ℝ) (ee t) = Real.cos (n * t) := by
  show (ee t ^ n).re = _
  rw [ee_pow, Complex.exp_ofReal_mul_I_re]

lemma imPowZ_ee (n : ℕ) (t : ℝ) : (imPowZ n : ℂ → ℝ) (ee t) = Real.sin (n * t) := by
  show (ee t ^ n).im = _
  rw [ee_pow, Complex.exp_ofReal_mul_I_im]

lemma hasFDerivAt_pow_real (n : ℕ) (z : ℂ) :
    HasFDerivAt (fun z : ℂ => z ^ n)
      ((((n : ℂ) * z ^ (n - 1)) • (1 : ℂ →L[ℂ] ℂ)).restrictScalars ℝ) z := by
  have := ((hasDerivAt_pow n z).hasFDerivAt).restrictScalars ℝ
  convert this using 2
  ext; simp

lemma fderiv_rePowZ (n : ℕ) (z w : ℂ) :
    fderiv ℝ (rePowZ n : ℂ → ℝ) z w = ((n : ℂ) * z ^ (n - 1) * w).re := by
  have h2 : HasFDerivAt (fun z : ℂ => (z ^ n).re) (Complex.reCLM.comp
      ((((n : ℂ) * z ^ (n - 1)) • (1 : ℂ →L[ℂ] ℂ)).restrictScalars ℝ)) z :=
    Complex.reCLM.hasFDerivAt.comp z (hasFDerivAt_pow_real n z)
  show fderiv ℝ (fun z : ℂ => (z ^ n).re) z w = _
  rw [h2.fderiv]
  simp [mul_comm]

lemma fderiv_imPowZ (n : ℕ) (z w : ℂ) :
    fderiv ℝ (imPowZ n : ℂ → ℝ) z w = ((n : ℂ) * z ^ (n - 1) * w).im := by
  have h2 : HasFDerivAt (fun z : ℂ => (z ^ n).im) (Complex.imCLM.comp
      ((((n : ℂ) * z ^ (n - 1)) • (1 : ℂ →L[ℂ] ℂ)).restrictScalars ℝ)) z :=
    Complex.imCLM.hasFDerivAt.comp z (hasFDerivAt_pow_real n z)
  show fderiv ℝ (fun z : ℂ => (z ^ n).im) z w = _
  rw [h2.fderiv]
  simp [mul_comm]

lemma fderiv_rePowZ_ee (n : ℕ) (t : ℝ) :
    fderiv ℝ (rePowZ n : ℂ → ℝ) (ee t) (ee t) = n * Real.cos (n * t) := by
  rw [fderiv_rePowZ]
  rcases n with _ | n
  · simp
  rw [mul_assoc, ← pow_succ, Nat.add_sub_cancel, ee_pow, ← Complex.ofReal_natCast,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

lemma fderiv_imPowZ_ee (n : ℕ) (t : ℝ) :
    fderiv ℝ (imPowZ n : ℂ → ℝ) (ee t) (ee t) = n * Real.sin (n * t) := by
  rw [fderiv_imPowZ]
  rcases n with _ | n
  · simp
  rw [mul_assoc, ← pow_succ, Nat.add_sub_cancel, ee_pow, ← Complex.ofReal_natCast,
    Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

/-! ### Green's identity on `H¹(𝔻)` against harmonic functions -/

/-- **Green's identity for `H¹(𝔻)`**: for `U` smooth and harmonic in `𝔻` and `x ∈ H¹(𝔻)`,
`∫_𝔻 ⟨∇x, ∇U⟩ = ∫_0^{2π} Tx(t) ∂_r U(e^{it}) dt`. -/
theorem integral_inner_grad_harmonic (U : smoothFns)
    (hU : ∀ z ∈ ball (0:ℂ) 1, Δ (U : ℂ → ℝ) z = 0) (x : H1) :
    ∫ z in ball (0:ℂ) 1, ⟪((x : Amb).snd : ℂ → ℂ) z, grad U z⟫ =
      ∫ t in Ioc 0 (2 * π), (trace x : ℝ → ℝ) t * fderiv ℝ (U : ℂ → ℝ) (ee t) (ee t) := by
  set h : ℝ → ℝ := fun t => fderiv ℝ (U : ℂ → ℝ) (ee t) (ee t) with hh
  have hU1 : ContDiff ℝ 1 (fderiv ℝ (U : ℂ → ℝ)) :=
    (mem_smoothFns.1 U.2).fderiv_right (m := 1) (by norm_cast)
  have hhc : Continuous h := by
    have hee : Continuous ee := by fun_prop
    exact (hU1.continuous.comp hee).clm_apply hee
  set hL : Lp ℝ 2 μT := (memLp_circle hhc).toLp h
  have eL : ∀ y : H1, ∫ z in ball (0:ℂ) 1, ⟪((y : Amb).snd : ℂ → ℂ) z, grad U z⟫ =
      ⟪gradOpD y, gradL2 U⟫ := by
    intro y
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [gradL2_ae U] with z hz
    rw [hz, gradOpD_apply]
  have eR : ∀ y : H1, ∫ t in Ioc 0 (2 * π), (trace y : ℝ → ℝ) t * h t = ⟪trace y, hL⟫ := by
    intro y
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(memLp_circle hhc).coeFn_toLp] with t ht
    rw [ht, real_inner_eq_re_inner, RCLike.inner_apply, RCLike.conj_to_real, RCLike.re_to_real,
      mul_comm]
  show ∫ z in ball (0:ℂ) 1, ⟪((x : Amb).snd : ℂ → ℂ) z, grad U z⟫ =
    ∫ t in Ioc 0 (2 * π), (trace x : ℝ → ℝ) t * h t
  rw [eL, eR]
  have hcl : IsClosed {y : H1 | ⟪gradOpD y, gradL2 U⟫ = ⟪trace y, hL⟫} :=
    isClosed_eq ((gradOpD.continuous).inner continuous_const)
      ((trace.continuous).inner continuous_const)
  refine denseRange_embedH.induction_on x hcl ?_
  intro v
  show ⟪gradOpD (embedH v), gradL2 U⟫ = ⟪trace (embedH v), hL⟫
  rw [← eL, ← eR]
  have hu2 : ContDiff ℝ 2 (U : ℂ → ℝ) := (mem_smoothFns.1 U.2).of_le (by norm_cast)
  have hv1 : ContDiff ℝ 1 (v : ℂ → ℝ) := contDiff_one_of_mem v.2
  have hG := SteklovGreen.green_disk hu2 hv1
  have hzero : ∫ z in ball (0:ℂ) 1, (v : ℂ → ℝ) z * Δ (U : ℂ → ℝ) z = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun z hz => by rw [hU z hz, mul_zero]
  rw [hzero, add_zero, intervalIntegral.integral_of_le (by positivity)] at hG
  have e1 : ∫ z in ball (0:ℂ) 1, ⟪(((embedH v : H1) : Amb).snd : ℂ → ℂ) z, grad U z⟫ =
      ∫ z in ball (0:ℂ) 1, ⟪grad (U : ℂ → ℝ) z, grad (v : ℂ → ℝ) z⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [gradL2_ae v] with z hz
    simp only [coe_embedH, embed_snd]
    rw [hz, real_inner_comm]
  have e2 : ∫ t in Ioc 0 (2 * π), (trace (embedH v) : ℝ → ℝ) t * h t =
      ∫ t in Ioc 0 (2 * π), (v : ℂ → ℝ) (ee t) * h t := by
    refine integral_congr_ae ?_
    filter_upwards [trace_embed_ae v] with t ht
    rw [ht]
  rw [e1, e2, hG]

/-- For a weak eigenfunction and a smooth `U` harmonic in `𝔻`:
`∫ Tx ∂_r U = τ ∫ ρ Tx U`. -/
theorem boundary_identity {ρ : ℂ → ℝ} {τ : ℝ} {x : H1} (hx : IsWeakSteklovEigen ρ τ x)
    (U : smoothFns) (hU : ∀ z ∈ ball (0:ℂ) 1, Δ (U : ℂ → ℝ) z = 0) :
    ∫ t in Ioc 0 (2 * π), (trace x : ℝ → ℝ) t * fderiv ℝ (U : ℂ → ℝ) (ee t) (ee t) =
      τ * ∫ t in Ioc 0 (2 * π), ρ (ee t) * ((trace x : ℝ → ℝ) t * (U : ℂ → ℝ) (ee t)) := by
  rw [← integral_inner_grad_harmonic U hU x]
  have h1 := hx (embedH U)
  have e1 : ∫ z in ball (0:ℂ) 1, ⟪((x : Amb).snd : ℂ → ℂ) z, grad U z⟫ =
      ∫ z in ball (0:ℂ) 1, ⟪((x : Amb).snd : ℂ → ℂ) z, (((embedH U : H1) : Amb).snd : ℂ → ℂ) z⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [gradL2_ae U] with z hz
    simp only [coe_embedH, embed_snd]
    rw [hz]
  rw [e1, h1]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [trace_embed_ae U] with t ht
  rw [ht]

/-! ### Analytic weights: summability, boundedness, continuity -/

namespace IsAnalyticWeight

variable {ρ : ℂ → ℝ}

lemma summable_coeff {R : ℤ → ℂ} {C q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hR : ∀ k, ‖R k‖ ≤ C * q ^ k.natAbs) : Summable fun k => ‖R k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hR ((summable_geom_int hq0 hq1).mul_left C)

lemma continuous (hA : IsAnalyticWeight ρ) : Continuous fun t : ℝ => ρ (ee t) := by
  obtain ⟨R, C, q, hq0, hq1, hR, hs⟩ := hA
  have hsum := summable_coeff hq0 hq1 hR
  have hc : Continuous fun t : ℝ => ∑' k : ℤ, R k * Complex.exp (k * t * Complex.I) := by
    refine continuous_tsum (fun _ => by fun_prop) hsum (fun k t => ?_)
    rw [norm_mul, norm_exp_int, mul_one]
  have : (fun t : ℝ => ρ (ee t)) =
      fun t : ℝ => (∑' k : ℤ, R k * Complex.exp (k * t * Complex.I)).re := by
    funext t; rw [(hs t).tsum_eq, Complex.ofReal_re]
  rw [this]; exact Complex.continuous_re.comp hc

lemma bounded (hA : IsAnalyticWeight ρ) : ∃ M, ∀ t : ℝ, |ρ (ee t)| ≤ M := by
  obtain ⟨R, C, q, hq0, hq1, hR, hs⟩ := hA
  have hsum := summable_coeff hq0 hq1 hR
  refine ⟨∑' k, ‖R k‖, fun t => ?_⟩
  have h1 : ‖(ρ (ee t) : ℂ)‖ ≤ ∑' k, ‖R k * Complex.exp (k * t * Complex.I)‖ := by
    rw [← (hs t).tsum_eq]
    exact norm_tsum_le_tsum_norm (hsum.congr fun k => by rw [norm_mul, norm_exp_int, mul_one])
  simpa [norm_mul, norm_exp_int] using h1

end IsAnalyticWeight

lemma integrableOn_trace (x : H1) : IntegrableOn (trace x : ℝ → ℝ) (Ioc 0 (2 * π)) :=
  (Lp.memLp (trace x)).integrable one_le_two

lemma integrableOn_weight_trace {ρ : ℂ → ℝ} (hA : IsAnalyticWeight ρ) (x : H1) :
    IntegrableOn (fun t => ρ (ee t) * (trace x : ℝ → ℝ) t) (Ioc 0 (2 * π)) := by
  obtain ⟨M, hM⟩ := hA.bounded
  have := (integrableOn_trace x).bdd_mul (c := M) hA.continuous.aestronglyMeasurable
    (Eventually.of_forall fun t => by simpa using hM t)
  exact this

/-! ### The coefficient relation -/

/-- The cosine/sine relations `m ∫ f cos(nt) = τ ∫ ρ f cos(nt)` (and with `sin`), `m = |n|`. -/
lemma cos_sin_relation {ρ : ℂ → ℝ} {τ : ℝ} {x : H1} (hx : IsWeakSteklovEigen ρ τ x) (m : ℕ) :
    (m : ℝ) * ∫ t in Ioc 0 (2 * π), (trace x : ℝ → ℝ) t * Real.cos (m * t) =
      τ * ∫ t in Ioc 0 (2 * π), ρ (ee t) * (trace x : ℝ → ℝ) t * Real.cos (m * t) ∧
    (m : ℝ) * ∫ t in Ioc 0 (2 * π), (trace x : ℝ → ℝ) t * Real.sin (m * t) =
      τ * ∫ t in Ioc 0 (2 * π), ρ (ee t) * (trace x : ℝ → ℝ) t * Real.sin (m * t) := by
  constructor
  · have h := boundary_identity hx (rePowZ m) (fun z _ => laplacian_rePowZ m z)
    simp only [fderiv_rePowZ_ee, rePowZ_ee] at h
    rw [← integral_const_mul]
    convert h using 1
    · congr 1; funext t; ring
    · congr 1; congr 1; funext t; ring
  · have h := boundary_identity hx (imPowZ m) (fun z _ => laplacian_imPowZ m z)
    simp only [fderiv_imPowZ_ee, imPowZ_ee] at h
    rw [← integral_const_mul]
    convert h using 1
    · congr 1; funext t; ring
    · congr 1; congr 1; funext t; ring

/-- `|n| f̂(n) = τ (ρ f)^(n)` for the trace `f` of a weak eigenfunction. -/
theorem coeff_relation {ρ : ℂ → ℝ} (hA : IsAnalyticWeight ρ) {τ : ℝ} {x : H1}
    (hx : IsWeakSteklovEigen ρ τ x) (n : ℤ) :
    (n.natAbs : ℂ) * fc (fun t => ((trace x : ℝ → ℝ) t : ℂ)) n =
      τ * fc (fun t => ((ρ (ee t) * (trace x : ℝ → ℝ) t : ℝ) : ℂ)) n := by
  set m := n.natAbs
  have hrel : (m : ℝ) * ∫ t in Ioc 0 (2 * π), (trace x : ℝ → ℝ) t * Real.cos (n * t) =
        τ * ∫ t in Ioc 0 (2 * π), ρ (ee t) * (trace x : ℝ → ℝ) t * Real.cos (n * t) ∧
      (m : ℝ) * ∫ t in Ioc 0 (2 * π), (trace x : ℝ → ℝ) t * Real.sin (n * t) =
        τ * ∫ t in Ioc 0 (2 * π), ρ (ee t) * (trace x : ℝ → ℝ) t * Real.sin (n * t) := by
    obtain ⟨h1, h2⟩ := cos_sin_relation hx m
    rcases Int.natAbs_eq n with hn | hn
    · rw [hn]; simp only [Int.cast_natCast]; exact ⟨h1, h2⟩
    · rw [hn]
      simp only [Int.cast_neg, Int.cast_natCast, neg_mul, Real.cos_neg, Real.sin_neg, mul_neg,
        integral_neg]
      exact ⟨h1, by linarith⟩
  rw [fc_real (integrableOn_trace x), fc_real (integrableOn_weight_trace hA x)]
  obtain ⟨h1, h2⟩ := hrel
  have h1' : (m : ℂ) * ((∫ t in Ioc 0 (2 * π), (trace x : ℝ → ℝ) t * Real.cos (n * t) : ℝ) : ℂ) =
      τ * ((∫ t in Ioc 0 (2 * π), ρ (ee t) * (trace x : ℝ → ℝ) t * Real.cos (n * t) : ℝ) : ℂ) := by
    exact_mod_cast h1
  have h2' : (m : ℂ) * ((∫ t in Ioc 0 (2 * π), (trace x : ℝ → ℝ) t * Real.sin (n * t) : ℝ) : ℂ) =
      τ * ((∫ t in Ioc 0 (2 * π), ρ (ee t) * (trace x : ℝ → ℝ) t * Real.sin (n * t) : ℝ) : ℂ) := by
    exact_mod_cast h2
  linear_combination ((2 * π : ℝ) : ℂ)⁻¹ * h1' - ((2 * π : ℝ) : ℂ)⁻¹ * Complex.I * h2'

/-! ### Uniqueness and the main theorem -/

/-- If a weak eigenfunction `x` has the same trace as `embedH U` for a smooth `U` harmonic
in `𝔻`, then `x = embedH U`. -/
theorem eq_embedH_of_trace {ρ : ℂ → ℝ} {τ : ℝ} {x : H1} (hx : IsWeakSteklovEigen ρ τ x)
    (U : smoothFns) (hU : ∀ z ∈ ball (0:ℂ) 1, Δ (U : ℂ → ℝ) z = 0)
    (htr : (trace x : ℝ → ℝ) =ᵐ[μT] fun t => (U : ℂ → ℝ) (ee t)) : x = embedH U := by
  set w := x - embedH U with hw
  have htw : trace w = 0 := by
    rw [Lp.eq_zero_iff_ae_eq_zero]
    have := Lp.coeFn_sub (trace x) (trace (embedH U))
    rw [hw, map_sub]
    filter_upwards [this, htr, trace_embed_ae U] with t h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, sub_self]; rfl
  have htw' : (trace w : ℝ → ℝ) =ᵐ[μT] 0 := by rw [htw]; exact Lp.coeFn_zero _ _ _
  have e1 : ⟪gradOpD x, gradOpD w⟫ = 0 := by
    rw [gradOpD_apply, gradOpD_apply, L2.inner_def]
    rw [show (∫ z, ⟪((x : Amb).snd : ℂ → ℂ) z, ((w : Amb).snd : ℂ → ℂ) z⟫ ∂μD) =
      ∫ z in ball (0:ℂ) 1, ⟪((x : Amb).snd : ℂ → ℂ) z, ((w : Amb).snd : ℂ → ℂ) z⟫ from rfl, hx w]
    rw [integral_eq_zero_of_ae, mul_zero]
    filter_upwards [htw'] with t ht
    rw [ht]; simp
  have e2 : ⟪gradOpD w, gradOpD (embedH U)⟫ = 0 := by
    rw [gradOpD_apply, gradOpD_apply, L2.inner_def]
    have : (∫ z, ⟪((w : Amb).snd : ℂ → ℂ) z, (((embedH U : H1) : Amb).snd : ℂ → ℂ) z⟫ ∂μD) =
        ∫ z in ball (0:ℂ) 1, ⟪((w : Amb).snd : ℂ → ℂ) z, grad U z⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [gradL2_ae U] with z hz
      simp only [coe_embedH, embed_snd]; rw [hz]
    rw [this, integral_inner_grad_harmonic U hU w, integral_eq_zero_of_ae]
    filter_upwards [htw'] with t ht
    rw [ht]; simp
  have hgw : ‖gradOpD w‖ ^ 2 = 0 := by
    have : gradOpD w = gradOpD x - gradOpD (embedH U) := by rw [hw, map_sub]
    rw [← real_inner_self_eq_norm_sq]
    nth_rewrite 1 [this]
    rw [inner_sub_left, e1, real_inner_comm, e2, sub_zero]
  have hn := norm_sq_le_trace_grad w
  rw [htw, norm_zero, hgw] at hn
  have : w = 0 := by
    have h0 : ‖w‖ ^ 2 ≤ 0 := by simpa using hn
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg w])
  exact sub_eq_zero.1 this

/-- A continuous function on `ℝ` vanishing a.e. on `(0, 2π]` vanishes on `(0, 2π]`. -/
lemma eq_zero_of_ae_Ioc {h : ℝ → ℝ} (hc : Continuous h) (hae : h =ᵐ[μT] 0) :
    ∀ t ∈ Ioc 0 (2 * π), h t = 0 := by
  have hopen : IsOpen ({t | h t ≠ 0} ∩ Ioo 0 (2 * π)) :=
    (isOpen_ne_fun hc continuous_const).inter isOpen_Ioo
  have hnull : volume ({t | h t ≠ 0} ∩ Ioo 0 (2 * π)) = 0 := by
    have h1 : μT {t | h t ≠ 0} = 0 := by
      rw [← ae_iff]; filter_upwards [hae] with t ht; simpa using ht
    rw [Measure.restrict_apply' measurableSet_Ioc] at h1
    exact measure_mono_null (inter_subset_inter_right _ Ioo_subset_Ioc_self) h1
  have hempty : {t | h t ≠ 0} ∩ Ioo 0 (2 * π) = ∅ := hopen.measure_eq_zero_iff volume |>.1 hnull
  have hIoo : ∀ t ∈ Ioo 0 (2 * π), h t = 0 := by
    intro t ht
    by_contra hne
    have : t ∈ ({t | h t ≠ 0} ∩ Ioo 0 (2 * π)) := ⟨hne, ht⟩
    rw [hempty] at this; exact this
  intro t ht
  rcases eq_or_lt_of_le ht.2 with heq | hlt
  · -- right endpoint: limit from the left
    have hcl : h t ∈ closure (h '' Ioo 0 (2 * π)) := by
      have hmem : t ∈ closure (Ioo 0 (2 * π)) := by
        rw [closure_Ioo (by positivity : (0:ℝ) ≠ 2 * π)]; exact ⟨ht.1.le, ht.2⟩
      exact mem_closure_image hc.continuousAt hmem
    have hsub : h '' Ioo 0 (2 * π) ⊆ {0} := by
      rintro _ ⟨s, hs, rfl⟩; exact hIoo s hs
    have := closure_mono hsub hcl
    rwa [closure_singleton] at this
  · exact hIoo t ⟨ht.1, hlt⟩

/-- A continuous function on `ℝ` whose cosine and sine moments over `(0, 2π]` all vanish is zero
on `(0, 2π]`. -/
lemma eq_zero_of_cos_sin {h : ℝ → ℝ} (hc : Continuous h)
    (hcs : ∀ m : ℕ, ∫ t in Ioc 0 (2 * π), h t * Real.cos (m * t) = 0 ∧
      ∫ t in Ioc 0 (2 * π), h t * Real.sin (m * t) = 0) :
    ∀ t ∈ Ioc 0 (2 * π), h t = 0 := by
  have hi : IntegrableOn h (Ioc 0 (2 * π)) := (memLp_circle hc).integrable one_le_two
  have hfc : ∀ n : ℤ, fc (fun t => (h t : ℂ)) n = 0 := by
    intro n
    rw [fc_real hi]
    obtain ⟨h1, h2⟩ := hcs n.natAbs
    have e : ∫ t in Ioc 0 (2 * π), h t * Real.cos (n * t) = 0 ∧
        ∫ t in Ioc 0 (2 * π), h t * Real.sin (n * t) = 0 := by
      rcases Int.natAbs_eq n with hn | hn
      · rw [hn]; simp only [Int.cast_natCast]; exact ⟨h1, h2⟩
      · rw [hn]
        simp only [Int.cast_neg, Int.cast_natCast, neg_mul, Real.cos_neg, Real.sin_neg, mul_neg,
          integral_neg, neg_eq_zero]
        exact ⟨h1, h2⟩
    rw [e.1, e.2]; simp
  have hae := ae_eq_zero_of_fc (memLp_circle hc).ofReal hfc
  apply eq_zero_of_ae_Ioc hc
  filter_upwards [hae] with t ht
  simpa using ht

lemma ee_toIocMod (θ : ℝ) : ee (toIocMod Real.two_pi_pos 0 θ) = ee θ := by
  have h := self_sub_toIocDiv_zsmul Real.two_pi_pos 0 θ
  rw [← h]
  simp only [ee, zsmul_eq_mul]
  rw [show ((θ - (toIocDiv Real.two_pi_pos 0 θ : ℝ) * (2 * π) : ℝ) : ℂ) * Complex.I =
    θ * Complex.I - (toIocDiv Real.two_pi_pos 0 θ : ℤ) * (2 * π * Complex.I) by push_cast; ring,
    Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

/-- **The classical boundary condition.** If `U` is smooth and harmonic in `𝔻` and its `H¹`
class is a weak weighted Steklov eigenfunction, then `∂_r U = τ ρ U` pointwise on the circle. -/
theorem boundary_condition {ρ : ℂ → ℝ} (hA : IsAnalyticWeight ρ) {τ : ℝ} (U : smoothFns)
    (hU : ∀ z ∈ ball (0:ℂ) 1, Δ (U : ℂ → ℝ) z = 0) (hx : IsWeakSteklovEigen ρ τ (embedH U)) :
    ∀ θ : ℝ, fderiv ℝ (U : ℂ → ℝ) (ee θ) (ee θ) = τ * ρ (ee θ) * (U : ℂ → ℝ) (ee θ) := by
  set dU : ℝ → ℝ := fun t => fderiv ℝ (U : ℂ → ℝ) (ee t) (ee t) with hdU
  have hee : Continuous ee := by fun_prop
  have hdUc : Continuous dU := by
    have hU1 : ContDiff ℝ 1 (fderiv ℝ (U : ℂ → ℝ)) :=
      (mem_smoothFns.1 U.2).fderiv_right (m := 1) (by norm_cast)
    exact (hU1.continuous.comp hee).clm_apply hee
  have hUc : Continuous fun t : ℝ => (U : ℂ → ℝ) (ee t) := (continuous_of_mem U.2).comp hee
  have hρc := hA.continuous
  -- the weak identity tested against `y`
  have key : ∀ y : H1, ∫ t in Ioc 0 (2 * π), (trace y : ℝ → ℝ) t * dU t =
      τ * ∫ t in Ioc 0 (2 * π), ρ (ee t) * ((U : ℂ → ℝ) (ee t) * (trace y : ℝ → ℝ) t) := by
    intro y
    rw [← integral_inner_grad_harmonic U hU y]
    have h1 := hx y
    have e1 : ∫ z in ball (0:ℂ) 1, ⟪((y : Amb).snd : ℂ → ℂ) z, grad U z⟫ =
        ∫ z in ball (0:ℂ) 1, ⟪(((embedH U : H1) : Amb).snd : ℂ → ℂ) z, ((y : Amb).snd : ℂ → ℂ) z⟫ := by
      refine integral_congr_ae ?_
      filter_upwards [gradL2_ae U] with z hz
      simp only [coe_embedH, embed_snd]
      rw [hz, real_inner_comm]
    rw [e1, h1]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [trace_embed_ae U] with t ht
    rw [ht]
  set h : ℝ → ℝ := fun t => dU t - τ * ρ (ee t) * (U : ℂ → ℝ) (ee t) with hh
  have hhc : Continuous h := hdUc.sub ((continuous_const.mul hρc).mul hUc)
  have hint : ∀ c : ℝ → ℝ, Continuous c → IntegrableOn c (Ioc 0 (2 * π)) := fun c hc =>
    (memLp_circle hc).integrable one_le_two
  have hmom : ∀ (V : smoothFns) (c : ℝ → ℝ), Continuous c →
      (∀ t, (V : ℂ → ℝ) (ee t) = c t) → ∫ t in Ioc 0 (2 * π), h t * c t = 0 := by
    intro V c hc hV
    have h1 := key (embedH V)
    have e1 : ∫ t in Ioc 0 (2 * π), (trace (embedH V) : ℝ → ℝ) t * dU t =
        ∫ t in Ioc 0 (2 * π), dU t * c t := by
      refine integral_congr_ae ?_
      filter_upwards [trace_embed_ae V] with t ht
      rw [ht, hV, mul_comm]
    have e2 : ∫ t in Ioc 0 (2 * π), ρ (ee t) * ((U : ℂ → ℝ) (ee t) *
        (trace (embedH V) : ℝ → ℝ) t) =
        ∫ t in Ioc 0 (2 * π), ρ (ee t) * (U : ℂ → ℝ) (ee t) * c t := by
      refine integral_congr_ae ?_
      filter_upwards [trace_embed_ae V] with t ht
      rw [ht, hV, mul_assoc]
    rw [e1, e2] at h1
    have i1 : IntegrableOn (fun t => dU t * c t) (Ioc 0 (2 * π)) := hint _ (hdUc.mul hc)
    have i2 : IntegrableOn (fun t => ρ (ee t) * (U : ℂ → ℝ) (ee t) * c t) (Ioc 0 (2 * π)) :=
      hint _ ((hρc.mul hUc).mul hc)
    have : (fun t => h t * c t) = fun t => dU t * c t - τ * (ρ (ee t) * (U : ℂ → ℝ) (ee t) * c t) := by
      funext t; simp only [hh]; ring
    rw [this, integral_sub i1 (i2.const_mul τ), integral_const_mul, h1, sub_self]
  have hzero := eq_zero_of_cos_sin hhc (fun m =>
    ⟨hmom (rePowZ m) _ (by fun_prop) (rePowZ_ee m), hmom (imPowZ m) _ (by fun_prop) (imPowZ_ee m)⟩)
  intro θ
  have hmem : toIocMod Real.two_pi_pos 0 θ ∈ Ioc 0 (2 * π) := by
    have := toIocMod_mem_Ioc Real.two_pi_pos 0 θ
    simpa using this
  have := hzero _ hmem
  simp only [hh, hdU, ee_toIocMod] at this
  linarith

/-- **Boundary regularity on the disk.** For a real-analytic weight `ρ`, every weak weighted
Steklov eigenfunction `x ∈ H¹(𝔻)` with eigenvalue `τ` is `embedH u` for a smooth `u : ℂ → ℝ`
which is harmonic on the disk `|z| < r` for some `r > 1` and satisfies the Steklov boundary
condition `∂_r u(e^{iθ}) = τ ρ(e^{iθ}) u(e^{iθ})` for every `θ`. In particular the function
component of `x` is `u` a.e. on `𝔻`, its gradient component is `∇u` a.e., and its trace is
`t ↦ u(e^{it})` a.e. -/
theorem weak_eigen_classical {ρ : ℂ → ℝ} (hA : IsAnalyticWeight ρ) {τ : ℝ} {x : H1}
    (hx : IsWeakSteklovEigen ρ τ x) :
    ∃ r > (1 : ℝ), ∃ u : smoothFns, x = embedH u ∧ HarmonicOnNhd (u : ℂ → ℝ) (ball 0 r) ∧
      ∀ θ : ℝ, fderiv ℝ (u : ℂ → ℝ) (ee θ) (ee θ) = τ * ρ (ee θ) * (u : ℂ → ℝ) (ee θ) := by
  obtain ⟨R, C, q, hq0, hq1, hR, hs⟩ := id hA
  set f : ℝ → ℝ := (trace x : ℝ → ℝ) with hf
  set F : ℤ → ℂ := fun n => fc (fun t => (f t : ℂ)) n with hF
  have hRs := IsAnalyticWeight.summable_coeff hq0 hq1 hR
  have hFb : ∀ n, ‖F n‖ ≤ (2 * π)⁻¹ * ∫ t in Ioc 0 (2 * π), ‖(f t : ℂ)‖ :=
    fun n => norm_fc_le _ n
  have hrel : ∀ n, (n.natAbs : ℂ) * F n = τ * ∑' k, R k * F (n - k) := by
    intro n
    simp only [hF]
    rw [coeff_relation hA hx n]
    congr 1
    have := fc_mul_eq_tsum hRs hs (f := fun t => (f t : ℂ)) (integrableOn_trace x).ofReal n
    rw [← this]; congr 1; funext t; push_cast; ring
  obtain ⟨lam, hlam, D, hD⟩ := exp_decay_of_relation hFb hq0 hq1 hR hrel
  have hconj : ∀ n, F (-n) = conj (F n) := fun n => fc_real_neg (integrableOn_trace x) n
  obtain ⟨r, hr, U, hUh, hUs⟩ := exists_harmonic_of_decay hconj hlam hD
  have hlinv0 : 0 ≤ lam⁻¹ := inv_nonneg.2 (by linarith)
  have hlinv1 : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam
  have hFs : Summable fun n => ‖F n‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      ((summable_geom_int hlinv0 hlinv1).mul_left D)
    have hp : 0 < lam ^ n.natAbs := pow_pos (by linarith) _
    rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ hp]
    exact hD n
  have hUc : Continuous fun t : ℝ => (U : ℂ → ℝ) (ee t) :=
    (continuous_of_mem U.2).comp (by fun_prop)
  have hcoef : ∀ n, fc (fun t => (f t : ℂ)) n = fc (fun t => ((U : ℂ → ℝ) (ee t) : ℂ)) n :=
    fun n => (fc_of_hasSum hFs hUs n).symm
  have htr : f =ᵐ[μT] fun t => (U : ℂ → ℝ) (ee t) :=
    ae_eq_of_fc_eq (Lp.memLp _) (memLp_circle hUc) hcoef
  have hΔ : ∀ z ∈ ball (0:ℂ) 1, Δ (U : ℂ → ℝ) z = 0 := fun z hz =>
    (hUh z (ball_subset_ball hr.le hz)).2.self_of_nhds
  have hxU := eq_embedH_of_trace hx U hΔ htr
  refine ⟨r, hr, U, hxU, hUh, ?_⟩
  subst hxU
  exact boundary_condition hA U hΔ hx

end SteklovBoundary

