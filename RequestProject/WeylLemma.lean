module

public import Mathlib
public import RequestProject.DiskDensity

/-!
# Weyl's lemma in the plane

A locally integrable `F` on an open set `U ⊆ ℂ` with a locally integrable weak gradient `G`
which is *weakly harmonic* (`∫ ⟪G, ∇φ⟫ = 0` for all compactly supported smooth `φ` in `U`)
agrees almost everywhere on `U` with a (classically) harmonic function.

The proof mollifies: convolutions `K ⋆ F` with smooth compactly supported kernels are smooth and
harmonic away from `∂U` (their Laplacian is a weak-harmonicity pairing), radial kernels reproduce
harmonic functions (mean value property), and convolutions commute (Fubini).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric InnerProductSpace Laplacian
open scoped ENNReal ContDiff Convolution RealInnerProductSpace

noncomputable section

namespace SteklovWeyl

/-- Convolution of a real kernel with a function, `(K ⋆ F)(x) = ∫ K t • F (x - t)`. -/
abbrev conv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : ℂ → ℝ) (F : ℂ → E) :
    ℂ → E :=
  K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] F

lemma conv_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (K : ℂ → ℝ) (F : ℂ → E)
    (x : ℂ) : conv K F x = ∫ t, K t • F (x - t) := by
  simp [conv, convolution_def]

/-- Derivative of a convolution with a smooth compactly supported kernel. -/
lemma fderiv_conv_apply {K : ℂ → ℝ} (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K)
    {F : ℂ → ℝ} (hF : LocallyIntegrable F volume) (z v : ℂ) :
    fderiv ℝ (conv K F) z v = ∫ s, fderiv ℝ K (z - s) v * F s := by
  have hd := hKc.hasFDerivAt_convolution_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (hK.of_le (by simp)) hF z
  have hcf : HasCompactSupport (fderiv ℝ K) := hKc.fderiv (𝕜 := ℝ)
  have hcf' : Continuous (fderiv ℝ K) := hK.continuous_fderiv (by simp)
  have hint := hcf.convolutionExists_left
    (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL ℂ) hcf' hF z
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hint]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have := integral_sub_left_eq_self (fun s => fderiv ℝ K (z - s) v * F s) (μ := volume) z
  simp only [sub_sub_cancel] at this
  rw [← this]

/-- Away from `∂U`, the derivative of `K ⋆ F` is the convolution of `K` with the weak gradient. -/
lemma fderiv_conv_eq (U : Set ℂ) {F : ℂ → ℝ} {G : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (hw : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v : ℂ,
      ∫ t, F t * fderiv ℝ φ t v = - ∫ t, inner ℝ (G t) v * φ t)
    {K : ℂ → ℝ} (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) {r : ℝ}
    (hKs : tsupport K ⊆ closedBall 0 r) {z : ℂ} (hz : closedBall z r ⊆ U) (v : ℂ) :
    fderiv ℝ (conv K F) z v = conv K (fun s => ⟪G s, v⟫) z := by
  have hsupp : ∀ s, K (z - s) ≠ 0 → s ∈ closedBall z r := by
    intro s hs
    have : z - s ∈ tsupport K := subset_tsupport _ hs
    have := hKs this
    rw [mem_closedBall, dist_zero_right] at this
    rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]; exact this
  have hts : tsupport (fun s => K (z - s)) ⊆ closedBall z r :=
    closure_minimal (fun s hs => hsupp s hs) isClosed_closedBall
  have hφ1 : ContDiff ℝ ∞ (fun s => K (z - s)) := hK.comp (contDiff_const.sub contDiff_id)
  have hφ2 : HasCompactSupport (fun s => K (z - s)) :=
    HasCompactSupport.intro (isCompact_closedBall z r)
      (fun s hs => by by_contra h; exact hs (hsupp s h))
  have key := hw _ hφ1 hφ2 (hts.trans hz) v
  have hder : ∀ t, fderiv ℝ (fun s => K (z - s)) t v = - fderiv ℝ K (z - t) v := by
    intro t
    have h1 : HasFDerivAt K (fderiv ℝ K (z - t)) (z - t) :=
      ((hK.of_le (by simp)).differentiable one_ne_zero
        _).hasFDerivAt
    have h2 : HasFDerivAt (fun s => K (z - s))
        ((fderiv ℝ K (z - t)).comp (-ContinuousLinearMap.id ℝ ℂ)) t :=
      h1.comp t ((hasFDerivAt_id t).const_sub z)
    rw [h2.fderiv]; simp
  simp only [hder] at key
  rw [fderiv_conv_apply hK hKc hF, conv_apply]
  have e1 : ∫ s, fderiv ℝ K (z - s) v * F s = - ∫ t, F t * -fderiv ℝ K (z - t) v := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only; ring
  have e2 : ∫ t, K t • ⟪G (z - t), v⟫ = ∫ t, ⟪G t, v⟫ * K (z - t) := by
    have := integral_sub_left_eq_self (fun t => ⟪G t, v⟫ * K (z - t)) (μ := volume) z
    simp only [sub_sub_cancel] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [smul_eq_mul]; ring
  rw [e1, key, neg_neg, e2]

lemma reflect_props {K : ℂ → ℝ} (hK : ContDiff ℝ ∞ K) {r : ℝ}
    (hKs : tsupport K ⊆ closedBall 0 r) (z : ℂ) :
    ContDiff ℝ ∞ (fun s => K (z - s)) ∧ HasCompactSupport (fun s => K (z - s)) ∧
      tsupport (fun s => K (z - s)) ⊆ closedBall z r ∧
      ∀ t v, fderiv ℝ (fun s => K (z - s)) t v = - fderiv ℝ K (z - t) v := by
  have hsupp : ∀ s, K (z - s) ≠ 0 → s ∈ closedBall z r := by
    intro s hs
    have : z - s ∈ tsupport K := subset_tsupport _ hs
    have := hKs this
    rw [mem_closedBall, dist_zero_right] at this
    rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]; exact this
  refine ⟨hK.comp (contDiff_const.sub contDiff_id), HasCompactSupport.intro
    (isCompact_closedBall z r) (fun s hs => by by_contra h; exact hs (hsupp s h)),
    closure_minimal (fun s hs => hsupp s hs) isClosed_closedBall, fun t v => ?_⟩
  have h1 : HasFDerivAt K (fderiv ℝ K (z - t)) (z - t) :=
    ((hK.of_le (by simp)).differentiable one_ne_zero _).hasFDerivAt
  have h2 : HasFDerivAt (fun s => K (z - s))
      ((fderiv ℝ K (z - t)).comp (-ContinuousLinearMap.id ℝ ℂ)) t :=
    h1.comp t ((hasFDerivAt_id t).const_sub z)
  rw [h2.fderiv]; simp

lemma locallyIntegrable_inner {G : ℂ → ℂ} (hG : LocallyIntegrable G volume) (v : ℂ) :
    LocallyIntegrable (fun s => ⟪G s, v⟫) volume := by
  rw [locallyIntegrable_iff] at hG ⊢
  exact fun k hk => (hG k hk).inner_const v

lemma integrable_kernel_mul {K : ℂ → ℝ} (hK : Continuous K) (hKc : HasCompactSupport K)
    {g : ℂ → ℝ} (hg : LocallyIntegrable g volume) (z : ℂ) :
    Integrable (fun s => K (z - s) * g s) volume := by
  have := hKc.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hK hg z
  have h2 := this.integrable_swap
  simpa [smul_eq_mul] using h2

/-- The Laplacian of a function on `ℂ` as a sum of second directional derivatives. -/
lemma laplacian_eq_fderiv_fderiv {f : ℂ → ℝ} {z : ℂ} (hf : ContDiffAt ℝ 2 f z) :
    Δ f z = fderiv ℝ (fun w => fderiv ℝ f w 1) z 1 +
      fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z Complex.I := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) z := by
    have := hf.fderiv_right (m := 1) (by norm_num)
    exact this.differentiableAt (by norm_num)
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]
  rw [fderiv_clm_apply hd (differentiableAt_const _),
    fderiv_clm_apply hd (differentiableAt_const _)]
  simp

lemma inner_eq_re_im (g w : ℂ) : ⟪g, w⟫ = w.re * ⟪g, 1⟫ + w.im * ⟪g, Complex.I⟫ := by
  simp [Complex.inner]

/-- **Convolutions of a weakly harmonic function are harmonic away from `∂U`.** -/
lemma harmonicAt_conv (U : Set ℂ) {F : ℂ → ℝ} {G : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (hG : LocallyIntegrable G volume)
    (hw : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v : ℂ,
      ∫ t, F t * fderiv ℝ φ t v = - ∫ t, inner ℝ (G t) v * φ t)
    (hh : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ t, ⟪G t, SteklovH1.grad φ t⟫ = 0)
    {K : ℂ → ℝ} (hK : ContDiff ℝ ∞ K) (hKc : HasCompactSupport K) {r r' : ℝ}
    (hKs : tsupport K ⊆ closedBall 0 r) (hrr : r < r') {y : ℂ} (hy : closedBall y r' ⊆ U) :
    HarmonicAt (conv K F) y := by
  have hsm : ContDiff ℝ ∞ (conv K F) := hKc.contDiff_convolution_left _ hK hF
  have hc2 : ∀ z, ContDiffAt ℝ 2 (conv K F) z := fun z => (hsm.of_le (by norm_cast)).contDiffAt
  -- the Laplacian vanishes wherever a slightly larger ball fits in `U`
  have hΔ : ∀ z ρ, r < ρ → closedBall z ρ ⊆ U → Δ (conv K F) z = 0 := by
    intro z ρ hρ hzU
    have hloc : ∀ v : ℂ, (fun w => fderiv ℝ (conv K F) w v) =ᶠ[𝓝 z]
        conv K (fun s => ⟪G s, v⟫) := by
      intro v
      filter_upwards [ball_mem_nhds z (sub_pos.2 hρ)] with w hwz
      refine fderiv_conv_eq U hF hw hK hKc hKs ?_ v
      intro p hp
      apply hzU
      rw [mem_closedBall] at hp ⊢
      rw [mem_ball] at hwz
      linarith [dist_triangle p w z]
    rw [laplacian_eq_fderiv_fderiv (hc2 z), (hloc 1).fderiv_eq, (hloc Complex.I).fderiv_eq,
      fderiv_conv_apply hK hKc (locallyIntegrable_inner hG 1),
      fderiv_conv_apply hK hKc (locallyIntegrable_inner hG Complex.I)]
    have hcd : Continuous (fderiv ℝ K) := hK.continuous_fderiv (by simp)
    have hi : ∀ v : ℂ, Integrable (fun s => fderiv ℝ K (z - s) v * ⟪G s, v⟫) volume := fun v =>
      integrable_kernel_mul (K := fun p => fderiv ℝ K p v) (by fun_prop)
        (hKc.fderiv_apply (𝕜 := ℝ) v) (locallyIntegrable_inner hG v) z
    rw [← integral_add (hi 1) (hi Complex.I)]
    obtain ⟨h1, h2, h3, h4⟩ := reflect_props hK hKs z
    have key := hh _ h1 h2 (h3.trans ((closedBall_subset_closedBall hρ.le).trans hzU))
    rw [← neg_eq_zero, ← integral_neg, ← key]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only
    rw [inner_eq_re_im (G s) (SteklovH1.grad _ s)]
    have hre : (SteklovH1.grad (fun s => K (z - s)) s).re = - fderiv ℝ K (z - s) 1 := by
      have := SteklovH1.inner_grad (fun s => K (z - s)) s 1
      rw [h4] at this; rw [← this]; simp [Complex.inner]
    have him : (SteklovH1.grad (fun s => K (z - s)) s).im = - fderiv ℝ K (z - s) Complex.I := by
      have := SteklovH1.inner_grad (fun s => K (z - s)) s Complex.I
      rw [h4] at this; rw [← this]; simp [Complex.inner]
    rw [hre, him]; ring
  refine ⟨hc2 y, ?_⟩
  have hpos : 0 < (r' - r) / 2 := by linarith
  filter_upwards [ball_mem_nhds y hpos] with z hz
  refine hΔ z ((r + r') / 2) (by linarith) ?_
  intro p hp
  apply hy
  rw [mem_closedBall] at hp ⊢
  rw [mem_ball] at hz
  linarith [dist_triangle p z y]

/-! ### A radial smooth kernel and the mean value property -/

/-- A radial smooth kernel supported in `ball 0 ε`. -/
def radK (ε : ℝ) (t : ℂ) : ℝ := Real.smoothTransition (1 - ‖t‖ ^ 2 / ε ^ 2)

lemma radK_contDiff (ε : ℝ) : ContDiff ℝ ∞ (radK ε) := by
  unfold radK
  exact Real.smoothTransition.contDiff.comp
    (contDiff_const.sub ((contDiff_norm_sq ℝ).div_const _))

lemma radK_continuous (ε : ℝ) : Continuous (radK ε) :=
  (radK_contDiff ε).continuous

lemma radK_nonneg (ε : ℝ) (t : ℂ) : 0 ≤ radK ε t := Real.smoothTransition.nonneg _

lemma radK_le_one (ε : ℝ) (t : ℂ) : radK ε t ≤ 1 := Real.smoothTransition.le_one _

lemma radK_eq_zero {ε : ℝ} (hε : 0 < ε) {t : ℂ} (ht : ε ≤ ‖t‖) : radK ε t = 0 := by
  unfold radK
  apply Real.smoothTransition.zero_of_nonpos
  have : 1 ≤ ‖t‖ ^ 2 / ε ^ 2 := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  linarith

lemma radK_tsupport {ε : ℝ} (hε : 0 < ε) : tsupport (radK ε) ⊆ closedBall 0 ε := by
  refine closure_minimal (fun t ht => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_zero_right]
  by_contra h
  exact ht (radK_eq_zero hε (not_le.1 h).le)

lemma radK_hasCompactSupport {ε : ℝ} (hε : 0 < ε) : HasCompactSupport (radK ε) :=
  (isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _) (radK_tsupport hε)

lemma radK_zero {ε : ℝ} : radK ε 0 = 1 := by
  simp [radK, Real.smoothTransition.one]

lemma radK_integral_pos {ε : ℝ} (hε : 0 < ε) : 0 < ∫ t, radK ε t := by
  refine (radK_continuous ε).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (radK_hasCompactSupport hε) (radK_nonneg ε) (x := 0) ?_
  rw [radK_zero]; exact one_ne_zero

lemma radK_rot (ε : ℝ) (a t : ℂ) (ha : ‖a‖ = 1) : radK ε (a * t) = radK ε t := by
  simp [radK, ha]

/-- Circle averages with an arbitrary complex offset `x - e^{iα} t`. -/
lemma integral_rot_eq {h : ℂ → ℝ} {x t : ℂ} (hh : HarmonicOnNhd h (closedBall x ‖t‖)) :
    ∫ α in (0:ℝ)..2 * Real.pi, h (x - Complex.exp (α * Complex.I) * t) =
      2 * Real.pi * h x := by
  set β := Complex.arg (-t)
  have hrep : ∀ α : ℝ, x - Complex.exp (α * Complex.I) * t = circleMap x ‖t‖ (α + β) := by
    intro α
    have := Complex.norm_mul_exp_arg_mul_I (-t)
    rw [norm_neg] at this
    simp only [circleMap, Complex.ofReal_add, add_mul, Complex.exp_add]
    have e : x - Complex.exp (α * Complex.I) * t =
        x + Complex.exp (α * Complex.I) * (‖t‖ * Complex.exp (β * Complex.I)) := by
      rw [this]; ring
    rw [e]; ring
  simp_rw [hrep]
  rw [intervalIntegral.integral_comp_add_right (fun θ => h (circleMap x ‖t‖ θ)), zero_add]
  have hper : Function.Periodic (fun θ => h (circleMap x ‖t‖ θ)) (2 * Real.pi) :=
    fun θ => by simp only [periodic_circleMap x ‖t‖ θ]
  rw [show 2 * Real.pi + β = β + 2 * Real.pi by ring, hper.intervalIntegral_add_eq β 0,
    zero_add]
  have hmv := HarmonicOnNhd.circleAverage_eq (R := ‖t‖) (by rwa [abs_norm])
  rw [Real.circleAverage_def] at hmv
  rw [← hmv, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- **Mean value property against a radial kernel.** -/
lemma conv_radK_harmonic {h : ℂ → ℝ} (hc : Continuous h) {x : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hh : HarmonicOnNhd h (closedBall x ε)) :
    conv (radK ε) h x = (∫ t, radK ε t) * h x := by
  set k := radK ε with hk
  rw [conv_apply]
  simp only [smul_eq_mul]
  -- rotation invariance
  have hrot : ∀ α : ℝ, ∫ t, k t * h (x - t) =
      ∫ t, k t * h (x - Complex.exp (α * Complex.I) * t) := by
    intro α
    set R := rotation (Circle.exp α)
    have hR : ∀ t, R t = Complex.exp (α * Complex.I) * t := fun t => by
      simp [R, rotation_apply, Circle.coe_exp]
    have hmp := R.measurePreserving
    have := hmp.integral_comp R.toHomeomorph.measurableEmbedding (fun t => k t * h (x - t))
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hR]
    rw [hk, radK_rot ε _ t (by simp)]
  -- a bound for `h` on the closed ball
  obtain ⟨M, hM⟩ := (isCompact_closedBall x ε).exists_bound_of_continuousOn hc.continuousOn
  set f : ℝ → ℂ → ℝ := fun α t => k t * h (x - Complex.exp (α * Complex.I) * t) with hf
  have hfc : Continuous (Function.uncurry f) := by
    simp only [hf]
    have := radK_continuous ε
    fun_prop
  have hint : Integrable (Function.uncurry f)
      ((volume.restrict (Ioc 0 (2 * Real.pi))).prod volume) := by
    have hg : Integrable (fun p : ℝ × ℂ => (1 : ℝ) * (closedBall (0:ℂ) ε).indicator
        (fun _ => M) p.2) ((volume.restrict (Ioc 0 (2 * Real.pi))).prod volume) := by
      refine Integrable.mul_prod (f := fun _ : ℝ => (1:ℝ)) (integrable_const (1:ℝ)) ?_
      exact (integrableOn_const (measure_closedBall_lt_top (x := (0:ℂ)) (r := ε)).ne).integrable_indicator
        measurableSet_closedBall
    refine hg.mono' hfc.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    obtain ⟨α, t⟩ := p
    simp only [Function.uncurry, hf, one_mul]
    by_cases ht : t ∈ closedBall (0:ℂ) ε
    · rw [indicator_of_mem ht, norm_mul]
      have h1 : ‖k t‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (radK_nonneg ε t)]; exact radK_le_one ε t
      have h2 : ‖h (x - Complex.exp (α * Complex.I) * t)‖ ≤ M := by
        apply hM
        rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul,
          Complex.norm_exp_ofReal_mul_I, one_mul]
        simpa using ht
      calc ‖k t‖ * ‖h (x - Complex.exp (α * Complex.I) * t)‖ ≤ 1 * M :=
            mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
        _ = M := one_mul M
    · rw [indicator_of_notMem ht]
      have : ε ≤ ‖t‖ := by
        rw [mem_closedBall, dist_zero_right, not_le] at ht; exact ht.le
      simp [hk, radK_eq_zero hε this]
  have hswap := integral_integral_swap hint
  have hL : ∫ α in Ioc 0 (2 * Real.pi), ∫ t, f α t = 2 * Real.pi * ∫ t, k t * h (x - t) := by
    simp only [hf, ← hrot]
    rw [setIntegral_const, Real.volume_real_Ioc_of_le (by positivity), smul_eq_mul, sub_zero]
  have hR : ∫ t, ∫ α in Ioc 0 (2 * Real.pi), f α t = 2 * Real.pi * ((∫ t, k t) * h x) := by
    rw [← integral_mul_const, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hf]
    by_cases ht : ‖t‖ < ε
    · rw [integral_const_mul, ← intervalIntegral.integral_of_le (by positivity),
        integral_rot_eq (hh.mono (closedBall_subset_closedBall ht.le))]
      ring
    · simp [hk, radK_eq_zero hε (not_lt.1 ht)]
  have := hswap.symm
  rw [hL, hR] at this
  exact (mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0) this).symm

/-! ### Convolutions commute -/

lemma exists_support_closedBall {A : ℂ → ℝ} (hAc : HasCompactSupport A) :
    ∃ R, 0 ≤ R ∧ ∀ t, A t ≠ 0 → ‖t‖ ≤ R := by
  obtain ⟨R, hR⟩ := hAc.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun t ht => ?_⟩
  have := hR (subset_tsupport _ ht)
  rw [mem_closedBall, dist_zero_right] at this
  exact this.trans (le_max_left _ _)

/-- **Fubini for iterated convolutions**: `A ⋆ (B ⋆ F) = B ⋆ (A ⋆ F)`. -/
lemma conv_conv_comm {A B : ℂ → ℝ} (hA : Continuous A) (hAc : HasCompactSupport A)
    (hB : Continuous B) (hBc : HasCompactSupport B) {F : ℂ → ℝ}
    (hF : LocallyIntegrable F volume) (hFm : StronglyMeasurable F) (x : ℂ) :
    conv A (conv B F) x = conv B (conv A F) x := by
  simp only [conv_apply, smul_eq_mul]
  obtain ⟨RA, hRA0, hRA⟩ := exists_support_closedBall hAc
  obtain ⟨RB, hRB0, hRB⟩ := exists_support_closedBall hBc
  obtain ⟨MB, hMB⟩ := hB.bounded_above_of_compact_support hBc
  set R := RA + RB
  set Φ : ℂ → ℂ → ℝ := fun t s => A t * (B s * F (x - t - s)) with hΦ
  set Ψ : ℂ × ℂ → ℝ := fun p => A p.1 * (B (p.2 - p.1) * F (x - p.2)) with hΨ
  have hΨm : AEStronglyMeasurable Ψ (volume.prod volume) := by
    have h1 : StronglyMeasurable (fun p : ℂ × ℂ => F (x - p.2)) :=
      hFm.comp_measurable (by fun_prop)
    have h2 : Continuous (fun p : ℂ × ℂ => A p.1) := by fun_prop
    have h3 : Continuous (fun p : ℂ × ℂ => B (p.2 - p.1)) := by fun_prop
    exact (h2.aestronglyMeasurable.mul (h3.aestronglyMeasurable.mul h1.aestronglyMeasurable))
  have hΨi : Integrable Ψ (volume.prod volume) := by
    have hFi : Integrable ((closedBall x R).indicator F) volume :=
      (hF.integrableOn_isCompact (isCompact_closedBall x R)).integrable_indicator
        measurableSet_closedBall
    have hg2 : Integrable (fun y => MB * ‖(closedBall x R).indicator F (x - y)‖) volume :=
      ((hFi.comp_sub_left x).norm).const_mul MB
    have hg : Integrable (fun p : ℂ × ℂ => ‖A p.1‖ * (MB * ‖(closedBall x R).indicator F
        (x - p.2)‖)) (volume.prod volume) :=
      Integrable.mul_prod (hA.integrable_of_hasCompactSupport hAc).norm hg2
    refine hg.mono' hΨm (Eventually.of_forall fun p => ?_)
    obtain ⟨t, y⟩ := p
    simp only [hΨ, norm_mul]
    by_cases hAt : A t = 0
    · simp [hAt]
    by_cases hBt : B (y - t) = 0
    · have hMB0 : 0 ≤ MB := (norm_nonneg _).trans (hMB 0)
      simp only [hBt, norm_zero, zero_mul, mul_zero]
      exact mul_nonneg (norm_nonneg _) (mul_nonneg hMB0 (norm_nonneg _))
    have ht := hRA t hAt
    have hy := hRB _ hBt
    have hyR : x - y ∈ closedBall x R := by
      rw [mem_closedBall, dist_eq_norm, sub_sub_cancel_left, norm_neg]
      have := norm_le_norm_add_norm_sub' y t
      rw [norm_sub_rev] at hy
      linarith [norm_sub_rev y t]
    rw [indicator_of_mem hyR]
    gcongr
    exact (Real.norm_eq_abs _ ▸ hMB (y - t))
  have hΦi : Integrable (Function.uncurry Φ) (volume.prod volume) := by
    have hmp := measurePreserving_prod_add (μ := (volume : Measure ℂ)) (ν := (volume : Measure ℂ))
    have := (hmp.integrable_comp hΨm).2 hΨi
    refine this.congr (Eventually.of_forall fun p => ?_)
    simp only [Function.comp, hΨ, hΦ, Function.uncurry]
    congr 3 <;> ring
  have hswap := integral_integral_swap hΦi
  have eL : ∫ t, A t * ∫ s, B s * F (x - t - s) = ∫ t, ∫ s, Φ t s := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hΦ]; rw [integral_const_mul]
  have eR : ∫ s, B s * ∫ t, A t * F (x - s - t) = ∫ s, ∫ t, Φ t s := by
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hΦ]; rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [show x - s - t = x - t - s by ring]; ring
  rw [eL, eR, hswap]

/-! ### Interior regions and the a.e. identification -/

/-- Points of `U` whose closed `s`-ball lies in `U` for some `s > ε`. -/
def S (U : Set ℂ) (ε : ℝ) : Set ℂ := {x | ∃ s > ε, closedBall x s ⊆ U}

lemma isOpen_S (U : Set ℂ) (ε : ℝ) : IsOpen (S U ε) := by
  rw [Metric.isOpen_iff]
  rintro x ⟨s, hs, hsU⟩
  refine ⟨(s - ε) / 2, by linarith, fun y hy => ⟨(s + ε) / 2, by linarith, fun p hp => hsU ?_⟩⟩
  rw [mem_ball] at hy; rw [mem_closedBall] at hp ⊢
  linarith [dist_triangle p y x]

lemma S_subset (U : Set ℂ) {ε : ℝ} (hε : 0 ≤ ε) : S U ε ⊆ U := by
  rintro x ⟨s, hs, hsU⟩
  exact hsU (mem_closedBall_self (by linarith))

lemma S_anti (U : Set ℂ) {ε ε' : ℝ} (h : ε ≤ ε') : S U ε' ⊆ S U ε := by
  rintro x ⟨s, hs, hsU⟩
  exact ⟨s, lt_of_le_of_lt h hs, hsU⟩

lemma iUnion_S {U : Set ℂ} (hU : IsOpen U) : ⋃ n : ℕ, S U (1 / (n + 1)) = U := by
  refine Subset.antisymm (iUnion_subset fun n => S_subset U (by positivity)) fun x hx => ?_
  obtain ⟨s, hs, hsU⟩ := Metric.isOpen_iff.1 hU x hx
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (half_pos hs)
  refine mem_iUnion.2 ⟨n, s / 2, hn, (closedBall_subset_ball (half_lt_self hs)).trans hsU⟩

/-- The standard bump sequence with `rOut = 1/(n+2)`. -/
def bumpSeq (n : ℕ) : ContDiffBump (0 : ℂ) :=
  ⟨1 / (n + 2) / 2, 1 / (n + 2), by positivity, by
    have : (0:ℝ) < 1 / (n + 2) := by positivity
    linarith⟩

lemma bumpSeq_rOut (n : ℕ) : (bumpSeq n).rOut = 1 / (n + 2) := rfl

lemma tendsto_bumpSeq_rOut : Tendsto (fun n => (bumpSeq n).rOut) atTop (𝓝 0) := by
  simp only [bumpSeq_rOut]
  have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have h2 : Tendsto (fun n : ℕ => (1:ℝ) / ((n + 1 : ℕ) + 1)) atTop (𝓝 0) :=
    this.comp (tendsto_add_atTop_nat 1)
  refine h2.congr fun n => ?_
  push_cast; ring

lemma eventually_bumpSeq_lt {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ n in atTop, (bumpSeq n).rOut < δ :=
  (tendsto_order.1 tendsto_bumpSeq_rOut).2 δ hδ

/-- **Mollifications of an `L²` function converge in `L²`** (along the bump sequence). -/
lemma tendsto_eLpNorm_moll {F : ℂ → ℝ} (hFL : MemLp F 2 volume) (hFm : StronglyMeasurable F) :
    Tendsto (fun n => eLpNorm (F - SteklovDensity.moll (bumpSeq n) F) 2 volume) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro e he
  have hpos : 0 < (min e 1).toReal :=
    ENNReal.toReal_pos (lt_min he one_pos).ne' (ne_top_of_le_ne_top ENNReal.one_ne_top
      (min_le_right _ _))
  obtain ⟨δ, hδ, hm⟩ := SteklovDensity.moll_tendsto hFL hFm hpos
  filter_upwards [eventually_bumpSeq_lt hδ] with n hn
  refine (hm _ hn).trans ?_
  rw [ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_right _ _))]
  exact min_le_left _ _

/-- **Key identification**: on `S U ε`, `(∫ k_ε) F = k_ε ⋆ F` almost everywhere. -/
lemma ae_eq_conv_radK (U : Set ℂ) {F : ℂ → ℝ} {G : ℂ → ℂ} (hFL : MemLp F 2 volume)
    (hFm : StronglyMeasurable F) (hG : LocallyIntegrable G volume)
    (hw : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v : ℂ,
      ∫ t, F t * fderiv ℝ φ t v = - ∫ t, inner ℝ (G t) v * φ t)
    (hh : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ t, ⟪G t, SteklovH1.grad φ t⟫ = 0)
    {ε : ℝ} (hε : 0 < ε) :
    (fun x => (∫ t, radK ε t) * F x) =ᵐ[volume.restrict (S U ε)] conv (radK ε) F := by
  have hF := hFL.locallyIntegrable one_le_two
  set c := ∫ t, radK ε t with hc
  set W := conv (radK ε) F with hW
  set u : ℕ → ℂ → ℝ := fun n => SteklovDensity.moll (bumpSeq n) F with hu
  have hWc : Continuous W :=
    (radK_hasCompactSupport hε).continuous_convolution_left _ (radK_continuous ε) hF
  have huc : ∀ n, Continuous (u n) := fun n => SteklovDensity.continuous_moll _ hF
  -- pointwise identity `c u_n = η_n ⋆ W` near points of `S U ε`
  have hpt : ∀ x ∈ S U ε, ∀ᶠ n in atTop, c * u n x = conv ((bumpSeq n).normed volume) W x := by
    rintro x ⟨s, hs, hsU⟩
    filter_upwards [eventually_bumpSeq_lt (sub_pos.2 hs)] with n hn
    set b := bumpSeq n
    have hharm : HarmonicOnNhd (u n) (closedBall x ε) := by
      intro z hz
      refine harmonicAt_conv U hF hG hw hh (b.contDiff_normed (n := ⊤))
        b.hasCompactSupport_normed (r := b.rOut) (r' := s - ε)
        (by rw [b.tsupport_normed_eq]) hn ?_
      intro p hp
      apply hsU
      rw [mem_closedBall] at hp hz ⊢
      linarith [dist_triangle p z x]
    have hmv := conv_radK_harmonic (huc n) hε hharm
    rw [← hmv]
    exact conv_conv_comm (radK_continuous ε) (radK_hasCompactSupport hε)
      (b.continuous_normed) b.hasCompactSupport_normed hF hFm x
  -- Fatou in `L²(S)`
  set f : ℕ → ℂ → ℝ := fun n x => c * F x - c * u n x with hf
  have hlim : ∀ᵐ x ∂(volume.restrict (S U ε)), Tendsto (fun n => f n x) atTop
      (𝓝 (c * F x - W x)) := by
    rw [ae_restrict_iff' (isOpen_S U ε).measurableSet]
    refine Eventually.of_forall fun x hx => ?_
    refine tendsto_const_nhds.sub ?_
    have h2 := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
      tendsto_bumpSeq_rOut hWc x
    exact h2.congr' ((hpt x hx).mono fun n hn => hn.symm)
  have hfm : ∀ n, AEStronglyMeasurable (f n) (volume.restrict (S U ε)) := fun n =>
    ((hFm.aestronglyMeasurable.const_mul c).sub
      ((huc n).aestronglyMeasurable.const_mul c)).restrict
  have hfat := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := 2) hfm _ hlim
  have hbound : ∀ n, eLpNorm (f n) 2 (volume.restrict (S U ε)) ≤
      ‖c‖ₑ * eLpNorm (F - u n) 2 volume := by
    intro n
    have : f n = c • (F - u n) := by
      funext x; simp [hf, mul_sub]
    rw [this, eLpNorm_const_smul]
    exact mul_le_mul_right (eLpNorm_restrict_le _ _ _ _) _
  have hto : Tendsto (fun n => ‖c‖ₑ * eLpNorm (F - u n) 2 volume) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (tendsto_eLpNorm_moll hFL hFm) (a := ‖c‖ₑ)
      (Or.inr enorm_ne_top)
    simpa using this
  have hzero : eLpNorm (fun x => c * F x - W x) 2 (volume.restrict (S U ε)) = 0 := by
    refine le_antisymm (hfat.trans ?_) (zero_le)
    have hli : atTop.liminf (fun n => ‖c‖ₑ * eLpNorm (F - u n) 2 volume) = 0 := hto.liminf_eq
    rw [← hli]
    exact liminf_le_liminf (Eventually.of_forall hbound)
  have hmeas : AEStronglyMeasurable (fun x => c * F x - W x) (volume.restrict (S U ε)) :=
    ((hFm.aestronglyMeasurable.const_mul c).sub hWc.aestronglyMeasurable).restrict
  rw [eLpNorm_eq_zero_iff hmeas two_ne_zero] at hzero
  filter_upwards [hzero] with x hx
  simpa [sub_eq_zero] using hx

/-! ### Weyl's lemma -/

/-- **Weyl's lemma (planar, `H¹` form).** Let `U ⊆ ℂ` be open, `F ∈ L²(ℂ)` (strongly measurable
representative) with locally integrable weak gradient `G` on `U`, i.e.
`∫ F ∂_v φ = -∫ ⟪G, v⟫ φ` for all compactly supported smooth `φ` with support in `U`, and assume
`F` is weakly harmonic: `∫ ⟪G, ∇φ⟫ = 0` for all such `φ`. Then `F` agrees almost everywhere on
`U` with a function harmonic (in the classical `C²`, `Δ h = 0` sense) on `U`. -/
theorem weyl_lemma {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℝ} {G : ℂ → ℂ}
    (hFL : MemLp F 2 volume) (hFm : StronglyMeasurable F) (hG : LocallyIntegrable G volume)
    (hw : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v : ℂ,
      ∫ t, F t * fderiv ℝ φ t v = - ∫ t, inner ℝ (G t) v * φ t)
    (hh : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ t, ⟪G t, SteklovH1.grad φ t⟫ = 0) :
    ∃ h : ℂ → ℝ, HarmonicOnNhd h U ∧ F =ᵐ[volume.restrict U] h := by
  have hF := hFL.locallyIntegrable one_le_two
  set ε : ℕ → ℝ := fun n => 1 / (n + 1) with hεdef
  have hε : ∀ n, 0 < ε n := fun n => by positivity
  set Sn : ℕ → Set ℂ := fun n => S U (ε n) with hSn
  set c : ℕ → ℝ := fun n => ∫ t, radK (ε n) t with hc
  set w : ℕ → ℂ → ℝ := fun n => (c n)⁻¹ • conv (radK (ε n)) F with hw'
  have hwc : ∀ n, Continuous (w n) := fun n =>
    ((radK_hasCompactSupport (hε n)).continuous_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (radK_continuous _) hF).const_smul (c n)⁻¹
  have hharm : ∀ n, HarmonicOnNhd (w n) (Sn n) := by
    rintro n x ⟨s, hs, hsU⟩
    exact (harmonicAt_conv U hF hG hw hh (radK_contDiff _) (radK_hasCompactSupport (hε n))
      (radK_tsupport (hε n)) hs hsU).const_smul
  have hae : ∀ n, F =ᵐ[volume.restrict (Sn n)] w n := by
    intro n
    filter_upwards [ae_eq_conv_radK U hFL hFm hG hw hh (hε n)] with x hx
    have hc0 : c n ≠ 0 := (radK_integral_pos (hε n)).ne'
    simp only [hw', Pi.smul_apply, smul_eq_mul, ← hx]
    field_simp
    rfl
  have hagree : ∀ m n, EqOn (w m) (w n) (Sn m ∩ Sn n) := by
    intro m n
    have hmn : w m =ᵐ[volume.restrict (Sn m ∩ Sn n)] w n := by
      have h1 := ae_restrict_of_ae_restrict_of_subset (inter_subset_left (t := Sn n)) (hae m)
      have h2 := ae_restrict_of_ae_restrict_of_subset (inter_subset_right (s := Sn m)) (hae n)
      filter_upwards [h1, h2] with x hx1 hx2
      rw [← hx1, ← hx2]
    exact Measure.eqOn_open_of_ae_eq hmn ((isOpen_S U _).inter (isOpen_S U _))
      (hwc m).continuousOn (hwc n).continuousOn
  classical
  set N : ℂ → ℕ := fun x => if hx : ∃ n, x ∈ Sn n then Nat.find hx else 0 with hN
  have hNmem : ∀ n x, x ∈ Sn n → x ∈ Sn (N x) := by
    intro n x hx
    have hex : ∃ n, x ∈ Sn n := ⟨n, hx⟩
    simp only [hN, dif_pos hex]
    exact Nat.find_spec hex
  set h : ℂ → ℝ := fun x => w (N x) x with hh'
  have heq : ∀ n, EqOn h (w n) (Sn n) := fun n x hx =>
    hagree (N x) n ⟨hNmem n x hx, hx⟩
  have hUn : (⋃ n, Sn n) = U := iUnion_S hU
  refine ⟨h, fun x hx => ?_, ?_⟩
  · rw [← hUn, mem_iUnion] at hx
    obtain ⟨n, hn⟩ := hx
    have hev : h =ᶠ[𝓝 x] w n :=
      Filter.eventually_of_mem ((isOpen_S U _).mem_nhds hn) (heq n)
    exact (harmonicAt_congr_nhds hev).2 (hharm n x hn)
  · rw [← hUn, EventuallyEq, ae_restrict_iUnion_iff]
    intro n
    filter_upwards [hae n, ae_restrict_mem (isOpen_S U (ε n)).measurableSet] with x hx hxS
    rw [hx, heq n hxS]

end SteklovWeyl
