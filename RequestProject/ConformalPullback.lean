module

public import RequestProject.ArcLength
public import RequestProject.HolomorphicInverse
public import RequestProject.MinMaxTransfer
public import RequestProject.PaperStatements

/-!
# Proposition 2.1.1 (conformal pullback of the Steklov spectrum)

For `F` holomorphic on a neighbourhood of `𝔻̄`, injective on `𝔻̄` with `F' ≠ 0` on `𝕋`, and
`Ω = F(𝔻)`, we prove `Spec_St(Ω) = Spec_St(𝔻, |F'|)` for the min–max spectra of `Defs.lean`.

Ingredients:
* the Dirichlet energy is conformally invariant (change of variables with Jacobian `|F'|²`);
* the boundary mass transforms with the arc-length factor `|F'|` (area formula for the curve
  `t ↦ F(e^{it})`, `RequestProject.ArcLength`);
* `frontier Ω = F(𝕋)`;
* test functions are transported with smooth cut-offs: `u ↦ χ · (u ∘ F)` and
  `w ↦ χ' · (w ∘ F⁻¹)`, using the holomorphic inverse on a neighbourhood of `F(𝔻̄)`;
* the min–max transfer lemma `Steklov.minMax_le_of_transfer`.
-/

@[expose] public section

open Set Filter Topology Metric MeasureTheory
open scoped ENNReal ContDiff Real Manifold

noncomputable section

namespace ConformalPullback

/-- Smooth cut-off: `χ = 1` on a neighbourhood of a compact `K`, `tsupport χ ⊆ U`. -/
theorem exists_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ (∃ W, IsOpen W ∧ K ⊆ W ∧ ∀ z ∈ W, χ z = 1) ∧
      tsupport χ ⊆ U := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  obtain ⟨χ, hχ, -, hsupp, hone⟩ := exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, ℂ)
    (n := (⊤ : ℕ∞)) (isOpen_thickening (δ := δ) (E := K)) (isClosed_cthickening (δ := δ / 2))
    (cthickening_subset_thickening' hδ (by linarith) K)
  refine ⟨χ, contMDiff_iff_contDiff.1 hχ, ⟨thickening (δ / 2) K, isOpen_thickening,
    self_subset_thickening (by positivity) K, fun z hz =>
      (hone z).1 (thickening_subset_cthickening _ _ hz)⟩, ?_⟩
  rw [tsupport, hsupp]
  exact (closure_thickening_subset_cthickening _ _).trans hsub

/-- Cut-off composition is smooth. -/
theorem contDiff_mul_comp {χ : ℂ → ℝ} {Φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ U) (hΦ : ContDiffOn ℝ ∞ Φ U) {u : ℂ → ℝ}
    (hu : ContDiff ℝ ∞ u) : ContDiff ℝ ∞ (fun z => χ z * u (Φ z)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ U
  · exact hχ.contDiffAt.mul (hu.contDiffAt.comp z (hΦ.contDiffAt (hU.mem_nhds hz)))
  · have hz' : z ∉ tsupport χ := fun h => hz (hsupp h)
    rw [notMem_tsupport_iff_eventuallyEq] at hz'
    refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [hz'] with x hx
    simp [hx]

/-- Holomorphic maps are real-smooth. -/
lemma contDiffOn_of_differentiableOn {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) : ContDiffOn ℝ ∞ F U :=
  (hF.contDiffOn hU).restrict_scalars ℝ

variable {F : ℂ → ℂ} {U : Set ℂ}

/-- `frontier F(𝔻) = F(𝕋)`. -/
theorem frontier_image_ball (hcb : closedBall (0 : ℂ) 1 ⊆ U) (hF : DifferentiableOn ℂ F U)
    (hinj : InjOn F (closedBall 0 1)) :
    frontier (F '' ball 0 1) = F '' sphere 0 1 := by
  have hopen : IsOpen (F '' ball 0 1) :=
    HolInv.isOpen_image (hF.mono (ball_subset_closedBall.trans hcb))
      (hinj.mono ball_subset_closedBall) subset_rfl isOpen_ball
  have hcont : ContinuousOn F (closedBall 0 1) := hF.continuousOn.mono hcb
  have hcl : closure (F '' ball 0 1) = F '' closedBall 0 1 := by
    apply le_antisymm
    · exact closure_minimal (image_mono ball_subset_closedBall)
        ((isCompact_closedBall 0 1).image_of_continuousOn hcont).isClosed
    · have := ContinuousOn.image_closure (s := ball (0 : ℂ) 1)
        (by rwa [closure_ball (0 : ℂ) one_ne_zero])
      rwa [closure_ball (0 : ℂ) one_ne_zero] at this
  rw [frontier, hcl, hopen.interior_eq, ← closedBall_diff_ball, hinj.image_diff,
    inter_eq_right.2 ball_subset_closedBall]


/-- **Boundary change of variables.**  For `F` holomorphic near `𝔻̄` and injective on `𝔻̄`,
`∫_{F(𝕋)} g dμH¹ = ∫_0^{2π} g(F(e^{it})) |F'(e^{it})| dt`. -/
theorem boundary_lintegral (hU : IsOpen U) (hcb : closedBall (0 : ℂ) 1 ⊆ U)
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F (closedBall 0 1)) {g : ℂ → ℝ≥0∞}
    (hg : Measurable g) :
    ∫⁻ z in F '' sphere 0 1, g z ∂μH[1] =
      ∫⁻ t in Ioc 0 (2 * π), g (F (Complex.exp (t * Complex.I))) *
        ENNReal.ofReal ‖deriv F (Complex.exp (t * Complex.I))‖ := by
  set c := circleMap (0 : ℂ) 1
  have hc : ∀ t : ℝ, c t = Complex.exp (t * Complex.I) := fun t => by simp [c, circleMap]
  have hsph : ∀ t, c t ∈ sphere (0 : ℂ) 1 := fun t => by
    rw [mem_sphere_zero_iff_norm]; simp [c]
  have hU' : ∀ t, c t ∈ U := fun t => hcb (sphere_subset_closedBall (hsph t))
  have hγ : ∀ t, HasDerivAt (F ∘ c) (deriv F (c t) * (c t * Complex.I)) t := fun t =>
    (hF.differentiableAt (hU.mem_nhds (hU' t))).hasDerivAt.comp t (hasDerivAt_circleMap 0 1 t)
  have hγ' : Continuous fun t => deriv F (c t) * (c t * Complex.I) := by
    refine Continuous.mul ?_ ((continuous_circleMap 0 1).mul continuous_const)
    exact ((hF.deriv hU).continuousOn).comp_continuous (continuous_circleMap 0 1) hU'
  have hinjc : InjOn c (Ioc 0 (2 * π)) := by
    have := injOn_circleMap_of_abs_sub_le (a := 0) (b := 2 * π) (c := 0) one_ne_zero
      (by rw [zero_sub, abs_neg, abs_of_pos Real.two_pi_pos])
    rwa [Set.uIoc_of_le Real.two_pi_pos.le] at this
  have hinjγ : InjOn (F ∘ c) (Ioc 0 (2 * π)) :=
    hinj.comp hinjc fun t _ => sphere_subset_closedBall (hsph t)
  have himg : (F ∘ c) '' Ioc 0 (2 * π) = F '' sphere 0 1 := by
    rw [image_comp, image_circleMap_Ioc, abs_one]
  rw [← himg, ArcLength.lintegral_image_hausdorffMeasure hγ hγ' Ioc_subset_Icc_self
    measurableSet_Ioc hinjγ hg]
  refine lintegral_congr fun t => ?_
  simp only [Function.comp, hc]
  rw [mul_comm, ← ofReal_norm_eq_enorm, norm_mul, norm_mul, Complex.norm_I, ← hc,
    show ‖c t‖ = 1 by simpa using hsph t]
  simp


/-- The real-linear map `z ↦ z * c`. -/
abbrev mulR (c : ℂ) : ℂ →L[ℝ] ℂ :=
  (ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ

lemma mulR_apply (c z : ℂ) : mulR c z = z * c := by simp [mulR]

/-- Precomposition with multiplication by `c` scales operator norms by `|c|`. -/
lemma norm_comp_mulR (L : ℂ →L[ℝ] ℝ) (c : ℂ) : ‖L.comp (mulR c)‖ = ‖L‖ * ‖c‖ := by
  apply le_antisymm
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    rw [ContinuousLinearMap.comp_apply, mulR_apply]
    calc ‖L (z * c)‖ ≤ ‖L‖ * ‖z * c‖ := L.le_opNorm _
      _ = ‖L‖ * ‖c‖ * ‖z‖ := by rw [norm_mul]; ring
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    have hc' : 0 < ‖c‖ := norm_pos_iff.2 hc
    rw [← le_div_iff₀ hc']
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    have : L z = (L.comp (mulR c)) (z / c) := by
      rw [ContinuousLinearMap.comp_apply, mulR_apply, div_mul_cancel₀ _ hc]
    rw [this]
    calc ‖(L.comp (mulR c)) (z / c)‖ ≤ ‖L.comp (mulR c)‖ * ‖z / c‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖L.comp (mulR c)‖ / ‖c‖ * ‖z‖ := by rw [norm_div]; ring

/-- The Jacobian determinant of `z ↦ z * c` is `|c|²`. -/
lemma det_mulR (c : ℂ) : (mulR c).det = ‖c‖ ^ 2 := by
  have : ((mulR c : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) = Algebra.lmul ℝ ℂ c := by
    ext z; simp [mulR, mul_comm]
  rw [ContinuousLinearMap.det, this, ← Algebra.norm_apply, Algebra.norm_complex_apply,
    Complex.normSq_eq_norm_sq]

/-- **Conformal invariance of the Dirichlet energy.** -/
theorem dirichletEnergy_image (hU : IsOpen U) (hF : DifferentiableOn ℂ F U)
    {s : Set ℂ} (hs : s ⊆ U) (hsm : MeasurableSet s) (hinj : InjOn F s) {u : ℂ → ℝ}
    (hu : Differentiable ℝ u) :
    Steklov.dirichletEnergy (F '' s) u = ∫⁻ z in s, ‖fderiv ℝ (u ∘ F) z‖ₑ ^ 2 := by
  have hFd : ∀ x ∈ s, HasFDerivAt F (mulR (deriv F x)) x := fun x hx =>
    ((hF.differentiableAt (hU.mem_nhds (hs hx))).hasDerivAt.hasFDerivAt).restrictScalars ℝ
  unfold Steklov.dirichletEnergy
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hsm
    (fun x hx => (hFd x hx).hasFDerivWithinAt) hinj]
  refine setLIntegral_congr_fun hsm fun x hx => ?_
  rw [fderiv_comp x (hu (F x)) (hFd x hx).differentiableAt, (hFd x hx).fderiv, det_mulR,
    ← enorm_norm ((fderiv ℝ u (F x)).comp (mulR (deriv F x))), norm_comp_mulR,
    abs_of_nonneg (by positivity), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm,
    enorm_mul, enorm_norm, enorm_norm, mul_pow, mul_comm]


/-- The linear map of test functions `u ↦ χ · (u ∘ Φ)`. -/
def cutoffComp (χ : ℂ → ℝ) (Φ : ℂ → ℂ) : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ) where
  toFun u := fun z => χ z * u (Φ z)
  map_add' u v := by ext z; simp [mul_add]
  map_smul' a u := by ext z; simp; ring

lemma cutoffComp_apply (χ : ℂ → ℝ) (Φ : ℂ → ℂ) (u : ℂ → ℝ) (z : ℂ) :
    cutoffComp χ Φ u z = χ z * u (Φ z) := rfl

lemma dirichletEnergy_ball_congr {w₁ w₂ : ℂ → ℝ} (h : EqOn w₁ w₂ (ball 0 1)) :
    Steklov.dirichletEnergy (ball 0 1) w₁ = Steklov.dirichletEnergy (ball 0 1) w₂ := by
  unfold Steklov.dirichletEnergy
  refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [(Filter.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz) h).fderiv_eq]

lemma exp_mem_sphere (t : ℝ) : Complex.exp (t * Complex.I) ∈ sphere (0 : ℂ) 1 := by
  rw [mem_sphere_zero_iff_norm, Complex.norm_exp_ofReal_mul_I]

lemma weightedBoundaryMass_congr (ρ : ℂ → ℝ) {w₁ w₂ : ℂ → ℝ} (h : EqOn w₁ w₂ (sphere 0 1)) :
    Steklov.weightedBoundaryMass ρ w₁ = Steklov.weightedBoundaryMass ρ w₂ := by
  unfold Steklov.weightedBoundaryMass
  refine lintegral_congr fun t => ?_
  rw [h (exp_mem_sphere t)]

/-- The boundary mass of `Ω = F(𝔻)` in terms of the weighted boundary mass on the circle. -/
lemma boundaryMass_image (hU : IsOpen U) (hcb : closedBall (0 : ℂ) 1 ⊆ U)
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F (closedBall 0 1)) {u : ℂ → ℝ}
    (hu : Continuous u) :
    Steklov.boundaryMass (F '' ball 0 1) u =
      Steklov.weightedBoundaryMass (fun z => ‖deriv F z‖) (u ∘ F) := by
  unfold Steklov.boundaryMass Steklov.weightedBoundaryMass
  rw [frontier_image_ball hcb hF hinj,
    boundary_lintegral hU hcb hF hinj (by fun_prop : Measurable fun z => ‖u z‖ₑ ^ 2)]
  rfl

/-- **Proposition 2.1.1 (conformal pullback)**, for the min–max spectra of `Defs.lean`. -/
theorem prop_2_1_1 : Prop_2_1_1 := by
  intro F ⟨U, hU, hcb, hF⟩ hinj hF'
  obtain ⟨U', hU', hcb', hU'U, hinj', hd'⟩ :=
    HolInv.exists_open_nbhd_injOn_deriv_ne_zero hU hcb hF hinj hF'
  have hF₁ : DifferentiableOn ℂ F U' := hF.mono hU'U
  have hFs : ContDiffOn ℝ ∞ F U' := contDiffOn_of_differentiableOn hU' hF₁
  set ρ : ℂ → ℝ := fun z => ‖deriv F z‖
  -- cut-off near the closed disk
  obtain ⟨χ₁, hχ₁, ⟨W₁, hW₁, hKW₁, hχ₁one⟩, hsupp₁⟩ :=
    exists_cutoff (isCompact_closedBall (0 : ℂ) 1) hU' hcb'
  -- holomorphic inverse on `V = F(U')`
  set G := Function.invFunOn F U'
  set V := F '' U'
  have hV : IsOpen V := HolInv.isOpen_image hF₁ hinj' subset_rfl hU'
  have hGd : DifferentiableOn ℂ G V := by
    rintro _ ⟨z, hz, rfl⟩
    exact (HolInv.hasDerivAt_invFunOn hU' hF₁ hinj' hz
      (hd' z hz)).differentiableAt.differentiableWithinAt
  have hGs : ContDiffOn ℝ ∞ G V := contDiffOn_of_differentiableOn hV hGd
  have hK₂ : IsCompact (F '' closedBall 0 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn (hF₁.continuousOn.mono hcb')
  obtain ⟨χ₂, hχ₂, ⟨W₂, hW₂, hKW₂, hχ₂one⟩, hsupp₂⟩ :=
    exists_cutoff hK₂ hV (image_mono hcb')
  -- `T₂ w ∘ F = w` on the closed disk
  have hT₂F : ∀ w : ℂ → ℝ, EqOn (cutoffComp χ₂ G w ∘ F) w (closedBall 0 1) := by
    intro w z hz
    simp only [Function.comp, cutoffComp_apply]
    have hG : G (F z) = z := HolInv.invFunOn_apply_self hinj' (hcb' hz)
    rw [hχ₂one _ (hKW₂ ⟨z, hz, rfl⟩), hG, one_mul]
  have hT₁ : ∀ u : ℂ → ℝ, EqOn (cutoffComp χ₁ F u) (u ∘ F) (closedBall 0 1) := by
    intro u z hz
    simp only [Function.comp, cutoffComp_apply]
    rw [hχ₁one z (hKW₁ hz), one_mul]
  funext k
  unfold Steklov.steklovSpectrum Steklov.weightedSteklovSpectrum Steklov.steklovEigenvalue
    Steklov.weightedSteklovEigenvalue
  apply le_antisymm
  · -- `σ_k(Ω) ≤ σ_k(𝔻, ρ)`: transport disk test functions to `Ω`
    refine Steklov.minMax_le_of_transfer (cutoffComp χ₂ G) (by simp [Steklov.boundaryMass]) ?_ k
    intro w hw
    have hTw : ContDiff ℝ ∞ (cutoffComp χ₂ G w) := contDiff_mul_comp hV hχ₂ hsupp₂ hGs hw
    refine ⟨hTw, ?_, ?_⟩
    · rw [dirichletEnergy_image hU' hF₁ (ball_subset_closedBall.trans hcb') measurableSet_ball
        (hinj'.mono (ball_subset_closedBall.trans hcb')) (hTw.differentiable (by simp))]
      exact dirichletEnergy_ball_congr ((hT₂F w).mono ball_subset_closedBall)
    · rw [boundaryMass_image hU' hcb' hF₁ (hinj'.mono hcb') hTw.continuous]
      exact weightedBoundaryMass_congr ρ ((hT₂F w).mono sphere_subset_closedBall)
  · -- `σ_k(𝔻, ρ) ≤ σ_k(Ω)`: transport test functions on `Ω` to the disk
    refine Steklov.minMax_le_of_transfer (cutoffComp χ₁ F)
      (by simp [Steklov.weightedBoundaryMass]) ?_ k
    intro u hu
    have hTu : ContDiff ℝ ∞ (cutoffComp χ₁ F u) := contDiff_mul_comp hU' hχ₁ hsupp₁ hFs hu
    refine ⟨hTu, ?_, ?_⟩
    · rw [dirichletEnergy_image hU' hF₁ (ball_subset_closedBall.trans hcb') measurableSet_ball
        (hinj'.mono (ball_subset_closedBall.trans hcb')) (hu.differentiable (by simp))]
      rw [dirichletEnergy_ball_congr ((hT₁ u).mono ball_subset_closedBall)]
      rfl
    · rw [boundaryMass_image hU' hcb' hF₁ (hinj'.mono hcb') hu.continuous]
      exact weightedBoundaryMass_congr ρ ((hT₁ u).mono sphere_subset_closedBall)

end ConformalPullback
