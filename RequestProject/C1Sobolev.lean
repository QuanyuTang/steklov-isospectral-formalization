module

public import RequestProject.C1H1
public import RequestProject.ConformalSobolev

/-!
# Sobolev pullback for a conformal map with only a `C¹` boundary extension

`SteklovH1.C1Conf` bundles exactly the hypotheses of the general `C¹` Proposition 2.1.1
(`SteklovC1.Prop_2_1_1_C1`), except simple connectivity (which is not needed):

* `F` holomorphic on the open disk `𝔻`, `F(𝔻) = Ω`, `Ω` open and bounded;
* `F` injective on `𝔻̄` with `F(𝔻̄) = Ω̄`;
* `F` real-`C¹` on an open `U ⊇ 𝔻̄`, and a real-`C¹` map `G` on an open `W ⊇ Ω̄` with `G ∘ F = id`
  on `𝔻̄` (so `F : 𝔻̄ → Ω̄` is a `C¹` diffeomorphism in the usual manifold-with-boundary sense of
  "restriction of a `C¹` map on an open neighbourhood");
* `dF_z(1) ≠ 0` on `𝕋`.

**Nothing holomorphic is assumed across `𝕋`.**  The pullback of a smooth function is only `C¹`
up to the boundary, so the graph-closure spaces are compared via `SteklovH1.embedC1_mem_H1`
(`C¹` graphs lie in `H¹`), which rests on the mollification `SteklovC1.exists_smooth_C1_approx`.

Main result: `C1Conf.sobolevPullback : c.dom.H1 ≃L[ℝ] H1`, `x ↦ x ∘ F` with inverse `y ↦ y ∘ G`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Real ComplexConjugate

noncomputable section

namespace SteklovH1

/-- A conformal map `F : 𝔻 → Ω` extending to a `C¹` diffeomorphism `𝔻̄ → Ω̄`
(the hypotheses of the general `C¹` Proposition 2.1.1). -/
structure C1Conf where
  F : ℂ → ℂ
  Ω : Set ℂ
  isOpen_Ω : IsOpen Ω
  bdd : Bornology.IsBounded Ω
  diff : DifferentiableOn ℂ F (ball 0 1)
  img : F '' ball 0 1 = Ω
  inj : InjOn F (closedBall 0 1)
  cl : F '' closedBall 0 1 = closure Ω
  U : Set ℂ
  isOpen_U : IsOpen U
  cb : closedBall (0 : ℂ) 1 ⊆ U
  C1 : ContDiffOn ℝ 1 F U
  G : ℂ → ℂ
  W : Set ℂ
  isOpen_W : IsOpen W
  clW : closure Ω ⊆ W
  GC1 : ContDiffOn ℝ 1 G W
  GF : ∀ z ∈ closedBall (0 : ℂ) 1, G (F z) = z
  deriv_ne_sphere : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0

namespace C1Conf

variable (c : C1Conf)


/-! ### Geometry of `F` and `G` -/

lemma Ω_sub_W : c.Ω ⊆ c.W := subset_closure.trans c.clW

lemma mem_Ω {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : c.F z ∈ c.Ω := c.img ▸ mem_image_of_mem _ hz

lemma measurableSet_Ω : MeasurableSet c.Ω := c.isOpen_Ω.measurableSet

lemma hasDerivAt {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : HasDerivAt c.F (deriv c.F z) z :=
  (c.diff.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt

lemma hasFDerivAt {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasFDerivAt c.F (ConformalPullback.mulR (deriv c.F z)) z :=
  (c.hasDerivAt hz).hasFDerivAt.restrictScalars ℝ

lemma fderiv_F {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    fderiv ℝ c.F z = ConformalPullback.mulR (deriv c.F z) := (c.hasFDerivAt hz).fderiv

lemma hasFDerivAt_G {w : ℂ} (hw : w ∈ c.W) : HasFDerivAt c.G (fderiv ℝ c.G w) w :=
  ((c.GC1.differentiableOn one_ne_zero).differentiableAt (c.isOpen_W.mem_nhds hw)).hasFDerivAt

/-- `dG_{F z} ∘ dF_z = id` on `𝔻`. -/
lemma fderiv_G_comp {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (fderiv ℝ c.G (c.F z)).comp (ConformalPullback.mulR (deriv c.F z)) =
      ContinuousLinearMap.id ℝ ℂ := by
  have h1 : HasFDerivAt (fun y => c.G (c.F y))
      ((fderiv ℝ c.G (c.F z)).comp (ConformalPullback.mulR (deriv c.F z))) z :=
    (c.hasFDerivAt_G (c.Ω_sub_W (c.mem_Ω hz))).comp z (c.hasFDerivAt hz)
  have h2 : (fun y => c.G (c.F y)) =ᶠ[𝓝 z] id := by
    filter_upwards [isOpen_ball.mem_nhds hz] with y hy
    exact c.GF y (ball_subset_closedBall hy)
  exact h1.unique ((hasFDerivAt_id z).congr_of_eventuallyEq h2)

lemma deriv_ne {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : deriv c.F z ≠ 0 := by
  intro h0
  have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) (c.fderiv_G_comp hz)
  simp [h0] at h

lemma norm_deriv_eq {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    ‖deriv c.F z‖ = ‖fderiv ℝ c.F z 1‖ := by
  rw [c.fderiv_F hz, ConformalPullback.mulR_apply, one_mul]

/-- Bounds `m ≤ |F'| ≤ M` on the open disk, from the `C¹` extensions of `F` and `F⁻¹`. -/
lemma exists_bounds : ∃ m M : ℝ, 0 < m ∧ ∀ z ∈ ball (0 : ℂ) 1,
    m ≤ ‖deriv c.F z‖ ∧ ‖deriv c.F z‖ ≤ M := by
  have hKc : IsCompact (closure c.Ω) := c.bdd.isCompact_closure
  obtain ⟨MG, hMG⟩ := hKc.exists_bound_of_continuousOn
    ((c.GC1.continuousOn_fderiv_of_isOpen c.isOpen_W le_rfl).mono c.clW)
  obtain ⟨MF, hMF⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    ((c.C1.continuousOn_fderiv_of_isOpen c.isOpen_U le_rfl).mono c.cb)
  refine ⟨(max MG 1)⁻¹, MF, by positivity, fun z hz => ⟨?_, ?_⟩⟩
  · have h := congrArg (fun L : ℂ →L[ℝ] ℂ => L 1) (c.fderiv_G_comp hz)
    simp only [ContinuousLinearMap.comp_apply, ConformalPullback.mulR_apply, one_mul,
      ContinuousLinearMap.id_apply] at h
    have h1 : (1 : ℝ) ≤ max MG 1 * ‖deriv c.F z‖ := by
      calc (1 : ℝ) = ‖fderiv ℝ c.G (c.F z) (deriv c.F z)‖ := by rw [h, norm_one]
        _ ≤ ‖fderiv ℝ c.G (c.F z)‖ * ‖deriv c.F z‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ max MG 1 * ‖deriv c.F z‖ := mul_le_mul_of_nonneg_right
            ((hMG _ (subset_closure (c.mem_Ω hz))).trans (le_max_left _ _)) (norm_nonneg _)
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    linarith [h1]
  · rw [c.norm_deriv_eq hz]
    calc ‖fderiv ℝ c.F z 1‖ ≤ ‖fderiv ℝ c.F z‖ * ‖(1 : ℂ)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ MF := by rw [norm_one, mul_one]; exact hMF z (ball_subset_closedBall hz)

lemma continuousOn_deriv : ContinuousOn (deriv c.F) (ball 0 1) :=
  (c.diff.deriv isOpen_ball).continuousOn

/-! ### Change of variables -/

theorem lintegral_Ω (φ : ℂ → ℝ≥0∞) :
    ∫⁻ w in c.Ω, φ w = ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv c.F z‖ ^ 2) * φ (c.F z) := by
  rw [← c.img, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball
    (fun x hx => (c.hasFDerivAt hx).hasFDerivWithinAt) (c.inj.mono ball_subset_closedBall)]
  refine setLIntegral_congr_fun measurableSet_ball fun z _ => ?_
  rw [ConformalPullback.det_mulR, abs_of_nonneg (by positivity)]

theorem integral_Ω {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : ℂ → E) :
    ∫ w in c.Ω, φ w = ∫ z in ball (0 : ℂ) 1, (‖deriv c.F z‖ ^ 2) • φ (c.F z) := by
  rw [← c.img, integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball
    (fun x hx => (c.hasFDerivAt hx).hasFDerivWithinAt) (c.inj.mono ball_subset_closedBall)]
  refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
  rw [ConformalPullback.det_mulR, abs_of_nonneg (by positivity)]

lemma aemeasurable_F : AEMeasurable c.F (volume.restrict (ball (0 : ℂ) 1)) :=
  c.diff.continuousOn.aemeasurable measurableSet_ball

theorem ae_comp {p : ℂ → Prop} (h : ∀ᵐ w ∂(volume.restrict c.Ω), p w) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), p (c.F z) := by
  obtain ⟨m, M, hm, hb⟩ := c.exists_bounds
  set N := toMeasurable (volume.restrict c.Ω) {w | ¬ p w}
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume.restrict c.Ω N = 0 := by
    rw [measure_toMeasurable]; exact h
  set f : ℂ → ℝ≥0∞ := (N ∩ c.Ω).indicator 1
  have hf : Measurable f := measurable_one.indicator (hN.inter c.measurableSet_Ω)
  have h1 : ∫⁻ w in c.Ω, f w = 0 := by
    rw [lintegral_indicator (hN.inter c.measurableSet_Ω)]
    simp only [Pi.one_apply, lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter]
    exact measure_mono_null inter_subset_left hN0
  rw [c.lintegral_Ω] at h1
  have hmeas : AEMeasurable (fun z => ENNReal.ofReal (‖deriv c.F z‖ ^ 2) * f (c.F z))
      (volume.restrict (ball (0 : ℂ) 1)) := by
    refine AEMeasurable.mul ?_ (hf.comp_aemeasurable c.aemeasurable_F)
    exact ((c.continuousOn_deriv.norm.pow 2).aemeasurable measurableSet_ball).ennreal_ofReal
  have h2 := (lintegral_eq_zero_iff' hmeas).1 h1
  have h2' : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)),
      ENNReal.ofReal (‖deriv c.F z‖ ^ 2) * f (c.F z) = 0 := h2
  rw [ae_restrict_iff' measurableSet_ball] at h2' ⊢
  filter_upwards [h2'] with z hz hzb
  have hz := hz hzb
  have hpos : ENNReal.ofReal (‖deriv c.F z‖ ^ 2) ≠ 0 := by
    have := (hb z hzb).1
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have : 0 < ‖deriv c.F z‖ := hm.trans_le this
    positivity
  simp only [mul_eq_zero, hpos, false_or] at hz
  have hz' : c.F z ∉ N ∩ c.Ω := by
    intro hmem; simp [f, Set.indicator_of_mem hmem] at hz
  by_contra hp
  exact hz' ⟨subset_toMeasurable _ _ hp, c.mem_Ω hzb⟩

/-! ### The inverse `G` on `Ω` -/

lemma G_F {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : c.G (c.F z) = z := c.GF z (ball_subset_closedBall hz)

lemma F_G {w : ℂ} (hw : w ∈ c.Ω) : c.F (c.G w) = w := by
  rw [← c.img] at hw
  obtain ⟨z, hz, rfl⟩ := hw; rw [c.G_F hz]

lemma G_mem_ball {w : ℂ} (hw : w ∈ c.Ω) : c.G w ∈ ball (0 : ℂ) 1 := by
  rw [← c.img] at hw
  obtain ⟨z, hz, rfl⟩ := hw; rw [c.G_F hz]; exact hz

lemma hasDerivAt_G {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    HasDerivAt c.G (deriv c.F z)⁻¹ (c.F z) := by
  refine HasDerivAt.of_local_left_inverse (f := c.F) ?_ ?_ (c.deriv_ne hz) ?_
  · exact (c.hasFDerivAt_G (c.Ω_sub_W (c.mem_Ω hz))).continuousAt
  · rw [c.G_F hz]; exact c.hasDerivAt hz
  · filter_upwards [c.isOpen_Ω.mem_nhds (c.mem_Ω hz)] with y hy
    exact c.F_G hy

lemma deriv_G_F {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : deriv c.G (c.F z) = (deriv c.F z)⁻¹ :=
  (c.hasDerivAt_G hz).deriv

lemma differentiableOn_G : DifferentiableOn ℂ c.G c.Ω := by
  intro w hw
  rw [← c.img] at hw
  obtain ⟨z, hz, rfl⟩ := hw
  exact (c.hasDerivAt_G hz).differentiableAt.differentiableWithinAt

lemma hasDerivAt_G' {w : ℂ} (hw : w ∈ c.Ω) : HasDerivAt c.G (deriv c.G w) w :=
  (c.differentiableOn_G.differentiableAt (c.isOpen_Ω.mem_nhds hw)).hasDerivAt

lemma aemeasurable_G : AEMeasurable c.G (volume.restrict c.Ω) :=
  c.differentiableOn_G.continuousOn.aemeasurable c.measurableSet_Ω

theorem lintegral_Ω_G (φ : ℂ → ℝ≥0∞) :
    ∫⁻ w in c.Ω, φ (c.G w) = ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv c.F z‖ ^ 2) * φ z := by
  rw [c.lintegral_Ω]
  refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [c.G_F hz]

theorem ae_comp_G {p : ℂ → Prop} (h : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), p z) :
    ∀ᵐ w ∂(volume.restrict c.Ω), p (c.G w) := by
  set N := toMeasurable (volume.restrict (ball (0 : ℂ) 1)) {z | ¬ p z}
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume.restrict (ball (0 : ℂ) 1) N = 0 := by
    rw [measure_toMeasurable]; exact h
  set f : ℂ → ℝ≥0∞ := N.indicator 1
  have hf : Measurable f := measurable_one.indicator hN
  have h1 : ∫⁻ w in c.Ω, f (c.G w) = 0 := by
    rw [c.lintegral_Ω_G]
    refine le_antisymm ?_ (zero_le)
    calc ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv c.F z‖ ^ 2) * f z
        ≤ ∫⁻ z in ball (0 : ℂ) 1, (⊤ : ℝ≥0∞) * f z :=
          lintegral_mono fun z => mul_le_mul' le_top le_rfl
      _ = (⊤ : ℝ≥0∞) * ∫⁻ z in ball (0 : ℂ) 1, f z := lintegral_const_mul _ hf
      _ = 0 := by
          rw [lintegral_indicator hN]
          simp only [Pi.one_apply, lintegral_const, one_mul, Measure.restrict_apply
            MeasurableSet.univ, univ_inter]
          rw [hN0, mul_zero]
  have h2 := (lintegral_eq_zero_iff' (hf.comp_aemeasurable c.aemeasurable_G)).1 h1
  have h2' : ∀ᵐ w ∂(volume.restrict c.Ω), f (c.G w) = 0 := h2
  filter_upwards [h2'] with w hw
  by_contra hp
  have : c.G w ∈ N := subset_toMeasurable _ _ hp
  simp [f, Set.indicator_of_mem this] at hw

/-! ### The domain `Ω` with its boundary measure -/

lemma frontier_eq : frontier c.Ω = c.F '' sphere 0 1 :=
  SteklovC1.frontier_eq_image_sphere c.isOpen_Ω c.img c.cl c.inj

/-- The boundary weight `ρ(z) = ‖dF_z(1)‖ = |F'(z)|` on `𝕋`. -/
def ρ : ℂ → ℝ := fun z => ‖fderiv ℝ c.F z 1‖

lemma continuousOn_ρ : ContinuousOn c.ρ (sphere 0 1) :=
  (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp_continuousOn
    (c.C1.continuousOn_fderiv_of_isOpen c.isOpen_U le_rfl)).norm).mono
    (sphere_subset_closedBall.trans c.cb)

lemma ρ_pos : ∀ z ∈ sphere (0 : ℂ) 1, 0 < c.ρ z := fun z hz =>
  norm_pos_iff.2 (c.deriv_ne_sphere z hz)

/-- **Boundary change of variables**:
`∫_{∂Ω} g dH¹ = ∫_0^{2π} g(F(e^{it})) ρ(e^{it}) dt` (arc length of a `C¹` curve). -/
theorem lintegral_frontier {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in frontier c.Ω, g x ∂(Measure.hausdorffMeasure 1) =
      ∫⁻ t in Ioc 0 (2 * π), g (c.F (Complex.exp (t * Complex.I))) *
        ENNReal.ofReal (c.ρ (Complex.exp (t * Complex.I))) := by
  rw [c.frontier_eq]
  exact SteklovC1.boundary_lintegral_C1 c.diff c.isOpen_U c.cb c.C1 c.inj hg

lemma exists_ρ_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ sphere (0 : ℂ) 1, c.ρ z ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn c.continuousOn_ρ
  refine ⟨max M 0, le_max_right _ _, fun z hz => ?_⟩
  have := hM z hz
  rw [Real.norm_eq_abs] at this
  exact (le_abs_self _).trans (this.trans (le_max_left _ _))

lemma bdry_finite : Measure.hausdorffMeasure 1 (frontier c.Ω) ≠ ⊤ := by
  have h := c.lintegral_frontier (g := fun _ => 1) measurable_const
  rw [setLIntegral_const, one_mul] at h
  rw [h]
  obtain ⟨M, -, hM⟩ := c.exists_ρ_bound
  refine ne_top_of_le_ne_top (b := ∫⁻ _ in Ioc 0 (2 * π), ENNReal.ofReal M) ?_ ?_
  · rw [setLIntegral_const, Real.volume_Ioc]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  · refine lintegral_mono fun t => ?_
    rw [one_mul]
    exact ENNReal.ofReal_le_ofReal (hM _ (ConformalPullback.exp_mem_sphere t))

/-- `Ω` as a bounded domain with finite boundary length. -/
def dom : BddDomain := ⟨c.Ω, c.isOpen_Ω, c.bdd, c.bdry_finite⟩

lemma dom_carrier : c.dom.carrier = c.Ω := rfl

/-! ### Composition estimates -/

lemma lintegral_comp_F_le {m : ℝ} (hm : 0 < m)
    (hb : ∀ z ∈ ball (0 : ℂ) 1, m ≤ ‖deriv c.F z‖) (φ : ℂ → ℝ≥0∞) :
    ∫⁻ z in ball (0 : ℂ) 1, φ (c.F z) ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * ∫⁻ w in c.Ω, φ w := by
  rw [c.lintegral_Ω, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have h1 : 1 ≤ (m ^ 2)⁻¹ * ‖deriv c.F z‖ ^ 2 := by
    rw [inv_mul_eq_div, one_le_div (by positivity)]
    exact pow_le_pow_left₀ hm.le (hb z hz) 2
  calc φ (c.F z) = 1 * φ (c.F z) := (one_mul _).symm
    _ ≤ _ := by
      refine mul_le_mul' ?_ le_rfl
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1

lemma lintegral_comp_G_le {M : ℝ} (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖deriv c.F z‖ ≤ M)
    (φ : ℂ → ℝ≥0∞) :
    ∫⁻ w in c.Ω, φ (c.G w) ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ z in ball (0 : ℂ) 1, φ z := by
  rw [c.lintegral_Ω_G, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  exact pow_le_pow_left₀ (norm_nonneg _) (hb z hz) 2

lemma lintegral_grad_F (g : ℂ → ℂ) :
    ∫⁻ z in ball (0 : ℂ) 1, ‖conj (deriv c.F z) * g (c.F z)‖ₑ ^ 2 = ∫⁻ w in c.Ω, ‖g w‖ₑ ^ 2 := by
  rw [c.lintegral_Ω]
  refine setLIntegral_congr_fun measurableSet_ball fun z _ => ?_
  rw [enorm_mul, mul_pow, ← ofReal_norm_eq_enorm (conj _), Complex.norm_conj,
    ← ENNReal.ofReal_pow (norm_nonneg _)]

lemma lintegral_grad_G (g : ℂ → ℂ) :
    ∫⁻ w in c.Ω, ‖conj (deriv c.G w) * g (c.G w)‖ₑ ^ 2 = ∫⁻ z in ball (0 : ℂ) 1, ‖g z‖ₑ ^ 2 := by
  rw [c.lintegral_Ω]
  refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [c.deriv_G_F hz, c.G_F hz, enorm_mul, mul_pow,
    ← ofReal_norm_eq_enorm (conj _), Complex.norm_conj, norm_inv, ← mul_assoc,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have : ‖deriv c.F z‖ ^ 2 * ‖deriv c.F z‖⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.2 (c.deriv_ne hz)), one_pow]
  rw [this, ENNReal.ofReal_one, one_mul]

/-! ### The pullback and pushforward on `L²` -/

open ConfMap (cmul cmul_apply sm_comp norm_le_of_enorm_sq_le norm_eq_of_enorm_sq_eq)

lemma memLp_pullF (f : Lp ℝ 2 c.dom.μ) :
    MemLp (fun z => (ContinuousLinearMap.id ℝ ℝ) ((f : ℂ → ℝ) (c.F z))) 2 μD := by
  obtain ⟨m, M, hm, hb⟩ := c.exists_bounds
  refine memLp_two_of_lintegral (sm_comp (Lp.stronglyMeasurable f) c.aemeasurable_F) ?_
  refine (c.lintegral_comp_F_le hm (fun z hz => (hb z hz).1)
    (fun w => ‖(f : ℂ → ℝ) w‖ₑ ^ 2)).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact lintegral_lt_top_of_memLp (Lp.memLp f)

lemma memLp_pullG (g : Lp ℂ 2 c.dom.μ) :
    MemLp (fun z => cmul (deriv c.F z) ((g : ℂ → ℂ) (c.F z))) 2 μD := by
  refine memLp_two_of_lintegral ?_ ?_
  · simp only [cmul_apply]
    refine (sm_comp (Lp.stronglyMeasurable g) c.aemeasurable_F).mul ?_
    exact (Complex.continuous_conj.comp_continuousOn c.continuousOn_deriv).aestronglyMeasurable
      measurableSet_ball
  · simp only [cmul_apply]
    simp_rw [mul_comm _ (conj _)]
    rw [c.lintegral_grad_F]
    exact lintegral_lt_top_of_memLp (Lp.memLp g)

lemma memLp_pushF (f : Lp ℝ 2 μD) :
    MemLp (fun w => (ContinuousLinearMap.id ℝ ℝ) ((f : ℂ → ℝ) (c.G w))) 2 c.dom.μ := by
  obtain ⟨m, M, hm, hb⟩ := c.exists_bounds
  refine memLp_two_of_lintegral (sm_comp (Lp.stronglyMeasurable f) c.aemeasurable_G) ?_
  refine (c.lintegral_comp_G_le (fun z hz => (hb z hz).2)
    (fun w => ‖(f : ℂ → ℝ) w‖ₑ ^ 2)).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact lintegral_lt_top_of_memLp (Lp.memLp f)

lemma memLp_pushG (g : Lp ℂ 2 μD) :
    MemLp (fun w => cmul (deriv c.G w) ((g : ℂ → ℂ) (c.G w))) 2 c.dom.μ := by
  refine memLp_two_of_lintegral ?_ ?_
  · simp only [cmul_apply]
    refine (sm_comp (Lp.stronglyMeasurable g) c.aemeasurable_G).mul ?_
    exact (Complex.continuous_conj.comp_continuousOn
      ((c.differentiableOn_G.deriv c.isOpen_Ω).continuousOn)).aestronglyMeasurable
      c.measurableSet_Ω
  · simp only [cmul_apply]
    simp_rw [mul_comm _ (conj _)]
    change ∫⁻ w in c.Ω, _ < ⊤
    rw [c.lintegral_grad_G]
    exact lintegral_lt_top_of_memLp (Lp.memLp g)

/-- `f ↦ f ∘ F`, `L²(Ω) → L²(𝔻)`. -/
def pullF : Lp ℝ 2 c.dom.μ →ₗ[ℝ] Lp ℝ 2 μD :=
  wcomp c.F (fun _ => ContinuousLinearMap.id ℝ ℝ) _ _ c.memLp_pullF c.ae_comp

/-- `g ↦ conj(F') · g ∘ F` (pullback of gradients). -/
def pullG : Lp ℂ 2 c.dom.μ →ₗ[ℝ] Lp ℂ 2 μD :=
  wcomp c.F (fun z => cmul (deriv c.F z)) _ _ c.memLp_pullG c.ae_comp

/-- `f ↦ f ∘ G`, `L²(𝔻) → L²(Ω)`. -/
def pushF : Lp ℝ 2 μD →ₗ[ℝ] Lp ℝ 2 c.dom.μ :=
  wcomp c.G (fun _ => ContinuousLinearMap.id ℝ ℝ) _ _ c.memLp_pushF c.ae_comp_G

/-- `g ↦ conj(G') · g ∘ G`. -/
def pushG : Lp ℂ 2 μD →ₗ[ℝ] Lp ℂ 2 c.dom.μ :=
  wcomp c.G (fun w => cmul (deriv c.G w)) _ _ c.memLp_pushG c.ae_comp_G

lemma pullF_ae (f : Lp ℝ 2 c.dom.μ) : (c.pullF f : ℂ → ℝ) =ᵐ[μD] fun z => (f : ℂ → ℝ) (c.F z) :=
  wcomp_ae _ _ _ _ _ _ f

lemma pullG_ae (g : Lp ℂ 2 c.dom.μ) :
    (c.pullG g : ℂ → ℂ) =ᵐ[μD] fun z => (g : ℂ → ℂ) (c.F z) * conj (deriv c.F z) := by
  filter_upwards [wcomp_ae c.F (fun z => cmul (deriv c.F z)) c.dom.μ μD c.memLp_pullG
    c.ae_comp g] with z hz
  rw [pullG, hz, cmul_apply]

lemma pushF_ae (f : Lp ℝ 2 μD) : (c.pushF f : ℂ → ℝ) =ᵐ[c.dom.μ] fun w => (f : ℂ → ℝ) (c.G w) :=
  wcomp_ae _ _ _ _ _ _ f

lemma pushG_ae (g : Lp ℂ 2 μD) :
    (c.pushG g : ℂ → ℂ) =ᵐ[c.dom.μ] fun w => (g : ℂ → ℂ) (c.G w) * conj (deriv c.G w) := by
  filter_upwards [wcomp_ae c.G (fun w => cmul (deriv c.G w)) μD c.dom.μ c.memLp_pushG
    c.ae_comp_G g] with z hz
  rw [pushG, hz, cmul_apply]

lemma norm_pullF_le {m : ℝ} (hm : 0 < m) (hb : ∀ z ∈ ball (0 : ℂ) 1, m ≤ ‖deriv c.F z‖)
    (f : Lp ℝ 2 c.dom.μ) : ‖c.pullF f‖ ≤ m⁻¹ * ‖f‖ := by
  refine norm_le_of_enorm_sq_le (by positivity) ?_
  rw [BddDomain.enorm_Lp_sq, BddDomain.enorm_Lp_sq,
    lintegral_congr_ae ((c.pullF_ae f).mono fun z hz => by rw [hz]), inv_pow]
  exact c.lintegral_comp_F_le hm hb (fun w => ‖(f : ℂ → ℝ) w‖ₑ ^ 2)

lemma norm_pushF_le {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ ball (0 : ℂ) 1, ‖deriv c.F z‖ ≤ M)
    (f : Lp ℝ 2 μD) : ‖c.pushF f‖ ≤ M * ‖f‖ := by
  refine norm_le_of_enorm_sq_le hM ?_
  rw [BddDomain.enorm_Lp_sq, BddDomain.enorm_Lp_sq,
    lintegral_congr_ae ((c.pushF_ae f).mono fun z hz => by rw [hz])]
  exact c.lintegral_comp_G_le hb (fun w => ‖(f : ℂ → ℝ) w‖ₑ ^ 2)

lemma norm_pullG (g : Lp ℂ 2 c.dom.μ) : ‖c.pullG g‖ = ‖g‖ := by
  have h : ‖c.pullG g‖ₑ ^ 2 = ‖g‖ₑ ^ 2 := by
    rw [BddDomain.enorm_Lp_sq, BddDomain.enorm_Lp_sq,
      lintegral_congr_ae ((c.pullG_ae g).mono fun z hz => by rw [hz])]
    simp_rw [mul_comm _ (conj _)]
    exact c.lintegral_grad_F _
  exact norm_eq_of_enorm_sq_eq h

lemma norm_pushG (g : Lp ℂ 2 μD) : ‖c.pushG g‖ = ‖g‖ := by
  have h : ‖c.pushG g‖ₑ ^ 2 = ‖g‖ₑ ^ 2 := by
    rw [BddDomain.enorm_Lp_sq, BddDomain.enorm_Lp_sq,
      lintegral_congr_ae ((c.pushG_ae g).mono fun z hz => by rw [hz])]
    simp_rw [mul_comm _ (conj _)]
    exact c.lintegral_grad_G _
  exact norm_eq_of_enorm_sq_eq h

lemma pushF_pullF (f : Lp ℝ 2 c.dom.μ) : c.pushF (c.pullF f) = f := by
  ext1
  filter_upwards [c.pushF_ae (c.pullF f), c.ae_comp_G (c.pullF_ae f),
    ae_restrict_mem c.measurableSet_Ω] with w h1 h2 h3
  rw [h1, h2, c.F_G h3]

lemma pullF_pushF (f : Lp ℝ 2 μD) : c.pullF (c.pushF f) = f := by
  ext1
  filter_upwards [c.pullF_ae (c.pushF f), c.ae_comp (c.pushF_ae f),
    ae_restrict_mem measurableSet_ball] with z h1 h2 h3
  rw [h1, h2, c.G_F h3]

lemma pushG_pullG (g : Lp ℂ 2 c.dom.μ) : c.pushG (c.pullG g) = g := by
  ext1
  filter_upwards [c.pushG_ae (c.pullG g), c.ae_comp_G (c.pullG_ae g),
    ae_restrict_mem c.measurableSet_Ω] with w h1 h2 h3
  have hz := c.G_mem_ball h3
  have hd := c.deriv_G_F hz
  rw [c.F_G h3] at hd
  rw [h1, h2, c.F_G h3, hd, map_inv₀, mul_assoc,
    mul_inv_cancel₀ ((map_ne_zero _).2 (c.deriv_ne hz)), mul_one]

lemma pullG_pushG (g : Lp ℂ 2 μD) : c.pullG (c.pushG g) = g := by
  ext1
  filter_upwards [c.pullG_ae (c.pushG g), c.ae_comp (c.pushG_ae g),
    ae_restrict_mem measurableSet_ball] with z h1 h2 h3
  rw [h1, h2, c.G_F h3, c.deriv_G_F h3, map_inv₀, mul_assoc,
    inv_mul_cancel₀ ((map_ne_zero _).2 (c.deriv_ne h3)), mul_one]

lemma exists_C : ∃ C : ℝ, 0 ≤ C ∧ (∀ f : Lp ℝ 2 c.dom.μ, ‖c.pullF f‖ ≤ C * ‖f‖) ∧
    (∀ g : Lp ℂ 2 c.dom.μ, ‖c.pullG g‖ ≤ C * ‖g‖) ∧ (∀ f : Lp ℝ 2 μD, ‖c.pushF f‖ ≤ C * ‖f‖) ∧
    (∀ g : Lp ℂ 2 μD, ‖c.pushG g‖ ≤ C * ‖g‖) := by
  obtain ⟨m, M, hm, hb⟩ := c.exists_bounds
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 (mem_ball_self zero_lt_one)).2
  refine ⟨max (max m⁻¹ M) 1, by positivity, fun f => ?_, fun g => ?_, fun f => ?_, fun g => ?_⟩
  · exact (c.norm_pullF_le hm (fun z hz => (hb z hz).1) f).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _)) (norm_nonneg _))
  · rw [c.norm_pullG]; exact le_mul_of_one_le_left (norm_nonneg _) (le_max_right _ _)
  · exact (c.norm_pushF_le hM (fun z hz => (hb z hz).2) f).trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_left _ _)) (norm_nonneg _))
  · rw [c.norm_pushG]; exact le_mul_of_one_le_left (norm_nonneg _) (le_max_right _ _)

/-- The pullback `(f, g) ↦ (f ∘ F, conj(F') · g ∘ F)` on the ambient spaces. -/
def pullAmb : c.dom.Amb →L[ℝ] Amb :=
  prodMapL c.pullF c.pullG c.exists_C.choose c.exists_C.choose_spec.1
    c.exists_C.choose_spec.2.1 c.exists_C.choose_spec.2.2.1

/-- The pushforward `(f, g) ↦ (f ∘ G, conj(G') · g ∘ G)` on the ambient spaces. -/
def pushAmb : Amb →L[ℝ] c.dom.Amb :=
  prodMapL c.pushF c.pushG c.exists_C.choose c.exists_C.choose_spec.1
    c.exists_C.choose_spec.2.2.2.1 c.exists_C.choose_spec.2.2.2.2

@[simp] lemma pullAmb_fst (x : c.dom.Amb) : (c.pullAmb x).fst = c.pullF x.fst := by
  simp [pullAmb]
@[simp] lemma pullAmb_snd (x : c.dom.Amb) : (c.pullAmb x).snd = c.pullG x.snd := by
  simp [pullAmb]
@[simp] lemma pushAmb_fst (x : Amb) : (c.pushAmb x).fst = c.pushF x.fst := by
  simp [pushAmb]
@[simp] lemma pushAmb_snd (x : Amb) : (c.pushAmb x).snd = c.pushG x.snd := by
  simp [pushAmb]

lemma pushAmb_pullAmb (x : c.dom.Amb) : c.pushAmb (c.pullAmb x) = x :=
  ConfMap.dom_amb_ext (by simp [pushF_pullF]) (by simp [pushG_pullG])

lemma pullAmb_pushAmb (x : Amb) : c.pullAmb (c.pushAmb x) = x :=
  ConfMap.amb_ext (by simp [pullF_pushF]) (by simp [pullG_pushG])

/-! ### Transport of smooth functions: only `C¹` up to the boundary -/

lemma exists_cutoff_F : ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧
    (∃ W₁, IsOpen W₁ ∧ closedBall (0 : ℂ) 1 ⊆ W₁ ∧ ∀ z ∈ W₁, χ z = 1) ∧
      tsupport χ ⊆ c.U ∧ HasCompactSupport χ :=
  SteklovC1.exists_cutoff_compact (isCompact_closedBall 0 1) c.isOpen_U c.cb

lemma exists_cutoff_G : ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧
    (∃ W₂, IsOpen W₂ ∧ closure c.Ω ⊆ W₂ ∧ ∀ z ∈ W₂, χ z = 1) ∧
      tsupport χ ⊆ c.W ∧ HasCompactSupport χ :=
  SteklovC1.exists_cutoff_compact c.bdd.isCompact_closure c.isOpen_W c.clW

/-- `Φ₁ = χ₁ F`, a globally `C¹` map equal to `F` near `𝔻̄`. -/
def Φ₁ : ℂ → ℂ := fun z => (c.exists_cutoff_F.choose z : ℂ) * c.F z

/-- `Φ₂ = χ₂ G`, a globally `C¹` map equal to `G` near `Ω̄`. -/
def Φ₂ : ℂ → ℂ := fun z => (c.exists_cutoff_G.choose z : ℂ) * c.G z

lemma contDiff_Φ₁ : ContDiff ℝ 1 c.Φ₁ :=
  SteklovC1.cutoff_mul_contDiff c.isOpen_U c.exists_cutoff_F.choose_spec.1
    c.exists_cutoff_F.choose_spec.2.2.1 c.C1

lemma contDiff_Φ₂ : ContDiff ℝ 1 c.Φ₂ :=
  SteklovC1.cutoff_mul_contDiff c.isOpen_W c.exists_cutoff_G.choose_spec.1
    c.exists_cutoff_G.choose_spec.2.2.1 c.GC1

lemma Φ₁_eventually {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : c.Φ₁ =ᶠ[𝓝 z] c.F := by
  obtain ⟨W₁, hW, hKW, h1⟩ := c.exists_cutoff_F.choose_spec.2.1
  filter_upwards [hW.mem_nhds (hKW hz)] with y hy
  simp [Φ₁, h1 y hy]

lemma Φ₂_eventually {w : ℂ} (hw : w ∈ closure c.Ω) : c.Φ₂ =ᶠ[𝓝 w] c.G := by
  obtain ⟨W₂, hW, hKW, h1⟩ := c.exists_cutoff_G.choose_spec.2.1
  filter_upwards [hW.mem_nhds (hKW hw)] with y hy
  simp [Φ₂, h1 y hy]

/-- The pullback `u ∘ Φ₁` of a smooth function: globally `C¹`, equal to `u ∘ F` near `𝔻̄`. -/
def pullC1 (u : smoothFns) : ℂ → ℝ := fun z => (u : ℂ → ℝ) (c.Φ₁ z)

/-- The pushforward `u ∘ Φ₂` of a smooth function: globally `C¹`, equal to `u ∘ G` near `Ω̄`. -/
def pushC1 (u : smoothFns) : ℂ → ℝ := fun w => (u : ℂ → ℝ) (c.Φ₂ w)

lemma contDiff_pullC1 (u : smoothFns) : ContDiff ℝ 1 (c.pullC1 u) :=
  (contDiff_one_of_mem u.2).comp c.contDiff_Φ₁

lemma contDiff_pushC1 (u : smoothFns) : ContDiff ℝ 1 (c.pushC1 u) :=
  (contDiff_one_of_mem u.2).comp c.contDiff_Φ₂

lemma pullC1_eventually (u : smoothFns) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    c.pullC1 u =ᶠ[𝓝 z] fun z => (u : ℂ → ℝ) (c.F z) :=
  (c.Φ₁_eventually hz).mono fun y hy => by simp [pullC1, hy]

lemma pushC1_eventually (u : smoothFns) {w : ℂ} (hw : w ∈ closure c.Ω) :
    c.pushC1 u =ᶠ[𝓝 w] fun w => (u : ℂ → ℝ) (c.G w) :=
  (c.Φ₂_eventually hw).mono fun y hy => by simp [pushC1, hy]

lemma pullC1_eq (u : smoothFns) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    c.pullC1 u z = (u : ℂ → ℝ) (c.F z) := (c.pullC1_eventually u hz).eq_of_nhds

lemma grad_pullC1 (u : smoothFns) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    grad (c.pullC1 u) z = conj (deriv c.F z) * grad u (c.F z) := by
  unfold grad
  rw [(c.pullC1_eventually u (ball_subset_closedBall hz)).fderiv_eq]
  exact grad_comp_holo (((contDiff_one_of_mem u.2).differentiable one_ne_zero) _)
    (c.hasDerivAt hz)

lemma grad_pushC1 (u : smoothFns) {w : ℂ} (hw : w ∈ c.Ω) :
    grad (c.pushC1 u) w = conj (deriv c.G w) * grad u (c.G w) := by
  unfold grad
  rw [(c.pushC1_eventually u (subset_closure hw)).fderiv_eq]
  exact grad_comp_holo (((contDiff_one_of_mem u.2).differentiable one_ne_zero) _)
    (c.hasDerivAt_G' hw)

lemma pullAmb_embed (u : smoothFns) :
    c.pullAmb (c.dom.embed u) = embedC1 (c.pullC1 u) (c.contDiff_pullC1 u) := by
  refine ConfMap.amb_ext ?_ ?_
  · rw [pullAmb_fst, BddDomain.embed_fst, embedC1_fst]
    ext1
    filter_upwards [c.pullF_ae (c.dom.toL2 u), c.ae_comp (c.dom.toL2_ae u),
      MemLp.coeFn_toLp (memLp_disk (c.contDiff_pullC1 u).continuous),
      ae_restrict_mem measurableSet_ball] with z h1 h2 h3 hz
    rw [h1, h2, h3, c.pullC1_eq u (ball_subset_closedBall hz)]
  · rw [pullAmb_snd, BddDomain.embed_snd, embedC1_snd]
    ext1
    filter_upwards [c.pullG_ae (c.dom.gradL2 u), c.ae_comp (c.dom.gradL2_ae u),
      MemLp.coeFn_toLp (memLp_disk (continuous_grad (c.contDiff_pullC1 u))),
      ae_restrict_mem measurableSet_ball] with z h1 h2 h3 hz
    rw [h1, h2, h3, c.grad_pullC1 u hz, mul_comm]

lemma pushAmb_embed (u : smoothFns) :
    c.pushAmb (embed u) = c.dom.embedC1 (c.pushC1 u) (c.contDiff_pushC1 u) := by
  refine ConfMap.dom_amb_ext ?_ ?_
  · rw [pushAmb_fst, embed_fst, BddDomain.embedC1_fst]
    ext1
    filter_upwards [c.pushF_ae (toL2 u), c.ae_comp_G (toL2_ae u),
      MemLp.coeFn_toLp (c.dom.memLp_dom (c.contDiff_pushC1 u).continuous),
      ae_restrict_mem c.measurableSet_Ω] with w h1 h2 h3 hw
    rw [h1, h2, h3]
    exact ((c.pushC1_eventually u (subset_closure hw)).eq_of_nhds).symm
  · rw [pushAmb_snd, embed_snd, BddDomain.embedC1_snd]
    ext1
    filter_upwards [c.pushG_ae (gradL2 u), c.ae_comp_G (gradL2_ae u),
      MemLp.coeFn_toLp (c.dom.memLp_dom (continuous_grad (c.contDiff_pushC1 u))),
      ae_restrict_mem c.measurableSet_Ω] with w h1 h2 h3 hw
    rw [h1, h2, h3, c.grad_pushC1 u hw, mul_comm]

/-! ### The Sobolev pullback `H¹(Ω) ≅ H¹(𝔻)` -/

lemma pullAmb_mem (x : c.dom.H1) : c.pullAmb x ∈ H1 := by
  have hx : (x : c.dom.Amb) ∈ closure (LinearMap.range c.dom.embed : Set c.dom.Amb) := x.2
  have h1 := image_closure_subset_closure_image c.pullAmb.continuous ⟨_, hx, rfl⟩
  have hH : IsClosed (H1 : Set Amb) := Submodule.isClosed_topologicalClosure _
  refine closure_minimal ?_ hH h1
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  rw [c.pullAmb_embed]
  exact embedC1_mem_H1 _ _

lemma pushAmb_mem (x : H1) : c.pushAmb x ∈ c.dom.H1 := by
  have hx : (x : Amb) ∈ closure (LinearMap.range embed : Set Amb) := x.2
  have h1 := image_closure_subset_closure_image c.pushAmb.continuous ⟨_, hx, rfl⟩
  have hH : IsClosed (c.dom.H1 : Set c.dom.Amb) := Submodule.isClosed_topologicalClosure _
  refine closure_minimal ?_ hH h1
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  rw [c.pushAmb_embed]
  exact c.dom.embedC1_mem_H1 _ _

/-- The Sobolev pullback `H¹(Ω) → H¹(𝔻)`, `u ↦ u ∘ F`. -/
def pullH1 : c.dom.H1 →L[ℝ] H1 :=
  (c.pullAmb.comp c.dom.H1.subtypeL).codRestrict H1 c.pullAmb_mem

/-- The Sobolev pushforward `H¹(𝔻) → H¹(Ω)`, `v ↦ v ∘ G`. -/
def pushH1 : H1 →L[ℝ] c.dom.H1 :=
  (c.pushAmb.comp H1.subtypeL).codRestrict c.dom.H1 c.pushAmb_mem

/-- **Sobolev pullback isomorphism** `H¹(Ω) ≃ H¹(𝔻)` for a conformal map with a `C¹`
diffeomorphic boundary extension: `(f, g) ↦ (f ∘ F, conj(F') · g ∘ F)`, a continuous linear
equivalence with inverse `(f, g) ↦ (f ∘ G, conj(G') · g ∘ G)`. -/
def sobolevPullback : c.dom.H1 ≃L[ℝ] H1 :=
  ContinuousLinearEquiv.equivOfInverse c.pullH1 c.pushH1
    (fun x => Subtype.ext (c.pushAmb_pullAmb x)) (fun x => Subtype.ext (c.pullAmb_pushAmb x))

lemma sobolevPullback_apply (x : c.dom.H1) : (c.sobolevPullback x : Amb) = c.pullAmb x := rfl

lemma sobolevPullback_symm_apply (x : H1) :
    (c.sobolevPullback.symm x : c.dom.Amb) = c.pushAmb x := rfl

lemma sobolevPullback_embedH (u : smoothFns) :
    c.sobolevPullback (c.dom.embedH u) = embedC1H (c.pullC1 u) (c.contDiff_pullC1 u) :=
  Subtype.ext (c.pullAmb_embed u)

end C1Conf

end SteklovH1
