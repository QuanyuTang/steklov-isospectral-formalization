module

public import RequestProject.C1Transfer
public import RequestProject.ConformalPullback

/-!
# Proposition 2.1.1 (conformal pullback) in the paper's generality

Let `F : 𝔻 → Ω` be a conformal bijection onto a bounded simply connected plane domain which
extends to a `C¹` diffeomorphism `𝔻̄ → Ω̄`, with `F' ≠ 0` on `𝕋`.  Then
`Spec_St(Ω) = Spec_St(𝔻, |F'|_𝕋)`.

**`C¹` on a closed set.**  As usual for manifolds with boundary, a map on a closed set is called
`C¹` if it is the restriction of a `C¹` map on an open neighbourhood.  Thus the hypotheses are:
`F` is holomorphic and injective on `𝔻`, `F(𝔻) = Ω`, `F` is injective on `𝔻̄` with `F(𝔻̄) = Ω̄`,
`F` is (real) `C¹` on an open `U ⊇ 𝔻̄`, and there is a map `G`, (real) `C¹` on an open `W ⊇ Ω̄`, with
`G ∘ F = id` on `𝔻̄` (the inverse diffeomorphism).  Nothing holomorphic is assumed across `𝕋`.
On `𝕋` the derivative `F'` is the (real) derivative of the `C¹` extension evaluated at `1`; it
is complex-linear there (`fderiv_eq_mul`), so `|F'(z)| = ‖fderiv ℝ F z 1‖`.

The proof is by approximation in the min–max principle (`SteklovC1.minMax_le_of_C1_comp`): test
functions are transported by composition with mollified (smooth) approximations of `F` and of
`G`, using conformal invariance of the Dirichlet integral and the `C¹` arc-length formula on the
boundary curve `t ↦ F(e^{it})`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Steklov PlaneDomain
open scoped ENNReal ContDiff Real

noncomputable section

namespace SteklovC1

/-! ### Min–max values only depend on smooth test functions -/

lemma minMax_congr_smooth {E B E' B' : (ℂ → ℝ) → ℝ≥0∞}
    (hE : ∀ u, ContDiff ℝ ∞ u → E u = E' u) (hB : ∀ u, ContDiff ℝ ∞ u → B u = B' u) (k : ℕ) :
    minMax E B k = minMax E' B' k := by
  unfold minMax
  have hadm : ∀ V, AdmissibleSpace B k V ↔ AdmissibleSpace B' k V := by
    intro V
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun u hu h0 => by rw [← hB u (h1 u hu)]; exact h3 u hu h0⟩
    · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, fun u hu h0 => by rw [hB u (h1 u hu)]; exact h3 u hu h0⟩
  refine iInf_congr fun V => ?_
  by_cases hV : AdmissibleSpace B k V
  · have hV' := (hadm V).1 hV
    rw [iInf_pos hV, iInf_pos hV']
    refine iSup_congr fun u => iSup_congr fun hu => iSup_congr fun _ => ?_
    rw [hE u (hV.1 u hu), hB u (hV.1 u hu)]
  · have hV' : ¬ AdmissibleSpace B' k V := fun h => hV ((hadm V).2 h)
    rw [iInf_neg hV, iInf_neg hV']

/-! ### Cut-offs -/

lemma exists_cutoff_compact {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ (∃ W, IsOpen W ∧ K ⊆ W ∧ ∀ z ∈ W, χ z = 1) ∧
      tsupport χ ⊆ U ∧ HasCompactSupport χ := by
  obtain ⟨χ, hχ, hW, hsupp⟩ := ConformalPullback.exists_cutoff hK
    (hU.inter (isOpen_thickening (δ := 1) (E := K)))
    (subset_inter hKU (self_subset_thickening one_pos K))
  refine ⟨χ, hχ, hW, hsupp.trans inter_subset_left, ?_⟩
  exact (hK.cthickening (r := 1)).of_isClosed_subset (isClosed_tsupport _)
    (hsupp.trans (inter_subset_right.trans (thickening_subset_cthickening _ _)))

lemma cutoff_mul_contDiff {χ : ℂ → ℝ} {Φ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ U) (hΦ : ContDiffOn ℝ 1 Φ U) :
    ContDiff ℝ 1 (fun z => (χ z : ℂ) * Φ z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  have hχ' : ContDiffAt ℝ 1 (fun z => (χ z : ℂ)) z :=
    (Complex.ofRealCLM.contDiff.comp (hχ.of_le (by simp))).contDiffAt
  by_cases hz : z ∈ U
  · exact hχ'.mul (hΦ.contDiffAt (hU.mem_nhds hz))
  · have hz' : z ∉ tsupport χ := fun h => hz (hsupp h)
    rw [notMem_tsupport_iff_eventuallyEq] at hz'
    refine contDiffAt_const (c := (0 : ℂ)).congr_of_eventuallyEq ?_
    filter_upwards [hz'] with x hx
    simp [hx]

lemma cutoff_mul_hasCompactSupport {χ : ℂ → ℝ} (hχ : HasCompactSupport χ) (Φ : ℂ → ℂ) :
    HasCompactSupport (fun z => (χ z : ℂ) * Φ z) :=
  HasCompactSupport.mul_right (f := fun z => (χ z : ℂ)) (hχ.comp_left Complex.ofReal_zero)

/-! ### Boundary behaviour of the `C¹` extension -/

variable {F : ℂ → ℂ} {U : Set ℂ}

/-- The derivative of the `C¹` extension is complex-linear on `𝔻̄`. -/
lemma fderiv_eq_mul (hF : DifferentiableOn ℂ F (ball 0 1)) (hU : IsOpen U)
    (hcb : closedBall (0 : ℂ) 1 ⊆ U) (hC : ContDiffOn ℝ 1 F U) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) 1) (w : ℂ) : fderiv ℝ F z w = w * fderiv ℝ F z 1 := by
  have hcont : ContinuousOn (fun z => fderiv ℝ F z) U :=
    hC.continuousOn_fderiv_of_isOpen hU le_rfl
  have h1 : ContinuousOn (fun z => fderiv ℝ F z w) (closedBall 0 1) :=
    ((ContinuousLinearMap.apply ℝ ℂ w).continuous.comp_continuousOn hcont).mono hcb
  have h2 : ContinuousOn (fun z => w * fderiv ℝ F z 1) (closedBall 0 1) :=
    (continuousOn_const.mul
      ((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp_continuousOn hcont)).mono hcb
  refine Set.EqOn.of_subset_closure (s := ball 0 1) ?_ h1 h2 ball_subset_closedBall
    (by rw [closure_ball (0 : ℂ) one_ne_zero]) hz
  intro x hx
  have hd : DifferentiableAt ℂ F x := hF.differentiableAt (isOpen_ball.mem_nhds hx)
  simp only
  rw [hd.fderiv_restrictScalars ℝ]
  simp only [ContinuousLinearMap.coe_restrictScalars']
  rw [show w = w • (1 : ℂ) by simp, map_smul, smul_eq_mul]
  simp

lemma frontier_eq_image_sphere {Ω : Set ℂ} (hΩo : IsOpen Ω) (himg : F '' ball 0 1 = Ω)
    (hcl : F '' closedBall 0 1 = closure Ω) (hinj : InjOn F (closedBall 0 1)) :
    frontier Ω = F '' sphere 0 1 := by
  rw [frontier, ← hcl, hΩo.interior_eq, ← himg, ← closedBall_diff_ball, hinj.image_diff,
    inter_eq_right.2 ball_subset_closedBall]

/-- **Boundary change of variables for a `C¹` boundary extension.** -/
lemma boundary_lintegral_C1 (hF : DifferentiableOn ℂ F (ball 0 1)) (hU : IsOpen U)
    (hcb : closedBall (0 : ℂ) 1 ⊆ U) (hC : ContDiffOn ℝ 1 F U)
    (hinj : InjOn F (closedBall 0 1)) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ x in F '' sphere 0 1, g x ∂μH[1] =
      ∫⁻ t in Ioc 0 (2 * π), g (F (Complex.exp (t * Complex.I))) *
        ENNReal.ofReal ‖fderiv ℝ F (Complex.exp (t * Complex.I)) 1‖ := by
  set c := circleMap (0 : ℂ) 1
  have hc : ∀ t : ℝ, c t = Complex.exp (t * Complex.I) := fun t => by simp [c, circleMap]
  have hsph : ∀ t, c t ∈ sphere (0 : ℂ) 1 := fun t => by
    rw [mem_sphere_zero_iff_norm]; simp [c]
  have hU' : ∀ t, c t ∈ U := fun t => hcb (sphere_subset_closedBall (hsph t))
  have hdiff : ∀ z ∈ U, DifferentiableAt ℝ F z := fun z hz =>
    (hC.contDiffAt (hU.mem_nhds hz)).differentiableAt one_ne_zero
  have hγ : ∀ t, HasDerivAt (F ∘ c) (fderiv ℝ F (c t) (c t * Complex.I)) t := fun t =>
    (hdiff _ (hU' t)).hasFDerivAt.comp_hasDerivAt t (hasDerivAt_circleMap 0 1 t)
  have hcont : ContinuousOn (fun z => fderiv ℝ F z) U :=
    hC.continuousOn_fderiv_of_isOpen hU le_rfl
  have hγ' : Continuous fun t => fderiv ℝ F (c t) (c t * Complex.I) := by
    have h1 : Continuous fun t => fderiv ℝ F (c t) :=
      hcont.comp_continuous (continuous_circleMap 0 1) hU'
    exact h1.clm_apply ((continuous_circleMap 0 1).mul continuous_const)
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
  rw [mul_comm, ← ofReal_norm_eq_enorm, ← hc,
    fderiv_eq_mul hF hU hcb hC (sphere_subset_closedBall (hsph t)), norm_mul, norm_mul,
    Complex.norm_I, show ‖c t‖ = 1 by simpa using hsph t]
  simp

/-! ### The boundary measure of the weighted problem -/

/-- The measure `ρ(e^{it}) dt` on `(0, 2π]`, pushed to the circle. -/
def weightMeasure (ρ : ℂ → ℝ) : Measure ℂ :=
  Measure.map (fun t : ℝ => Complex.exp (t * Complex.I))
    ((volume.restrict (Ioc 0 (2 * π))).withDensity
      fun t => ENNReal.ofReal (ρ (Complex.exp (t * Complex.I))))

lemma continuous_weight {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ (sphere 0 1)) :
    Continuous fun t : ℝ => ρ (Complex.exp (t * Complex.I)) :=
  hρ.comp_continuous (by fun_prop) ConformalPullback.exp_mem_sphere

lemma lintegral_weightMeasure {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ (sphere 0 1)) {w : ℂ → ℝ}
    (hw : Continuous w) :
    ∫⁻ x, ‖w x‖ₑ ^ 2 ∂weightMeasure ρ = weightedBoundaryMass ρ w := by
  unfold weightMeasure weightedBoundaryMass
  rw [lintegral_map (by fun_prop) (by fun_prop),
    lintegral_withDensity_eq_lintegral_mul _ (by
      exact ENNReal.measurable_ofReal.comp (continuous_weight hρ).measurable)
      (by have := hw.measurable; fun_prop)]
  refine lintegral_congr fun t => ?_
  simp [mul_comm]

lemma isFiniteMeasure_weightMeasure {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ (sphere 0 1)) :
    IsFiniteMeasure (weightMeasure ρ) := by
  unfold weightMeasure
  have : IsFiniteMeasure ((volume.restrict (Ioc 0 (2 * π))).withDensity
      fun t => ENNReal.ofReal (ρ (Complex.exp (t * Complex.I)))) := by
    refine isFiniteMeasure_withDensity ?_
    obtain ⟨M, hM⟩ := (isCompact_sphere (0 : ℂ) 1).exists_bound_of_continuousOn hρ
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono (g := fun _ => ENNReal.ofReal M)
      fun t => ENNReal.ofReal_le_ofReal ?_) ?_)
    · exact (le_abs_self _).trans (hM _ (ConformalPullback.exp_mem_sphere t))
    · rw [lintegral_const]; simp [ENNReal.mul_lt_top]
  infer_instance

end SteklovC1

open SteklovC1

/-- **Proposition 2.1.1 (conformal pullback), general `C¹` version** (statement).

Hypotheses, exactly as in the paper: `Ω` is a bounded simply connected domain; `F` is a conformal
bijection `𝔻 → Ω` (holomorphic on `𝔻`, `F(𝔻) = Ω`, injective); `F` extends to a `C¹`
diffeomorphism `𝔻̄ → Ω̄` (`F` injective on `𝔻̄` with `F(𝔻̄) = Ω̄`, `F` real-`C¹` on an open
neighbourhood of `𝔻̄`, with a real-`C¹` inverse `G` defined on an open neighbourhood of `Ω̄`); and
`F' ≠ 0` on `𝕋`.  Conclusion: `Spec_St(Ω) = Spec_St(𝔻, |F'|_𝕋)` with `|F'(z)| = ‖dF_z(1)‖`.

The proof (`prop_2_1_1_C1`) does not use simple connectivity or `F' ≠ 0` on `𝕋`; they are kept
because they are hypotheses of the paper's statement. -/
def Prop_2_1_1_C1 : Prop :=
  ∀ (F : ℂ → ℂ) (Ω : Set ℂ),
    IsDomain Ω → Bornology.IsBounded Ω → SimplyConnectedSpace Ω →
    DifferentiableOn ℂ F (ball 0 1) → F '' ball 0 1 = Ω →
    InjOn F (closedBall 0 1) → F '' closedBall 0 1 = closure Ω →
    (∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ ContDiffOn ℝ 1 F U) →
    (∃ G : ℂ → ℂ, ∃ W : Set ℂ, IsOpen W ∧ closure Ω ⊆ W ∧ ContDiffOn ℝ 1 G W ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, G (F z) = z) →
    (∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) →
    steklovSpectrum Ω = weightedSteklovSpectrum (fun z => ‖fderiv ℝ F z 1‖)

theorem prop_2_1_1_C1 : Prop_2_1_1_C1 := by
  intro F Ω hdom hbdd _hsc hF himg hinj hcl ⟨U, hU, hcb, hC⟩ ⟨G, W, hW, hclW, hGC, hGF⟩ _hF'
  have hΩo : IsOpen Ω := hdom.1
  have hfr : frontier Ω = F '' sphere 0 1 := frontier_eq_image_sphere hΩo himg hcl hinj
  set ρ : ℂ → ℝ := fun z => ‖fderiv ℝ F z 1‖ with hρdef
  have hρ : ContinuousOn ρ (sphere 0 1) := by
    have hcont : ContinuousOn (fun z => fderiv ℝ F z) U :=
      hC.continuousOn_fderiv_of_isOpen hU le_rfl
    exact (((ContinuousLinearMap.apply ℝ ℂ (1 : ℂ)).continuous.comp_continuousOn
      hcont).norm).mono (sphere_subset_closedBall.trans hcb)
  haveI := isFiniteMeasure_weightMeasure hρ
  have hbdry : ∀ g : ℂ → ℝ≥0∞, Measurable g →
      ∫⁻ x in frontier Ω, g x ∂μH[1] = ∫⁻ t in Ioc 0 (2 * π),
        g (F (Complex.exp (t * Complex.I))) * ENNReal.ofReal (ρ (Complex.exp (t * Complex.I))) :=
    fun g hg => by rw [hfr]; exact boundary_lintegral_C1 hF hU hcb hC hinj hg
  have hen : ∀ u : ℂ → ℝ, Differentiable ℝ u →
      dirichletEnergy Ω u = ∫⁻ z in ball 0 1, ‖fderiv ℝ (u ∘ F) z‖ₑ ^ 2 := fun u hu => by
    rw [← himg]
    exact ConformalPullback.dirichletEnergy_image isOpen_ball hF subset_rfl measurableSet_ball
      (hinj.mono ball_subset_closedBall) hu
  obtain ⟨χ₁, hχ₁, ⟨W₁, hW₁, hKW₁, hχ₁one⟩, hsupp₁, hcs₁⟩ :=
    exists_cutoff_compact (isCompact_closedBall 0 1) hU hcb
  set Φ₁ : ℂ → ℂ := fun z => (χ₁ z : ℂ) * F z with hΦ₁def
  have hΦ₁ : ContDiff ℝ 1 Φ₁ := cutoff_mul_contDiff hU hχ₁ hsupp₁ hC
  have hΦ₁c : HasCompactSupport Φ₁ := cutoff_mul_hasCompactSupport hcs₁ F
  have hΦ₁F : ∀ z ∈ W₁, Φ₁ z = F z := fun z hz => by simp [Φ₁, hχ₁one z hz]
  have hK₂ : IsCompact (closure Ω) := by
    rw [← hcl]; exact (isCompact_closedBall 0 1).image_of_continuousOn (hC.continuousOn.mono hcb)
  obtain ⟨χ₂, hχ₂, ⟨W₂, hW₂, hKW₂, hχ₂one⟩, hsupp₂, hcs₂⟩ := exists_cutoff_compact hK₂ hW hclW
  set Φ₂ : ℂ → ℂ := fun z => (χ₂ z : ℂ) * G z with hΦ₂def
  have hΦ₂ : ContDiff ℝ 1 Φ₂ := cutoff_mul_contDiff hW hχ₂ hsupp₂ hGC
  have hΦ₂c : HasCompactSupport Φ₂ := cutoff_mul_hasCompactSupport hcs₂ G
  have hΦ₂F : ∀ z ∈ closedBall (0 : ℂ) 1, Φ₂ (F z) = z := fun z hz => by
    have : F z ∈ W₂ := hKW₂ (hcl ▸ mem_image_of_mem F hz)
    simp [Φ₂, hχ₂one _ this, hGF z hz]
  funext k
  unfold steklovSpectrum weightedSteklovSpectrum steklovEigenvalue weightedSteklovEigenvalue
  apply le_antisymm
  · -- `σ_k(Ω) ≤ σ_k(𝔻, ρ)`: transport disk test functions by `w ↦ w ∘ Φ₂`
    have hfin : volume Ω ≠ ⊤ := hbdd.measure_lt_top.ne
    haveI : IsFiniteMeasure (μH[1].restrict (frontier Ω)) := by
      refine ⟨?_⟩
      have h1 := hbdry (fun _ => 1) measurable_const
      have h2 := lintegral_weightMeasure hρ (w := fun _ => (1 : ℝ)) continuous_const
      rw [Measure.restrict_apply_univ, ← setLIntegral_one, h1]
      unfold weightedBoundaryMass at h2
      simp only [enorm_one, one_pow, one_mul, lintegral_one] at h2 ⊢
      rw [← h2]
      exact measure_lt_top _ _
    refine minMax_le_of_C1_comp (Ω₂ := Ω) (ν := μH[1].restrict (frontier Ω)) hfin hΦ₂ hΦ₂c
      (E₁ := dirichletEnergy (ball 0 1)) (B₁ := weightedBoundaryMass ρ) ?_ ?_ k
    · intro w hw
      have hd : Differentiable ℝ (w ∘ Φ₂) :=
        (hw.differentiable (by simp)).comp (hΦ₂.differentiable one_ne_zero)
      have := hen _ hd
      unfold dirichletEnergy at this
      rw [this]
      exact (ConformalPullback.dirichletEnergy_ball_congr (w₁ := (w ∘ Φ₂) ∘ F) (w₂ := w)
        fun z hz => by simp [Function.comp, hΦ₂F z (ball_subset_closedBall hz)]).symm
    · intro w hw
      rw [hbdry _ (by have := hw.continuous.measurable; have := hΦ₂.continuous.measurable; fun_prop)]
      unfold weightedBoundaryMass
      refine lintegral_congr fun t => ?_
      simp only [hΦ₂F _ (sphere_subset_closedBall (ConformalPullback.exp_mem_sphere t))]
  · -- `σ_k(𝔻, ρ) ≤ σ_k(Ω)`: transport test functions on `Ω` by `u ↦ u ∘ Φ₁`
    have h := minMax_le_of_C1_comp (Ω₂ := ball 0 1) (ν := weightMeasure ρ)
      measure_ball_lt_top.ne hΦ₁ hΦ₁c (E₁ := dirichletEnergy Ω) (B₁ := boundaryMass Ω) ?_ ?_ k
    · rwa [minMax_congr_smooth (E' := dirichletEnergy (ball 0 1))
        (B' := weightedBoundaryMass ρ) (fun _ _ => rfl)
        (fun u hu => lintegral_weightMeasure hρ hu.continuous)] at h
    · intro u hu
      rw [hen u (hu.differentiable (by simp))]
      refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
      have : u ∘ Φ₁ =ᶠ[𝓝 z] u ∘ F := by
        filter_upwards [hW₁.mem_nhds (hKW₁ (ball_subset_closedBall hz))] with x hx
        simp [Function.comp, hΦ₁F x hx]
      rw [this.fderiv_eq]
    · intro u hu
      unfold boundaryMass
      rw [hbdry _ (by have := hu.continuous.measurable; fun_prop),
        show (∫⁻ x, ‖u (Φ₁ x)‖ₑ ^ 2 ∂weightMeasure ρ) = ∫⁻ x, ‖(u ∘ Φ₁) x‖ₑ ^ 2 ∂weightMeasure ρ
          from rfl, lintegral_weightMeasure hρ (hu.continuous.comp hΦ₁.continuous)]
      unfold weightedBoundaryMass
      refine lintegral_congr fun t => ?_
      simp only [Function.comp,
        hΦ₁F _ (hKW₁ (sphere_subset_closedBall (ConformalPullback.exp_mem_sphere t)))]

end
