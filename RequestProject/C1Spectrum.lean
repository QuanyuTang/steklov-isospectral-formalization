module

public import RequestProject.C1Sobolev
public import RequestProject.DomainDensity
public import RequestProject.ConformalSpectrum
public import RequestProject.MainTheoremDom

/-!
# The general `C¹` Proposition 2.1.1 as an identification of weak `H¹` spectra

For a conformal map `F : 𝔻 → Ω` that extends to a `C¹` diffeomorphism `𝔻̄ → Ω̄`
(`SteklovH1.C1Conf`, no holomorphy across `𝕋`), we prove:

* `C1Conf.mem_H1_iff_isWeakGradientPair`: `H¹(Ω)` (closure of smooth graphs) is the weak-gradient
  space `W^{1,2}(Ω)`;
* `C1Conf.exists_hasTraceIneq`: the trace inequality on `Ω`;
* `C1Conf.inner_trace_pull`, `C1Conf.inner_grad_pull`: the Sobolev pullback
  `C1Conf.sobolevPullback : H¹(Ω) ≃ H¹(𝔻)` matches the Dirichlet forms and turns the boundary form
  `∫_{∂Ω} Tx Ty dH¹` into `∫_0^{2π} ρ(e^{it}) T(Px) T(Py) dt` with `ρ = ‖dF(1)‖ = |F'|`;
* `C1Conf.isCompactOperator_trace`: `T : H¹(Ω) → L²(∂Ω, H¹)` is compact;
* `C1Conf.weak_spectral_theorem_dom`: the full weak Steklov spectrum of `Ω` posed on `H¹(Ω)`, with
  multiplicities, equals the weak `ρ`-weighted spectrum of the disk.

The packaged statement is `SteklovC1.Prop_2_1_1_C1_Weak`, proved as `prop_2_1_1_C1_weak` under
exactly the hypotheses of `Prop_2_1_1_C1`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Real ComplexConjugate InnerProductSpace

noncomputable section

namespace SteklovH1

namespace C1Conf

open SteklovDensity

variable (c : C1Conf)

/-- **Weak chain rule** for the conformal map `F` (with only a `C¹` boundary extension). -/
theorem pullAmb_isWeakGradientPair (x : c.dom.Amb) (hx : c.dom.IsWeakGradientPair x) :
    IsWeakGradientPair (c.pullAmb x) := by
  intro φ hφ v
  set f := x.fst
  set g := x.snd
  set Ω := c.Ω
  have hΩm : MeasurableSet Ω := c.measurableSet_Ω
  set F : ℂ → ℝ := Ω.indicator (f : ℂ → ℝ) with hFdef
  set Gg : ℂ → ℂ := Ω.indicator (g : ℂ → ℂ) with hGdef
  have hFm : StronglyMeasurable F := (Lp.stronglyMeasurable f).indicator hΩm
  have hGm : StronglyMeasurable Gg := (Lp.stronglyMeasurable g).indicator hΩm
  have hFL : MemLp F 2 volume := (memLp_indicator_iff_restrict hΩm).2 (Lp.memLp f)
  have hGL : MemLp Gg 2 volume := (memLp_indicator_iff_restrict hΩm).2 (Lp.memLp g)
  have hFl := hFL.locallyIntegrable one_le_two
  have hGl := hGL.locallyIntegrable one_le_two
  -- the weak identity on the whole plane
  have hwF : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∀ v : ℂ, ∫ t, F t * fderiv ℝ ψ t v = - ∫ t, inner ℝ (Gg t) v * ψ t := by
    intro ψ h1 h2 h3 v
    have e1 : (fun t => F t * fderiv ℝ ψ t v) = Ω.indicator (fun t => f t * fderiv ℝ ψ t v) := by
      funext t; by_cases ht : t ∈ Ω <;> simp [hFdef, ht]
    have e2 : (fun t => inner ℝ (Gg t) v * ψ t) = Ω.indicator (fun t => inner ℝ (g t) v * ψ t) := by
      funext t; by_cases ht : t ∈ Ω <;> simp [hGdef, ht]
    rw [e1, e2, integral_indicator hΩm, integral_indicator hΩm]
    exact hx ψ ⟨h1, h2, h3⟩ v
  -- the compact set `K = G(tsupport φ)` and a margin `δ`
  have hK : IsCompact (c.F '' tsupport φ) :=
    hφ.2.1.isCompact.image_of_continuousOn (c.diff.continuousOn.mono hφ.2.2)
  have hKΩ : c.F '' tsupport φ ⊆ Ω := by
    rintro _ ⟨z, hz, rfl⟩; exact c.mem_Ω (hφ.2.2 hz)
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open c.isOpen_Ω hKΩ
  -- test vectors in `L²(𝔻)`
  have hφ1 := hφ.contDiff_one
  have hcφ : Continuous φ := hφ1.continuous
  have hcφ' : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv one_ne_zero
  have hψ₁ : MemLp (fun z => fderiv ℝ φ z v) 2 μD := memLp_disk (by fun_prop)
  have hψ₂ : MemLp (fun z => φ z • v) 2 μD := memLp_disk (by fun_prop)
  set ψ₁ := hψ₁.toLp _
  set ψ₂ := hψ₂.toLp _
  -- the functionals
  set A : Lp ℝ 2 c.dom.μ → ℝ := fun h => inner ℝ (c.pullF h) ψ₁ with hA
  set B : Lp ℂ 2 c.dom.μ → ℝ := fun k => inner ℝ (c.pullG k) ψ₂ with hB
  have hAf : A f = ∫ z in ball (0:ℂ) 1, (c.pullAmb x).fst z * fderiv ℝ φ z v := by
    rw [hA]; simp only; rw [inner_toLp_real]; rfl
  have hBg : B g = ∫ z in ball (0:ℂ) 1, inner ℝ ((c.pullAmb x).snd z) v * φ z := by
    rw [hB]; simp only; rw [inner_toLp_smul]; rfl
  rw [← hAf, ← hBg]
  -- bounds
  obtain ⟨C, hC0, hCF, hCG, -, -⟩ := c.exists_C
  have hAb : ∀ h, |A h| ≤ C * ‖ψ₁‖ * ‖h‖ := fun h => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖c.pullF h‖ * ‖ψ₁‖ ≤ C * ‖h‖ * ‖ψ₁‖ := mul_le_mul_of_nonneg_right (hCF h) (norm_nonneg _)
      _ = _ := by ring
  have hBb : ∀ k, |B k| ≤ C * ‖ψ₂‖ * ‖k‖ := fun k => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖c.pullG k‖ * ‖ψ₂‖ ≤ C * ‖k‖ * ‖ψ₂‖ := mul_le_mul_of_nonneg_right (hCG k) (norm_nonneg _)
      _ = _ := by ring
  have hAlin : ∀ h h', A (h - h') = A h - A h' := fun h h' => by
    simp only [hA, map_sub, inner_sub_left]
  have hBlin : ∀ k k', B (k - k') = B k - B k' := fun k k' => by
    simp only [hB, map_sub, inner_sub_left]
  -- the identity for mollified functions
  have hmoll : ∀ b : ContDiffBump (0 : ℂ), b.rOut ≤ δ →
      ∃ fb : Lp ℝ 2 c.dom.μ, ∃ gb : Lp ℂ 2 c.dom.μ, A fb = - B gb ∧
        (fb : ℂ → ℝ) =ᵐ[c.dom.μ] moll b F ∧ (gb : ℂ → ℂ) =ᵐ[c.dom.μ] moll b Gg := by
    intro b hb
    have hsm : moll b F ∈ smoothFns := contDiff_moll b hFl
    set u : smoothFns := ⟨moll b F, hsm⟩
    have hgc : Continuous (moll b Gg) := continuous_moll b hGl
    refine ⟨c.dom.toL2 u, (c.dom.memLp_dom hgc).toLp _, ?_, c.dom.toL2_ae u,
      (c.dom.memLp_dom hgc).coeFn_toLp⟩
    set w := c.pullC1 u
    have hibp := ibp_disk (c.contDiff_pullC1 u) hφ v
    have e1 : A (c.dom.toL2 u) = ∫ z in ball (0:ℂ) 1, w z * fderiv ℝ φ z v := by
      rw [hA]; simp only; rw [inner_toLp_real]
      refine integral_congr_ae ?_
      filter_upwards [c.pullF_ae (c.dom.toL2 u), c.ae_comp (c.dom.toL2_ae u),
        ae_restrict_mem measurableSet_ball] with z h1 h2 hz
      rw [h1, h2, show w z = _ from c.pullC1_eq u (ball_subset_closedBall hz)]
    have e2 : B ((c.dom.memLp_dom hgc).toLp _) =
        ∫ z in ball (0:ℂ) 1, fderiv ℝ w z v * φ z := by
      rw [hB]; simp only; rw [inner_toLp_smul]
      refine integral_congr_ae ?_
      filter_upwards [c.pullG_ae ((c.dom.memLp_dom hgc).toLp _),
        c.ae_comp (c.dom.memLp_dom hgc).coeFn_toLp, ae_restrict_mem measurableSet_ball]
        with z h1 h2 hz
      rw [h1, h2, ← inner_grad, c.grad_pullC1 u hz]
      by_cases hφz : φ z = 0
      · simp [hφz]
      · have hzK : c.F z ∈ c.F '' tsupport φ := ⟨z, subset_tsupport _ hφz, rfl⟩
        have hball : closedBall (c.F z) b.rOut ⊆ Ω :=
          ((closedBall_subset_closedBall hb).trans (closedBall_subset_cthickening hzK δ)).trans hδK
        rw [show grad (u : ℂ → ℝ) (c.F z) = moll b Gg (c.F z) from
          grad_moll Ω hFl hGl hwF b (c.F z) hball, mul_comm ((starRingEnd ℂ) _) (moll b Gg _)]
    rw [e1, e2, hibp]
  -- conclude by an `ε`-argument
  set K₁ := C * ‖ψ₁‖
  set K₂ := C * ‖ψ₂‖
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  have key : ∀ ε > 0, |A f + B g| ≤ ε := by
    intro ε hε
    set ε' := ε / (K₁ + K₂ + 1) with hε'
    have hε'0 : 0 < ε' := by positivity
    obtain ⟨δ₁, hδ₁, hmF⟩ := moll_tendsto hFL hFm hε'0
    obtain ⟨δ₂, hδ₂, hmG⟩ := moll_tendsto hGL hGm hε'0
    set r := min (min δ₁ δ₂) δ / 2 with hr
    have hr0 : 0 < r := by positivity
    have hrm : r < min (min δ₁ δ₂) δ := by rw [hr]; linarith [lt_min (lt_min hδ₁ hδ₂) hδ]
    let b : ContDiffBump (0 : ℂ) := ⟨r / 2, r, by positivity, by linarith⟩
    have hb1 : b.rOut < δ₁ := hrm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hb2 : b.rOut < δ₂ := hrm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hb3 : b.rOut ≤ δ := (hrm.trans_le (min_le_right _ _)).le
    obtain ⟨fb, gb, hid, hfb, hgb⟩ := hmoll b hb3
    have hnf : ‖f - fb‖ ≤ ε' := by
      rw [Lp.norm_def]
      refine ENNReal.toReal_le_of_le_ofReal hε'0.le ?_
      have hae : ((f - fb : Lp ℝ 2 c.dom.μ) : ℂ → ℝ) =ᵐ[c.dom.μ] F - moll b F := by
        filter_upwards [Lp.coeFn_sub f fb, hfb, ae_restrict_mem hΩm] with z h1 h2 h3
        rw [h1, Pi.sub_apply, h2, Pi.sub_apply, hFdef, Set.indicator_of_mem (show z ∈ Ω from h3)]
      rw [eLpNorm_congr_ae hae]
      exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hmF b hb1)
    have hng : ‖g - gb‖ ≤ ε' := by
      rw [Lp.norm_def]
      refine ENNReal.toReal_le_of_le_ofReal hε'0.le ?_
      have hae : ((g - gb : Lp ℂ 2 c.dom.μ) : ℂ → ℂ) =ᵐ[c.dom.μ] Gg - moll b Gg := by
        filter_upwards [Lp.coeFn_sub g gb, hgb, ae_restrict_mem hΩm] with z h1 h2 h3
        rw [h1, Pi.sub_apply, h2, Pi.sub_apply, hGdef, Set.indicator_of_mem (show z ∈ Ω from h3)]
      rw [eLpNorm_congr_ae hae]
      exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hmG b hb2)
    have hsplit : A f + B g = A (f - fb) + B (g - gb) := by
      rw [hAlin, hBlin, hid]; ring
    rw [hsplit]
    calc |A (f - fb) + B (g - gb)| ≤ |A (f - fb)| + |B (g - gb)| := abs_add_le _ _
      _ ≤ K₁ * ‖f - fb‖ + K₂ * ‖g - gb‖ := add_le_add (hAb _) (hBb _)
      _ ≤ K₁ * ε' + K₂ * ε' := add_le_add (mul_le_mul_of_nonneg_left hnf hK₁)
          (mul_le_mul_of_nonneg_left hng hK₂)
      _ ≤ ε := by
          rw [← add_mul, hε', mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  have h0 : A f + B g = 0 := by
    by_contra hne
    have := key (|A f + B g| / 2) (by positivity)
    linarith [abs_pos.2 hne]
  linarith

/-- **`H¹(Ω) = W^{1,2}(Ω)`** for a `C¹`-diffeomorphic conformal image `Ω = F(𝔻)`. -/
theorem mem_H1_iff_isWeakGradientPair (x : c.dom.Amb) :
    x ∈ c.dom.H1 ↔ c.dom.IsWeakGradientPair x := by
  constructor
  · intro hx φ hφ v
    exact c.dom.weak_gradient ⟨x, hx⟩ hφ v
  · intro hx
    have h1 : c.pullAmb x ∈ H1 :=
      (SteklovH1.mem_H1_iff_isWeakGradientPair _).2 (c.pullAmb_isWeakGradientPair x hx)
    have h2 := c.pushAmb_mem ⟨_, h1⟩
    simpa [c.pushAmb_pullAmb] using h2


/-! ### The trace inequality and the trace identity -/

/-- **Trace inequality** on a `C¹`-diffeomorphic conformal image. -/
theorem exists_hasTraceIneq : ∃ C, c.dom.HasTraceIneq C := by
  obtain ⟨m, M, hm, hb⟩ := c.exists_bounds
  obtain ⟨R, hR0, hR⟩ := c.exists_ρ_bound
  refine ⟨R * (3 * (m ^ 2)⁻¹ + 1), fun u hu => ?_⟩
  set us : smoothFns := ⟨u, hu⟩
  set w := c.pullC1 us
  have hw : ContDiff ℝ 1 w := c.contDiff_pullC1 us
  set A := ∫⁻ z in c.dom.carrier, ‖u z‖ₑ ^ 2
  set E := Steklov.dirichletEnergy c.dom.carrier u
  have hmeas : Measurable fun x => ‖u x‖ₑ ^ 2 := (hu.continuous.measurable.enorm).pow_const 2
  have h1 : Steklov.boundaryMass c.dom.carrier u ≤
      ENNReal.ofReal R * ∫⁻ t in Ioc 0 (2 * π), ‖w (Complex.exp (t * Complex.I))‖ₑ ^ 2 := by
    unfold Steklov.boundaryMass
    rw [dom_carrier, c.lintegral_frontier hmeas, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun t => ?_
    have hs := ConformalPullback.exp_mem_sphere t
    rw [show w (Complex.exp (t * Complex.I)) = u (c.F (Complex.exp (t * Complex.I))) from
      c.pullC1_eq us (sphere_subset_closedBall hs), mul_comm]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hR _ hs)) le_rfl
  have h2 := trace_ineq_lintegral hw
  have h3 : ∫⁻ z in ball (0:ℂ) 1, ‖w z‖ₑ ^ 2 ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * A := by
    calc ∫⁻ z in ball (0:ℂ) 1, ‖w z‖ₑ ^ 2 = ∫⁻ z in ball (0:ℂ) 1, ‖u (c.F z)‖ₑ ^ 2 :=
          setLIntegral_congr_fun measurableSet_ball fun z hz => by
            rw [show w z = u (c.F z) from c.pullC1_eq us (ball_subset_closedBall hz)]
      _ ≤ _ := c.lintegral_comp_F_le hm (fun z hz => (hb z hz).1) (fun x => ‖u x‖ₑ ^ 2)
  have h4 : ∫⁻ z in ball (0:ℂ) 1, ‖fderiv ℝ w z‖ₑ ^ 2 = E := by
    calc ∫⁻ z in ball (0:ℂ) 1, ‖fderiv ℝ w z‖ₑ ^ 2
        = ∫⁻ z in ball (0:ℂ) 1, ‖conj (deriv c.F z) * grad u (c.F z)‖ₑ ^ 2 :=
          setLIntegral_congr_fun measurableSet_ball fun z hz => by
            rw [← ofReal_norm_eq_enorm, ← norm_grad, c.grad_pullC1 us hz, ofReal_norm_eq_enorm]
      _ = ∫⁻ x in c.Ω, ‖grad u x‖ₑ ^ 2 := c.lintegral_grad_F _
      _ = E := by
          refine lintegral_congr fun x => ?_
          rw [← ofReal_norm_eq_enorm, norm_grad, ofReal_norm_eq_enorm]
  set a := ENNReal.ofReal ((m ^ 2)⁻¹)
  have hC : ENNReal.ofReal (R * (3 * (m ^ 2)⁻¹ + 1)) = ENNReal.ofReal R * (3 * a + 1) := by
    rw [ENNReal.ofReal_mul hR0, ENNReal.ofReal_add (by positivity) zero_le_one,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, ENNReal.ofReal_one]
  rw [hC, mul_assoc]
  refine h1.trans ?_
  gcongr
  refine h2.trans ?_
  rw [h4]
  calc 3 * (∫⁻ z in ball (0:ℂ) 1, ‖w z‖ₑ ^ 2) + E ≤ 3 * (a * A) + E := by gcongr
    _ ≤ 3 * (a * A) + 3 * (a * E) + (A + E) := add_le_add le_self_add le_add_self
    _ = (3 * a + 1) * (A + E) := by ring

/-- The weighted trace of the pullback, `x ↦ √ρ · T(Px)`. -/
def wtrace : c.dom.H1 →L[ℝ] Lp ℝ 2 μT :=
  (weightOp c.continuousOn_ρ).comp (c.sobolevPullback : c.dom.H1 →L[ℝ] H1)

lemma wtrace_apply (x : c.dom.H1) :
    c.wtrace x = weightOp c.continuousOn_ρ (c.sobolevPullback x) := by
  rw [wtrace, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

lemma enorm_trace_embedH (u : smoothFns) :
    ‖c.dom.trace (c.dom.embedH u)‖ₑ ^ 2 = ‖c.wtrace (c.dom.embedH u)‖ₑ ^ 2 := by
  obtain ⟨C, hC⟩ := c.exists_hasTraceIneq
  rw [c.dom.trace_embed hC, BddDomain.enorm_traceSmooth_sq, c.wtrace_apply,
    c.sobolevPullback_embedH, ← h1BoundaryMass_eq_weightOp]
  unfold h1BoundaryMass Steklov.boundaryMass
  rw [dom_carrier, c.lintegral_frontier
    ((continuous_of_mem u.2).measurable.enorm.pow_const 2)]
  refine (lintegral_congr_ae ?_).symm
  filter_upwards [trace_embedC1_ae (c.pullC1 u) (c.contDiff_pullC1 u)] with t ht
  rw [ht, c.pullC1_eq u (sphere_subset_closedBall (ConformalPullback.exp_mem_sphere t))]

/-- `‖Tx‖_{L²(∂Ω)} = ‖√ρ · T(Px)‖_{L²(𝕋)}` on all of `H¹(Ω)`. -/
theorem norm_trace_eq (x : c.dom.H1) : ‖c.dom.trace x‖ = ‖c.wtrace x‖ := by
  refine c.dom.denseRange_embedH.induction_on x
    (isClosed_eq (continuous_norm.comp c.dom.trace.continuous)
      (continuous_norm.comp c.wtrace.continuous)) (fun u => ?_)
  exact ConfMap.norm_eq_of_enorm_sq_eq (c.enorm_trace_embedH u)

/-- **The traces match under the Sobolev pullback**:
`∫_{∂Ω} Tx · Ty dH¹ = ∫_0^{2π} ρ(e^{it}) · T(Px)(t) · T(Py)(t) dt`, `ρ = ‖dF(1)‖`. -/
theorem inner_trace_pull (x y : c.dom.H1) :
    ∫ w, (c.dom.trace x : ℂ → ℝ) w * (c.dom.trace y : ℂ → ℝ) w ∂c.dom.ν =
      ∫ t in Ioc 0 (2 * π), c.ρ (Complex.exp (t * Complex.I)) *
        ((trace (c.sobolevPullback x) : ℝ → ℝ) t * (trace (c.sobolevPullback y) : ℝ → ℝ) t) := by
  rw [← inner_weightOp c.continuousOn_ρ c.ρ_pos]
  have := ConfMap.inner_eq_of_norm_eq c.dom.trace c.wtrace c.norm_trace_eq x y
  rw [L2.inner_def, c.wtrace_apply, c.wtrace_apply] at this
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [real_inner_eq_re_inner, RCLike.inner_apply, RCLike.conj_to_real, RCLike.re_to_real,
    mul_comm]

/-- **Conformal invariance of the Dirichlet form**: `∫_Ω ⟨∇x, ∇y⟩ = ∫_𝔻 ⟨∇(Px), ∇(Py)⟩`. -/
theorem inner_grad_pull (x y : c.dom.H1) :
    ∫ w in c.dom.carrier, ⟪((x : c.dom.Amb).snd : ℂ → ℂ) w, ((y : c.dom.Amb).snd : ℂ → ℂ) w⟫_ℝ =
      ∫ z in ball (0 : ℂ) 1, ⟪((c.sobolevPullback x : Amb).snd : ℂ → ℂ) z,
        ((c.sobolevPullback y : Amb).snd : ℂ → ℂ) z⟫_ℝ := by
  let L : Lp ℂ 2 c.dom.μ →ₗᵢ[ℝ] Lp ℂ 2 μD := ⟨c.pullG, c.norm_pullG⟩
  have := L.inner_map_map (x : c.dom.Amb).snd (y : c.dom.Amb).snd
  rw [L2.inner_def, L2.inner_def] at this
  rw [← this]
  rfl

/-- **Weak Steklov eigenfunctions of `Ω` correspond to weak `ρ`-weighted eigenfunctions of the
disk** under the Sobolev pullback. -/
theorem isWeakSteklovEigenDom_iff (τ : ℝ) (x : c.dom.H1) :
    IsWeakSteklovEigenDom c.dom τ x ↔ IsWeakSteklovEigen c.ρ τ (c.sobolevPullback x) := by
  constructor
  · intro h y
    have := h (c.sobolevPullback.symm y)
    rw [c.inner_grad_pull, c.inner_trace_pull, ContinuousLinearEquiv.apply_symm_apply] at this
    exact this
  · intro h y
    rw [c.inner_grad_pull, c.inner_trace_pull]
    exact h _

/-- **The trace `H¹(Ω) → L²(∂Ω, H¹)` is compact.** -/
theorem isCompactOperator_trace : IsCompactOperator c.dom.trace := by
  have hW : IsCompactOperator c.wtrace := by
    have h1 : IsCompactOperator (weightOp c.continuousOn_ρ) := by
      have := SteklovH1.isCompactOperator_trace.clm_comp (mulOp (bdryWeight c.ρ)
        (continuous_bdryWeight c.continuousOn_ρ) _
        (exists_bdryWeight_bound c.continuousOn_ρ).choose_spec)
      exact this
    exact h1.comp_clm _
  exact isCompactOperator_of_norm_le _ _ hW 1 (fun x => by rw [c.norm_trace_eq, one_mul])

/-- **Weak Steklov spectral theorem on `Ω`, posed on `H¹(Ω)`**, with multiplicities; the
eigenvalue sequence is the `ρ`-weighted (smooth-test) disk spectrum. -/
theorem weak_spectral_theorem_dom :
    ∃ (e : ℕ → c.dom.H1) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = 0 ∧ Tendsto σ atTop atTop ∧
      (∀ k, e k ≠ 0 ∧ IsWeakSteklovEigenDom c.dom (σ k) (e k)) ∧
      (∀ τ, (∃ x : c.dom.H1, x ≠ 0 ∧ IsWeakSteklovEigenDom c.dom τ x) ↔ ∃ k, σ k = τ) ∧
      (∀ τ, ∃ S : Submodule ℝ c.dom.H1, (∀ x, x ∈ S ↔ IsWeakSteklovEigenDom c.dom τ x) ∧
        Module.finrank ℝ S = Set.ncard {k | σ k = τ}) ∧
      (∀ k, Steklov.weightedSteklovEigenvalue c.ρ k = ENNReal.ofReal (σ k)) := by
  obtain ⟨e, σ, hmono, h0, htend, heig, hiff, -, hdim, hspec⟩ :=
    weighted_disk_spectral_theorem c.continuousOn_ρ c.ρ_pos
  set P := c.sobolevPullback
  refine ⟨fun k => P.symm (e k), σ, hmono, h0, htend, fun k => ⟨?_, ?_⟩, fun τ => ?_,
    fun τ => ?_, hspec⟩
  · simpa using (heig k).1
  · rw [c.isWeakSteklovEigenDom_iff, ContinuousLinearEquiv.apply_symm_apply]
    exact (heig k).2
  · rw [← hiff τ]
    constructor
    · rintro ⟨x, hx, hxe⟩
      exact ⟨P x, by simpa using hx, (c.isWeakSteklovEigenDom_iff τ x).1 hxe⟩
    · rintro ⟨y, hy, hye⟩
      refine ⟨P.symm y, by simpa using hy, ?_⟩
      rw [c.isWeakSteklovEigenDom_iff, ContinuousLinearEquiv.apply_symm_apply]
      exact hye
  · refine ⟨(weakEigenspace c.continuousOn_ρ τ).map
      (P.symm.toLinearEquiv : H1 →ₗ[ℝ] c.dom.H1), fun x => ?_, ?_⟩
    · rw [Submodule.mem_map_equiv, mem_weakEigenspace c.continuousOn_ρ c.ρ_pos,
        c.isWeakSteklovEigenDom_iff]
      rfl
    · rw [LinearEquiv.finrank_map_eq, hdim]

/-- The smooth-test spectrum of `Ω` equals its `H¹(Ω)` min–max spectrum. -/
theorem steklovSpectrum_eq_h1 : Steklov.steklovSpectrum c.Ω = h1SteklovSpectrum c.Ω := by
  obtain ⟨C, hC⟩ := c.exists_hasTraceIneq
  have hD : IsOpen c.Ω ∧ Bornology.IsBounded c.Ω ∧
      Measure.hausdorffMeasure 1 (frontier c.Ω) ≠ ⊤ := ⟨c.isOpen_Ω, c.bdd, c.bdry_finite⟩
  unfold h1SteklovSpectrum
  rw [dif_pos hD]
  funext k
  exact c.dom.steklovEigenvalue_eq_h1 (C := C) hC k

end C1Conf

end SteklovH1

namespace SteklovC1

open SteklovH1 Steklov PlaneDomain

/-- **Proposition 2.1.1 (general `C¹` version), weak `H¹` formulation.**  Same hypotheses as
`Prop_2_1_1_C1` (conformal `F : 𝔻 → Ω` extending to a `C¹` diffeomorphism `𝔻̄ → Ω̄`, encoded by
`C¹` extensions of `F` and of its inverse to open neighbourhoods of `𝔻̄` and `Ω̄`; nothing
holomorphic across `𝕋`).  Conclusion, with `ρ(z) = ‖dF_z(1)‖ = |F'(z)|`:

* `H¹(Ω)` (closure of smooth graphs) is `W^{1,2}(Ω)` (weak-gradient pairs);
* the trace inequality holds and the trace `H¹(Ω) → L²(∂Ω, H¹)` is compact;
* there is a continuous linear isomorphism `P : H¹(Ω) ≃ H¹(𝔻)` which is composition with `F` on
  smooth functions, preserves the Dirichlet form, and transforms the boundary form of `Ω` into the
  `ρ`-weighted boundary form of the disk; hence weak Steklov eigenfunctions correspond exactly;
* the weak Steklov spectrum of `Ω` posed on `H¹(Ω)` is enumerated with multiplicities by `σ`,
  and `σ` equals the smooth-test spectrum of `Ω`, the `ρ`-weighted disk spectrum, and the `H¹(Ω)`
  min–max spectrum. -/
def Prop_2_1_1_C1_Weak : Prop :=
  ∀ (F : ℂ → ℂ) (Ω : Set ℂ),
    IsDomain Ω → Bornology.IsBounded Ω → SimplyConnectedSpace Ω →
    DifferentiableOn ℂ F (ball 0 1) → F '' ball 0 1 = Ω →
    InjOn F (closedBall 0 1) → F '' closedBall 0 1 = closure Ω →
    (∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ ContDiffOn ℝ 1 F U) →
    (∃ G : ℂ → ℂ, ∃ W : Set ℂ, IsOpen W ∧ closure Ω ⊆ W ∧ ContDiffOn ℝ 1 G W ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, G (F z) = z) →
    (∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) →
    ∃ D : BddDomain, D.carrier = Ω ∧
      (∀ x : D.Amb, x ∈ D.H1 ↔ D.IsWeakGradientPair x) ∧
      (∃ C, D.HasTraceIneq C) ∧ IsCompactOperator D.trace ∧
      (∃ P : D.H1 ≃L[ℝ] H1,
        (∀ u : smoothFns,
          ((P (D.embedH u) : Amb).fst : ℂ → ℝ) =ᵐ[μD] fun z => (u : ℂ → ℝ) (F z)) ∧
        (∀ x y : D.H1, ∫ w in Ω, inner ℝ (((x : D.Amb).snd : ℂ → ℂ) w)
            (((y : D.Amb).snd : ℂ → ℂ) w) =
          ∫ z in ball (0 : ℂ) 1, inner ℝ (((P x : Amb).snd : ℂ → ℂ) z)
            (((P y : Amb).snd : ℂ → ℂ) z)) ∧
        (∀ x y : D.H1, ∫ w, (D.trace x : ℂ → ℝ) w * (D.trace y : ℂ → ℝ) w ∂D.ν =
          ∫ t in Ioc 0 (2 * π), ‖fderiv ℝ F (Complex.exp (t * Complex.I)) 1‖ *
            ((trace (P x) : ℝ → ℝ) t * (trace (P y) : ℝ → ℝ) t)) ∧
        (∀ τ (x : D.H1), IsWeakSteklovEigenDom D τ x ↔
          IsWeakSteklovEigen (fun z => ‖fderiv ℝ F z 1‖) τ (P x))) ∧
      ∃ (e : ℕ → D.H1) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = 0 ∧ Tendsto σ atTop atTop ∧
        (∀ k, e k ≠ 0 ∧ IsWeakSteklovEigenDom D (σ k) (e k)) ∧
        (∀ τ, (∃ x : D.H1, x ≠ 0 ∧ IsWeakSteklovEigenDom D τ x) ↔ ∃ k, σ k = τ) ∧
        (∀ τ, ∃ S : Submodule ℝ D.H1, (∀ x, x ∈ S ↔ IsWeakSteklovEigenDom D τ x) ∧
          Module.finrank ℝ S = Set.ncard {k | σ k = τ}) ∧
        (∀ k, steklovSpectrum Ω k = ENNReal.ofReal (σ k)) ∧
        (∀ k, weightedSteklovSpectrum (fun z => ‖fderiv ℝ F z 1‖) k = ENNReal.ofReal (σ k)) ∧
        (∀ k, h1SteklovSpectrum Ω k = ENNReal.ofReal (σ k))

theorem prop_2_1_1_C1_weak : Prop_2_1_1_C1_Weak := by
  intro F Ω hdom hbdd hsc hF himg hinj hcl hU hG hder
  obtain ⟨U, hUo, hcb, hC⟩ := hU
  obtain ⟨G, W, hWo, hclW, hGC, hGF⟩ := hG
  have hspec := prop_2_1_1_C1 F Ω hdom hbdd hsc hF himg hinj hcl ⟨U, hUo, hcb, hC⟩
    ⟨G, W, hWo, hclW, hGC, hGF⟩ hder
  let c : C1Conf := ⟨F, Ω, hdom.1, hbdd, hF, himg, hinj, hcl, U, hUo, hcb, hC, G, W, hWo, hclW,
    hGC, hGF, hder⟩
  obtain ⟨e, σ, hmono, h0, htend, heig, hiff, hdim, hw⟩ := c.weak_spectral_theorem_dom
  have hh1 := c.steklovSpectrum_eq_h1
  refine ⟨c.dom, rfl, c.mem_H1_iff_isWeakGradientPair, c.exists_hasTraceIneq,
    c.isCompactOperator_trace, ⟨c.sobolevPullback, fun u => ?_, c.inner_grad_pull,
    c.inner_trace_pull, c.isWeakSteklovEigenDom_iff⟩, e, σ, hmono, h0, htend, heig, hiff, hdim,
    fun k => ?_, hw, fun k => ?_⟩
  · rw [c.sobolevPullback_embedH]
    filter_upwards [MemLp.coeFn_toLp (memLp_disk (c.contDiff_pullC1 u).continuous),
      ae_restrict_mem measurableSet_ball] with z h1 hz
    change _ = (u : ℂ → ℝ) (c.F z)
    rw [← c.pullC1_eq u (ball_subset_closedBall hz)]
    exact h1
  · rw [hspec]; exact hw k
  · change h1SteklovSpectrum c.Ω k = _
    rw [← hh1]; change steklovSpectrum Ω k = _
    rw [hspec]; exact hw k

/-- In particular such a domain has the full weak Steklov spectrum posed on
`H¹(Ω) = W^{1,2}(Ω)`, with multiplicities (`SteklovH1.HasSobolevWeakSteklovSpectrum`). -/
theorem hasSobolevWeakSteklovSpectrum_C1 (F : ℂ → ℂ) (Ω : Set ℂ)
    (hdom : IsDomain Ω) (hbdd : Bornology.IsBounded Ω) (hsc : SimplyConnectedSpace Ω)
    (hF : DifferentiableOn ℂ F (ball 0 1)) (himg : F '' ball 0 1 = Ω)
    (hinj : InjOn F (closedBall 0 1)) (hcl : F '' closedBall 0 1 = closure Ω)
    (hU : ∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ ContDiffOn ℝ 1 F U)
    (hG : ∃ G : ℂ → ℂ, ∃ W : Set ℂ, IsOpen W ∧ closure Ω ⊆ W ∧ ContDiffOn ℝ 1 G W ∧
      ∀ z ∈ closedBall (0 : ℂ) 1, G (F z) = z)
    (hder : ∀ z ∈ sphere (0 : ℂ) 1, fderiv ℝ F z 1 ≠ 0) :
    HasSobolevWeakSteklovSpectrum Ω := by
  obtain ⟨D, hD, hW, -, hK, -, e, σ, hmono, h0, htend, heig, hiff, hdim, hsp, -, -⟩ :=
    prop_2_1_1_C1_weak F Ω hdom hbdd hsc hF himg hinj hcl hU hG hder
  exact ⟨D, hD, hW, hK, e, σ, hmono, h0, htend, heig, hiff, hdim, hsp⟩

end SteklovC1
