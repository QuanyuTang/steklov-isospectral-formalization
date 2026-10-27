module

public import Mathlib
public import RequestProject.TraceCompact
public import RequestProject.H1MinMax
public import RequestProject.AbstractSpectral

/-!
# The weak weighted Steklov eigenproblem on the unit disk

For a weight `ρ` continuous and positive on the unit circle we verify, for the genuine Sobolev
space `SteklovH1.H1` of the disk, the hypotheses of the abstract spectral theorem
`SteklovSpectral.spectral_theorem`:

* compactness of the weighted trace (from `SteklovH1.isCompactOperator_trace`);
* coercivity of `‖∇x‖² + ∫ ρ |Tx|²`, from the Poincaré–trace inequality
  `∫_𝔻 u² ≤ 2 ∫_𝕋 u² + 2 ∫_𝔻 |∇u|²` (`SteklovH1.poincare_trace`);
* infinite-dimensionality of the range of the trace (traces of `(Re z)ⁿ` are `cos ⁿ θ`).

Consequently (`SteklovH1.weighted_disk_spectral_theorem`) the weak weighted Steklov problem
`∫_𝔻 ⟨∇u, ∇v⟩ = σ ∫_0^{2π} ρ(e^{it}) Tu Tv dt` for all `v ∈ H¹(𝔻)` has a discrete spectrum
`σ_0 ≤ σ_1 ≤ … → ∞`, counted with multiplicity (eigenspace dimensions equal repetition counts),
and this sequence is the smooth-test min–max sequence `Steklov.weightedSteklovEigenvalue ρ`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal RealInnerProductSpace ContDiff

noncomputable section

namespace SteklovH1

/-! ### Poincaré–trace inequality -/

/-- **Poincaré–trace inequality** on the unit disk, for `C¹` functions:
`∫_𝔻 u² ≤ 2 ∫_0^{2π} u(e^{it})² dt + 2 ∫_𝔻 |∇u|²`. -/
theorem poincare_trace {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) :
    ∫ z in Metric.ball (0:ℂ) 1, u z ^ 2 ≤
      2 * (∫ t in (0:ℝ)..(2 * π), u (Complex.exp (t * Complex.I)) ^ 2) +
        2 * ∫ z in Metric.ball (0:ℂ) 1, ‖fderiv ℝ u z‖ ^ 2 := by
  have hcu : Continuous u := hu.continuous
  have hcD : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  set H : ℂ → ℝ := fun z => ‖fderiv ℝ u z‖ ^ 2 with hH
  have hHc : Continuous H := hcD.norm.pow 2
  rw [← integral_rays_eq_disk (H := fun z => u z ^ 2) (by fun_prop),
    ← integral_rays_eq_disk hHc]
  set G : ℝ → ℝ := fun θ => ∫ r in (0:ℝ)..1, r * H (r * Complex.exp (θ * Complex.I)) with hG
  have hGc : Continuous G :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (θ r : ℝ) => r * H (r * Complex.exp (θ * Complex.I))) (by fun_prop) 0 1
  have hbc : Continuous fun θ : ℝ => u (Complex.exp (θ * Complex.I)) ^ 2 := by fun_prop
  have hR : ∫ θ in (0:ℝ)..(2 * π), (2 * u (Complex.exp (θ * Complex.I)) ^ 2 + 2 * G θ) =
      2 * (∫ t in (0:ℝ)..(2 * π), u (Complex.exp (t * Complex.I)) ^ 2) +
        2 * ∫ θ in (0:ℝ)..(2 * π), G θ := by
    have hI1 : IntervalIntegrable (fun θ : ℝ => 2 * u (Complex.exp (θ * Complex.I)) ^ 2) volume
        0 (2 * π) := (continuous_const.mul hbc).intervalIntegrable _ _
    have hI2 : IntervalIntegrable (fun θ : ℝ => 2 * G θ) volume 0 (2 * π) :=
      (continuous_const.mul hGc).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hI1 hI2, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
  change _ ≤ 2 * (∫ t in (0:ℝ)..(2 * π), u (Complex.exp (t * Complex.I)) ^ 2) +
    2 * ∫ θ in (0:ℝ)..(2 * π), G θ
  rw [← hR]
  refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ (fun θ _ => ?_)
  · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (θ r : ℝ) => r * u (r * Complex.exp (θ * Complex.I)) ^ 2) (by fun_prop)
      0 1).intervalIntegrable _ _
  · exact ((continuous_const.mul hbc).add (continuous_const.mul hGc)).intervalIntegrable _ _
  -- the ray estimate
  set e : ℂ := Complex.exp (θ * Complex.I)
  have hray : ∀ r ∈ Icc (0:ℝ) 1, r * u (r * e) ^ 2 ≤ 2 * u e ^ 2 + 2 * G θ := by
    intro r hr
    have hrad := radial_sq_le hu θ hr.2
    set I := ∫ σ in r..1, ‖fderiv ℝ u (σ * Complex.exp (θ * Complex.I))‖ ^ 2
    have hcI : Continuous fun σ : ℝ => ‖fderiv ℝ u (σ * Complex.exp (θ * Complex.I))‖ ^ 2 := by
      fun_prop
    have h1 : r * (1 - r) * I ≤ ∫ σ in r..1, σ * H (σ * e) := by
      rw [← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_mono_on hr.2 ((continuous_const.mul hcI).intervalIntegrable _ _)
        ((continuous_id.mul (hHc.comp (by fun_prop))).intervalIntegrable _ _) (fun σ hσ => ?_)
      have h0 : 0 ≤ ‖fderiv ℝ u (σ * Complex.exp (θ * Complex.I))‖ ^ 2 := by positivity
      have : r * (1 - r) ≤ σ := by nlinarith [hr.1, hr.2, hσ.1]
      exact mul_le_mul_of_nonneg_right this h0
    have h2 : ∫ σ in r..1, σ * H (σ * e) ≤ G θ := by
      refine intervalIntegral.integral_mono_interval hr.1 hr.2 le_rfl ?_
        ((continuous_id.mul (hHc.comp (by fun_prop))).intervalIntegrable _ _)
      rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact Eventually.of_forall (fun σ hσ => by
        simp only [Pi.zero_apply]
        exact mul_nonneg hσ.1.le (by positivity))
    have h3 : r * (u e - u (r * e)) ^ 2 ≤ G θ := by
      have := mul_le_mul_of_nonneg_left hrad hr.1
      calc r * (u e - u (r * e)) ^ 2 ≤ r * ((1 - r) * I) := this
        _ = r * (1 - r) * I := by ring
        _ ≤ G θ := h1.trans h2
    have h4 : u (r * e) ^ 2 ≤ 2 * u e ^ 2 + 2 * (u e - u (r * e)) ^ 2 := by
      nlinarith [sq_nonneg (2 * u e - u (r * e))]
    have h5 : r * u e ^ 2 ≤ u e ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hr.2) (sq_nonneg (u e))]
    have h6 : r * u (r * e) ^ 2 ≤ 2 * (r * u e ^ 2) + 2 * (r * (u e - u (r * e)) ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left h4 hr.1]
    linarith
  calc ∫ r in (0:ℝ)..1, r * u (r * e) ^ 2
      ≤ ∫ r in (0:ℝ)..1, (2 * u e ^ 2 + 2 * G θ) := by
        refine intervalIntegral.integral_mono_on zero_le_one ?_
          (continuous_const.intervalIntegrable _ _) hray
        exact (continuous_id.mul ((hcu.comp (by fun_prop)).pow 2)).intervalIntegrable _ _
    _ = 2 * u e ^ 2 + 2 * G θ := by simp

/-! ### `L²` norms as integrals -/

lemma norm_toLp_sq_eq {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}
    {f : α → F} (hf : MemLp f 2 μ) : ‖hf.toLp f‖ ^ 2 = ∫ a, ‖f a‖ ^ 2 ∂μ := by
  have hint : Integrable (fun a => ‖f a‖ ^ 2) μ := by
    simpa using hf.integrable_norm_pow (p := 2) two_ne_zero
  have h1 : ENNReal.ofReal (‖hf.toLp f‖ ^ 2) = ENNReal.ofReal (∫ a, ‖f a‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (fun _ => by positivity)),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm, enorm_toLp_sq]
    congr 1; ext a
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  exact (ENNReal.ofReal_eq_ofReal_iff (by positivity)
    (integral_nonneg (fun _ => by positivity))).1 h1

lemma norm_Lp_sq_eq {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}
    (f : Lp F 2 μ) : ‖f‖ ^ 2 = ∫ a, ‖(f : α → F) a‖ ^ 2 ∂μ := by
  conv_lhs => rw [← Lp.toLp_coeFn f (Lp.memLp f)]
  exact norm_toLp_sq_eq _

lemma norm_toL2_sq (u : smoothFns) :
    ‖toL2 u‖ ^ 2 = ∫ z in Metric.ball (0:ℂ) 1, (u : ℂ → ℝ) z ^ 2 := by
  rw [show toL2 u = (memLp_disk (continuous_of_mem u.2)).toLp u from rfl, norm_toLp_sq_eq]
  simp [Real.norm_eq_abs, sq_abs]

lemma norm_gradL2_sq (u : smoothFns) :
    ‖gradL2 u‖ ^ 2 = ∫ z in Metric.ball (0:ℂ) 1, ‖fderiv ℝ (u : ℂ → ℝ) z‖ ^ 2 := by
  rw [show gradL2 u = (memLp_disk (continuous_grad (contDiff_one_of_mem u.2))).toLp
    (grad u) from rfl, norm_toLp_sq_eq]
  simp [norm_grad]

lemma norm_traceSmooth_sq (u : smoothFns) :
    ‖traceSmooth u‖ ^ 2 = ∫ t in (0:ℝ)..(2 * π), (u : ℂ → ℝ) (Complex.exp (t * Complex.I)) ^ 2 := by
  rw [show traceSmooth u = (memLp_bdry u).toLp _ from rfl, norm_toLp_sq_eq,
    intervalIntegral.integral_of_le (by positivity)]
  simp [Real.norm_eq_abs, sq_abs]

/-! ### Coercivity on `H¹(𝔻)` -/

/-- The gradient component `H¹(𝔻) → L²(𝔻; ℝ²)`. -/
def gradOpD : H1 →L[ℝ] Lp ℂ 2 μD :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap.comp H1.subtypeL)

lemma gradOpD_apply (x : H1) : gradOpD x = (x : Amb).snd := rfl

/-- **Coercivity**: `‖x‖² ≤ 2 ‖T x‖² + 3 ‖∇x‖²` on `H¹(𝔻)`. -/
theorem norm_sq_le_trace_grad (x : H1) :
    ‖x‖ ^ 2 ≤ 2 * ‖trace x‖ ^ 2 + 3 * ‖gradOpD x‖ ^ 2 := by
  refine denseRange_embedH.induction_on x ?_ (fun u => ?_)
  · exact isClosed_le (continuous_norm.pow 2)
      ((continuous_const.mul ((continuous_norm.comp trace.continuous).pow 2)).add
        (continuous_const.mul ((continuous_norm.comp gradOpD.continuous).pow 2)))
  · have hn : ‖embedH u‖ ^ 2 = ‖toL2 u‖ ^ 2 + ‖gradL2 u‖ ^ 2 :=
      WithLp.prod_norm_sq_eq_of_L2 (embed u)
    have hg : gradOpD (embedH u) = gradL2 u := rfl
    rw [hn, hg, trace_embed, norm_toL2_sq, norm_gradL2_sq, norm_traceSmooth_sq]
    have := poincare_trace (contDiff_one_of_mem u.2)
    have h0 : 0 ≤ ∫ z in Metric.ball (0:ℂ) 1, ‖fderiv ℝ (u : ℂ → ℝ) z‖ ^ 2 :=
      integral_nonneg (fun _ => by positivity)
    linarith

/-! ### Infinite-dimensionality of the trace space -/

/-- A polynomial in `cos t` vanishing for a.e. `t ∈ (0, 2π]` is zero. -/
lemma poly_eq_zero_of_ae_cos {p : Polynomial ℝ}
    (h : ∀ᵐ t ∂μT, p.eval (Real.cos t) = 0) : p = 0 := by
  by_contra hp
  set Z : Set ℝ := {t ∈ Ioo 0 π | p.eval (Real.cos t) = 0}
  have hZ : Z.Finite := by
    refine Set.Finite.of_finite_image (f := Real.cos) ?_ ?_
    · refine (p.roots.toFinset.finite_toSet).subset ?_
      rintro _ ⟨t, ⟨_, ht⟩, rfl⟩
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_roots hp).2 ht
    · exact Real.injOn_cos.mono (fun t ht => Ioo_subset_Icc_self ht.1)
  have h0 : μT {t | p.eval (Real.cos t) ≠ 0} = 0 := by
    rw [← ae_iff]; simpa using h
  have hsub : Ioo 0 π \ Z ⊆ {t | p.eval (Real.cos t) ≠ 0} ∩ Ioc 0 (2 * π) := by
    intro t ⟨ht, htZ⟩
    refine ⟨fun h0 => htZ ⟨ht, h0⟩, ht.1, ?_⟩
    have := ht.2; have := Real.pi_pos; linarith
  have h1 : volume (Ioo 0 π \ Z) ≤ 0 := by
    calc volume (Ioo 0 π \ Z) ≤ volume ({t | p.eval (Real.cos t) ≠ 0} ∩ Ioc 0 (2 * π)) :=
          measure_mono hsub
      _ = μT {t | p.eval (Real.cos t) ≠ 0} := (Measure.restrict_apply' measurableSet_Ioc).symm
      _ = 0 := h0
  rw [measure_diff_null (hZ.measure_zero volume), Real.volume_Ioo, sub_zero] at h1
  exact absurd (le_antisymm h1 (zero_le)) (ENNReal.ofReal_pos.2 Real.pi_pos).ne'

/-- The smooth functions `(Re z)ⁿ`. -/
def rePow (n : ℕ) : smoothFns :=
  ⟨fun z : ℂ => z.re ^ n, (Complex.reCLM.contDiff.pow n : ContDiff ℝ ∞ fun z : ℂ => z.re ^ n)⟩

/-- If the trace of `∑ gₙ (Re z)ⁿ` vanishes, all `gₙ` vanish. -/
lemma coeff_eq_zero_of_trace {s : Finset ℕ} {g : ℕ → ℝ}
    (h : trace (embedH (∑ n ∈ s, g n • rePow n)) = 0) : ∀ n ∈ s, g n = 0 := by
  set p : Polynomial ℝ := ∑ n ∈ s, Polynomial.C (g n) * Polynomial.X ^ n
  have hae := trace_embed_ae (∑ n ∈ s, g n • rePow n)
  rw [h] at hae
  have hp0 : p = 0 := by
    refine poly_eq_zero_of_ae_cos ?_
    filter_upwards [hae, Lp.coeFn_zero ℝ 2 μT] with t h1 h2
    rw [h2] at h1
    have : ((∑ n ∈ s, g n • rePow n : smoothFns) : ℂ → ℝ) (Complex.exp (t * Complex.I)) =
        p.eval (Real.cos t) := by
      simp [p, rePow, Polynomial.eval_finset_sum, Complex.exp_ofReal_mul_I_re]
    rw [← this]; exact h1.symm
  intro n hn
  have := congrArg (fun q : Polynomial ℝ => q.coeff n) hp0
  simp only [p, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,
    Polynomial.coeff_zero] at this
  rwa [Finset.sum_ite_eq s n, if_pos hn] at this

/-! ### The weighted trace and the abstract hypotheses -/

section Weighted

variable {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ (Metric.sphere 0 1))

/-- The weighted trace `x ↦ √ρ(e^{it}) · Tx(t)`, so that `‖weightOp x‖² = ∫ ρ |Tx|²`. -/
def weightOp : H1 →L[ℝ] Lp ℝ 2 μT :=
  (mulOp (bdryWeight ρ) (continuous_bdryWeight hρ) (exists_bdryWeight_bound hρ).choose
    (exists_bdryWeight_bound hρ).choose_spec).comp trace

lemma weightOp_ae (x : H1) :
    (weightOp hρ x : ℝ → ℝ) =ᵐ[μT] fun t => bdryWeight ρ t * (trace x : ℝ → ℝ) t :=
  mulOp_ae (bdryWeight ρ) (continuous_bdryWeight hρ) _ (exists_bdryWeight_bound hρ).choose_spec
    (trace x)

lemma h1BoundaryMass_eq_weightOp (x : H1) : h1BoundaryMass ρ x = ‖weightOp hρ x‖ₑ ^ 2 :=
  h1BoundaryMass_eq_enorm hρ (exists_bdryWeight_bound hρ).choose_spec x

lemma h1SteklovEigenvalue_eq_closureMinMax (k : ℕ) :
    h1SteklovEigenvalue ρ k = closureMinMax gradOpD (weightOp hρ) k := by
  have hE : ∀ x, h1Energy x = ‖gradOpD x‖ₑ ^ 2 := fun x => rfl
  simp only [h1SteklovEigenvalue, H1Admissible, closureMinMax, hE, h1BoundaryMass_eq_weightOp hρ]

variable (hpos : ∀ z ∈ Metric.sphere (0:ℂ) 1, 0 < ρ z)
include hρ hpos

lemma exists_weight_lower : ∃ m > 0, ∀ t : ℝ, m ≤ ρ (Complex.exp (t * Complex.I)) := by
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere (0:ℂ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hρ
  refine ⟨ρ z₀, hpos z₀ hz₀, fun t => ?_⟩
  exact hmin (show Complex.exp (t * Complex.I) ∈ Metric.sphere (0:ℂ) 1 by
    simp [Complex.norm_exp_ofReal_mul_I])

lemma norm_weightOp_sq_ge : ∃ m > 0, ∀ x : H1, m * ‖trace x‖ ^ 2 ≤ ‖weightOp hρ x‖ ^ 2 := by
  obtain ⟨m, hm, hmle⟩ := exists_weight_lower hρ hpos
  refine ⟨m, hm, fun x => ?_⟩
  rw [norm_Lp_sq_eq (trace x), norm_Lp_sq_eq (weightOp hρ x), ← integral_const_mul]
  have hi1 : Integrable (fun t => ‖(trace x : ℝ → ℝ) t‖ ^ 2) μT := by
    simpa using (Lp.memLp (trace x)).integrable_norm_pow (p := 2) two_ne_zero
  have hi2 : Integrable (fun t => ‖(weightOp hρ x : ℝ → ℝ) t‖ ^ 2) μT := by
    simpa using (Lp.memLp (weightOp hρ x)).integrable_norm_pow (p := 2) two_ne_zero
  refine integral_mono_ae (hi1.const_mul m) hi2 ?_
  filter_upwards [weightOp_ae hρ x] with t ht
  rw [ht, norm_mul, mul_pow, Real.norm_eq_abs (bdryWeight ρ t), sq_abs, bdryWeight,
    Real.sq_sqrt (le_trans hm.le (hmle t))]
  exact mul_le_mul_of_nonneg_right (hmle t) (by positivity)

lemma trace_eq_zero_of_weightOp {x : H1} (h : weightOp hρ x = 0) : trace x = 0 := by
  obtain ⟨m, hm, hle⟩ := norm_weightOp_sq_ge hρ hpos
  have := hle x
  rw [h, norm_zero] at this
  have : ‖trace x‖ ^ 2 ≤ 0 := by nlinarith
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg (trace x)])

lemma linearIndependent_weightOp_rePow :
    LinearIndependent ℝ (fun n : ℕ => weightOp hρ (embedH (rePow n))) := by
  rw [linearIndependent_iff']
  intro s g hg
  refine coeff_eq_zero_of_trace (trace_eq_zero_of_weightOp hρ hpos ?_)
  simpa [map_sum, map_smul] using hg

/-- The hypotheses of the abstract spectral theorem hold for the weighted disk problem. -/
theorem hyp_weighted : SteklovSpectral.Hyp gradOpD (weightOp hρ) where
  compact := by
    have := isCompactOperator_trace.clm_comp (mulOp (bdryWeight ρ) (continuous_bdryWeight hρ) _
      (exists_bdryWeight_bound hρ).choose_spec)
    exact this
  coercive := by
    obtain ⟨m, hm, hle⟩ := norm_weightOp_sq_ge hρ hpos
    refine ⟨1 / (3 + 2 / m), by positivity, fun x => ?_⟩
    rw [SteklovSpectral.aB_self, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
    have h1 := norm_sq_le_trace_grad x
    have h2 := hle x
    have h3 : 2 * ‖trace x‖ ^ 2 ≤ 2 / m * ‖weightOp hρ x‖ ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hm]; linarith
    have h4 : 0 ≤ ‖gradOpD x‖ ^ 2 := by positivity
    have h5 : 0 ≤ ‖weightOp hρ x‖ ^ 2 := by positivity
    have h6 : 0 ≤ 2 / m := by positivity
    nlinarith
  infinite := by
    intro hfin
    set R := LinearMap.range (weightOp hρ : H1 →ₗ[ℝ] Lp ℝ 2 μT)
    set d := Module.finrank ℝ R
    let b : Fin (d + 1) → R := fun i =>
      ⟨weightOp hρ (embedH (rePow i)), LinearMap.mem_range_self _ _⟩
    have hli : LinearIndependent ℝ b := by
      refine LinearIndependent.of_comp R.subtype ?_
      exact (linearIndependent_weightOp_rePow hρ hpos).comp (fun i : Fin (d + 1) => (i : ℕ))
        Fin.val_injective
    have := hli.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega

end Weighted

/-! ### The weak weighted Steklov eigenproblem -/

/-- **Weak weighted Steklov eigenfunction** on the disk: `x ∈ H¹(𝔻)` satisfies
`∫_𝔻 ⟨∇x, ∇y⟩ = τ ∫_0^{2π} ρ(e^{it}) Tx(t) Ty(t) dt` for every `y ∈ H¹(𝔻)`
(the weak form of `Δu = 0` in `𝔻`, `∂_ν u = τ ρ u` on `∂𝔻`). -/
def IsWeakSteklovEigen (ρ : ℂ → ℝ) (τ : ℝ) (x : H1) : Prop :=
  ∀ y : H1, ∫ z in Metric.ball (0:ℂ) 1, ⟪((x : Amb).snd : ℂ → ℂ) z, ((y : Amb).snd : ℂ → ℂ) z⟫ =
    τ * ∫ t in Ioc 0 (2 * π),
      ρ (Complex.exp (t * Complex.I)) * ((trace x : ℝ → ℝ) t * (trace y : ℝ → ℝ) t)

section Weighted2

variable {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ (Metric.sphere 0 1))
  (hpos : ∀ z ∈ Metric.sphere (0:ℂ) 1, 0 < ρ z)

/-- The space of weak weighted Steklov eigenfunctions with eigenvalue `τ` (including `0`). -/
def weakEigenspace (τ : ℝ) : Submodule ℝ H1 :=
  SteklovSpectral.eigenspace gradOpD (weightOp hρ) τ

include hpos in
lemma inner_weightOp (x y : H1) :
    ⟪weightOp hρ x, weightOp hρ y⟫ = ∫ t in Ioc 0 (2 * π),
      ρ (Complex.exp (t * Complex.I)) * ((trace x : ℝ → ℝ) t * (trace y : ℝ → ℝ) t) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [weightOp_ae hρ x, weightOp_ae hρ y] with t hx hy
  rw [hx, hy, real_inner_eq_re_inner, RCLike.inner_apply, RCLike.conj_to_real, RCLike.re_to_real]
  have h0 : 0 ≤ ρ (Complex.exp (t * Complex.I)) := (hpos _ (by
    simp [Complex.norm_exp_ofReal_mul_I])).le
  have hw : bdryWeight ρ t * bdryWeight ρ t = ρ (Complex.exp (t * Complex.I)) :=
    Real.mul_self_sqrt h0
  calc bdryWeight ρ t * (trace y : ℝ → ℝ) t * (bdryWeight ρ t * (trace x : ℝ → ℝ) t)
      = (bdryWeight ρ t * bdryWeight ρ t) * ((trace x : ℝ → ℝ) t * (trace y : ℝ → ℝ) t) := by ring
    _ = _ := by rw [hw]

include hpos in
lemma mem_weakEigenspace {τ : ℝ} {x : H1} :
    x ∈ weakEigenspace hρ τ ↔ IsWeakSteklovEigen ρ τ x := by
  unfold weakEigenspace IsWeakSteklovEigen
  rw [SteklovSpectral.mem_eigenspace]
  refine forall_congr' (fun y => ?_)
  rw [inner_weightOp hρ hpos, L2.inner_def]
  rfl

lemma gradOpD_const : gradOpD (embedH (rePow 0)) = 0 := by
  have h := norm_gradL2_sq (rePow 0)
  have hf : fderiv ℝ ((rePow 0 : smoothFns) : ℂ → ℝ) = 0 := by
    have : ((rePow 0 : smoothFns) : ℂ → ℝ) = fun _ => (1:ℝ) := by
      funext z; simp [rePow]
    rw [this]; funext z; exact fderiv_const_apply _
  rw [hf] at h
  simp only [Pi.zero_apply, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, integral_zero] at h
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h)

lemma embedH_const_ne_zero : embedH (rePow 0) ≠ 0 := by
  intro h
  have := coeff_eq_zero_of_trace (s := {0}) (g := fun _ => 1) (by simp [h])
  simpa using this 0 (Finset.mem_singleton_self 0)

include hpos in
/-- **The weighted Steklov spectrum of the disk** (weak `H¹` formulation, with multiplicities).
For a weight `ρ` continuous and positive on the unit circle there are weak eigenfunctions `e k`
and eigenvalues `σ k`, nondecreasing with `σ 0 = 0` and `σ k → ∞`, such that

* every weak eigenvalue is some `σ k`, and every weak eigenfunction for `τ` lies in the span of
  the `e k` with `σ k = τ`;
* the space of weak eigenfunctions for `τ` has dimension `#{k | σ k = τ}`;
* `σ k` equals the smooth-test min–max eigenvalue `Steklov.weightedSteklovEigenvalue ρ k`.

So the variationally defined weighted spectrum used in the main theorem is exactly the weak
`H¹` Steklov spectrum, counted with multiplicity. -/
theorem weighted_disk_spectral_theorem :
    ∃ (e : ℕ → H1) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = 0 ∧ Tendsto σ atTop atTop ∧
      (∀ k, e k ≠ 0 ∧ IsWeakSteklovEigen ρ (σ k) (e k)) ∧
      (∀ τ, (∃ x : H1, x ≠ 0 ∧ IsWeakSteklovEigen ρ τ x) ↔ ∃ k, σ k = τ) ∧
      (∀ τ, weakEigenspace hρ τ = Submodule.span ℝ (e '' {k | σ k = τ})) ∧
      (∀ τ, Module.finrank ℝ (weakEigenspace hρ τ) = Set.ncard {k | σ k = τ}) ∧
      (∀ k, Steklov.weightedSteklovEigenvalue ρ k = ENNReal.ofReal (σ k)) := by
  have H := hyp_weighted hρ hpos
  obtain ⟨e, σ, hmono, hnn, htend, heig, hspan, hdim, hbot, hmm⟩ :=
    SteklovSpectral.spectral_theorem H
  have hmem : ∀ τ x, x ∈ weakEigenspace hρ τ ↔ IsWeakSteklovEigen ρ τ x :=
    fun τ x => mem_weakEigenspace hρ hpos
  have h0 : ∃ k, σ k = 0 := by
    refine (hbot 0).1 (fun hb => embedH_const_ne_zero ?_)
    have hm : embedH (rePow 0) ∈ SteklovSpectral.eigenspace gradOpD (weightOp hρ) 0 := by
      intro y; rw [gradOpD_const]; simp
    rw [hb, Submodule.mem_bot] at hm
    exact hm
  obtain ⟨k₀, hk₀⟩ := h0
  refine ⟨e, σ, hmono, le_antisymm (hk₀ ▸ hmono (Nat.zero_le k₀)) (hnn 0), htend,
    fun k => ⟨(heig k).1, (hmem _ _).1 (heig k).2⟩, fun τ => ?_, hspan, hdim, fun k => ?_⟩
  · rw [← hbot τ, Ne, Submodule.eq_bot_iff]
    push_neg
    exact ⟨fun ⟨x, hx0, hx⟩ => ⟨x, (hmem τ x).2 hx, hx0⟩,
      fun ⟨x, hx, hx0⟩ => ⟨x, hx0, (hmem τ x).1 hx⟩⟩
  · rw [weightedSteklovEigenvalue_eq_h1 hρ, h1SteklovEigenvalue_eq_closureMinMax hρ, hmm]

end Weighted2

end SteklovH1
