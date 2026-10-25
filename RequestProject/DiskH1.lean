module

public import Mathlib
public import RequestProject.DiskTrace
public import RequestProject.Defs

/-!
# The Sobolev space `H¹(𝔻)` and its boundary trace

We construct `H¹` of the unit disk `𝔻 = ball 0 1 ⊆ ℂ ≅ ℝ²` concretely inside the Hilbert space
`E = L²(𝔻) ⊕₂ L²(𝔻; ℂ)` of pairs (function, gradient):

* `SteklovH1.embed u = (u|_𝔻, ∇u|_𝔻)` for globally smooth `u : ℂ → ℝ`, where the gradient is
  the Riesz representative `∇u(z) ∈ ℂ ≅ ℝ²` of `Du(z)`, so `|∇u(z)| = ‖Du(z)‖`;
* `SteklovH1.H1 = closure (range embed)`, a closed subspace, hence a real Hilbert space.

The relation with genuine `L²` functions and weak gradients is proved:
`SteklovH1.weak_gradient` shows that for every `(f, g) ∈ H1`, `g` is the weak gradient of `f`
on `𝔻` (`∫ f ∂_v φ = -∫ ⟪g, v⟫ φ` for compactly supported smooth `φ` in `𝔻`), and
`SteklovH1.snd_eq_zero_of_fst_eq_zero` shows that the gradient component is determined by the
function component, so `H1` is (isometric to) a subspace of `L²(𝔻)` with `L²` weak gradients.

The **trace** `SteklovH1.trace : H1 →L[ℝ] L²((0,2π])` is the continuous extension of
`u ↦ (t ↦ u(e^{it}))`, which is bounded by the trace inequality `SteklovH1.trace_ineq`;
`SteklovH1.trace_embed` proves that on smooth functions it is the actual boundary restriction.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace SteklovH1

/-- Lebesgue measure on the unit disk. -/
abbrev μD : Measure ℂ := volume.restrict (Metric.ball (0:ℂ) 1)

/-- Lebesgue measure on the parameter interval `(0, 2π]` of the unit circle. -/
abbrev μT : Measure ℝ := volume.restrict (Ioc 0 (2 * π))

/-- The ambient Hilbert space `L²(𝔻) ⊕₂ L²(𝔻; ℝ²)` (gradients valued in `ℂ ≅ ℝ²`). -/
abbrev Amb := WithLp 2 (Lp ℝ 2 μD × Lp ℂ 2 μD)

/-- The gradient of a real function on the plane, as a vector of `ℂ ≅ ℝ²`
(Riesz representative of the derivative). -/
def grad (u : ℂ → ℝ) (z : ℂ) : ℂ := (InnerProductSpace.toDual ℝ ℂ).symm (fderiv ℝ u z)

lemma norm_grad (u : ℂ → ℝ) (z : ℂ) : ‖grad u z‖ = ‖fderiv ℝ u z‖ := by
  simp [grad]

lemma inner_grad (u : ℂ → ℝ) (z v : ℂ) : inner ℝ (grad u z) v = fderiv ℝ u z v := by
  simp [grad, InnerProductSpace.toDual_symm_apply]

/-- The globally smooth real functions on the plane. -/
def smoothFns : Submodule ℝ (ℂ → ℝ) where
  carrier := {u | ContDiff ℝ ∞ u}
  add_mem' := fun {a b} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) => ha.add hb
  zero_mem' := (contDiff_const : ContDiff ℝ ∞ (fun _ : ℂ => (0:ℝ)))
  smul_mem' := fun c u (hu : ContDiff ℝ ∞ u) => hu.const_smul c

lemma mem_smoothFns {u : ℂ → ℝ} : u ∈ smoothFns ↔ ContDiff ℝ ∞ u := Iff.rfl

lemma continuous_of_mem {u : ℂ → ℝ} (hu : u ∈ smoothFns) : Continuous u :=
  (mem_smoothFns.1 hu).continuous

lemma contDiff_one_of_mem {u : ℂ → ℝ} (hu : u ∈ smoothFns) : ContDiff ℝ 1 u :=
  (mem_smoothFns.1 hu).of_le (by exact_mod_cast le_top)

lemma continuous_grad {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) : Continuous (grad u) := by
  have h1 : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  exact (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp h1

instance : IsFiniteMeasure μD := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact measure_ball_lt_top

instance : IsFiniteMeasure μT := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc]
  exact ENNReal.ofReal_lt_top

/-- A continuous function is in `L²(𝔻)`. -/
lemma memLp_disk {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} (hf : Continuous f) :
    MemLp f 2 μD := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' Metric.isOpen_ball.measurableSet]
  exact Eventually.of_forall (fun z hz => hC z (Metric.ball_subset_closedBall hz))

/-- A continuous function of `t` is in `L²((0,2π])`. -/
lemma memLp_circle {f : ℝ → ℝ} (hf : Continuous f) : MemLp f 2 μT := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall (fun t ht => hC t (Ioc_subset_Icc_self ht))

/-- `u ↦ u|_𝔻 ∈ L²(𝔻)` on smooth functions. -/
def toL2 : smoothFns →ₗ[ℝ] Lp ℝ 2 μD where
  toFun u := (memLp_disk (continuous_of_mem u.2)).toLp u
  map_add' u v := by
    simp only [Submodule.coe_add]
    exact MemLp.toLp_add _ _
  map_smul' c u := by
    simp only [Submodule.coe_smul, RingHom.id_apply]
    exact MemLp.toLp_const_smul _ _

lemma grad_add {u v : ℂ → ℝ} (hu : ContDiff ℝ 1 u) (hv : ContDiff ℝ 1 v) :
    grad (u + v) = grad u + grad v := by
  ext1 z
  simp only [grad, Pi.add_apply]
  rw [fderiv_add (hu.differentiable one_ne_zero z) (hv.differentiable one_ne_zero z), map_add]

lemma grad_smul {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) (c : ℝ) :
    grad (c • u) = c • grad u := by
  ext1 z
  simp only [grad, Pi.smul_apply]
  rw [fderiv_const_smul (hu.differentiable one_ne_zero z), map_smul]

/-- `u ↦ ∇u|_𝔻 ∈ L²(𝔻; ℝ²)` on smooth functions. -/
def gradL2 : smoothFns →ₗ[ℝ] Lp ℂ 2 μD where
  toFun u := (memLp_disk (continuous_grad (contDiff_one_of_mem u.2))).toLp (grad u)
  map_add' u v := by
    simp only [Submodule.coe_add]
    rw [← MemLp.toLp_add]
    congr 1
    exact grad_add (contDiff_one_of_mem u.2) (contDiff_one_of_mem v.2)
  map_smul' c u := by
    simp only [Submodule.coe_smul, RingHom.id_apply]
    rw [← MemLp.toLp_const_smul]
    congr 1
    exact grad_smul (contDiff_one_of_mem u.2) c

/-- The embedding `u ↦ (u, ∇u)` of smooth functions into `L²(𝔻) ⊕₂ L²(𝔻; ℝ²)`. -/
def embed : smoothFns →ₗ[ℝ] Amb :=
  (WithLp.linearEquiv 2 ℝ (Lp ℝ 2 μD × Lp ℂ 2 μD)).symm.toLinearMap ∘ₗ (toL2.prod gradL2)

@[simp] lemma embed_fst (u : smoothFns) : (embed u).fst = toL2 u := rfl
@[simp] lemma embed_snd (u : smoothFns) : (embed u).snd = gradL2 u := rfl

/-- **The Sobolev space `H¹(𝔻)`**: the closure of `{(u, ∇u)}` (u globally smooth) in
`L²(𝔻) ⊕₂ L²(𝔻; ℝ²)`. -/
def H1 : Submodule ℝ Amb := (LinearMap.range embed).topologicalClosure

instance : CompleteSpace H1 :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Smooth functions as elements of `H¹(𝔻)`. -/
def embedH : smoothFns →ₗ[ℝ] H1 :=
  LinearMap.codRestrict H1 embed
    (fun u => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self embed u))

@[simp] lemma coe_embedH (u : smoothFns) : (embedH u : Amb) = embed u := rfl

lemma denseRange_embedH : DenseRange embedH := by
  rw [DenseRange, Subtype.dense_iff]
  intro x hx
  have : Set.range embedH = ((↑) : H1 → Amb) ⁻¹' (LinearMap.range embed) := by
    ext y; constructor
    · rintro ⟨u, rfl⟩; exact ⟨u, rfl⟩
    · rintro ⟨u, hu⟩; exact ⟨u, Subtype.ext hu⟩
  rw [this]
  have hx' : x ∈ closure (LinearMap.range embed : Set Amb) := hx
  refine closure_mono ?_ hx'
  intro y hy
  exact ⟨⟨y, Submodule.le_topologicalClosure _ hy⟩, hy, rfl⟩

/-! ### Norms -/

lemma enorm_toLp_sq {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {μ : Measure α}
    {f : α → F} (hf : MemLp f 2 μ) : ‖hf.toLp f‖ₑ ^ 2 = ∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ := by
  rw [Lp.enorm_toLp, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    hf.aestronglyMeasurable]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp

lemma enorm_sq_real (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

lemma enorm_amb_sq (x : Amb) : ‖x‖ₑ ^ 2 = ‖x.fst‖ₑ ^ 2 + ‖x.snd‖ₑ ^ 2 := by
  simp only [← ofReal_norm_eq_enorm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
    WithLp.prod_norm_sq_eq_of_L2]

lemma enorm_toL2_sq (u : smoothFns) :
    ‖toL2 u‖ₑ ^ 2 = ∫⁻ z in Metric.ball (0:ℂ) 1, ‖(u : ℂ → ℝ) z‖ₑ ^ 2 :=
  enorm_toLp_sq (memLp_disk (continuous_of_mem u.2))

lemma enorm_gradL2_sq (u : smoothFns) :
    ‖gradL2 u‖ₑ ^ 2 = ∫⁻ z in Metric.ball (0:ℂ) 1, ‖fderiv ℝ (u : ℂ → ℝ) z‖ₑ ^ 2 := by
  rw [show gradL2 u = (memLp_disk (continuous_grad (contDiff_one_of_mem u.2))).toLp
    (grad u) from rfl, enorm_toLp_sq]
  congr 1; ext z
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_grad]

/-- The `H¹`-embedding computes the Dirichlet energy on the disk. -/
lemma enorm_embed_snd_sq (u : smoothFns) :
    ‖(embed u).snd‖ₑ ^ 2 = Steklov.dirichletEnergy (Metric.ball 0 1) u :=
  enorm_gradL2_sq u

/-! ### The trace -/

/-- `u ↦ (t ↦ u(e^{it})) ∈ L²((0,2π])` on smooth functions. -/
lemma memLp_bdry (u : smoothFns) :
    MemLp (fun t : ℝ => (u : ℂ → ℝ) (Complex.exp (t * Complex.I))) 2 μT :=
  memLp_circle (by have := continuous_of_mem u.2; fun_prop)

def traceSmooth : smoothFns →ₗ[ℝ] Lp ℝ 2 μT where
  toFun u := (memLp_bdry u).toLp _
  map_add' u v := by
    rw [← MemLp.toLp_add]; rfl
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]; rfl

lemma traceSmooth_ae (u : smoothFns) :
    (traceSmooth u : ℝ → ℝ) =ᵐ[μT] fun t => (u : ℂ → ℝ) (Complex.exp (t * Complex.I)) :=
  MemLp.coeFn_toLp (memLp_bdry u)

lemma enorm_traceSmooth_sq (u : smoothFns) :
    ‖traceSmooth u‖ₑ ^ 2 =
      ∫⁻ t in Ioc 0 (2 * π), ‖(u : ℂ → ℝ) (Complex.exp (t * Complex.I))‖ₑ ^ 2 :=
  enorm_toLp_sq (memLp_bdry u)

/-- The trace inequality in `ℝ≥0∞` form. -/
lemma trace_ineq_lintegral {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) :
    ∫⁻ t in Ioc 0 (2 * π), ‖u (Complex.exp (t * Complex.I))‖ₑ ^ 2 ≤
      3 * (∫⁻ z in Metric.ball (0:ℂ) 1, ‖u z‖ₑ ^ 2) +
        ∫⁻ z in Metric.ball (0:ℂ) 1, ‖fderiv ℝ u z‖ₑ ^ 2 := by
  have hcu : Continuous u := hu.continuous
  have hcf : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hL : ∫⁻ t in Ioc 0 (2 * π), ‖u (Complex.exp (t * Complex.I))‖ₑ ^ 2 =
      ENNReal.ofReal (∫ t in (0:ℝ)..(2 * π), u (Complex.exp (t * Complex.I)) ^ 2) := by
    rw [intervalIntegral.integral_of_le (by positivity), ofReal_integral_eq_lintegral_ofReal]
    · congr 1; ext t; exact enorm_sq_real _
    · exact ((memLp_circle (f := fun t : ℝ => u (Complex.exp (t * Complex.I)) ^ 2)
        (by fun_prop)).integrable one_le_two)
    · exact Eventually.of_forall (fun t => sq_nonneg _)
  have hR : 3 * (∫⁻ z in Metric.ball (0:ℂ) 1, ‖u z‖ₑ ^ 2) +
        ∫⁻ z in Metric.ball (0:ℂ) 1, ‖fderiv ℝ u z‖ₑ ^ 2 =
      ENNReal.ofReal (∫ z in Metric.ball (0:ℂ) 1, traceDensity u z) := by
    rw [ofReal_integral_eq_lintegral_ofReal]
    · rw [← lintegral_const_mul' _ _ ENNReal.ofNat_ne_top, ← lintegral_add_left]
      · congr 1; ext z
        rw [traceDensity, ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num), enorm_sq_real, ← ofReal_norm_eq_enorm,
          ENNReal.ofReal_pow (norm_nonneg _)]
        norm_num
      · exact (hcu.measurable.enorm.pow_const 2).const_mul _
    · exact (memLp_disk (continuous_traceDensity hu)).integrable one_le_two
    · exact Eventually.of_forall (fun z => traceDensity_nonneg u z)
  rw [hL, hR]
  exact ENNReal.ofReal_le_ofReal (trace_ineq hu)

lemma enorm_traceSmooth_sq_le (u : smoothFns) :
    ‖traceSmooth u‖ₑ ^ 2 ≤ 3 * ‖embed u‖ₑ ^ 2 := by
  rw [enorm_traceSmooth_sq, enorm_amb_sq, embed_fst, embed_snd, enorm_toL2_sq, enorm_gradL2_sq]
  refine (trace_ineq_lintegral (contDiff_one_of_mem u.2)).trans ?_
  rw [mul_add]
  exact add_le_add_right (le_mul_of_one_le_left' (by norm_num : (1:ℝ≥0∞) ≤ 3)) _

lemma norm_traceSmooth_le (u : smoothFns) : ‖traceSmooth u‖ ≤ 2 * ‖embed u‖ := by
  have h := enorm_traceSmooth_sq_le u
  simp only [← ofReal_norm_eq_enorm] at h
  have h' : ENNReal.ofReal (‖traceSmooth u‖ ^ 2) ≤ ENNReal.ofReal (3 * ‖embed u‖ ^ 2) := by
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat,
      ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
    exact h
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h'
  nlinarith [norm_nonneg (traceSmooth u), norm_nonneg (embed u)]

lemma norm_traceSmooth_le' (u : smoothFns) : ‖traceSmooth u‖ ≤ 2 * ‖embedH u‖ :=
  norm_traceSmooth_le u

/-- **The trace operator** `H¹(𝔻) → L²((0,2π])`, the continuous extension of the boundary
restriction `u ↦ u(e^{it})` of smooth functions. -/
def trace : H1 →L[ℝ] Lp ℝ 2 μT := traceSmooth.extendOfNorm embedH

/-- On smooth functions, the trace is the actual boundary restriction. -/
theorem trace_embed (u : smoothFns) : trace (embedH u) = traceSmooth u :=
  LinearMap.extendOfNorm_eq denseRange_embedH ⟨2, norm_traceSmooth_le'⟩ u

/-- On smooth functions, the trace is (a.e.) `t ↦ u(e^{it})`. -/
theorem trace_embed_ae (u : smoothFns) :
    (trace (embedH u) : ℝ → ℝ) =ᵐ[μT] fun t => (u : ℂ → ℝ) (Complex.exp (t * Complex.I)) := by
  rw [trace_embed]; exact traceSmooth_ae u

/-- The trace inequality on `H¹(𝔻)`. -/
theorem norm_trace_le (x : H1) : ‖trace x‖ ≤ 2 * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le denseRange_embedH 2 norm_traceSmooth_le' x

/-! ### Weak gradients -/

/-- Compactly supported smooth test functions in the open unit disk. -/
def IsDiskTest (φ : ℂ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Metric.ball 0 1

lemma IsDiskTest.eq_zero {φ : ℂ → ℝ} (hφ : IsDiskTest φ) {z : ℂ}
    (hz : z ∉ Metric.ball (0:ℂ) 1) : φ z = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hz (hφ.2.2 h))

lemma IsDiskTest.fderiv_eq_zero {φ : ℂ → ℝ} (hφ : IsDiskTest φ) {z : ℂ}
    (hz : z ∉ Metric.ball (0:ℂ) 1) : fderiv ℝ φ z = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hz (hφ.2.2 (tsupport_fderiv_subset ℝ h)))

lemma IsDiskTest.contDiff_one {φ : ℂ → ℝ} (hφ : IsDiskTest φ) : ContDiff ℝ 1 φ :=
  hφ.1.of_le (by exact_mod_cast le_top)

/-- Integration by parts on the disk against a test function, for `C¹` functions. -/
lemma ibp_disk {u φ : ℂ → ℝ} (hu : ContDiff ℝ 1 u) (hφ : IsDiskTest φ) (v : ℂ) :
    ∫ z in Metric.ball (0:ℂ) 1, u z * fderiv ℝ φ z v =
      - ∫ z in Metric.ball (0:ℂ) 1, fderiv ℝ u z v * φ z := by
  have hφ1 := hφ.contDiff_one
  have hcu : Continuous u := hu.continuous
  have hcφ : Continuous φ := hφ1.continuous
  have hcu' : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hcφ' : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv one_ne_zero
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      simp [hφ.fderiv_eq_zero hz]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by simp [hφ.eq_zero hz])]
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ => (hu.differentiable one_ne_zero) x) (fun x _ => (hφ1.differentiable one_ne_zero) x)
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hφ.2.1.mul_left
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (hφ.2.1.fderiv_apply (𝕜 := ℝ) v).mul_left
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop) hφ.2.1.mul_left

lemma inner_toLp_real {f : Lp ℝ 2 μD} {w : ℂ → ℝ} (hw : MemLp w 2 μD) :
    inner ℝ f (hw.toLp w) = ∫ z in Metric.ball (0:ℂ) 1, f z * w z := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toLp] with z hz
  rw [hz]; simp [mul_comm]

lemma inner_toLp_smul {g : Lp ℂ 2 μD} {φ : ℂ → ℝ} {v : ℂ} (hw : MemLp (fun z => φ z • v) 2 μD) :
    inner ℝ g (hw.toLp _) = ∫ z in Metric.ball (0:ℂ) 1, inner ℝ (g z) v * φ z := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toLp] with z hz
  rw [hz, real_inner_smul_right, mul_comm]

lemma gradL2_ae (u : smoothFns) : (gradL2 u : ℂ → ℂ) =ᵐ[μD] grad u :=
  MemLp.coeFn_toLp (memLp_disk (continuous_grad (contDiff_one_of_mem u.2)))

lemma toL2_ae (u : smoothFns) : (toL2 u : ℂ → ℝ) =ᵐ[μD] u :=
  MemLp.coeFn_toLp (memLp_disk (continuous_of_mem u.2))

/-- **Elements of `H¹(𝔻)` are `L²` functions with `L²` weak gradients.** For `(f, g) ∈ H1`,
every compactly supported smooth `φ` in `𝔻` and every direction `v`,
`∫_𝔻 f ∂_v φ = -∫_𝔻 ⟪g, v⟫ φ`. -/
theorem weak_gradient (x : H1) {φ : ℂ → ℝ} (hφ : IsDiskTest φ) (v : ℂ) :
    ∫ z in Metric.ball (0:ℂ) 1, (x : Amb).fst z * fderiv ℝ φ z v =
      - ∫ z in Metric.ball (0:ℂ) 1, inner ℝ ((x : Amb).snd z) v * φ z := by
  have hφ1 := hφ.contDiff_one
  have hcφ : Continuous φ := hφ1.continuous
  have hcφ' : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv one_ne_zero
  have hw1 : MemLp (fun z => fderiv ℝ φ z v) 2 μD := memLp_disk (by fun_prop)
  have hw2 : MemLp (fun z => φ z • v) 2 μD := memLp_disk (by fun_prop)
  set L : Amb → ℝ := fun y => inner ℝ y.fst (hw1.toLp _) + inner ℝ y.snd (hw2.toLp _) with hL
  have hLc : Continuous L := by
    have h1 : Continuous fun y : Amb => y.fst :=
      continuous_fst.comp (WithLp.prod_continuous_ofLp 2 _ _)
    have h2 : Continuous fun y : Amb => y.snd :=
      continuous_snd.comp (WithLp.prod_continuous_ofLp 2 _ _)
    exact (h1.inner continuous_const).add (h2.inner continuous_const)
  have hzero : ∀ y ∈ (H1 : Set Amb), L y = 0 := by
    intro y hy
    have hsub : (LinearMap.range embed : Set Amb) ⊆ {y | L y = 0} := by
      rintro _ ⟨u, rfl⟩
      simp only [mem_setOf_eq, hL, embed_fst, embed_snd]
      rw [inner_toLp_real, inner_toLp_smul]
      have e1 : ∫ z in Metric.ball (0:ℂ) 1, (toL2 u : ℂ → ℝ) z * fderiv ℝ φ z v =
          ∫ z in Metric.ball (0:ℂ) 1, (u : ℂ → ℝ) z * fderiv ℝ φ z v := by
        refine integral_congr_ae ?_
        filter_upwards [toL2_ae u] with z hz; rw [hz]
      have e2 : ∫ z in Metric.ball (0:ℂ) 1, inner ℝ ((gradL2 u : ℂ → ℂ) z) v * φ z =
          ∫ z in Metric.ball (0:ℂ) 1, fderiv ℝ (u : ℂ → ℝ) z v * φ z := by
        refine integral_congr_ae ?_
        filter_upwards [gradL2_ae u] with z hz; rw [hz, inner_grad]
      rw [e1, e2, ibp_disk (contDiff_one_of_mem u.2) hφ v, neg_add_cancel]
    exact closure_minimal hsub (isClosed_eq hLc continuous_const) hy
  have := hzero x x.2
  simp only [hL] at this
  rw [inner_toLp_real, inner_toLp_smul] at this
  linarith

lemma integrable_inner_snd (x : H1) (v : ℂ) :
    IntegrableOn (fun z => inner ℝ ((x : Amb).snd z) v) (Metric.ball (0:ℂ) 1) :=
  ((Lp.memLp (x : Amb).snd).integrable one_le_two).inner_const v

/-- **Uniqueness of weak gradients**: the gradient component of an element of `H¹(𝔻)` is
determined by its function component. -/
theorem snd_eq_zero_of_fst_eq_zero (x : H1) (h : (x : Amb).fst = 0) : (x : Amb).snd = 0 := by
  have hv : ∀ v : ℂ, ∀ᵐ z ∂μD, inner ℝ ((x : Amb).snd z) v = 0 := by
    intro v
    have hU := Metric.isOpen_ball (x := (0:ℂ)) (ε := 1)
    have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
      (f := fun z => inner ℝ ((x : Amb).snd z) v)
      (integrable_inner_snd x v).locallyIntegrableOn ?_
    · rw [ae_restrict_iff' hU.measurableSet]; exact key
    · intro φ h1 h2 h3
      have hφ : IsDiskTest φ := ⟨h1, h2, h3⟩
      have hw := weak_gradient x hφ v
      have h0 : ∫ z in Metric.ball (0:ℂ) 1, (x : Amb).fst z * fderiv ℝ φ z v = 0 := by
        rw [h]
        have : ((0 : Lp ℝ 2 μD) : ℂ → ℝ) =ᵐ[μD] 0 := Lp.coeFn_zero _ _ _
        rw [integral_congr_ae (this.mono fun z hz => by rw [hz]; simp : _ =ᵐ[μD] fun _ => (0:ℝ))]
        simp
      rw [h0, zero_eq_neg] at hw
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.ball (0:ℂ) 1)
        (fun z hz => by simp [hφ.eq_zero hz])]
      rw [← hw]
      refine setIntegral_congr_fun hU.measurableSet (fun z _ => ?_)
      simp [smul_eq_mul, mul_comm]
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hv 1, hv Complex.I] with z h1 h2
  apply Complex.ext
  · simpa [Complex.inner] using h1
  · simpa [Complex.inner] using h2

/-- The function component `H¹(𝔻) → L²(𝔻)` is injective. -/
theorem fst_injective : Function.Injective fun x : H1 => (x : Amb).fst := by
  intro x y hxy
  have h0 : ((x - y : H1) : Amb).fst = 0 := by
    simp only [Submodule.coe_sub, WithLp.sub_fst] at *
    rw [hxy, sub_self]
  have h1 := snd_eq_zero_of_fst_eq_zero _ h0
  rw [← sub_eq_zero]
  apply Subtype.ext
  have : ((x - y : H1) : Amb) = 0 := by
    rw [← norm_eq_zero, ← sq_eq_zero_iff, WithLp.prod_norm_sq_eq_of_L2, h0, h1]
    simp
  simpa using this

end SteklovH1
