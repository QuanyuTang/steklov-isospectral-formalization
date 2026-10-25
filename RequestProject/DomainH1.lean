module

public import Mathlib
public import RequestProject.DiskH1
public import RequestProject.AbstractMinMax

/-!
# `H¹(Ω)`, its boundary trace, and the `H¹` Steklov min–max on a bounded plane domain

For a bounded open `Ω ⊆ ℂ ≅ ℝ²` whose topological boundary has finite one-dimensional Hausdorff
measure (`SteklovH1.BddDomain`):

* `H1 Ω` is the closure of `{(u|_Ω, ∇u|_Ω) : u globally smooth}` in `L²(Ω) ⊕₂ L²(Ω; ℝ²)`;
  its elements are `L²` functions with `L²` weak gradients (`BddDomain.weak_gradient`), and the
  gradient is determined by the function (`BddDomain.snd_eq_zero_of_fst_eq_zero`);
* `trace : H1 Ω →L L²(∂Ω, H¹)` is the continuous extension of `u ↦ u|_{∂Ω}`. Under the trace
  inequality `∫_{∂Ω} u² ≤ C (∫_Ω u² + ∫_Ω |∇u|²)` for smooth `u` (`BddDomain.HasTraceIneq`) it
  agrees with the boundary restriction on smooth functions (`BddDomain.trace_embed_ae`);
* `BddDomain.h1SteklovEigenvalue` is the min–max of `∫_Ω |∇x|² / ∫_{∂Ω} |Tx|² dH¹` over
  `(k+1)`-dimensional subspaces of `H1 Ω` on which the boundary mass is positive definite.

`BddDomain.steklovEigenvalue_eq_h1`: under the trace inequality, `Steklov.steklovEigenvalue Ω k`
(the min–max over globally smooth test functions) equals the `H¹` min–max value for every `k`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff

noncomputable section

namespace SteklovH1

/-- A bounded open plane domain whose boundary has finite length (`H¹`-measure). -/
structure BddDomain where
  carrier : Set ℂ
  isOpen : IsOpen carrier
  isBounded : Bornology.IsBounded carrier
  bdry_finite : Measure.hausdorffMeasure 1 (frontier carrier) ≠ ⊤

namespace BddDomain

variable (D : BddDomain)

/-- Lebesgue measure on `Ω`. -/
abbrev μ : Measure ℂ := volume.restrict D.carrier

/-- Arc length on `∂Ω`. -/
abbrev ν : Measure ℂ := (Measure.hausdorffMeasure 1).restrict (frontier D.carrier)

/-- The ambient Hilbert space `L²(Ω) ⊕₂ L²(Ω; ℝ²)`. -/
abbrev Amb := WithLp 2 (Lp ℝ 2 D.μ × Lp ℂ 2 D.μ)

instance : IsFiniteMeasure D.μ := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact D.isBounded.measure_lt_top

instance : IsFiniteMeasure D.ν := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
  exact lt_top_iff_ne_top.2 D.bdry_finite

lemma isCompact_closure : IsCompact (closure D.carrier) := D.isBounded.isCompact_closure

lemma memLp_dom {F : Type*} [NormedAddCommGroup F] {f : ℂ → F} (hf : Continuous f) :
    MemLp f 2 D.μ := by
  obtain ⟨C, hC⟩ := D.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' D.isOpen.measurableSet]
  exact Eventually.of_forall (fun z hz => hC z (subset_closure hz))

lemma memLp_bdry {f : ℂ → ℝ} (hf : Continuous f) : MemLp f 2 D.ν := by
  obtain ⟨C, hC⟩ := D.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' isClosed_frontier.measurableSet]
  exact Eventually.of_forall (fun z hz => hC z (frontier_subset_closure hz))

/-- `u ↦ u|_Ω ∈ L²(Ω)`. -/
def toL2 : smoothFns →ₗ[ℝ] Lp ℝ 2 D.μ where
  toFun u := (D.memLp_dom (continuous_of_mem u.2)).toLp u
  map_add' u v := by
    simp only [Submodule.coe_add]
    exact MemLp.toLp_add _ _
  map_smul' c u := by
    simp only [Submodule.coe_smul, RingHom.id_apply]
    exact MemLp.toLp_const_smul _ _

/-- `u ↦ ∇u|_Ω ∈ L²(Ω; ℝ²)`. -/
def gradL2 : smoothFns →ₗ[ℝ] Lp ℂ 2 D.μ where
  toFun u := (D.memLp_dom (continuous_grad (contDiff_one_of_mem u.2))).toLp (grad u)
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

/-- `u ↦ (u, ∇u)`. -/
def embed : smoothFns →ₗ[ℝ] D.Amb :=
  (WithLp.linearEquiv 2 ℝ (Lp ℝ 2 D.μ × Lp ℂ 2 D.μ)).symm.toLinearMap ∘ₗ (D.toL2.prod D.gradL2)

@[simp] lemma embed_fst (u : smoothFns) : (D.embed u).fst = D.toL2 u := rfl
@[simp] lemma embed_snd (u : smoothFns) : (D.embed u).snd = D.gradL2 u := rfl

/-- **The Sobolev space `H¹(Ω)`** (closure of smooth functions in the graph norm). -/
def H1 : Submodule ℝ D.Amb := (LinearMap.range D.embed).topologicalClosure

instance : CompleteSpace D.H1 :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Smooth functions as elements of `H¹(Ω)`. -/
def embedH : smoothFns →ₗ[ℝ] D.H1 :=
  LinearMap.codRestrict D.H1 D.embed
    (fun u => Submodule.le_topologicalClosure _ (LinearMap.mem_range_self D.embed u))

@[simp] lemma coe_embedH (u : smoothFns) : (D.embedH u : D.Amb) = D.embed u := rfl

lemma denseRange_embedH : DenseRange D.embedH := by
  rw [DenseRange, Subtype.dense_iff]
  intro x hx
  have : Set.range D.embedH = ((↑) : D.H1 → D.Amb) ⁻¹' (LinearMap.range D.embed) := by
    ext y; constructor
    · rintro ⟨u, rfl⟩; exact ⟨u, rfl⟩
    · rintro ⟨u, hu⟩; exact ⟨u, Subtype.ext hu⟩
  rw [this]
  have hx' : x ∈ closure (LinearMap.range D.embed : Set D.Amb) := hx
  refine closure_mono ?_ hx'
  intro y hy
  exact ⟨⟨y, Submodule.le_topologicalClosure _ hy⟩, hy, rfl⟩

lemma toL2_ae (u : smoothFns) : (D.toL2 u : ℂ → ℝ) =ᵐ[D.μ] u :=
  MemLp.coeFn_toLp (D.memLp_dom (continuous_of_mem u.2))

lemma gradL2_ae (u : smoothFns) : (D.gradL2 u : ℂ → ℂ) =ᵐ[D.μ] grad u :=
  MemLp.coeFn_toLp (D.memLp_dom (continuous_grad (contDiff_one_of_mem u.2)))

lemma enorm_amb_sq (x : D.Amb) : ‖x‖ₑ ^ 2 = ‖x.fst‖ₑ ^ 2 + ‖x.snd‖ₑ ^ 2 := by
  simp only [← ofReal_norm_eq_enorm]
  rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
    WithLp.prod_norm_sq_eq_of_L2]

lemma enorm_toL2_sq (u : smoothFns) :
    ‖D.toL2 u‖ₑ ^ 2 = ∫⁻ z in D.carrier, ‖(u : ℂ → ℝ) z‖ₑ ^ 2 :=
  enorm_toLp_sq (D.memLp_dom (continuous_of_mem u.2))

lemma enorm_gradL2_sq (u : smoothFns) :
    ‖D.gradL2 u‖ₑ ^ 2 = Steklov.dirichletEnergy D.carrier u := by
  rw [show D.gradL2 u = (D.memLp_dom (continuous_grad (contDiff_one_of_mem u.2))).toLp
    (grad u) from rfl, enorm_toLp_sq]
  unfold Steklov.dirichletEnergy
  congr 1; ext z
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_grad]

/-! ### The trace -/

/-- `u ↦ u|_{∂Ω} ∈ L²(∂Ω, H¹)` on smooth functions. -/
def traceSmooth : smoothFns →ₗ[ℝ] Lp ℝ 2 D.ν where
  toFun u := (D.memLp_bdry (continuous_of_mem u.2)).toLp u
  map_add' u v := by
    simp only [Submodule.coe_add]
    exact MemLp.toLp_add _ _
  map_smul' c u := by
    simp only [Submodule.coe_smul, RingHom.id_apply]
    exact MemLp.toLp_const_smul _ _

lemma traceSmooth_ae (u : smoothFns) : (D.traceSmooth u : ℂ → ℝ) =ᵐ[D.ν] u :=
  MemLp.coeFn_toLp (D.memLp_bdry (continuous_of_mem u.2))

lemma enorm_traceSmooth_sq (u : smoothFns) :
    ‖D.traceSmooth u‖ₑ ^ 2 = Steklov.boundaryMass D.carrier u :=
  enorm_toLp_sq (D.memLp_bdry (continuous_of_mem u.2))

/-- The **trace inequality** on `Ω` with constant `C`, for globally smooth functions. -/
def HasTraceIneq (C : ℝ) : Prop :=
  ∀ u : ℂ → ℝ, ContDiff ℝ ∞ u →
    Steklov.boundaryMass D.carrier u ≤
      ENNReal.ofReal C * ((∫⁻ z in D.carrier, ‖u z‖ₑ ^ 2) + Steklov.dirichletEnergy D.carrier u)

/-- The trace operator `H¹(Ω) → L²(∂Ω)` (continuous extension of the boundary restriction). -/
def trace : D.H1 →L[ℝ] Lp ℝ 2 D.ν := D.traceSmooth.extendOfNorm D.embedH

lemma norm_traceSmooth_le {C : ℝ} (hC : D.HasTraceIneq C) (u : smoothFns) :
    ‖D.traceSmooth u‖ ≤ Real.sqrt C * ‖D.embedH u‖ := by
  have h := hC u u.2
  rw [← enorm_traceSmooth_sq, ← enorm_toL2_sq, ← enorm_gradL2_sq, ← embed_fst, ← embed_snd,
    ← enorm_amb_sq, ← coe_embedH] at h
  simp only [← ofReal_norm_eq_enorm] at h
  rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _)] at h
  have hC0 : ∀ a : ℝ, 0 ≤ a → ENNReal.ofReal C * ENNReal.ofReal a = ENNReal.ofReal (max C 0 * a) := by
    intro a ha
    rw [ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left
      (zero_le)]
  rw [hC0 _ (by positivity)] at h
  have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h
  have h3 : ‖D.traceSmooth u‖ ≤ Real.sqrt (max C 0 * ‖(D.embedH u : D.Amb)‖ ^ 2) :=
    Real.le_sqrt_of_sq_le h2
  rw [Real.sqrt_mul (le_max_right _ _), Real.sqrt_sq (norm_nonneg _)] at h3
  calc ‖D.traceSmooth u‖ ≤ _ := h3
    _ = Real.sqrt C * ‖D.embedH u‖ := by
      congr 1
      rcases le_total C 0 with h | h
      · rw [max_eq_right h, Real.sqrt_zero, Real.sqrt_eq_zero'.2 h]
      · rw [max_eq_left h]

/-- On smooth functions, the trace is the boundary restriction. -/
theorem trace_embed {C : ℝ} (hC : D.HasTraceIneq C) (u : smoothFns) :
    D.trace (D.embedH u) = D.traceSmooth u :=
  LinearMap.extendOfNorm_eq D.denseRange_embedH ⟨_, D.norm_traceSmooth_le hC⟩ u

theorem trace_embed_ae {C : ℝ} (hC : D.HasTraceIneq C) (u : smoothFns) :
    (D.trace (D.embedH u) : ℂ → ℝ) =ᵐ[D.ν] u := by
  rw [D.trace_embed hC]; exact D.traceSmooth_ae u

/-- The trace inequality on `H¹(Ω)`. -/
theorem norm_trace_le {C : ℝ} (hC : D.HasTraceIneq C) (x : D.H1) :
    ‖D.trace x‖ ≤ Real.sqrt C * ‖x‖ :=
  LinearMap.norm_extendOfNorm_apply_le D.denseRange_embedH _ (D.norm_traceSmooth_le hC) x

/-! ### Weak gradients -/

/-- Compactly supported smooth test functions in `Ω`. -/
def IsTest (φ : ℂ → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ D.carrier

lemma IsTest.eq_zero {D : BddDomain} {φ : ℂ → ℝ} (hφ : D.IsTest φ) {z : ℂ}
    (hz : z ∉ D.carrier) : φ z = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hz (hφ.2.2 h))

lemma IsTest.fderiv_eq_zero {D : BddDomain} {φ : ℂ → ℝ} (hφ : D.IsTest φ) {z : ℂ}
    (hz : z ∉ D.carrier) : fderiv ℝ φ z = 0 :=
  image_eq_zero_of_notMem_tsupport (fun h => hz (hφ.2.2 (tsupport_fderiv_subset ℝ h)))

lemma IsTest.contDiff_one {D : BddDomain} {φ : ℂ → ℝ} (hφ : D.IsTest φ) : ContDiff ℝ 1 φ :=
  hφ.1.of_le (by exact_mod_cast le_top)

lemma ibp {u φ : ℂ → ℝ} (hu : ContDiff ℝ 1 u) (hφ : D.IsTest φ) (v : ℂ) :
    ∫ z in D.carrier, u z * fderiv ℝ φ z v = - ∫ z in D.carrier, fderiv ℝ u z v * φ z := by
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

lemma inner_toLp_real {f : Lp ℝ 2 D.μ} {w : ℂ → ℝ} (hw : MemLp w 2 D.μ) :
    inner ℝ f (hw.toLp w) = ∫ z in D.carrier, f z * w z := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toLp] with z hz
  rw [hz]; simp [mul_comm]

lemma inner_toLp_smul {g : Lp ℂ 2 D.μ} {φ : ℂ → ℝ} {v : ℂ}
    (hw : MemLp (fun z => φ z • v) 2 D.μ) :
    inner ℝ g (hw.toLp _) = ∫ z in D.carrier, inner ℝ (g z) v * φ z := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hw.coeFn_toLp] with z hz
  rw [hz, real_inner_smul_right, mul_comm]

/-- **Elements of `H¹(Ω)` are `L²` functions with `L²` weak gradients.** -/
theorem weak_gradient (x : D.H1) {φ : ℂ → ℝ} (hφ : D.IsTest φ) (v : ℂ) :
    ∫ z in D.carrier, (x : D.Amb).fst z * fderiv ℝ φ z v =
      - ∫ z in D.carrier, inner ℝ ((x : D.Amb).snd z) v * φ z := by
  have hφ1 := hφ.contDiff_one
  have hcφ : Continuous φ := hφ1.continuous
  have hcφ' : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv one_ne_zero
  have hw1 : MemLp (fun z => fderiv ℝ φ z v) 2 D.μ := D.memLp_dom (by fun_prop)
  have hw2 : MemLp (fun z => φ z • v) 2 D.μ := D.memLp_dom (by fun_prop)
  set L : D.Amb → ℝ := fun y => inner ℝ y.fst (hw1.toLp _) + inner ℝ y.snd (hw2.toLp _)
    with hL
  have hLc : Continuous L := by
    have h1 : Continuous fun y : D.Amb => y.fst :=
      continuous_fst.comp (WithLp.prod_continuous_ofLp 2 _ _)
    have h2 : Continuous fun y : D.Amb => y.snd :=
      continuous_snd.comp (WithLp.prod_continuous_ofLp 2 _ _)
    exact (h1.inner continuous_const).add (h2.inner continuous_const)
  have hzero : ∀ y ∈ (D.H1 : Set D.Amb), L y = 0 := by
    intro y hy
    have hsub : (LinearMap.range D.embed : Set D.Amb) ⊆ {y | L y = 0} := by
      rintro _ ⟨u, rfl⟩
      simp only [mem_setOf_eq, hL, embed_fst, embed_snd]
      rw [D.inner_toLp_real, D.inner_toLp_smul]
      have e1 : ∫ z in D.carrier, (D.toL2 u : ℂ → ℝ) z * fderiv ℝ φ z v =
          ∫ z in D.carrier, (u : ℂ → ℝ) z * fderiv ℝ φ z v := by
        refine integral_congr_ae ?_
        filter_upwards [D.toL2_ae u] with z hz; rw [hz]
      have e2 : ∫ z in D.carrier, inner ℝ ((D.gradL2 u : ℂ → ℂ) z) v * φ z =
          ∫ z in D.carrier, fderiv ℝ (u : ℂ → ℝ) z v * φ z := by
        refine integral_congr_ae ?_
        filter_upwards [D.gradL2_ae u] with z hz; rw [hz, inner_grad]
      rw [e1, e2, D.ibp (contDiff_one_of_mem u.2) hφ v, neg_add_cancel]
    exact closure_minimal hsub (isClosed_eq hLc continuous_const) hy
  have := hzero x x.2
  simp only [hL] at this
  rw [D.inner_toLp_real, D.inner_toLp_smul] at this
  linarith

/-- **Uniqueness of weak gradients** in `H¹(Ω)`. -/
theorem snd_eq_zero_of_fst_eq_zero (x : D.H1) (h : (x : D.Amb).fst = 0) :
    (x : D.Amb).snd = 0 := by
  have hv : ∀ v : ℂ, ∀ᵐ z ∂D.μ, inner ℝ ((x : D.Amb).snd z) v = 0 := by
    intro v
    have hU := D.isOpen
    have hint : IntegrableOn (fun z => inner ℝ ((x : D.Amb).snd z) v) D.carrier :=
      ((Lp.memLp (x : D.Amb).snd).integrable one_le_two).inner_const v
    have key := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume)
      (f := fun z => inner ℝ ((x : D.Amb).snd z) v)
      hint.locallyIntegrableOn ?_
    · rw [ae_restrict_iff' hU.measurableSet]; exact key
    · intro φ h1 h2 h3
      have hφ : D.IsTest φ := ⟨h1, h2, h3⟩
      have hw := D.weak_gradient x hφ v
      have h0 : ∫ z in D.carrier, (x : D.Amb).fst z * fderiv ℝ φ z v = 0 := by
        rw [h]
        have : ((0 : Lp ℝ 2 D.μ) : ℂ → ℝ) =ᵐ[D.μ] 0 := Lp.coeFn_zero _ _ _
        rw [integral_congr_ae (this.mono fun z hz => by rw [hz]; simp :
          _ =ᵐ[D.μ] fun _ => (0:ℝ))]
        simp
      rw [h0, zero_eq_neg] at hw
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := D.carrier)
        (fun z hz => by simp [hφ.eq_zero hz])]
      rw [← hw]
      refine setIntegral_congr_fun hU.measurableSet (fun z _ => ?_)
      simp [smul_eq_mul, mul_comm]
  rw [Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hv 1, hv Complex.I] with z h1 h2
  apply Complex.ext
  · simpa [Complex.inner] using h1
  · simpa [Complex.inner] using h2

/-! ### `H¹` min–max -/

/-- Dirichlet energy of `x ∈ H¹(Ω)`: `∫_Ω |∇x|²` (weak gradient). -/
def h1Energy (x : D.H1) : ℝ≥0∞ := ‖(x : D.Amb).snd‖ₑ ^ 2

/-- Boundary mass of `x ∈ H¹(Ω)`: `∫_{∂Ω} |Tx|² dH¹`, with `T` the trace. -/
def h1BoundaryMass (x : D.H1) : ℝ≥0∞ := ∫⁻ z, ‖(D.trace x : ℂ → ℝ) z‖ₑ ^ 2 ∂D.ν

/-- The `k`-th variational Steklov eigenvalue of `Ω` on `H¹(Ω)`. -/
def h1SteklovEigenvalue (k : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule ℝ D.H1)
    (_ : Module.finrank ℝ V = k + 1 ∧ ∀ x ∈ V, x ≠ 0 → D.h1BoundaryMass x ≠ 0),
    ⨆ (x : D.H1) (_ : x ∈ V) (_ : x ≠ 0), D.h1Energy x / D.h1BoundaryMass x

lemma enorm_Lp_sq {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] {m : Measure α}
    (f : Lp F 2 m) : ‖f‖ₑ ^ 2 = ∫⁻ a, ‖(f : α → F) a‖ₑ ^ 2 ∂m := by
  conv_lhs => rw [← Lp.toLp_coeFn f (Lp.memLp f)]
  exact enorm_toLp_sq _

/-- The gradient component as a continuous linear map on `H¹(Ω)`. -/
def gradOp : D.H1 →L[ℝ] Lp ℂ 2 D.μ :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap.comp D.H1.subtypeL)

lemma gradOp_apply (x : D.H1) : D.gradOp x = (x : D.Amb).snd := rfl

lemma h1SteklovEigenvalue_eq_closureMinMax (k : ℕ) :
    D.h1SteklovEigenvalue k = closureMinMax D.gradOp D.trace k := by
  have hE : ∀ x, D.h1Energy x = ‖D.gradOp x‖ₑ ^ 2 := fun x => rfl
  have hB : ∀ x, D.h1BoundaryMass x = ‖D.trace x‖ₑ ^ 2 := fun x => (enorm_Lp_sq _).symm
  simp only [h1SteklovEigenvalue, closureMinMax, hE, hB]

/-- **`H¹`/smooth min–max equality on `Ω`**: under the trace inequality, the smooth-test Steklov
eigenvalues of `Ω` are the `H¹(Ω)` variational eigenvalues, for every index. -/
theorem steklovEigenvalue_eq_h1 {C : ℝ} (hC : D.HasTraceIneq C) (k : ℕ) :
    Steklov.steklovEigenvalue D.carrier k = D.h1SteklovEigenvalue k := by
  rw [h1SteklovEigenvalue_eq_closureMinMax]
  refine minMax_eq_closureMinMax D.gradOp D.trace D.embedH D.denseRange_embedH ?_ ?_ k
  · intro u
    rw [gradOp_apply, coe_embedH, embed_snd, enorm_gradL2_sq]
  · intro u
    rw [D.trace_embed hC, enorm_traceSmooth_sq]

end BddDomain

end SteklovH1
