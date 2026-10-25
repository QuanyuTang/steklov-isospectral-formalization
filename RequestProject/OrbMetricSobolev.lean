module

public import RequestProject.OrbMetricBounds

/-!
# The metric Sobolev space `H¹(O, g)` of a disk-type orbisurface

For a `SteklovOrb.DiskOrbisurface` `O` with metric `g = λ|dz|²` (conformal coordinate `z ∈ 𝔻̄`):

* `L2g O = L²(𝔻, dA_g)`, `dA_g = λ dA` (`O.areaMeasure`): the metric `L²` space of functions;
* the metric `L²` space of `1`-forms: since `|du|²_g dA_g = λ⁻¹|∇u|² · λ dA = |∇u|² dA`
  (`metric_form_norm`), `du ↦ ∇u` identifies it isometrically with `L²(𝔻, dA; ℝ²)`;
* `MAmb O = L²(𝔻, dA_g) ⊕₂ L²(𝔻, dA; ℝ²)` and the graph embedding `metricEmbed u = (u, ∇u)` of an
  orbifold-smooth function, whose squared norm is `∫ u² dA_g + ∫ |du|²_g dA_g`;
* **`H1Met O`**: the closure of these graphs — the Riemannian Sobolev completion of the
  orbifold-smooth functions for the norm `‖u‖² = ∫ u² dA_g + ∫ |du|²_g dA_g`.

Main results:
* `restrict_le_smul_area`: `dA ≤ c⁻¹ dA_g` on `𝔻` (from `λ ≥ c > 0`, `exists_lam_lower`);
* `norm_le_of_mem_H1Met`: `‖x‖ ≤ K ‖J x‖` on `H1Met`, from the weighted estimate
  `exists_weighted_bound` (`J` forgets the weight on the function component);
* `metricSobolevEquiv O : O.H1Met ≃L[ℝ] H1`: the metric Sobolev space is isomorphic (as a Banach
  space, not isometrically) to `H¹(𝔻)`, by the identity on functions and gradients.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Real ComplexConjugate InnerProductSpace

noncomputable section

namespace SteklovOrb

open Steklov SteklovH1

/-! ### Comparison of `L²` spaces for comparable measures -/

/-- The identity map `L²(μ) → L²(ν)` when `ν ≤ k • μ`. -/
def lpMono {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {k : ℝ≥0∞} (hk : k ≠ ⊤)
    (h : ν ≤ k • μ) : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 ν where
  toFun f := ((Lp.memLp f).of_measure_le_smul hk h).toLp f
  map_add' f g := by
    rw [← MemLp.toLp_add]
    apply MemLp.toLp_congr
    exact (Lp.coeFn_add f g).filter_mono (Measure.absolutelyContinuous_of_le_smul h).ae_le
  map_smul' c f := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    apply MemLp.toLp_congr
    exact (Lp.coeFn_smul c f).filter_mono (Measure.absolutelyContinuous_of_le_smul h).ae_le

lemma lpMono_ae {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {k : ℝ≥0∞} (hk : k ≠ ⊤)
    (h : ν ≤ k • μ) (f : Lp ℝ 2 μ) : (lpMono hk h f : α → ℝ) =ᵐ[ν] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).of_measure_le_smul hk h)

lemma norm_lpMono_le {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {k : ℝ≥0∞} (hk : k ≠ ⊤)
    (h : ν ≤ k • μ) (f : Lp ℝ 2 μ) :
    ‖lpMono hk h f‖ ≤ (k ^ (1 / (2 : ℝ))).toReal * ‖f‖ := by
  change ‖((Lp.memLp f).of_measure_le_smul hk h).toLp f‖ ≤ _
  rw [Lp.norm_toLp, Lp.norm_def, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hk)
    (Lp.eLpNorm_ne_top f)) ?_
  refine (eLpNorm_mono_measure _ h).trans (le_of_eq ?_)
  rw [eLpNorm_smul_measure_of_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  simp [smul_eq_mul]

namespace DiskOrbisurface

variable (O : DiskOrbisurface)

open SteklovBranch

/-! ### Comparison of the metric area with Euclidean area -/

/-- Integrals against the metric area measure: `∫ f dA_g = ∫_𝔻 λ f dA`. -/
lemma lintegral_areaMeasure (f : ℂ → ℝ≥0∞) :
    ∫⁻ z, f z ∂O.areaMeasure =
      ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (O.lamI z) * f z := by
  unfold areaMeasure
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ O.aemeasurable_lam
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine lintegral_congr_ae ?_
  filter_upwards [O.ae_ball_not_cone] with z hz
  simp only [Pi.mul_apply]
  rw [O.lamI_eq ⟨O.cb (ball_subset_closedBall hz.1), hz.2⟩]

instance : IsFiniteMeasure O.areaMeasure := ⟨O.area_lt_top⟩

/-- **Euclidean area is dominated by the metric area on `𝔻`**: `dA ≤ c⁻¹ dA_g`. -/
theorem exists_restrict_le_smul_area :
    ∃ k : ℝ≥0∞, k ≠ ⊤ ∧ (volume.restrict (ball (0 : ℂ) 1)) ≤ k • O.areaMeasure := by
  obtain ⟨c, hc, hcl⟩ := O.exists_lam_lower
  refine ⟨ENNReal.ofReal c⁻¹, ENNReal.ofReal_ne_top, Measure.le_iff.2 fun s hs => ?_⟩
  rw [Measure.smul_apply, smul_eq_mul, areaMeasure, withDensity_apply _ hs,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← setLIntegral_one]
  refine setLIntegral_mono_ae ?_ ?_
  · exact (aemeasurable_const.mul O.aemeasurable_lam.restrict)
  · filter_upwards [O.ae_ball_not_cone] with z hz _
    rw [← ENNReal.ofReal_mul (inv_nonneg.2 hc.le), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [inv_mul_eq_div, le_div_iff₀ hc, one_mul]
    exact hcl z hz

/-- The metric area measure is absolutely continuous with respect to Euclidean area on `𝔻`. -/
lemma areaMeasure_ac : O.areaMeasure ≪ volume.restrict (ball (0 : ℂ) 1) :=
  withDensity_absolutelyContinuous _ _

/-! ### The metric function and form spaces -/

/-- **The metric `L²` space of functions** `L²(O, dA_g)`. -/
abbrev L2g : Type := Lp ℝ 2 O.areaMeasure

/-- The squared metric norm of a differential: `∫ |du|²_g dA_g = ∫_𝔻 |∇u|² dA` — the metric
`L²` norm of `1`-forms agrees with the Euclidean `L²` norm of the gradient (conformal invariance
in dimension two), so `du ↦ ∇u` identifies `L²(T*O, g)` with `L²(𝔻; ℝ²)`. -/
theorem metric_form_norm (u : ℂ → ℝ) :
    ∫⁻ z, ENNReal.ofReal (O.metricGradSq u z) ∂O.areaMeasure =
      eLpNorm (grad u) 2 μD ^ 2 := by
  rw [show ∫⁻ z, ENNReal.ofReal (O.metricGradSq u z) ∂O.areaMeasure = O.energy u from rfl,
    O.energy_eq, dirichletEnergy_eq_eLpNorm_sq]
  congr 1
  exact eLpNorm_congr_norm_ae (Eventually.of_forall fun z => (norm_grad u z).symm)

/-- **Ambient space of the metric Sobolev space**: `L²(O, dA_g) ⊕₂ L²(T*O, g)`, with the form
space realized as `L²(𝔻; ℝ²)` through `du ↦ ∇u` (`metric_form_norm`). -/
abbrev MAmb : Type := WithLp 2 (O.L2g × Lp ℂ 2 μD)

lemma IsOrbSmooth.memLp_area {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) : MemLp u 2 O.areaMeasure := by
  obtain ⟨M, hM⟩ := hu.bounded
  refine MemLp.of_bound hu.continuous.aestronglyMeasurable M ?_
  refine O.areaMeasure_ac.ae_le ?_
  have : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), ‖u z‖ ≤ M := by
    rw [ae_restrict_iff' measurableSet_ball]
    exact Eventually.of_forall fun z hz => by simpa using hM z hz
  exact this

/-- The graph `(u, du)` of an orbifold-smooth function in `L²(O, dA_g) ⊕₂ L²(T*O, g)`. -/
def metricEmbed (u : ℂ → ℝ) (hu : O.IsOrbSmooth u) : O.MAmb :=
  WithLp.toLp 2 ((hu.memLp_area O).toLp u, (hu.memLp_grad).toLp (grad u))

/-- **The metric Sobolev space** `H¹(O, g)`: closure of the graphs of orbifold-smooth functions
in `L²(O, dA_g) ⊕₂ L²(T*O, g)`, i.e. the completion of the orbifold-smooth functions for
`‖u‖² = ∫ u² dA_g + ∫ |du|²_g dA_g`. -/
def H1Met : Submodule ℝ O.MAmb :=
  (Submodule.span ℝ (Set.range fun p : {u : ℂ → ℝ // O.IsOrbSmooth u} =>
    O.metricEmbed p.1 p.2)).topologicalClosure

instance : CompleteSpace O.H1Met :=
  (Submodule.isClosed_topologicalClosure _).completeSpace_coe

/-- Squared norm of a graph: `‖(u, du)‖² = ∫ u² dA_g + ∫ |du|²_g dA_g`. -/
theorem enorm_metricEmbed_sq {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    ‖O.metricEmbed u hu‖ₑ ^ 2 =
      (∫⁻ z, ‖u z‖ₑ ^ 2 ∂O.areaMeasure) + O.energy u := by
  have h2 : ‖O.metricEmbed u hu‖ₑ ^ 2 = ‖(hu.memLp_area O).toLp u‖ₑ ^ 2 +
      ‖(hu.memLp_grad).toLp (grad u)‖ₑ ^ 2 := by
    simp only [← ofReal_norm_eq_enorm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_add (by positivity) (by positivity),
      metricEmbed, WithLp.prod_norm_sq_eq_of_L2]
    rfl
  rw [h2, enorm_toLp_sq, enorm_toLp_sq]
  congr 1
  rw [show ∫⁻ z, ‖grad u z‖ₑ ^ 2 ∂μD = eLpNorm (grad u) 2 μD ^ 2 by
    rw [eLpNorm_two_sq], ← metric_form_norm]
  rfl

/-! ### Linearity of the graph map -/

lemma IsOrbSmooth.zero : O.IsOrbSmooth 0 := O.isOrbSmooth_of_contDiff contDiff_const

lemma IsOrbSmooth.differentiableAt {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) {z : ℂ}
    (hz : z ∉ range O.pt) : DifferentiableAt ℝ u z :=
  (hu.1.contDiffAt (O.isOpen_compl_S.mem_nhds hz)).differentiableAt (by simp)

lemma ae_not_cone : ∀ᵐ z ∂μD, z ∉ range O.pt :=
  ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 ((Set.finite_range O.pt).measure_zero _))

lemma metricEmbed_add {u v : ℂ → ℝ} (hu : O.IsOrbSmooth u) (hv : O.IsOrbSmooth v) :
    O.metricEmbed (u + v) (hu.add O hv) = O.metricEmbed u hu + O.metricEmbed v hv := by
  unfold metricEmbed
  rw [← WithLp.toLp_add, Prod.mk_add_mk, ← MemLp.toLp_add, ← MemLp.toLp_add]
  congr 2
  apply MemLp.toLp_congr
  filter_upwards [O.ae_not_cone] with z hz
  simp only [grad, Pi.add_apply]
  rw [fderiv_add (hu.differentiableAt O hz) (hv.differentiableAt O hz), map_add]

lemma metricEmbed_smul {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) (c : ℝ) :
    O.metricEmbed (c • u) (hu.smul O c) = c • O.metricEmbed u hu := by
  unfold metricEmbed
  rw [← WithLp.toLp_smul, Prod.smul_mk, ← MemLp.toLp_const_smul, ← MemLp.toLp_const_smul]
  congr 2
  apply MemLp.toLp_congr
  filter_upwards [O.ae_not_cone] with z hz
  simp only [grad, Pi.smul_apply]
  rw [fderiv_const_smul (hu.differentiableAt O hz), map_smul]

/-- Every element of the span of the graphs is the graph of one orbifold-smooth function. -/
lemma exists_eq_metricEmbed {x : O.MAmb}
    (hx : x ∈ Submodule.span ℝ (Set.range fun p : {u : ℂ → ℝ // O.IsOrbSmooth u} =>
      O.metricEmbed p.1 p.2)) :
    ∃ u, ∃ hu : O.IsOrbSmooth u, x = O.metricEmbed u hu := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨⟨u, hu⟩, rfl⟩ := hy
    exact ⟨u, hu, rfl⟩
  | zero =>
    exact ⟨0 • 0, (IsOrbSmooth.zero O).smul O 0, by rw [O.metricEmbed_smul (IsOrbSmooth.zero O), zero_smul]⟩
  | add y z _ _ hy hz =>
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨v, hv, rfl⟩ := hz
    exact ⟨u + v, hu.add O hv, (O.metricEmbed_add hu hv).symm⟩
  | smul c y _ hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    exact ⟨c • u, hu.smul O c, (O.metricEmbed_smul hu c).symm⟩

/-! ### Forgetting the weight: the comparison map to `L²(𝔻) ⊕₂ L²(𝔻; ℝ²)` -/

/-- A comparison constant `k` with `dA ≤ k dA_g` on `𝔻`. -/
def kArea : ℝ≥0∞ := Classical.choose O.exists_restrict_le_smul_area

lemma kArea_ne_top : O.kArea ≠ ⊤ := (Classical.choose_spec O.exists_restrict_le_smul_area).1

lemma restrict_le_kArea : volume.restrict (ball (0 : ℂ) 1) ≤ O.kArea • O.areaMeasure :=
  (Classical.choose_spec O.exists_restrict_le_smul_area).2

/-- The identity on functions `L²(𝔻, dA_g) → L²(𝔻, dA)` (bounded since `dA ≤ k dA_g`). -/
def iota : O.L2g →ₗ[ℝ] Lp ℝ 2 μD := lpMono O.kArea_ne_top O.restrict_le_kArea

/-- Norm constant of the comparison map. -/
def cForget : ℝ := max 1 (O.kArea ^ (1 / (2 : ℝ))).toReal

/-- **The comparison map** `J : L²(dA_g) ⊕₂ L²(T*O) → L²(dA) ⊕₂ L²(𝔻; ℝ²)`, the identity on
function and gradient components. -/
def forget : O.MAmb →L[ℝ] Amb :=
  prodMapL O.iota LinearMap.id O.cForget (zero_le_one.trans (le_max_left _ _))
    (fun f => (norm_lpMono_le _ _ f).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)))
    (fun x => by
      simp only [LinearMap.id_apply]
      exact le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _))

@[simp] lemma forget_fst (x : O.MAmb) : (O.forget x).fst = O.iota x.fst := prodMapL_fst _ _ _ _ _ _ x
@[simp] lemma forget_snd (x : O.MAmb) : (O.forget x).snd = x.snd := prodMapL_snd _ _ _ _ _ _ x

lemma iota_ae (f : O.L2g) : (O.iota f : ℂ → ℝ) =ᵐ[μD] f := lpMono_ae _ _ f

lemma metricEmbed_fst {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    (O.metricEmbed u hu).fst = (hu.memLp_area O).toLp u := rfl

lemma metricEmbed_snd {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    (O.metricEmbed u hu).snd = (hu.memLp_grad).toLp (grad u) := rfl

lemma orbEmbed_fst {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    (O.orbEmbed u hu).fst = (memLp_disk hu.continuous).toLp u := rfl

lemma orbEmbed_snd {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    (O.orbEmbed u hu).snd = (hu.memLp_grad).toLp (grad u) := rfl

lemma iota_toLp {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    O.iota ((hu.memLp_area O).toLp u) = (memLp_disk hu.continuous).toLp u := by
  have hac : volume.restrict (ball (0 : ℂ) 1) ≪ O.areaMeasure :=
    Measure.absolutelyContinuous_of_le_smul O.restrict_le_kArea
  apply Lp.ext
  have e1 := O.iota_ae ((hu.memLp_area O).toLp u)
  have e2 : (((hu.memLp_area O).toLp u : O.L2g) : ℂ → ℝ) =ᵐ[μD] u :=
    hac.ae_le (MemLp.coeFn_toLp (hu.memLp_area O))
  have e3 : (((memLp_disk hu.continuous).toLp u : Lp ℝ 2 μD) : ℂ → ℝ) =ᵐ[μD] u :=
    MemLp.coeFn_toLp (memLp_disk hu.continuous)
  exact e1.trans (e2.trans e3.symm)

/-- `J` sends the metric graph of `u` to its Euclidean graph. -/
theorem forget_metricEmbed {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    O.forget (O.metricEmbed u hu) = O.orbEmbed u hu := by
  apply WithLp.ofLp_injective 2
  refine Prod.ext ?_ ?_
  · change (O.forget (O.metricEmbed u hu)).fst = (O.orbEmbed u hu).fst
    rw [forget_fst, metricEmbed_fst, orbEmbed_fst, O.iota_toLp hu]
  · change (O.forget (O.metricEmbed u hu)).snd = (O.orbEmbed u hu).snd
    rw [forget_snd, metricEmbed_snd, orbEmbed_snd]

lemma enorm_orbEmbed_sq {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    ‖O.orbEmbed u hu‖ₑ ^ 2 = (∫⁻ z in ball (0 : ℂ) 1, ‖u z‖ₑ ^ 2) +
      ∫⁻ z in ball (0 : ℂ) 1, ‖fderiv ℝ u z‖ₑ ^ 2 := by
  rw [enorm_amb_sq]
  change ‖(memLp_disk hu.continuous).toLp u‖ₑ ^ 2 + ‖(hu.memLp_grad).toLp (grad u)‖ₑ ^ 2 = _
  rw [enorm_toLp_sq, enorm_toLp_sq]
  congr 1
  refine lintegral_congr fun z => ?_
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_grad]

/-- A constant for the inverse comparison, from the weighted Sobolev estimate. -/
def cWeight : ℝ≥0∞ := Classical.choose O.exists_weighted_bound

lemma cWeight_ne_top : O.cWeight ≠ ⊤ := (Classical.choose_spec O.exists_weighted_bound).1

lemma weighted_bound {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (O.lamI z) * ‖u z‖ₑ ^ 2 ≤
      O.cWeight * ((∫⁻ z in ball (0 : ℂ) 1, ‖u z‖ₑ ^ 2) +
        ∫⁻ z in ball (0 : ℂ) 1, ‖fderiv ℝ u z‖ₑ ^ 2) :=
  (Classical.choose_spec O.exists_weighted_bound).2 u hu

/-- On graphs: `‖(u, du)‖²_g ≤ (C + 1) ‖(u, ∇u)‖²_{H¹(𝔻)}`. -/
lemma enorm_metricEmbed_sq_le {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    ‖O.metricEmbed u hu‖ₑ ^ 2 ≤ (O.cWeight + 1) * ‖O.forget (O.metricEmbed u hu)‖ₑ ^ 2 := by
  rw [O.forget_metricEmbed, O.enorm_orbEmbed_sq, O.enorm_metricEmbed_sq, O.lintegral_areaMeasure,
    O.energy_eq, add_mul, one_mul]
  refine add_le_add (O.weighted_bound hu) ?_
  unfold dirichletEnergy
  exact le_add_self

/-- The constant `K = √(C + 1)` of the inverse comparison. -/
def cInv : ℝ := Real.sqrt (O.cWeight + 1).toReal

lemma norm_le_of_enorm_sq_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    {x : E} {y : F} {K : ℝ≥0∞} (hK : K ≠ ⊤) (h : ‖x‖ₑ ^ 2 ≤ K * ‖y‖ₑ ^ 2) :
    ‖x‖ ≤ Real.sqrt K.toReal * ‖y‖ := by
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_toReal hK,
    ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  rw [← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_sq (norm_nonneg y), ← Real.sqrt_mul
    ENNReal.toReal_nonneg]
  exact Real.sqrt_le_sqrt h

/-- **Inverse comparison on `H¹(O, g)`**: `‖x‖ ≤ K ‖J x‖`. -/
theorem norm_le_of_mem_H1Met {x : O.MAmb} (hx : x ∈ O.H1Met) :
    ‖x‖ ≤ O.cInv * ‖O.forget x‖ := by
  have hcl : IsClosed {x : O.MAmb | ‖x‖ ≤ O.cInv * ‖O.forget x‖} :=
    isClosed_le continuous_norm (continuous_const.mul (O.forget.continuous.norm))
  refine (closure_minimal (fun y hy => ?_) hcl) hx
  obtain ⟨u, hu, rfl⟩ := O.exists_eq_metricEmbed hy
  exact norm_le_of_enorm_sq_le (ENNReal.add_ne_top.2 ⟨O.cWeight_ne_top, ENNReal.one_ne_top⟩)
    (O.enorm_metricEmbed_sq_le hu)

/-- `J` maps `H¹(O, g)` into `H¹(𝔻)`. -/
theorem forget_mem_H1 {x : O.MAmb} (hx : x ∈ O.H1Met) : O.forget x ∈ H1 := by
  have hcl : IsClosed ((H1 : Submodule ℝ Amb).comap O.forget.toLinearMap : Set O.MAmb) := by
    rw [Submodule.comap_coe, ContinuousLinearMap.coe_coe]
    exact (Submodule.isClosed_topologicalClosure _).preimage O.forget.continuous
  have hspan : Submodule.span ℝ (Set.range fun p : {u : ℂ → ℝ // O.IsOrbSmooth u} =>
      O.metricEmbed p.1 p.2) ≤ (H1 : Submodule ℝ Amb).comap O.forget.toLinearMap := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    have h : O.forget (O.metricEmbed u hu) ∈ H1 := by
      rw [O.forget_metricEmbed hu]
      exact O.orbEmbed_mem_H1 hu
    rw [SetLike.mem_coe, Submodule.mem_comap, ContinuousLinearMap.coe_coe]
    exact h
  have h2 := Submodule.topologicalClosure_minimal _ hspan hcl hx
  rwa [Submodule.mem_comap, ContinuousLinearMap.coe_coe] at h2

/-- `J` restricted to `H¹(O, g)`, as a map into `H¹(𝔻)`. -/
def forgetH : O.H1Met →L[ℝ] H1 :=
  (O.forget.comp O.H1Met.subtypeL).codRestrict H1 fun x => O.forget_mem_H1 x.2

@[simp] lemma coe_forgetH (x : O.H1Met) : ((O.forgetH x : H1) : Amb) = O.forget x := rfl

lemma forgetH_injective : Function.Injective O.forgetH := by
  intro x y hxy
  have h := O.norm_le_of_mem_H1Met (x - y).2
  have h0 : O.forget ((x - y : O.H1Met) : O.MAmb) = 0 := by
    have := congrArg (fun z : H1 => (z : Amb)) hxy
    simp only [coe_forgetH] at this
    simp [this]
  rw [h0, norm_zero, mul_zero] at h
  exact sub_eq_zero.1 (Subtype.ext (by simpa using norm_le_zero_iff.1 h))

lemma forgetH_surjective : Function.Surjective O.forgetH := by
  set f : O.H1Met →L[ℝ] Amb := O.forget.comp O.H1Met.subtypeL
  have hanti : AntilipschitzWith ⟨O.cInv, Real.sqrt_nonneg _⟩ f :=
    f.antilipschitz_of_bound fun x => O.norm_le_of_mem_H1Met x.2
  have hclosed : IsClosed (Set.range f) := hanti.isClosed_range f.uniformContinuous
  have hsub : (H1 : Set Amb) ⊆ Set.range f := by
    refine closure_minimal ?_ hclosed
    rintro _ ⟨u, rfl⟩
    have hu : O.IsOrbSmooth u := O.isOrbSmooth_of_contDiff u.2
    refine ⟨⟨O.metricEmbed u hu, Submodule.le_topologicalClosure _
      (Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩)⟩, ?_⟩
    show O.forget (O.metricEmbed u hu) = embed u
    rw [O.forget_metricEmbed]
    rfl
  intro y
  obtain ⟨x, hx⟩ := hsub y.2
  exact ⟨x, Subtype.ext hx⟩

/-- **The metric Sobolev space of `O` is isomorphic to `H¹(𝔻)`**: the comparison map
`(u, du) ↦ (u, ∇u)` is a Banach-space isomorphism `H¹(O, g) ≃ H¹(𝔻)` (not an isometry: the
function norms `∫ u² dA_g` and `∫ u² dA` are only equivalent). -/
def metricSobolevEquiv : O.H1Met ≃L[ℝ] H1 :=
  (LinearEquiv.ofBijective O.forgetH.toLinearMap
    ⟨O.forgetH_injective, O.forgetH_surjective⟩).toContinuousLinearEquivOfBounds
    ‖O.forgetH‖ O.cInv (fun x => O.forgetH.le_opNorm x) (fun y => by
      set x := (LinearEquiv.ofBijective O.forgetH.toLinearMap
        ⟨O.forgetH_injective, O.forgetH_surjective⟩).symm y
      have hy : O.forgetH x = y :=
        (LinearEquiv.ofBijective O.forgetH.toLinearMap _).apply_symm_apply y
      calc ‖x‖ = ‖(x : O.MAmb)‖ := rfl
        _ ≤ O.cInv * ‖O.forget x‖ := O.norm_le_of_mem_H1Met x.2
        _ = O.cInv * ‖y‖ := by rw [← hy]; rfl)

@[simp] lemma coe_metricSobolevEquiv (x : O.H1Met) :
    ((O.metricSobolevEquiv x : H1) : Amb) = O.forget x := rfl

/-- The metric Sobolev space and the (Euclidean-norm) closure model `H1Orb` are isomorphic. -/
def metricSobolevEquivOrb : O.H1Met ≃L[ℝ] O.H1Orb :=
  O.metricSobolevEquiv.trans O.h1OrbEquiv.symm.toContinuousLinearEquiv

end DiskOrbisurface

end SteklovOrb
