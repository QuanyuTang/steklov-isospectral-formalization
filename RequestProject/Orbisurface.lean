module

public import RequestProject.OrbMinMax
public import RequestProject.AreaFormula
public import RequestProject.GeneralConformalPullback
public import RequestProject.ConformalSobolev

/-!
# Disk-type Riemannian orbisurfaces (coordinate model) and Proposition 2.2.1

**Coordinate model.**  A compact orientable Riemannian orbisurface `O` homeomorphic to a closed disk,
with finitely many interior cone points, is described through a conformal parametrization
`𝔻̄ → O` (which exists by uniformization; the model is *given* in this coordinate).  In the
coordinate `z ∈ 𝔻̄`:

* the cone points are distinct points `p_i ∈ 𝔻` with orders `m_i ≥ 2`;
* the orbifold chart at `p_i` is the branched map `w ↦ p_i + w^{m_i}` (`coneChart`), i.e. a
  neighbourhood of `p_i` is the quotient of a disk by the rotation group `μ_{m_i}`
  (`coneChart_eq_iff`, `exists_coneChart_eq`);
* the Riemannian metric is conformal, `g = λ(z)|dz|²`, with `λ` smooth and positive on a
  neighbourhood of `𝔻̄` minus the cone points, and **smooth and positive in every cone chart**:
  the pulled-back conformal factor `λ(p + w^m)|m w^{m-1}|²` extends to a smooth positive function
  across `w = 0` (`cone_metric`); this extension is automatically `μ_m`-invariant
  (`chartFactor_rot`, `coneMetric_invariant`);
* orbifold-smooth functions are functions smooth off the cone points whose expression in every
  cone chart is smooth at the centre (`IsOrbSmooth`).  As for the smooth test functions of plane
  domains, they are taken globally defined (restrictions to `𝔻̄` are what matters);
* area measure `dA_g = λ dA`, metric gradient norm `|du|²_g = λ⁻¹|du|²`, Dirichlet energy
  `E_g(u) = ∫ |du|²_g dA_g`, boundary line element `ds_g = √λ |dz|` on `𝕋`.

The Steklov spectrum of `O` is the min–max spectrum of `E_g / ∫_{∂O} u² ds_g` over
orbifold-smooth test functions (`DiskOrbisurface.steklovSpectrum`), **not** the disk spectrum by
definition.

**Proposition 2.2.1** (`DiskOrbisurface.prop_2_2_1`): `Spec_St(O) = Spec_St(𝔻, ρ)` with
`ρ = √λ|_𝕋` the boundary line element in the conformal coordinate.  Ingredients: conformal
invariance of the Dirichlet energy (`energy_eq`), finiteness of the energy of orbifold-smooth
functions computed in the cone charts (`cone_lintegral_le`, `dirichletEnergy_ne_top`), and
removal of the cone points by logarithmic cut-offs (`SteklovOrb.minMaxOn_le_of_singular_transfer`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Real ComplexConjugate

noncomputable section

namespace SteklovOrb

open Steklov

/-! ### Cone charts -/

/-- The orbifold chart of order `m` at `p`: `w ↦ p + w^m`. -/
def coneChart (p : ℂ) (m : ℕ) (w : ℂ) : ℂ := p + w ^ m

/-- Conformal factor of the metric `λ|dz|²` pulled back by the cone chart:
`λ(p + w^m) |m w^{m-1}|²`. -/
def chartFactor (lam : ℂ → ℝ) (p : ℂ) (m : ℕ) (w : ℂ) : ℝ :=
  lam (coneChart p m w) * ‖(m : ℂ) * w ^ (m - 1)‖ ^ 2

lemma coneChart_rot {p ζ : ℂ} {m : ℕ} (hζ : ζ ^ m = 1) (w : ℂ) :
    coneChart p m (ζ * w) = coneChart p m w := by
  simp [coneChart, mul_pow, hζ]

/-- The pulled-back conformal factor is invariant under the deck rotations `w ↦ ζ w`, `ζ^m = 1`. -/
lemma chartFactor_rot {lam : ℂ → ℝ} {p ζ : ℂ} {m : ℕ} (hm : m ≠ 0) (hζ : ζ ^ m = 1) (w : ℂ) :
    chartFactor lam p m (ζ * w) = chartFactor lam p m w := by
  have hζn : ‖ζ‖ = 1 := by
    have h := congrArg norm hζ
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm).1 h
  unfold chartFactor
  rw [coneChart_rot hζ, mul_pow, norm_mul, norm_mul, norm_mul, norm_pow ζ, hζn, one_pow, one_mul]

/-- The chart identifies exactly the `μ_m`-orbits: away from the centre, two points have the same
image iff they differ by an `m`-th root of unity. -/
lemma coneChart_eq_iff {p w w' : ℂ} {m : ℕ} (hw : w ≠ 0) :
    coneChart p m w' = coneChart p m w ↔ ∃ ζ : ℂ, ζ ^ m = 1 ∧ w' = ζ * w := by
  constructor
  · intro h
    refine ⟨w' / w, ?_, by field_simp⟩
    have h' : w' ^ m = w ^ m := by simpa [coneChart] using h
    rw [div_pow, h', div_self (pow_ne_zero _ hw)]
  · rintro ⟨ζ, hζ, rfl⟩
    exact coneChart_rot hζ w

/-- The chart covers a neighbourhood of the cone point: every `z` with `|z - p| < r^m` is
`p + w^m` with `|w| < r`. -/
lemma exists_coneChart_eq {p z : ℂ} {m : ℕ} (hm : m ≠ 0) {r : ℝ} (hr : 0 ≤ r)
    (hz : z ∈ ball p (r ^ m)) : ∃ w ∈ ball (0 : ℂ) r, coneChart p m w = z := by
  refine ⟨(z - p) ^ ((m : ℂ)⁻¹), ?_, ?_⟩
  · rw [mem_ball_zero_iff]
    have h1 : ‖(z - p) ^ ((m : ℂ)⁻¹)‖ ^ m = ‖z - p‖ := by
      rw [← norm_pow, Complex.cpow_nat_inv_pow _ hm]
    rw [mem_ball, dist_eq_norm] at hz
    rw [← h1] at hz
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr hm).1 hz
  · simp [coneChart, Complex.cpow_nat_inv_pow _ hm]

lemma contDiff_coneChart (p : ℂ) (m : ℕ) : ContDiff ℝ ∞ (coneChart p m) :=
  contDiff_const.add (contDiff_id.pow m)

lemma hasDerivAt_coneChart (p : ℂ) (m : ℕ) (w : ℂ) :
    HasDerivAt (coneChart p m) ((m : ℂ) * w ^ (m - 1)) w := by
  show HasDerivAt (fun w => p + w ^ m) _ w
  exact (hasDerivAt_pow m w).const_add p

lemma deriv_coneChart (p : ℂ) (m : ℕ) (w : ℂ) :
    deriv (coneChart p m) w = (m : ℂ) * w ^ (m - 1) := (hasDerivAt_coneChart p m w).deriv

/-! ### The orbisurface -/

/-- **A compact orientable Riemannian orbisurface of disk type, in its conformal coordinate.**
Cone points `pt i ∈ 𝔻` of orders `ord i ≥ 2`; conformal metric `λ|dz|²` smooth and positive on a
neighbourhood `U` of `𝔻̄` minus the cone points; in each cone chart `w ↦ pt i + w^{ord i}` the
pulled-back conformal factor extends to a smooth positive function `μ` across the centre. -/
structure DiskOrbisurface where
  n : ℕ
  pt : Fin n → ℂ
  ord : Fin n → ℕ
  pt_inj : Function.Injective pt
  pt_mem : ∀ i, ‖pt i‖ < 1
  two_le_ord : ∀ i, 2 ≤ ord i
  lam : ℂ → ℝ
  U : Set ℂ
  isOpen_U : IsOpen U
  cb : closedBall (0 : ℂ) 1 ⊆ U
  lam_smooth : ContDiffOn ℝ ∞ lam (U \ range pt)
  lam_pos : ∀ z ∈ U \ range pt, 0 < lam z
  cone_metric : ∀ i, ∃ r > 0, ∃ μ : ℂ → ℝ, ContDiffOn ℝ ∞ μ (ball 0 r) ∧
    (∀ w ∈ ball (0 : ℂ) r, 0 < μ w) ∧
    ∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → μ w = chartFactor lam (pt i) (ord i) w

namespace DiskOrbisurface

variable (O : DiskOrbisurface)

lemma ord_ne_zero (i : Fin O.n) : O.ord i ≠ 0 := by have := O.two_le_ord i; omega

/-- The smooth metric in a cone chart is invariant under the deck rotations. -/
theorem coneMetric_invariant (i : Fin O.n) {r : ℝ} {μ : ℂ → ℝ}
    (hμ : ∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → μ w = chartFactor O.lam (O.pt i) (O.ord i) w)
    {ζ : ℂ} (hζ : ζ ^ O.ord i = 1) {w : ℂ} (hw : w ∈ ball (0 : ℂ) r) :
    μ (ζ * w) = μ w := by
  have hζn : ‖ζ‖ = 1 := by
    have h := congrArg norm hζ
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (O.ord_ne_zero i)).1 h
  have hζw : ζ * w ∈ ball (0 : ℂ) r := by simpa [norm_mul, hζn] using hw
  by_cases h0 : w = 0
  · simp [h0]
  · rw [hμ _ hζw (mul_ne_zero (by rintro rfl; simp at hζn) h0), hμ _ hw h0,
      chartFactor_rot (O.ord_ne_zero i) hζ]

/-- The cone points as a finite set. -/
def S : Finset ℂ := Finset.univ.image O.pt

lemma coe_S : (O.S : Set ℂ) = range O.pt := by simp [S]

lemma S_mem {s : ℂ} (hs : s ∈ O.S) : ‖s‖ < 1 := by
  obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hs; exact O.pt_mem i

lemma isOpen_compl_S : IsOpen (range O.pt)ᶜ :=
  (Set.finite_range O.pt).isClosed.isOpen_compl

/-! ### Orbifold-smooth functions -/

/-- **Orbifold-smooth functions**: smooth off the cone points, and smooth at the centre of every
cone chart `w ↦ pt i + w^{ord i}`. -/
def IsOrbSmooth (u : ℂ → ℝ) : Prop :=
  ContDiffOn ℝ ∞ u (range O.pt)ᶜ ∧
    ∀ i, ContDiffAt ℝ ∞ (fun w => u (coneChart (O.pt i) (O.ord i) w)) 0

/-- Globally smooth functions are orbifold-smooth. -/
lemma isOrbSmooth_of_contDiff {u : ℂ → ℝ} (hu : ContDiff ℝ ∞ u) : O.IsOrbSmooth u :=
  ⟨hu.contDiffOn, fun _ => (hu.comp (contDiff_coneChart _ _)).contDiffAt⟩

lemma IsOrbSmooth.add {u v : ℂ → ℝ} (hu : O.IsOrbSmooth u) (hv : O.IsOrbSmooth v) :
    O.IsOrbSmooth (u + v) :=
  ⟨hu.1.add hv.1, fun i => (hu.2 i).add (hv.2 i)⟩

lemma IsOrbSmooth.smul {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) (c : ℝ) : O.IsOrbSmooth (c • u) :=
  ⟨hu.1.const_smul c, fun i => (hu.2 i).const_smul c⟩

/-- Orbifold-smooth functions are continuous (also at the cone points). -/
theorem IsOrbSmooth.continuous {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) : Continuous u := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ range O.pt
  · obtain ⟨i, rfl⟩ := hz
    set m := O.ord i
    have hm := O.ord_ne_zero i
    set R : ℂ → ℂ := fun z => (z - O.pt i) ^ ((m : ℂ)⁻¹)
    have hR : ContinuousAt R (O.pt i) := by
      have h1 : ContinuousAt (fun x : ℂ × ℂ => x.1 ^ x.2) (0, (m : ℂ)⁻¹) :=
        Complex.continuousAt_cpow_zero_of_re_pos (by
          simp only [Complex.inv_re, Complex.natCast_re, Complex.normSq_natCast]
          have : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm
          positivity)
      have h2 : ContinuousAt (fun z : ℂ => (z - O.pt i, (m : ℂ)⁻¹)) (O.pt i) := by fun_prop
      have h3 := ContinuousAt.comp (f := fun z : ℂ => (z - O.pt i, (m : ℂ)⁻¹)) (x := O.pt i)
        (by simpa using h1) h2
      exact h3
    have hR0 : R (O.pt i) = 0 := by
      simp only [R, sub_self]
      exact Complex.zero_cpow (inv_ne_zero (Nat.cast_ne_zero.2 hm))
    have huR : u = fun z => u (coneChart (O.pt i) m (R z)) := by
      funext z
      simp only [R, coneChart]
      rw [Complex.cpow_nat_inv_pow _ hm, add_sub_cancel]
    rw [huR]
    have hc := (hu.2 i).continuousAt
    rw [← hR0] at hc
    exact hc.comp hR
  · exact (hu.1.continuousOn.continuousAt (O.isOpen_compl_S.mem_nhds hz))

/-- Orbifold-smooth functions are bounded on the disk. -/
lemma IsOrbSmooth.bounded {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    ∃ M, ∀ z ∈ ball (0 : ℂ) 1, |u z| ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    hu.continuous.continuousOn
  exact ⟨M, fun z hz => by simpa using hM z (ball_subset_closedBall hz)⟩


/-! ### Area, metric gradient and Dirichlet energy -/

lemma lam_pos_ball {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hz' : z ∉ range O.pt) : 0 < O.lam z :=
  O.lam_pos z ⟨O.cb (ball_subset_closedBall hz), hz'⟩

lemma ae_ball_not_cone :
    ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), z ∈ ball (0 : ℂ) 1 \ range O.pt := by
  rw [ae_restrict_iff' measurableSet_ball]
  have h0 : volume (range O.pt) = 0 := (Set.finite_range O.pt).measure_zero _
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with z hz hzb
  exact ⟨hzb, hz⟩

lemma restrict_ball_eq :
    volume.restrict (ball (0 : ℂ) 1) = volume.restrict (ball (0 : ℂ) 1 \ range O.pt) := by
  refine (Measure.restrict_congr_set ?_).symm
  rw [diff_ae_eq_self]
  exact measure_mono_null inter_subset_right ((Set.finite_range O.pt).measure_zero _)

lemma aemeasurable_lam :
    AEMeasurable (fun z => ENNReal.ofReal (O.lam z)) (volume.restrict (ball (0 : ℂ) 1)) := by
  rw [O.restrict_ball_eq]
  refine (ContinuousOn.aemeasurable ?_ (measurableSet_ball.diff
    (Set.finite_range O.pt).measurableSet)).ennreal_ofReal
  exact O.lam_smooth.continuousOn.mono
    (diff_subset_diff_left (ball_subset_closedBall.trans O.cb))

/-- The Riemannian area measure `dA_g = λ dA` of `O` (in the conformal coordinate). -/
def areaMeasure : Measure ℂ :=
  (volume.restrict (ball (0 : ℂ) 1)).withDensity fun z => ENNReal.ofReal (O.lam z)

/-- The squared metric norm of the differential, `|du|²_g = λ⁻¹ |du|²`. -/
def metricGradSq (u : ℂ → ℝ) (z : ℂ) : ℝ := ‖fderiv ℝ u z‖ ^ 2 / O.lam z

/-- The Dirichlet energy of `O`: `E_g(u) = ∫_O |du|²_g dA_g`. -/
def energy (u : ℂ → ℝ) : ℝ≥0∞ := ∫⁻ z, ENNReal.ofReal (O.metricGradSq u z) ∂O.areaMeasure

/-- **Conformal invariance of the Dirichlet energy**: `E_g(u) = ∫_𝔻 |∇u|² dA`. -/
theorem energy_eq (u : ℂ → ℝ) : O.energy u = dirichletEnergy (ball 0 1) u := by
  unfold energy areaMeasure dirichletEnergy
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable₀ _ O.aemeasurable_lam
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine lintegral_congr_ae ?_
  filter_upwards [O.ae_ball_not_cone] with z hz
  have hl := O.lam_pos_ball hz.1 hz.2
  simp only [Pi.mul_apply, metricGradSq]
  rw [← ENNReal.ofReal_mul hl.le, mul_div_cancel₀ _ hl.ne', ← ofReal_norm_eq_enorm,
    ENNReal.ofReal_pow (norm_nonneg _)]

/-! ### The boundary line element -/

/-- Density of the boundary line element `ds_g = √λ |dz|` in the conformal coordinate. -/
def lineDensity (z : ℂ) : ℝ := Real.sqrt (O.lam z)

lemma sphere_sub : sphere (0 : ℂ) 1 ⊆ O.U \ range O.pt := fun z hz =>
  ⟨O.cb (sphere_subset_closedBall hz), by
    rintro ⟨i, rfl⟩
    have := O.pt_mem i
    rw [mem_sphere_zero_iff_norm] at hz
    linarith⟩

lemma continuousOn_lineDensity : ContinuousOn O.lineDensity (sphere 0 1) :=
  Real.continuous_sqrt.comp_continuousOn (O.lam_smooth.continuousOn.mono O.sphere_sub)

lemma lineDensity_pos {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : 0 < O.lineDensity z :=
  Real.sqrt_pos.2 (O.lam_pos z (O.sphere_sub hz))

/-- The boundary line measure of `∂O`, transported to the circle `𝕋` by the boundary
parametrization `t ↦ e^{it}`. -/
def lineMeasure : Measure ℂ := SteklovC1.weightMeasure O.lineDensity

/-- The boundary mass `∫_{∂O} u² ds_g`. -/
def bdryMass (u : ℂ → ℝ) : ℝ≥0∞ := ∫⁻ z, ‖u z‖ₑ ^ 2 ∂O.lineMeasure

theorem bdryMass_eq {u : ℂ → ℝ} (hu : Continuous u) :
    O.bdryMass u = weightedBoundaryMass O.lineDensity u :=
  SteklovC1.lintegral_weightMeasure O.continuousOn_lineDensity hu

/-! ### The Steklov spectrum of the orbisurface -/

/-- The Steklov spectrum of `O` (with multiplicities): min–max of `E_g(u) / ∫_{∂O} u² ds_g` over
orbifold-smooth test functions. -/
def steklovSpectrum (k : ℕ) : ℝ≥0∞ := minMaxOn O.IsOrbSmooth O.energy O.bdryMass k

/-! ### Dirichlet energy in a cone chart -/

/-- **Dirichlet integrals near a cone point are computed in the cone chart** (area formula for
the `m`-to-`1` branched chart):
`∫_{|z-p|<r^m} G ≤ ∫_{|w|<r} |m w^{m-1}|² G(p + w^m)`. -/
theorem cone_lintegral_le (p : ℂ) {m : ℕ} (hm : m ≠ 0) {r : ℝ} (hr : 0 ≤ r) (G : ℂ → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ z in ball p (r ^ m), G z ≤
      ∫⁻ w in ball (0 : ℂ) r, ‖(m : ℂ) * w ^ (m - 1)‖ₑ ^ 2 * G (coneChart p m w) := by
  set B := coneChart p m
  have hBd : DifferentiableOn ℂ B univ := fun w _ =>
    (hasDerivAt_coneChart p m w).differentiableAt.differentiableWithinAt
  have hcrit : {w ∈ ball (0 : ℂ) r | deriv B w = 0}.Countable := by
    refine (Set.countable_singleton (0 : ℂ)).mono ?_
    rintro w ⟨-, hw⟩
    rw [deriv_coneChart, mul_eq_zero] at hw
    rcases hw with h | h
    · exact absurd (Nat.cast_eq_zero.1 h) hm
    · exact eq_zero_of_pow_eq_zero h
  have hA := SteklovArea.lintegral_deriv_sq_mul_eq_fibreSum isOpen_univ hBd measurableSet_ball
    (subset_univ _) hcrit (G ∘ B) (hG.comp (contDiff_coneChart p m).continuous.measurable)
  rw [show deriv B = fun w => (m : ℂ) * w ^ (m - 1) from funext (deriv_coneChart p m)] at hA
  simp only [Function.comp] at hA
  rw [hA]
  calc ∫⁻ z in ball p (r ^ m), G z = ∫⁻ z, (ball p (r ^ m)).indicator G z :=
        (lintegral_indicator measurableSet_ball G).symm
    _ ≤ _ := lintegral_mono fun z => by
        by_cases hz : z ∈ ball p (r ^ m)
        · rw [indicator_of_mem hz]
          obtain ⟨w, hw, hwz⟩ := exists_coneChart_eq hm hr hz
          refine le_trans (le_of_eq ?_) (ENNReal.le_tsum
            (⟨w, hw, hwz⟩ : {w' // w' ∈ ball (0 : ℂ) r ∧ B w' = z}))
          simp [Function.comp, B, hwz]
        · rw [indicator_of_notMem hz]; exact zero_le

/-- Near each cone point, an orbifold-smooth function has finite Dirichlet integral (computed in
the cone chart, where it is `C¹`). -/
theorem cone_energy_finite {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) (i : Fin O.n) :
    ∃ r > 0, ∫⁻ z in ball (O.pt i) (r ^ O.ord i), ‖fderiv ℝ u z‖ₑ ^ 2 < ⊤ := by
  set p := O.pt i
  set m := O.ord i
  have hm : m ≠ 0 := O.ord_ne_zero i
  have hm2 : 2 ≤ m := O.two_le_ord i
  set v : ℂ → ℝ := fun w => u (coneChart p m w) with hvdef
  obtain ⟨δ, hδ, hδP⟩ : ∃ δ > 0, ∀ z ∈ ball p δ, z ∈ range O.pt → z = p := by
    have hcl : IsClosed (range O.pt \ {p}) := ((Set.finite_range O.pt).diff).isClosed
    have hp : p ∈ (range O.pt \ {p})ᶜ := by simp
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl p hp
    exact ⟨δ, hδ, fun z hz hzP => by
      by_contra hne
      exact hball hz ⟨hzP, hne⟩⟩
  obtain ⟨ε, hε, hC1⟩ : ∃ ε > 0, ∀ y ∈ ball (0 : ℂ) ε, ContDiffAt ℝ 1 v y :=
    Metric.eventually_nhds_iff.1 (((hu.2 i).of_le (by exact_mod_cast le_top)).eventually
      (by simp))
  have hCon : ContDiffOn ℝ 1 v (ball 0 ε) := fun y hy => (hC1 y hy).contDiffWithinAt
  have hfc : ContinuousOn (fderiv ℝ v) (ball 0 ε) :=
    hCon.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  set r := min (ε / 2) (min (1 / 2) δ) with hrdef
  have hr : 0 < r := lt_min (half_pos hε) (lt_min (by norm_num) hδ)
  have hrε : r < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hr1 : r < 1 := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by norm_num))
  have hrδ : r ≤ δ := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) r).exists_bound_of_continuousOn
    (hfc.mono (closedBall_subset_ball hrε))
  refine ⟨r, hr, ?_⟩
  have hmeas : Measurable fun z => ‖fderiv ℝ u z‖ₑ ^ 2 :=
    (measurable_fderiv ℝ u).enorm.pow_const 2
  refine (cone_lintegral_le p hm hr.le _ hmeas).trans_lt ?_
  refine (setLIntegral_mono' (g := fun _ => ENNReal.ofReal (C ^ 2)) measurableSet_ball
    fun w hw => ?_).trans_lt ?_
  · by_cases hw0 : w = 0
    · subst hw0
      have : (0 : ℂ) ^ (m - 1) = 0 := zero_pow (by omega)
      simp [this]
    · have hwn : ‖w‖ < r := mem_ball_zero_iff.1 hw
      have hBw : coneChart p m w ∉ range O.pt := by
        intro hP
        have hmem : coneChart p m w ∈ ball p δ := by
          rw [mem_ball, dist_eq_norm]
          simp only [coneChart, add_sub_cancel_left, norm_pow]
          calc ‖w‖ ^ m ≤ ‖w‖ := pow_le_of_le_one (norm_nonneg _) (hwn.trans hr1).le hm
            _ < δ := hwn.trans_le hrδ
        have := hδP _ hmem hP
        simp only [coneChart, add_eq_left] at this
        exact hw0 (eq_zero_of_pow_eq_zero this)
      have hud : DifferentiableAt ℝ u (coneChart p m w) :=
        (hu.1.contDiffAt (O.isOpen_compl_S.mem_nhds hBw)).differentiableAt (by simp)
      have hg := SteklovH1.grad_comp_holo hud (hasDerivAt_coneChart p m w)
      have hnorm : ‖fderiv ℝ v w‖ = ‖(m : ℂ) * w ^ (m - 1)‖ * ‖fderiv ℝ u (coneChart p m w)‖ := by
        rw [← SteklovH1.norm_grad, ← SteklovH1.norm_grad, hvdef, hg, norm_mul, Complex.norm_conj]
      have hb : ‖fderiv ℝ v w‖ ≤ C := hC w (ball_subset_closedBall hw)
      rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity), ← mul_pow,
        ← hnorm]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hb 2)
  · rw [setLIntegral_const]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top

/-- **Orbifold-smooth functions have finite Dirichlet energy.** -/
theorem IsOrbSmooth.dirichletEnergy_lt_top {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    dirichletEnergy (ball 0 1) u < ⊤ := by
  choose r hr hfin using O.cone_energy_finite hu
  set V := ⋃ i, ball (O.pt i) (r i ^ O.ord i)
  set K := closedBall (0 : ℂ) 1 \ V
  have hK : IsCompact K := (isCompact_closedBall 0 1).diff (isOpen_iUnion fun i => isOpen_ball)
  have hKP : K ⊆ (range O.pt)ᶜ := by
    rintro z ⟨-, hzV⟩ ⟨i, rfl⟩
    exact hzV (mem_iUnion.2 ⟨i, mem_ball_self (pow_pos (hr i) _)⟩)
  have hfc : ContinuousOn (fderiv ℝ u) (range O.pt)ᶜ :=
    hu.1.continuousOn_fderiv_of_isOpen O.isOpen_compl_S (by exact_mod_cast le_top)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hfc.mono hKP)
  have hsub : ball (0 : ℂ) 1 ⊆ K ∪ V := fun z hz => by
    by_cases h : z ∈ V
    · exact Or.inr h
    · exact Or.inl ⟨ball_subset_closedBall hz, h⟩
  unfold dirichletEnergy
  refine (lintegral_mono_set hsub).trans_lt ((lintegral_union_le _ _ _).trans_lt ?_)
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · refine (setLIntegral_mono' (g := fun _ => ENNReal.ofReal (C ^ 2))
      (hK.isClosed.measurableSet) fun z hz => ?_).trans_lt ?_
    · rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (hC z hz) 2)
    · rw [setLIntegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hK.measure_lt_top
  · refine (lintegral_iUnion_le _ _).trans_lt ?_
    rw [tsum_fintype]
    exact ENNReal.sum_lt_top.2 fun i _ => hfin i

/-! ### Proposition 2.2.1 -/

/-- **Proposition 2.2.1 (coordinate model).**  The Steklov spectrum of the orbisurface `O`
(orbifold-smooth test functions, metric Dirichlet energy, metric boundary line element) equals the
weighted Steklov spectrum of the disk with weight the boundary line element `ρ = √λ|_𝕋` of `O` in
its conformal coordinate, with multiplicities. -/
theorem prop_2_2_1 : O.steklovSpectrum = weightedSteklovSpectrum O.lineDensity := by
  funext k
  apply le_antisymm
  · exact minMaxOn_le_minMax (fun u hu => O.isOrbSmooth_of_contDiff hu) (fun u _ => O.energy_eq u)
      (fun u hu => O.bdryMass_eq hu.continuous) k
  · have hρ : Continuous fun t : ℝ => O.lineDensity (SteklovBranch.circ t) :=
      O.continuousOn_lineDensity.comp_continuous SteklovBranch.continuous_circ
        (fun t => mem_sphere_zero_iff_norm.2 (SteklovBranch.norm_circ t))
    refine minMaxOn_le_of_singular_transfer (P := O.IsOrbSmooth) hρ O.S (fun s hs => O.S_mem hs)
      LinearMap.id (fun u hu => ⟨hu.bounded, ?_, (O.energy_eq u).symm,
        (O.bdryMass_eq hu.continuous).symm⟩) (fun u hu => ?_) k
    · rw [O.coe_S]; exact hu.1
    · rw [O.energy_eq]; exact (hu.dirichletEnergy_lt_top).ne

end DiskOrbisurface

end SteklovOrb
