module

public import RequestProject.OrbMetricSobolev
public import RequestProject.H1MinMax

/-!
# Trace, energy, weak spectrum and min–max on the metric Sobolev space `H¹(O, g)`

For a `SteklovOrb.DiskOrbisurface` `O` and its metric Sobolev space `O.H1Met`
(`RequestProject/OrbMetricSobolev.lean`; norm `‖u‖² = ∫ u² dA_g + ∫ |du|²_g dA_g`):

* `trace_orbEmbed`: the disk trace of the graph of an orbifold-smooth `u` is its boundary
  restriction `t ↦ u(e^{it})`;
* `traceMet : H1Met → L²(∂O)` (bounded linear) with `traceMet_metricEmbed`: on orbifold-smooth `u`
  it is the boundary restriction — the genuine trace;
* `metricEnergy x = ‖du‖²_{L²(T*O, g)}` with `metricEnergy_metricEmbed : = E_g(u)`,
  `metricBoundaryMass x = ∫_{∂O} (Tx)² ds_g` with `metricBoundaryMass_metricEmbed : = ∫_{∂O} u² ds_g`;
* `IsWeakSteklovEigenMet τ x`: `∫ ⟨dx, dy⟩_g dA_g = τ ∫_{∂O} Tx Ty ds_g` for all `y ∈ H¹(O, g)`;
* `weak_spectral_theorem_met`: eigenpairs, multiplicities = eigenspace dimensions;
* `metricSteklovEigenvalue k`: the Courant–Fischer min–max of `metricEnergy / metricBoundaryMass`
  over `(k+1)`-dimensional subspaces of `H¹(O, g)` — the Riemannian orbifold variational spectrum;
* **`prop_2_2_1_metric`**: `metricSteklovEigenvalue = weightedSteklovSpectrum ρ_O`
  (with `ρ_O = √λ|_𝕋`) and `= O.steklovSpectrum` (orbifold-smooth min–max), for every index.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Real ComplexConjugate InnerProductSpace

noncomputable section

namespace SteklovOrb

open Steklov SteklovH1 SteklovBranch

/-! ### Min–max over subspaces is invariant under linear equivalences -/

/-- Courant–Fischer min–max value of `E / B` over `(k+1)`-dimensional subspaces on which `B` is
positive definite. -/
def subspaceMinMax {X : Type*} [AddCommGroup X] [Module ℝ X] (E B : X → ℝ≥0∞) (k : ℕ) :
    ℝ≥0∞ :=
  ⨅ (V : Submodule ℝ X) (_ : Module.finrank ℝ V = k + 1 ∧ ∀ x ∈ V, x ≠ 0 → B x ≠ 0),
    ⨆ (x : X) (_ : x ∈ V) (_ : x ≠ 0), E x / B x

lemma subspaceMinMax_le_of_equiv {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y]
    [Module ℝ Y] (P : X ≃ₗ[ℝ] Y) {EX BX : X → ℝ≥0∞} {EY BY : Y → ℝ≥0∞}
    (hE : ∀ x, EX x = EY (P x)) (hB : ∀ x, BX x = BY (P x)) (k : ℕ) :
    subspaceMinMax EX BX k ≤ subspaceMinMax EY BY k := by
  refine le_iInf₂ fun W hW => ?_
  refine iInf₂_le_of_le (W.map P.symm.toLinearMap) ⟨?_, ?_⟩ ?_
  · rw [LinearEquiv.finrank_map_eq]; exact hW.1
  · rintro x ⟨y, hy, rfl⟩ hx0
    rw [hB, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact hW.2 y hy (by rintro rfl; simp at hx0)
  · refine iSup₂_le fun x hx => iSup_le fun hx0 => ?_
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hE, hB, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact le_iSup₂_of_le y hy (le_iSup_of_le (by rintro rfl; simp at hx0) le_rfl)

lemma subspaceMinMax_eq_of_equiv {X Y : Type*} [AddCommGroup X] [Module ℝ X] [AddCommGroup Y]
    [Module ℝ Y] (P : X ≃ₗ[ℝ] Y) {EX BX : X → ℝ≥0∞} {EY BY : Y → ℝ≥0∞}
    (hE : ∀ x, EX x = EY (P x)) (hB : ∀ x, BX x = BY (P x)) (k : ℕ) :
    subspaceMinMax EX BX k = subspaceMinMax EY BY k :=
  le_antisymm (subspaceMinMax_le_of_equiv P hE hB k)
    (subspaceMinMax_le_of_equiv P.symm (fun y => by rw [hE, LinearEquiv.apply_symm_apply])
      (fun y => by rw [hB, LinearEquiv.apply_symm_apply]) k)

lemma h1SteklovEigenvalue_eq_subspaceMinMax (ρ : ℂ → ℝ) (k : ℕ) :
    h1SteklovEigenvalue ρ k = subspaceMinMax h1Energy (h1BoundaryMass ρ) k := rfl

namespace DiskOrbisurface

variable (O : DiskOrbisurface)

/-! ### The trace of orbifold-smooth graphs -/

/-- Orbifold-smooth graphs are approximated in `H¹(𝔻)` by graphs of smooth functions that agree
with `u` on the boundary circle (logarithmic cut-offs at the cone points). -/
theorem exists_smooth_near_orbEmbed {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : smoothFns, ‖O.orbEmbed u hu - embed v‖ < ε ∧
      ∀ z : ℂ, 1 ≤ ‖z‖ → (v : ℂ → ℝ) z = u z := by
  have hS : ContDiffOn ℝ ∞ u (↑O.S)ᶜ := by rw [O.coe_S]; exact hu.1
  have hE : eLpNorm (fderiv ℝ u) 2 μD ≠ ⊤ := by
    have h := hu.dirichletEnergy_lt_top
    rw [dirichletEnergy_eq_eLpNorm_sq] at h
    exact fun h' => by rw [h'] at h; simp at h
  have h1 := (O.tendsto_eLpNorm_corr_sub hu).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hε)))
  have h2 := (tendsto_eLpNorm_fderiv_corr_sub (fun s hs => O.S_mem hs) hu.bounded hS hE).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (half_pos hε)))
  obtain ⟨r, ⟨hr, hr1⟩, hr2⟩ :=
    (((eventually_goodRadius O.S (fun s hs => O.S_mem hs)).and h1).and h2).exists
  have hv : ContDiff ℝ ∞ (corr O.S r u) := corr_contDiff hr hS
  refine ⟨⟨_, hv⟩, ?_, fun z hz => corr_eq_on_circle hr u hz⟩
  refine (SteklovH1.norm_prod_le _).trans_lt ?_
  have hfst : ‖(O.orbEmbed u hu - embed ⟨_, hv⟩).fst‖ < ε / 2 := by
    change ‖(memLp_disk hu.continuous).toLp u - (memLp_disk hv.continuous).toLp _‖ < ε / 2
    rw [← MemLp.toLp_sub, Lp.norm_toLp, ← eLpNorm_neg, neg_sub]
    exact (ENNReal.toReal_lt_toReal (by
      exact ne_top_of_lt hr1) ENNReal.ofReal_ne_top).2 hr1 |>.trans_le
      (ENNReal.toReal_ofReal (by positivity)).le
  have hsnd : ‖(O.orbEmbed u hu - embed ⟨_, hv⟩).snd‖ < ε / 2 := by
    change ‖hu.memLp_grad.toLp (grad u) -
      (memLp_disk (continuous_grad (contDiff_one_of_mem hv))).toLp _‖ < ε / 2
    rw [← MemLp.toLp_sub, Lp.norm_toLp]
    have hcong : eLpNorm (grad u - grad (corr O.S r u)) 2 μD =
        eLpNorm (fderiv ℝ (corr O.S r u - u)) 2 μD := by
      refine eLpNorm_congr_norm_ae
        ((measurable_grad u).aestronglyMeasurable.sub (measurable_grad _).aestronglyMeasurable)
        (measurable_fderiv ℝ _).aestronglyMeasurable ?_
      have h0 : volume (O.S : Set ℂ) = 0 := O.S.finite_toSet.measure_zero _
      filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h0)] with z hz
      have hdu : DifferentiableAt ℝ u z :=
        (hS.contDiffAt ((O.S.finite_toSet.isClosed.isOpen_compl).mem_nhds hz)).differentiableAt
          (by simp)
      have hdv : DifferentiableAt ℝ (corr O.S r u) z := (hv.differentiable (by simp)) z
      rw [Pi.sub_apply, norm_grad_sub, fderiv_sub hdv hdu, norm_sub_rev]
    rw [hcong]
    exact (ENNReal.toReal_lt_toReal (ne_top_of_lt hr2) ENNReal.ofReal_ne_top).2 hr2 |>.trans_le
      (ENNReal.toReal_ofReal (by positivity)).le
  linarith

lemma memLp_bdry_orb {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    MemLp (fun t : ℝ => u (Complex.exp (t * Complex.I))) 2 μT :=
  memLp_circle (by have := hu.continuous; fun_prop)

/-- **Trace of orbifold-smooth graphs**: the disk trace of `(u, ∇u)` is `t ↦ u(e^{it})`. -/
theorem trace_orbEmbed {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    trace ⟨O.orbEmbed u hu, O.orbEmbed_mem_H1 hu⟩ = (O.memLp_bdry_orb hu).toLp _ := by
  set x : H1 := ⟨O.orbEmbed u hu, O.orbEmbed_mem_H1 hu⟩
  refine eq_of_forall_dist_le fun ε hε => ?_
  obtain ⟨v, hv, hvb⟩ := O.exists_smooth_near_orbEmbed hu (half_pos hε)
  have htv : trace (embedH v) = (O.memLp_bdry_orb hu).toLp _ := by
    rw [trace_embed]
    exact MemLp.toLp_congr (memLp_bdry v) (O.memLp_bdry_orb hu)
      (Eventually.of_forall fun t => hvb _ (by simp [Complex.norm_exp_ofReal_mul_I]))
  rw [← htv, dist_eq_norm, ← map_sub]
  refine (norm_trace_le _).trans ?_
  have : ‖x - embedH v‖ = ‖O.orbEmbed u hu - embed v‖ := rfl
  rw [this]
  linarith

/-! ### The trace on the metric Sobolev space -/

/-- **The trace** `H¹(O, g) → L²(∂O)` (boundary parametrized by `t ↦ e^{it}`), bounded linear. -/
def traceMet : O.H1Met →L[ℝ] Lp ℝ 2 μT := trace.comp O.metricSobolevEquiv.toContinuousLinearMap

lemma traceMet_apply (x : O.H1Met) : O.traceMet x = trace (O.metricSobolevEquiv x) := rfl

lemma metricEmbed_mem {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) : O.metricEmbed u hu ∈ O.H1Met :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩)

/-- **The trace of an orbifold-smooth function is its boundary restriction.** -/
theorem traceMet_metricEmbed {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    O.traceMet ⟨O.metricEmbed u hu, O.metricEmbed_mem hu⟩ = (O.memLp_bdry_orb hu).toLp _ := by
  rw [traceMet_apply, ← O.trace_orbEmbed hu]
  congr 1
  exact Subtype.ext (O.forget_metricEmbed hu)

/-! ### Energy and boundary forms -/

/-- The metric Dirichlet energy on `H¹(O, g)`: the squared `L²(T*O, g)` norm of the differential. -/
def metricEnergy (x : O.H1Met) : ℝ≥0∞ := ‖(x : O.MAmb).snd‖ₑ ^ 2

/-- The boundary mass `∫_{∂O} (Tx)² ds_g`, with the metric line element `ds_g = √λ |dz|`. -/
def metricBoundaryMass (x : O.H1Met) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 (2 * π),
    ‖(O.traceMet x : ℝ → ℝ) t‖ₑ ^ 2 * ENNReal.ofReal (O.lineDensity (Complex.exp (t * Complex.I)))

/-- On orbifold-smooth functions the metric energy is `E_g(u) = ∫ |du|²_g dA_g`. -/
theorem metricEnergy_metricEmbed {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    O.metricEnergy ⟨O.metricEmbed u hu, O.metricEmbed_mem hu⟩ = O.energy u := by
  unfold metricEnergy
  change ‖(hu.memLp_grad).toLp (grad u)‖ₑ ^ 2 = _
  rw [Lp.enorm_toLp, ← metric_form_norm]
  rfl

/-- On orbifold-smooth functions the boundary mass is `∫_{∂O} u² ds_g`. -/
theorem metricBoundaryMass_metricEmbed {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    O.metricBoundaryMass ⟨O.metricEmbed u hu, O.metricEmbed_mem hu⟩ = O.bdryMass u := by
  rw [O.bdryMass_eq hu.continuous, metricBoundaryMass, traceMet_metricEmbed, weightedBoundaryMass]
  refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
  have h := MemLp.coeFn_toLp (O.memLp_bdry_orb hu)
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at h
  filter_upwards [h] with t ht hmem
  rw [ht hmem]

lemma metricEnergy_eq (x : O.H1Met) : O.metricEnergy x = h1Energy (O.metricSobolevEquiv x) := by
  unfold metricEnergy h1Energy
  rw [coe_metricSobolevEquiv, forget_snd]

lemma metricBoundaryMass_eq (x : O.H1Met) :
    O.metricBoundaryMass x = h1BoundaryMass O.lineDensity (O.metricSobolevEquiv x) := rfl

/-! ### The weak Steklov problem on `H¹(O, g)` -/

/-- **Weak Steklov eigenfunctions of the orbisurface** on its metric Sobolev space:
`∫ ⟨dx, dy⟩_g dA_g = τ ∫_{∂O} Tx Ty ds_g` for all `y ∈ H¹(O, g)` (the metric pairing of
differentials is `∫ ⟨∇x, ∇y⟩ dA` by conformal invariance, `metric_form_norm`). -/
def IsWeakSteklovEigenMet (τ : ℝ) (x : O.H1Met) : Prop :=
  ∀ y : O.H1Met, ∫ z in ball (0 : ℂ) 1, ⟪((x : O.MAmb).snd : ℂ → ℂ) z, ((y : O.MAmb).snd : ℂ → ℂ) z⟫_ℝ =
    τ * ∫ t in Ioc 0 (2 * π), O.lineDensity (Complex.exp (t * Complex.I)) *
      ((O.traceMet x : ℝ → ℝ) t * (O.traceMet y : ℝ → ℝ) t)

lemma isWeakSteklovEigenMet_iff (τ : ℝ) (x : O.H1Met) :
    O.IsWeakSteklovEigenMet τ x ↔ IsWeakSteklovEigen O.lineDensity τ (O.metricSobolevEquiv x) := by
  have hsnd : ∀ x : O.H1Met, ((O.metricSobolevEquiv x : H1) : Amb).snd = (x : O.MAmb).snd :=
    fun x => by rw [coe_metricSobolevEquiv, forget_snd]
  constructor
  · intro h y
    have := h (O.metricSobolevEquiv.symm y)
    rw [traceMet_apply, traceMet_apply, ContinuousLinearEquiv.apply_symm_apply] at this
    rw [hsnd, ← this, ← hsnd (O.metricSobolevEquiv.symm y),
      ContinuousLinearEquiv.apply_symm_apply]
  · intro h y
    have := h (O.metricSobolevEquiv y)
    rw [hsnd, hsnd] at this
    rw [traceMet_apply, traceMet_apply]
    exact this

/-- **Weak Steklov spectral theorem on the metric Sobolev space `H¹(O, g)`**, with
multiplicities; the eigenvalue sequence is the orbifold-smooth min–max spectrum of `O`. -/
theorem weak_spectral_theorem_met :
    ∃ (e : ℕ → O.H1Met) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = 0 ∧ Tendsto σ atTop atTop ∧
      (∀ k, e k ≠ 0 ∧ O.IsWeakSteklovEigenMet (σ k) (e k)) ∧
      (∀ τ, (∃ x : O.H1Met, x ≠ 0 ∧ O.IsWeakSteklovEigenMet τ x) ↔ ∃ k, σ k = τ) ∧
      (∀ τ, ∃ S : Submodule ℝ O.H1Met, (∀ x, x ∈ S ↔ O.IsWeakSteklovEigenMet τ x) ∧
        Module.finrank ℝ S = Set.ncard {k | σ k = τ}) ∧
      (∀ k, O.steklovSpectrum k = ENNReal.ofReal (σ k)) := by
  have hρ := O.continuousOn_lineDensity
  have hpos : ∀ z ∈ sphere (0 : ℂ) 1, 0 < O.lineDensity z := fun z hz => O.lineDensity_pos hz
  obtain ⟨e, σ, hmono, h0, htend, heig, hiff, -, hdim, hspec⟩ :=
    weighted_disk_spectral_theorem hρ hpos
  set P := O.metricSobolevEquiv
  refine ⟨fun k => P.symm (e k), σ, hmono, h0, htend, fun k => ⟨?_, ?_⟩, fun τ => ?_,
    fun τ => ?_, fun k => ?_⟩
  · simpa using (heig k).1
  · rw [O.isWeakSteklovEigenMet_iff, ContinuousLinearEquiv.apply_symm_apply]
    exact (heig k).2
  · rw [← hiff τ]
    constructor
    · rintro ⟨x, hx, hxe⟩
      exact ⟨P x, by simpa using hx, (O.isWeakSteklovEigenMet_iff τ x).1 hxe⟩
    · rintro ⟨y, hy, hye⟩
      refine ⟨P.symm y, by simpa using hy, ?_⟩
      rw [O.isWeakSteklovEigenMet_iff, ContinuousLinearEquiv.apply_symm_apply]
      exact hye
  · refine ⟨(weakEigenspace hρ τ).map (P.symm.toLinearEquiv : H1 →ₗ[ℝ] O.H1Met), fun x => ?_, ?_⟩
    · rw [Submodule.mem_map_equiv, mem_weakEigenspace hρ hpos, O.isWeakSteklovEigenMet_iff]
      rfl
    · rw [LinearEquiv.finrank_map_eq, hdim]
  · rw [O.prop_2_2_1]; exact hspec k

/-! ### The Riemannian orbifold variational spectrum and Proposition 2.2.1 -/

/-- **The Steklov spectrum of `O` as a Riemannian orbifold** (with multiplicities): the
Courant–Fischer min–max of `∫ |du|²_g dA_g / ∫_{∂O} (Tu)² ds_g` over `(k+1)`-dimensional
subspaces of the metric Sobolev space `H¹(O, g)`. -/
def metricSteklovEigenvalue (k : ℕ) : ℝ≥0∞ :=
  subspaceMinMax O.metricEnergy O.metricBoundaryMass k

/-- **Proposition 2.2.1 for the Riemannian orbifold variational spectrum.**  The min–max spectrum
of `O` on its metric Sobolev space `H¹(O, g)` equals the weighted Steklov spectrum of the disk with
weight `ρ_O = √λ|_𝕋` (the boundary line element of `O` in its conformal coordinate), and equals the
orbifold-smooth min–max spectrum `O.steklovSpectrum`, with multiplicities. -/
theorem prop_2_2_1_metric :
    O.metricSteklovEigenvalue = weightedSteklovSpectrum O.lineDensity ∧
      O.metricSteklovEigenvalue = O.steklovSpectrum := by
  have h : O.metricSteklovEigenvalue = weightedSteklovSpectrum O.lineDensity := by
    funext k
    rw [metricSteklovEigenvalue,
      subspaceMinMax_eq_of_equiv O.metricSobolevEquiv.toLinearEquiv O.metricEnergy_eq
        O.metricBoundaryMass_eq k, ← h1SteklovEigenvalue_eq_subspaceMinMax,
      weightedSteklovSpectrum, weightedSteklovEigenvalue_eq_h1 O.continuousOn_lineDensity]
  exact ⟨h, h.trans O.prop_2_2_1.symm⟩

end DiskOrbisurface

end SteklovOrb
