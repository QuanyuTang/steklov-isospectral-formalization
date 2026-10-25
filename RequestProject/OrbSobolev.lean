module

public import RequestProject.Orbisurface
public import RequestProject.C1H1
public import RequestProject.DiskSpectral

/-!
# The orbifold Sobolev space of a disk-type orbisurface and its weak Steklov spectrum

For a `SteklovOrb.DiskOrbisurface` `O` (conformal coordinate `z ∈ 𝔻̄`):

* `DiskOrbisurface.orbEmbed u`: the graph `(u, ∇u)` of an orbifold-smooth function in
  `L²(𝔻) ⊕₂ L²(𝔻; ℝ²)` (its gradient is square integrable: `IsOrbSmooth.memLp_grad`; recall
  `∫ |du|²_g dA_g = ∫ |∇u|² dA`);
* `DiskOrbisurface.H1Orb`: the **orbifold Sobolev space**, the closure of the span of these graphs;
* `H1Orb_eq`: `H1Orb = H¹(𝔻)` — removal of the cone points at the Sobolev level (orbifold-smooth
  graphs are approximated by smooth ones via the logarithmic cut-off correction
  `SteklovBranch.corr`, `orbEmbed_mem_H1`);
* `weak_spectral_theorem_orb`: the weak Steklov problem of `O` posed on `H1Orb`
  (Dirichlet form against the boundary form `∫_{∂O} Tx Ty ds_g`) has a spectrum with
  multiplicities, equal to `O.steklovSpectrum` (orbifold-smooth min–max).

The `L²` part of the Sobolev norm is taken with respect to Euclidean area in the conformal
coordinate (the Dirichlet part is the metric one, by conformal invariance).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Real ComplexConjugate InnerProductSpace

noncomputable section

namespace SteklovOrb

namespace DiskOrbisurface

open Steklov SteklovH1 SteklovBranch

variable (O : DiskOrbisurface)

lemma measurable_grad (u : ℂ → ℝ) : Measurable (grad u) :=
  (InnerProductSpace.toDual ℝ ℂ).symm.continuous.measurable.comp (measurable_fderiv ℝ u)

lemma IsOrbSmooth.memLp_grad {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) : MemLp (grad u) 2 μD := by
  refine memLp_two_of_lintegral (measurable_grad u).aestronglyMeasurable ?_
  have h := hu.dirichletEnergy_lt_top
  unfold dirichletEnergy at h
  refine lt_of_eq_of_lt (lintegral_congr fun z => ?_) h
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, norm_grad]

/-- The graph `(u, ∇u)` of an orbifold-smooth function in `L²(𝔻) ⊕₂ L²(𝔻; ℝ²)`. -/
def orbEmbed (u : ℂ → ℝ) (hu : O.IsOrbSmooth u) : Amb :=
  WithLp.toLp 2 ((memLp_disk hu.continuous).toLp u, (hu.memLp_grad).toLp (grad u))

/-- **The orbifold Sobolev space** `H¹(O)`: closure of the span of the graphs of orbifold-smooth
functions. -/
def H1Orb : Submodule ℝ Amb :=
  (Submodule.span ℝ (Set.range fun p : {u : ℂ → ℝ // O.IsOrbSmooth u} =>
    O.orbEmbed p.1 p.2)).topologicalClosure

/-- `L²` convergence of the logarithmic cut-off correction. -/
theorem tendsto_eLpNorm_corr_sub {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) :
    Tendsto (fun r => eLpNorm (corr O.S r u - u) 2 μD) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hM⟩ := hu.bounded
  apply tendsto_zero_of_sq
  simp_rw [eLpNorm_two_sq]
  have hlim := tendsto_lintegral_filter_of_dominated_convergence (μ := μD) (l := 𝓝[>] (0:ℝ))
    (F := fun r z => ‖(corr O.S r u - u) z‖ₑ ^ 2) (f := fun _ => 0)
    (fun _ => ENNReal.ofReal ((O.S.card * (2 * |M|)) ^ 2)) ?_ ?_ ?_ ?_
  · simpa using hlim
  · filter_upwards [eventually_goodRadius O.S (fun s hs => O.S_mem hs)] with r hr
    have h1 : Continuous (corr O.S r u) := (corr_contDiff hr (by rw [O.coe_S]; exact hu.1)).continuous
    exact ((h1.sub hu.continuous).measurable.enorm).pow_const 2
  · refine Eventually.of_forall fun r => ?_
    rw [ae_restrict_iff' measurableSet_ball]
    refine Eventually.of_forall fun z hz => ?_
    show ‖(corr O.S r u - u) z‖ₑ ^ 2 ≤ _
    rw [corr_sub_eq, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) ?_ 2)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ s ∈ O.S, ‖logCut s r z * (u s - u z)‖ ≤ ∑ s ∈ O.S, 2 * |M| :=
          Finset.sum_le_sum fun s hs => by
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (logCut_nonneg z)]
            have hus := hM s (mem_ball_zero_iff.2 (O.S_mem hs))
            have huz := hM z hz
            calc logCut s r z * |u s - u z| ≤ 1 * |u s - u z| :=
                  mul_le_mul_of_nonneg_right (logCut_le_one z) (abs_nonneg _)
              _ ≤ 2 * |M| := by
                  rw [one_mul]
                  have := abs_sub (u s) (u z)
                  have h1 : |M| ≥ M := le_abs_self M
                  linarith
      _ = O.S.card * (2 * |M|) := by rw [Finset.sum_const, nsmul_eq_mul]
  · rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  · have h0 : volume (O.S : Set ℂ) = 0 := O.S.finite_toSet.measure_zero _
    filter_upwards [ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h0)] with z hz
    have hev : ∀ᶠ r in 𝓝[>] (0:ℝ), ∀ s ∈ O.S, r < ‖z - s‖ := by
      rw [Finset.eventually_all]
      intro s hs
      have : 0 < ‖z - s‖ := norm_pos_iff.2 (sub_ne_zero.2 fun h => hz (h ▸ hs))
      exact nhdsWithin_le_nhds (eventually_lt_nhds this)
    have hev1 : ∀ᶠ r in 𝓝[>] (0:ℝ), r < 1 := nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev, hev1, self_mem_nhdsWithin] with r h1 h2 h3
    have hsum : ∑ s ∈ O.S, logCut s r z * (u s - u z) = 0 := Finset.sum_eq_zero fun s hs => by
      rw [logCut_eq_zero h3 h2 (h1 s hs).le, zero_mul]
    have hc := congrFun (corr_sub_eq O.S r u) z
    simp only [Pi.sub_apply] at hc
    simp [hc, hsum]

/-- **Orbifold-smooth graphs lie in `H¹(𝔻)`** (cone points have zero capacity). -/
theorem orbEmbed_mem_H1 {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) : O.orbEmbed u hu ∈ H1 := by
  show O.orbEmbed u hu ∈ closure (LinearMap.range embed : Set Amb)
  rw [Metric.mem_closure_iff]
  intro ε hε
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
  refine ⟨embed ⟨_, hv⟩, ⟨⟨_, hv⟩, rfl⟩, ?_⟩
  rw [dist_eq_norm]
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
      refine eLpNorm_congr_norm_ae ?_
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

/-- **The orbifold Sobolev space is `H¹(𝔻)`** (in the conformal coordinate). -/
theorem H1Orb_eq : O.H1Orb = H1 := by
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
    rw [Submodule.span_le]
    rintro _ ⟨⟨u, hu⟩, rfl⟩
    exact O.orbEmbed_mem_H1 hu
  · refine Submodule.topologicalClosure_mono ?_
    rintro _ ⟨u, rfl⟩
    exact Submodule.subset_span ⟨⟨u, O.isOrbSmooth_of_contDiff u.2⟩, rfl⟩

/-- The trace `H¹(O) → L²(∂O)` in the boundary parametrization (the disk trace, via
`H1Orb_eq`). -/
def traceOrb (x : O.H1Orb) : Lp ℝ 2 μT := trace ⟨x, O.H1Orb_eq ▸ x.2⟩

/-- **Weak Steklov eigenfunctions of the orbisurface** posed on `H¹(O)`:
`∫ ⟨∇x, ∇y⟩ dA = τ ∫_{∂O} Tx Ty ds_g` for all `y ∈ H¹(O)`. -/
def IsWeakSteklovEigenOrb (τ : ℝ) (x : O.H1Orb) : Prop :=
  ∀ y : O.H1Orb, ∫ z in ball (0 : ℂ) 1, ⟪((x : Amb).snd : ℂ → ℂ) z, ((y : Amb).snd : ℂ → ℂ) z⟫_ℝ =
    τ * ∫ t in Ioc 0 (2 * π), O.lineDensity (Complex.exp (t * Complex.I)) *
      ((O.traceOrb x : ℝ → ℝ) t * (O.traceOrb y : ℝ → ℝ) t)

/-- `H¹(O) ≃ H¹(𝔻)` (equality of submodules, as a linear isometry equivalence). -/
def h1OrbEquiv : O.H1Orb ≃ₗᵢ[ℝ] H1 :=
  LinearIsometryEquiv.ofEq _ _ O.H1Orb_eq

lemma isWeakSteklovEigenOrb_iff (τ : ℝ) (x : O.H1Orb) :
    O.IsWeakSteklovEigenOrb τ x ↔ IsWeakSteklovEigen O.lineDensity τ (O.h1OrbEquiv x) := by
  constructor
  · intro h y
    exact h (O.h1OrbEquiv.symm y)
  · intro h y
    exact h (O.h1OrbEquiv y)

/-- **Weak Steklov spectral theorem for the orbisurface `O`**, posed on its Sobolev space, with
multiplicities; the eigenvalue sequence is the orbifold-smooth min–max spectrum of `O`. -/
theorem weak_spectral_theorem_orb :
    ∃ (e : ℕ → O.H1Orb) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = 0 ∧ Tendsto σ atTop atTop ∧
      (∀ k, e k ≠ 0 ∧ O.IsWeakSteklovEigenOrb (σ k) (e k)) ∧
      (∀ τ, (∃ x : O.H1Orb, x ≠ 0 ∧ O.IsWeakSteklovEigenOrb τ x) ↔ ∃ k, σ k = τ) ∧
      (∀ τ, ∃ S : Submodule ℝ O.H1Orb, (∀ x, x ∈ S ↔ O.IsWeakSteklovEigenOrb τ x) ∧
        Module.finrank ℝ S = Set.ncard {k | σ k = τ}) ∧
      (∀ k, O.steklovSpectrum k = ENNReal.ofReal (σ k)) := by
  have hρ := O.continuousOn_lineDensity
  have hpos : ∀ z ∈ sphere (0 : ℂ) 1, 0 < O.lineDensity z := fun z hz => O.lineDensity_pos hz
  obtain ⟨e, σ, hmono, h0, htend, heig, hiff, -, hdim, hspec⟩ :=
    weighted_disk_spectral_theorem hρ hpos
  set P := O.h1OrbEquiv
  refine ⟨fun k => P.symm (e k), σ, hmono, h0, htend, fun k => ⟨?_, ?_⟩, fun τ => ?_,
    fun τ => ?_, fun k => ?_⟩
  · simpa using (heig k).1
  · rw [O.isWeakSteklovEigenOrb_iff, LinearIsometryEquiv.apply_symm_apply]
    exact (heig k).2
  · rw [← hiff τ]
    constructor
    · rintro ⟨x, hx, hxe⟩
      exact ⟨P x, by simpa using hx, (O.isWeakSteklovEigenOrb_iff τ x).1 hxe⟩
    · rintro ⟨y, hy, hye⟩
      refine ⟨P.symm y, by simpa using hy, ?_⟩
      rw [O.isWeakSteklovEigenOrb_iff, LinearIsometryEquiv.apply_symm_apply]
      exact hye
  · refine ⟨(weakEigenspace hρ τ).map (P.symm.toLinearEquiv : H1 →ₗ[ℝ] O.H1Orb), fun x => ?_, ?_⟩
    · rw [Submodule.mem_map_equiv, mem_weakEigenspace hρ hpos, O.isWeakSteklovEigenOrb_iff]
      rfl
    · rw [LinearEquiv.finrank_map_eq, hdim]
  · rw [O.prop_2_2_1]; exact hspec k

end DiskOrbisurface

end SteklovOrb
