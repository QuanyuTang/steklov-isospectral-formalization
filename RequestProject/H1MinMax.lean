module

public import Mathlib
public import RequestProject.DiskH1
public import RequestProject.MinMaxApprox

/-!
# `H¹` min–max for the weighted Steklov problem on the disk equals the smooth-test min–max

The weighted Steklov Rayleigh quotient on `H¹(𝔻)` (`SteklovH1.H1`, the closure of smooth
functions in `L²(𝔻) ⊕₂ L²(𝔻; ℝ²)`, whose elements are `L²` functions with their `L²` weak
gradients) is `‖∇x‖²_{L²(𝔻)} / ∫₀^{2π} |Tx(t)|² ρ(e^{it}) dt`, where `T` is the trace operator.
`SteklovH1.h1SteklovEigenvalue ρ k` is its Courant–Fischer min–max value over
`(k+1)`-dimensional subspaces of `H¹(𝔻)` on which the boundary mass is positive definite.

Main result (`SteklovH1.weightedSteklovEigenvalue_eq_h1`): for every weight `ρ` continuous on the
unit circle and every `k`, `Steklov.weightedSteklovEigenvalue ρ k = h1SteklovEigenvalue ρ k`.
So the min–max over globally smooth test functions used in `MainTheorem` coincides with the
genuine `H¹` variational eigenvalues, for every index, i.e. including multiplicities.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal

noncomputable section

namespace SteklovH1

/-! ### Multiplication operators on `L²((0,2π])` -/

lemma memLp_mul_of_bound {w : ℝ → ℝ} (hw : Continuous w) {C : ℝ}
    (hC : ∀ᵐ t ∂μT, |w t| ≤ C) (f : Lp ℝ 2 μT) :
    MemLp (fun t => w t * f t) 2 μT :=
  MemLp.of_le_mul (c := C) (Lp.memLp f)
    (hw.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (by
      filter_upwards [hC] with t ht
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ht (norm_nonneg _))

/-- Multiplication by a continuous function bounded on `(0,2π]`, as a bounded operator. -/
def mulOp (w : ℝ → ℝ) (hw : Continuous w) (C : ℝ) (hC : ∀ᵐ t ∂μT, |w t| ≤ C) :
    Lp ℝ 2 μT →L[ℝ] Lp ℝ 2 μT :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_mul_of_bound hw hC f).toLp _
      map_add' := fun f g => by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_add f g] with t ht
        rw [ht, Pi.add_apply, mul_add]; rfl
      map_smul' := fun c f => by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [Lp.coeFn_smul c f] with t ht
        simp only [ht, Pi.smul_apply, smul_eq_mul]; ring }
    C
    (fun f => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_mul_of_bound hw hC f), hC] with t ht hCt
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [ht, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hCt (norm_nonneg _))

lemma mulOp_ae (w : ℝ → ℝ) (hw : Continuous w) (C : ℝ) (hC : ∀ᵐ t ∂μT, |w t| ≤ C)
    (f : Lp ℝ 2 μT) : (mulOp w hw C hC f : ℝ → ℝ) =ᵐ[μT] fun t => w t * f t :=
  MemLp.coeFn_toLp (memLp_mul_of_bound hw hC f)

/-! ### The `H¹` Rayleigh quotient and min–max -/

/-- Dirichlet energy of `x ∈ H¹(𝔻)`: the squared `L²(𝔻)` norm of its (weak) gradient. -/
def h1Energy (x : H1) : ℝ≥0∞ := ‖(x : Amb).snd‖ₑ ^ 2

/-- Weighted boundary mass of `x ∈ H¹(𝔻)`: `∫₀^{2π} |Tx(t)|² ρ(e^{it}) dt`, with `T` the trace. -/
def h1BoundaryMass (ρ : ℂ → ℝ) (x : H1) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 (2 * π),
    ‖(trace x : ℝ → ℝ) t‖ₑ ^ 2 * ENNReal.ofReal (ρ (Complex.exp (t * Complex.I)))

/-- Admissible `(k+1)`-dimensional subspaces of `H¹(𝔻)` (boundary mass positive definite). -/
def H1Admissible (ρ : ℂ → ℝ) (k : ℕ) (V : Submodule ℝ H1) : Prop :=
  Module.finrank ℝ V = k + 1 ∧ ∀ x ∈ V, x ≠ 0 → h1BoundaryMass ρ x ≠ 0

/-- The `k`-th variational eigenvalue of the weighted Steklov problem on `H¹(𝔻)`. -/
def h1SteklovEigenvalue (ρ : ℂ → ℝ) (k : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule ℝ H1) (_ : H1Admissible ρ k V),
    ⨆ (x : H1) (_ : x ∈ V) (_ : x ≠ 0), h1Energy x / h1BoundaryMass ρ x

/-! ### Comparison on smooth functions -/

@[simp] lemma h1BoundaryMass_zero (ρ : ℂ → ℝ) : h1BoundaryMass ρ 0 = 0 := by
  unfold h1BoundaryMass
  rw [map_zero]
  have : ∫⁻ t in Ioc 0 (2 * π), ‖((0 : Lp ℝ 2 μT) : ℝ → ℝ) t‖ₑ ^ 2 *
      ENNReal.ofReal (ρ (Complex.exp (t * Complex.I))) = ∫⁻ t in Ioc 0 (2 * π), 0 := by
    refine lintegral_congr_ae ?_
    filter_upwards [Lp.coeFn_zero ℝ 2 μT] with t ht
    rw [ht]; simp
  rw [this, lintegral_zero]

lemma h1BoundaryMass_embedH (ρ : ℂ → ℝ) (u : smoothFns) :
    h1BoundaryMass ρ (embedH u) = Steklov.weightedBoundaryMass ρ u := by
  unfold h1BoundaryMass Steklov.weightedBoundaryMass
  refine lintegral_congr_ae ?_
  filter_upwards [trace_embed_ae u] with t ht
  rw [ht]

lemma h1Energy_embedH (u : smoothFns) :
    h1Energy (embedH u) = Steklov.dirichletEnergy (Metric.ball 0 1) u :=
  enorm_embed_snd_sq u

/-- The boundary weight `√ρ(e^{it})`. -/
def bdryWeight (ρ : ℂ → ℝ) (t : ℝ) : ℝ := Real.sqrt (ρ (Complex.exp (t * Complex.I)))

lemma continuous_bdryWeight {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ (Metric.sphere 0 1)) :
    Continuous (bdryWeight ρ) := by
  unfold bdryWeight
  refine Real.continuous_sqrt.comp ?_
  refine hρ.comp_continuous (by fun_prop) (fun t => ?_)
  simp [Complex.norm_exp_ofReal_mul_I]

lemma exists_bdryWeight_bound {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ (Metric.sphere 0 1)) :
    ∃ C, ∀ᵐ t ∂μT, |bdryWeight ρ t| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    (continuous_bdryWeight hρ).continuousOn
  refine ⟨C, ?_⟩
  rw [ae_restrict_iff' measurableSet_Ioc]
  exact Eventually.of_forall (fun t ht => by
    simpa [Real.norm_eq_abs] using hC t (Ioc_subset_Icc_self ht))

lemma enorm_sq_bdryWeight (ρ : ℂ → ℝ) (t : ℝ) :
    ‖bdryWeight ρ t‖ₑ ^ 2 = ENNReal.ofReal (ρ (Complex.exp (t * Complex.I))) := by
  rw [enorm_sq_real, bdryWeight]
  rcases le_total 0 (ρ (Complex.exp (t * Complex.I))) with h | h
  · rw [Real.sq_sqrt h]
  · rw [Real.sqrt_eq_zero'.2 h, ENNReal.ofReal_of_nonpos h]; simp

lemma h1BoundaryMass_eq_enorm {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ (Metric.sphere 0 1)) {C : ℝ}
    (hC : ∀ᵐ t ∂μT, |bdryWeight ρ t| ≤ C) (x : H1) :
    h1BoundaryMass ρ x = ‖mulOp (bdryWeight ρ) (continuous_bdryWeight hρ) C hC (trace x)‖ₑ ^ 2 := by
  rw [show mulOp (bdryWeight ρ) (continuous_bdryWeight hρ) C hC (trace x) =
    (memLp_mul_of_bound (continuous_bdryWeight hρ) hC (trace x)).toLp _ from rfl, enorm_toLp_sq]
  unfold h1BoundaryMass
  refine lintegral_congr (fun t => ?_)
  rw [enorm_mul, mul_pow, enorm_sq_bdryWeight, mul_comm]

lemma enorm_sq_eq_ofReal {F : Type*} [NormedAddCommGroup F] (y : F) :
    ‖y‖ₑ ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

/-! ### The two inequalities -/

/-- Smooth admissible spaces embed into `H¹` admissible spaces with the same Rayleigh
quotients: `σ_k^{H¹} ≤ σ_k^{smooth}`. -/
theorem h1SteklovEigenvalue_le (ρ : ℂ → ℝ) (k : ℕ) :
    h1SteklovEigenvalue ρ k ≤ Steklov.weightedSteklovEigenvalue ρ k := by
  unfold Steklov.weightedSteklovEigenvalue Steklov.minMax
  refine le_iInf₂ (fun V hV => ?_)
  have hVs : V ≤ smoothFns := fun u hu => hV.1 u hu
  let f : V →ₗ[ℝ] H1 := embedH ∘ₗ Submodule.inclusion hVs
  have hf : ∀ v : V, f v = embedH ⟨v, hVs v.2⟩ := fun v => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hne
    have hv0 : (v : ℂ → ℝ) ≠ 0 := fun h => hne (Subtype.ext h)
    apply hV.2.2 v v.2 hv0
    have := h1BoundaryMass_embedH ρ ⟨v, hVs v.2⟩
    rw [← hf, hv] at this
    rw [← this, h1BoundaryMass_zero]
  let W : Submodule ℝ H1 := LinearMap.range f
  have hW : H1Admissible ρ k W := by
    refine ⟨?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hinj, hV.2.1]
    · rintro _ ⟨v, rfl⟩ hx
      have hv0 : (v : ℂ → ℝ) ≠ 0 := by
        intro h
        apply hx
        have : v = 0 := Subtype.ext h
        rw [this, map_zero]
      rw [hf, h1BoundaryMass_embedH]
      exact hV.2.2 v v.2 hv0
  refine iInf₂_le_of_le W hW ?_
  refine iSup₂_le (fun x hx => iSup_le (fun hx0 => ?_))
  obtain ⟨v, rfl⟩ := hx
  have hv0 : (v : ℂ → ℝ) ≠ 0 := by
    intro h
    apply hx0
    have : v = 0 := Subtype.ext h
    rw [this, map_zero]
  rw [hf, h1BoundaryMass_embedH, h1Energy_embedH]
  exact le_iSup₂_of_le (v : ℂ → ℝ) v.2 (le_iSup_of_le hv0 le_rfl)

/-- Density: `σ_k^{smooth} ≤ σ_k^{H¹}`. -/
theorem le_h1SteklovEigenvalue {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ (Metric.sphere 0 1)) (k : ℕ) :
    Steklov.weightedSteklovEigenvalue ρ k ≤ h1SteklovEigenvalue ρ k := by
  obtain ⟨C, hC⟩ := exists_bdryWeight_bound hρ
  set Bop : H1 →L[ℝ] Lp ℝ 2 μT := (mulOp (bdryWeight ρ) (continuous_bdryWeight hρ) C hC).comp
    trace with hBop
  set Aop : H1 →L[ℝ] Lp ℂ 2 μD := (ContinuousLinearMap.snd ℝ _ _).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap.comp H1.subtypeL) with hAop
  have hAx : ∀ x : H1, Aop x = (x : Amb).snd := fun x => rfl
  have hEx : ∀ x : H1, h1Energy x = ENNReal.ofReal (‖Aop x‖ ^ 2) := by
    intro x; rw [hAx, h1Energy, enorm_sq_eq_ofReal]
  have hBx : ∀ x : H1, h1BoundaryMass ρ x = ENNReal.ofReal (‖Bop x‖ ^ 2) := by
    intro x; rw [h1BoundaryMass_eq_enorm hρ hC, enorm_sq_eq_ofReal]; rfl
  unfold h1SteklovEigenvalue
  refine le_iInf₂ (fun W hW => ?_)
  set R := ⨆ (x : H1) (_ : x ∈ W) (_ : x ≠ 0), h1Energy x / h1BoundaryMass ρ x with hR
  refine le_of_forall_gt_imp_ge_of_dense (fun r hr => ?_)
  by_cases hrtop : r = ⊤
  · rw [hrtop]; exact le_top
  have hRtop : R ≠ ⊤ := ne_top_of_lt hr
  set M := R.toReal
  have hMr : M < r.toReal := by
    rw [ENNReal.toReal_lt_toReal hRtop hrtop]; exact hr
  -- the Rayleigh bound on `W`
  have hBne : ∀ x ∈ W, x ≠ 0 → Bop x ≠ 0 := by
    intro x hx hx0 h
    apply hW.2 x hx hx0
    rw [hBx, h, norm_zero]; simp
  have hM : ∀ x ∈ W, ‖Aop x‖ ^ 2 ≤ M * ‖Bop x‖ ^ 2 := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hq : h1Energy x / h1BoundaryMass ρ x ≤ R :=
      le_iSup₂_of_le x hx (le_iSup_of_le hx0 le_rfl)
    have hBpos : 0 < ‖Bop x‖ ^ 2 := by
      have := hBne x hx hx0; positivity
    rw [hEx, hBx, ENNReal.div_le_iff (ENNReal.ofReal_pos.2 hBpos).ne' ENNReal.ofReal_ne_top,
      ← ENNReal.ofReal_toReal hRtop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at hq
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hq
  obtain ⟨s, hs⟩ := exists_family_ratio_lt Aop Bop embedH denseRange_embedH W hW.1 hBne hM hMr
  -- the smooth test space spanned by the `s i`
  set V : Submodule ℝ (ℂ → ℝ) := Submodule.span ℝ (Set.range fun i => (s i : ℂ → ℝ)) with hV
  have hcomb : ∀ c : Fin (k + 1) → ℝ,
      (∑ i, c i • (s i : ℂ → ℝ)) = ((∑ i, c i • s i : smoothFns) : ℂ → ℝ) := by
    intro c; rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
  have hmemV : ∀ u ∈ V, ∃ c : Fin (k + 1) → ℝ, u = ∑ i, c i • (s i : ℂ → ℝ) := by
    intro u hu
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hu
    exact ⟨c, hc.symm⟩
  have hpos : ∀ c : Fin (k + 1) → ℝ, c ≠ 0 →
      Steklov.weightedBoundaryMass ρ (∑ i, c i • (s i : ℂ → ℝ)) ≠ 0 ∧
      Steklov.dirichletEnergy (Metric.ball 0 1) (∑ i, c i • (s i : ℂ → ℝ)) /
        Steklov.weightedBoundaryMass ρ (∑ i, c i • (s i : ℂ → ℝ)) ≤ r := by
    intro c hc
    have h := hs c hc
    rw [hcomb, ← h1BoundaryMass_embedH, ← h1Energy_embedH, hEx, hBx]
    have hBpos : 0 < ‖Bop (embedH (∑ i, c i • s i))‖ ^ 2 := by
      rcases (sq_nonneg ‖Bop (embedH (∑ i, c i • s i))‖).lt_or_eq with h' | h'
      · exact h'
      · rw [← h', mul_zero] at h
        exact absurd h (not_lt.2 (sq_nonneg _))
    refine ⟨(ENNReal.ofReal_pos.2 hBpos).ne', ?_⟩
    rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.2 hBpos).ne' ENNReal.ofReal_ne_top,
      ← ENNReal.ofReal_toReal hrtop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal h.le
  have hli : LinearIndependent ℝ (fun i => (s i : ℂ → ℝ)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push_neg at hne
    have hc0 : c ≠ 0 := fun h => by
      obtain ⟨i, hi⟩ := hne; exact hi (by rw [h]; rfl)
    apply (hpos c hc0).1
    rw [hc]
    simp [Steklov.weightedBoundaryMass]
  have hVadm : Steklov.AdmissibleSpace (Steklov.weightedBoundaryMass ρ) k V := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      have : V ≤ smoothFns := by
        rw [hV, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (s i).2
      exact this hu
    · rw [hV, finrank_span_eq_card hli, Fintype.card_fin]
    · intro u hu hu0
      obtain ⟨c, rfl⟩ := hmemV u hu
      have hc0 : c ≠ 0 := by
        rintro rfl; apply hu0; simp
      exact (hpos c hc0).1
  unfold Steklov.weightedSteklovEigenvalue Steklov.minMax
  refine iInf₂_le_of_le V hVadm ?_
  refine iSup₂_le (fun u hu => iSup_le (fun hu0 => ?_))
  obtain ⟨c, rfl⟩ := hmemV u hu
  have hc0 : c ≠ 0 := by
    rintro rfl; apply hu0; simp
  exact (hpos c hc0).2

/-- **The `H¹` and smooth-test min–max values agree**, for every index `k` (hence the
weighted Steklov spectra, with multiplicities, coincide). -/
theorem weightedSteklovEigenvalue_eq_h1 {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ (Metric.sphere 0 1))
    (k : ℕ) : Steklov.weightedSteklovEigenvalue ρ k = h1SteklovEigenvalue ρ k :=
  le_antisymm (le_h1SteklovEigenvalue hρ k) (h1SteklovEigenvalue_le ρ k)

end SteklovH1
