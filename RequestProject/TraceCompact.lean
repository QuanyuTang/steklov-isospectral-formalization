module

public import Mathlib
public import RequestProject.DiskH1
public import RequestProject.CompactCriterion

/-!
# Compactness of the trace `H¹(𝔻) → L²(𝕋)`

`SteklovH1.isCompactOperator_trace`: the trace operator `SteklovH1.trace` is compact.

Proof (elementary, no Fourier analysis). Split `(0, 2π]` into `N` arcs `I_j` of length `h = 2π/N`
and fix `r₀ ∈ [1/2, 1)`. For a smooth `u`, `ρ ∈ [r₀, 1]` and `θ ∈ I_j = (t_j, t_j + h]`,
* radially, `|u(e^{iθ}) - u(ρe^{iθ})|² ≤ (1-r₀) ∫_{r₀}^1 |∇u(σe^{iθ})|² dσ`;
* angularly, `|u(ρe^{iθ}) - u(ρe^{it_j})|² ≤ h ∫_{I_j} |∇u(ρe^{iψ})|² dψ`.
Hence the step function `w = ∑ u(ρe^{it_j}) 1_{I_j}` satisfies
`‖Tu - w‖² ≤ 2(1-r₀) X + 2h² E(ρ)` with `X = ∫∫ |∇u|²` over the polar rectangle and
`E(ρ) = ∫_0^{2π} |∇u(ρe^{iψ})|² dψ`; choosing `ρ` minimizing `E` gives
`dist(Tu, F_N)² ≤ (2(1-r₀) + 2h²/(1-r₀)) · 2‖∇u‖²` where `F_N` is the `N`-dimensional space of
step functions. By density this holds on `H¹(𝔻)`, so `T` is a uniform limit of operators with
finite-dimensional range, hence compact.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal

noncomputable section

namespace SteklovH1

/-- Cauchy–Schwarz on an interval: `(∫_a^b g)² ≤ (b - a) ∫_a^b g²`. -/
lemma sq_intervalIntegral_le {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in a..b, g x) ^ 2 ≤ (b - a) * ∫ x in a..b, g x ^ 2 := by
  rcases hab.lt_or_eq with hlt | heq
  · set L := b - a with hL
    have hLpos : 0 < L := by rw [hL]; linarith
    set I := ∫ x in a..b, g x
    set m := I / L
    have h0 : 0 ≤ ∫ x in a..b, (g x - m) ^ 2 :=
      intervalIntegral.integral_nonneg hab (fun x _ => sq_nonneg _)
    have hexp : ∫ x in a..b, (g x - m) ^ 2 = (∫ x in a..b, g x ^ 2) - 2 * m * I + m ^ 2 * L := by
      have : (fun x => (g x - m) ^ 2) = fun x => (g x ^ 2 - 2 * m * g x) + m ^ 2 := by
        ext; ring
      rw [this, intervalIntegral.integral_add, intervalIntegral.integral_sub,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
      · simp [hL, smul_eq_mul]; ring
      · exact (hg.pow 2).intervalIntegrable _ _
      · exact (continuous_const.mul hg).intervalIntegrable _ _
      · exact ((hg.pow 2).sub (continuous_const.mul hg)).intervalIntegrable _ _
      · exact continuous_const.intervalIntegrable _ _
    rw [hexp] at h0
    have hI : I = m * L := by simp only [m]; field_simp
    rw [hI] at h0 ⊢
    nlinarith
  · subst heq; simp

/-- Radial estimate. -/
lemma radial_sq_le {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) (θ : ℝ) {ρ : ℝ} (hρ : ρ ≤ 1) :
    (u (Complex.exp (θ * Complex.I)) - u (ρ * Complex.exp (θ * Complex.I))) ^ 2 ≤
      (1 - ρ) * ∫ σ in ρ..1, ‖fderiv ℝ u (σ * Complex.exp (θ * Complex.I))‖ ^ 2 := by
  set e : ℂ := Complex.exp (θ * Complex.I) with he
  have hne : ‖e‖ = 1 := by rw [he, Complex.norm_exp_ofReal_mul_I]
  have hcD : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hc : Continuous fun r : ℝ => (r : ℂ) * e := by fun_prop
  have hgc : Continuous fun r : ℝ => fderiv ℝ u (r * e) e := (hcD.comp hc).clm_apply continuous_const
  have hder : ∀ r : ℝ, HasDerivAt (fun r : ℝ => u (r * e)) (fderiv ℝ u (r * e) e) r := by
    intro r
    have hγ : HasDerivAt (fun r : ℝ => (r : ℂ) * e) e r := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const e)
    have := (hu.differentiable one_ne_zero (r * e)).hasFDerivAt.comp_hasDerivAt r hγ
    first
      | exact this
      | simpa [Function.comp_def] using this
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := ρ) (b := 1)
    (fun r _ => hder r) (hgc.intervalIntegrable _ _)
  simp only [Complex.ofReal_one, one_mul] at hFTC
  rw [← hFTC]
  refine (sq_intervalIntegral_le hgc hρ).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (by linarith)
  refine intervalIntegral.integral_mono_on hρ ((hgc.pow 2).intervalIntegrable _ _)
    (((hcD.comp hc).norm.pow 2).intervalIntegrable _ _) (fun r _ => ?_)
  have := (fderiv ℝ u (r * e)).le_opNorm e
  rw [hne, mul_one] at this
  have h2 : |fderiv ℝ u (r * e) e| ≤ ‖fderiv ℝ u (r * e)‖ := by simpa [Real.norm_eq_abs] using this
  nlinarith [abs_nonneg (fderiv ℝ u (r * e) e), sq_abs (fderiv ℝ u (r * e) e)]

/-- Angular estimate. -/
lemma angular_sq_le {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {t h θ : ℝ} (hθ : θ ∈ Icc t (t + h)) :
    (u (ρ * Complex.exp (θ * Complex.I)) - u (ρ * Complex.exp (t * Complex.I))) ^ 2 ≤
      h * ∫ ψ in t..(t + h), ‖fderiv ℝ u (ρ * Complex.exp (ψ * Complex.I))‖ ^ 2 := by
  obtain ⟨htθ, hθh⟩ := hθ
  have hcD : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  set γ : ℝ → ℂ := fun ψ => (ρ : ℂ) * Complex.exp (ψ * Complex.I) with hγdef
  set γ' : ℝ → ℂ := fun ψ => (ρ : ℂ) * Complex.exp (ψ * Complex.I) * Complex.I with hγ'def
  have hγc : Continuous γ := by fun_prop
  have hγ'c : Continuous γ' := by fun_prop
  have hγd : ∀ ψ : ℝ, HasDerivAt γ (γ' ψ) ψ := by
    intro ψ
    have h1 : HasDerivAt (fun ψ : ℝ => (ψ : ℂ) * Complex.I) Complex.I ψ := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := ψ)).mul_const Complex.I)
    have h2 := (h1.cexp).const_mul (ρ : ℂ)
    simpa [hγdef, hγ'def, mul_assoc] using h2
  have hgc : Continuous fun ψ : ℝ => fderiv ℝ u (γ ψ) (γ' ψ) :=
    (hcD.comp hγc).clm_apply hγ'c
  have hder : ∀ ψ : ℝ, HasDerivAt (fun ψ : ℝ => u (γ ψ)) (fderiv ℝ u (γ ψ) (γ' ψ)) ψ := by
    intro ψ
    exact (hu.differentiable one_ne_zero (γ ψ)).hasFDerivAt.comp_hasDerivAt ψ (hγd ψ)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := t) (b := θ)
    (fun r _ => hder r) (hgc.intervalIntegrable _ _)
  change (u (γ θ) - u (γ t)) ^ 2 ≤ _
  rw [← hFTC]
  have hbound : ∀ ψ : ℝ, (fderiv ℝ u (γ ψ) (γ' ψ)) ^ 2 ≤ ‖fderiv ℝ u (γ ψ)‖ ^ 2 := by
    intro ψ
    have hn : ‖γ' ψ‖ ≤ 1 := by
      simp only [hγ'def, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, mul_one,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
      exact hρ1
    have := (fderiv ℝ u (γ ψ)).le_opNorm (γ' ψ)
    have h2 : |fderiv ℝ u (γ ψ) (γ' ψ)| ≤ ‖fderiv ℝ u (γ ψ)‖ := by
      have h3 : ‖fderiv ℝ u (γ ψ)‖ * ‖γ' ψ‖ ≤ ‖fderiv ℝ u (γ ψ)‖ :=
        mul_le_of_le_one_right (norm_nonneg _) hn
      simpa [Real.norm_eq_abs] using this.trans h3
    nlinarith [abs_nonneg (fderiv ℝ u (γ ψ) (γ' ψ)), sq_abs (fderiv ℝ u (γ ψ) (γ' ψ))]
  have hNc : Continuous fun ψ : ℝ => ‖fderiv ℝ u (γ ψ)‖ ^ 2 := ((hcD.comp hγc).norm.pow 2)
  calc (∫ ψ in t..θ, fderiv ℝ u (γ ψ) (γ' ψ)) ^ 2
      ≤ (θ - t) * ∫ ψ in t..θ, (fderiv ℝ u (γ ψ) (γ' ψ)) ^ 2 := sq_intervalIntegral_le hgc htθ
    _ ≤ (θ - t) * ∫ ψ in t..θ, ‖fderiv ℝ u (γ ψ)‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by linarith)
        exact intervalIntegral.integral_mono_on htθ ((hgc.pow 2).intervalIntegrable _ _)
          (hNc.intervalIntegrable _ _) (fun ψ _ => hbound ψ)
    _ ≤ h * ∫ ψ in t..(t + h), ‖fderiv ℝ u (γ ψ)‖ ^ 2 := by
        have hI0 : 0 ≤ ∫ ψ in t..θ, ‖fderiv ℝ u (γ ψ)‖ ^ 2 :=
          intervalIntegral.integral_nonneg htθ (fun _ _ => by positivity)
        have hmono : ∫ ψ in t..θ, ‖fderiv ℝ u (γ ψ)‖ ^ 2 ≤
            ∫ ψ in t..(t + h), ‖fderiv ℝ u (γ ψ)‖ ^ 2 :=
          intervalIntegral.integral_mono_interval le_rfl htθ hθh
            (Eventually.of_forall (fun _ => by positivity)) (hNc.intervalIntegrable _ _)
        calc (θ - t) * ∫ ψ in t..θ, ‖fderiv ℝ u (γ ψ)‖ ^ 2
            ≤ h * ∫ ψ in t..θ, ‖fderiv ℝ u (γ ψ)‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (by linarith) hI0
          _ ≤ h * ∫ ψ in t..(t + h), ‖fderiv ℝ u (γ ψ)‖ ^ 2 :=
              mul_le_mul_of_nonneg_left hmono (by linarith)

/-! ### Step functions on the circle -/

/-- Grid points `t_j = j · 2π / N`. -/
def gridPt (N : ℕ) (j : ℕ) : ℝ := j * (2 * π / N)

lemma gridPt_succ (N j : ℕ) : gridPt N (j + 1) = gridPt N j + 2 * π / N := by
  unfold gridPt; push_cast; ring

lemma gridPt_zero (N : ℕ) : gridPt N 0 = 0 := by simp [gridPt]

lemma gridPt_N {N : ℕ} (hN : 0 < N) : gridPt N N = 2 * π := by
  unfold gridPt; field_simp

lemma gridPt_mono (N : ℕ) : Monotone (gridPt N) := by
  intro a b hab
  unfold gridPt
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (by positivity)

lemma gridPt_lt_iff {N : ℕ} (hN : 0 < N) {a b : ℕ} : gridPt N a < gridPt N b ↔ a < b := by
  unfold gridPt
  have hh : 0 < 2 * π / N := by positivity
  rw [mul_lt_mul_iff_left₀ hh]; exact_mod_cast Iff.rfl

/-- The `j`-th arc `(t_j, t_{j+1}]`. -/
def arc (N j : ℕ) : Set ℝ := Ioc (gridPt N j) (gridPt N (j + 1))

lemma arc_disjoint {N : ℕ} (hN : 0 < N) {i j : ℕ} (hij : i ≠ j) : Disjoint (arc N i) (arc N j) := by
  rw [Set.disjoint_left]
  rintro θ ⟨h1, h2⟩ ⟨h3, h4⟩
  have a1 : i < j + 1 := (gridPt_lt_iff hN).1 (h1.trans_le h4)
  have a2 : j < i + 1 := (gridPt_lt_iff hN).1 (h3.trans_le h2)
  omega

lemma iUnion_arc {N : ℕ} (hN : 0 < N) : (⋃ j : Fin N, arc N j) = Ioc 0 (2 * π) := by
  ext θ
  simp only [mem_iUnion, arc, mem_Ioc]
  constructor
  · rintro ⟨j, h1, h2⟩
    refine ⟨lt_of_le_of_lt ?_ h1, h2.trans ?_⟩
    · rw [← gridPt_zero N]; exact gridPt_mono N (Nat.zero_le _)
    · rw [← gridPt_N hN]; exact gridPt_mono N (by omega)
  · rintro ⟨h1, h2⟩
    have hh : 0 < 2 * π / N := by positivity
    set q := θ / (2 * π / N) with hq
    have hq0 : 0 < q := div_pos h1 hh
    have hqN : q ≤ N := by
      rw [hq, div_le_iff₀ hh]
      calc θ ≤ 2 * π := h2
        _ = N * (2 * π / N) := by field_simp
    set k := ⌈q⌉₊ with hk
    have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by
      rw [hk]; exact (Nat.ceil_pos.2 hq0).ne')
    have hkN : k ≤ N := Nat.ceil_le.2 hqN
    refine ⟨⟨k - 1, by omega⟩, ?_, ?_⟩
    · simp only [gridPt]
      have : ((k - 1 : ℕ) : ℝ) < q := by
        have := Nat.ceil_lt_add_one hq0.le
        rw [← hk] at this
        rw [Nat.cast_sub hk1]; push_cast; linarith
      calc ((k - 1 : ℕ) : ℝ) * (2 * π / N) < q * (2 * π / N) :=
            mul_lt_mul_of_pos_right this hh
        _ = θ := by rw [hq]; field_simp
    · simp only [gridPt]
      have : q ≤ ((k - 1 + 1 : ℕ) : ℝ) := by
        rw [Nat.sub_add_cancel hk1]; exact Nat.le_ceil q
      calc θ = q * (2 * π / N) := by rw [hq]; field_simp
        _ ≤ ((k - 1 + 1 : ℕ) : ℝ) * (2 * π / N) := mul_le_mul_of_nonneg_right this hh.le

/-- Step function with value `c j` on the `j`-th arc. -/
def stepFn (N : ℕ) (c : Fin N → ℝ) (θ : ℝ) : ℝ :=
  ∑ j : Fin N, (arc N j).indicator (fun _ => c j) θ

lemma stepFn_eq {N : ℕ} (hN : 0 < N) (c : Fin N → ℝ) {j : Fin N} {θ : ℝ} (hθ : θ ∈ arc N j) :
    stepFn N c θ = c j := by
  unfold stepFn
  rw [Finset.sum_eq_single j]
  · rw [indicator_of_mem hθ]
  · intro i _ hij
    have hne : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
    rw [indicator_of_notMem (Set.disjoint_right.1 (arc_disjoint hN hne) hθ)]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma measurable_stepFn (N : ℕ) (c : Fin N → ℝ) : Measurable (stepFn N c) := by
  unfold stepFn
  refine Finset.measurable_sum _ (fun j _ => ?_)
  exact measurable_const.indicator measurableSet_Ioc

lemma memLp_stepFn (N : ℕ) (c : Fin N → ℝ) : MemLp (stepFn N c) 2 μT := by
  refine MemLp.of_bound (measurable_stepFn N c).aestronglyMeasurable (∑ j, |c j|) ?_
  refine Eventually.of_forall (fun θ => ?_)
  unfold stepFn
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => ?_))
  by_cases h : θ ∈ arc N j
  · rw [indicator_of_mem h, Real.norm_eq_abs]
  · rw [indicator_of_notMem h, norm_zero]; exact abs_nonneg _

/-- Step functions as elements of `L²((0,2π])`. -/
def stepMap (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] Lp ℝ 2 μT where
  toFun c := (memLp_stepFn N c).toLp _
  map_add' c d := by
    rw [← MemLp.toLp_add]
    congr 1
    ext θ
    simp only [stepFn, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : θ ∈ arc N j
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]
  map_smul' a c := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    congr 1
    ext θ
    simp only [stepFn, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    by_cases h : θ ∈ arc N j
    · simp [indicator_of_mem h]
    · simp [indicator_of_notMem h]

/-- The `N`-dimensional space of step functions. -/
def stepSpace (N : ℕ) : Submodule ℝ (Lp ℝ 2 μT) := LinearMap.range (stepMap N)

instance (N : ℕ) : FiniteDimensional ℝ (stepSpace N) := LinearMap.finiteDimensional_range _

/-! ### Integral bookkeeping -/

/-- Fubini for continuous functions on a rectangle (interval integrals). -/
lemma intervalIntegral_swap {F : ℝ → ℝ → ℝ} (hF : Continuous (Function.uncurry F))
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, F x y = ∫ y in c..d, ∫ x in a..b, F x y := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  refine integral_integral_swap ?_
  rw [Measure.prod_restrict]
  have : IntegrableOn (Function.uncurry F) (Icc a b ×ˢ Icc c d) :=
    hF.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  rw [← Measure.volume_eq_prod]
  exact this.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- The polar annulus `r₀ < σ < 1` (`r₀ ≥ 1/2`) has `∫∫ H dσ dθ ≤ 2 ∫_𝔻 H` for `H ≥ 0`. -/
lemma polar_annulus_le {H : ℂ → ℝ} (hH : Continuous H) (hH0 : ∀ z, 0 ≤ H z) {r₀ : ℝ}
    (hr0 : 1 / 2 ≤ r₀) (hr1 : r₀ ≤ 1) :
    ∫ θ in (0:ℝ)..(2 * π), ∫ σ in r₀..1, H (σ * Complex.exp (θ * Complex.I)) ≤
      2 * ∫ z in Metric.ball (0:ℂ) 1, H z := by
  rw [← integral_rays_eq_disk hH, ← intervalIntegral.integral_const_mul]
  have hc : ∀ θ : ℝ, Continuous fun σ : ℝ => H (σ * Complex.exp (θ * Complex.I)) := by
    intro θ; fun_prop
  refine intervalIntegral.integral_mono_on (by positivity) ?_ ?_ (fun θ _ => ?_)
  · exact (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (θ σ : ℝ) => H (σ * Complex.exp (θ * Complex.I))) (by fun_prop) r₀ 1).intervalIntegrable _ _
  · exact (continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (θ σ : ℝ) => σ * H (σ * Complex.exp (θ * Complex.I))) (by fun_prop) 0 1)).intervalIntegrable _ _
  · rw [← intervalIntegral.integral_const_mul]
    calc ∫ σ in r₀..1, H (σ * Complex.exp (θ * Complex.I))
        ≤ ∫ σ in r₀..1, 2 * (σ * H (σ * Complex.exp (θ * Complex.I))) := by
          refine intervalIntegral.integral_mono_on hr1 ((hc θ).intervalIntegrable _ _)
            ((continuous_const.mul (continuous_id.mul (hc θ))).intervalIntegrable _ _)
            (fun σ hσ => ?_)
          have := hH0 (σ * Complex.exp (θ * Complex.I))
          nlinarith [hσ.1]
      _ ≤ ∫ σ in (0:ℝ)..1, 2 * (σ * H (σ * Complex.exp (θ * Complex.I))) := by
          refine intervalIntegral.integral_mono_interval (by linarith) hr1 le_rfl ?_
            ((continuous_const.mul (continuous_id.mul (hc θ))).intervalIntegrable _ _)
          rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
          exact Eventually.of_forall (fun σ hσ => by
            have := hH0 (σ * Complex.exp (θ * Complex.I))
            simp only [Pi.zero_apply]
            exact mul_nonneg zero_le_two (mul_nonneg hσ.1.le this))

/-! ### The step-function approximation of the trace of a smooth function -/

/-- **Main estimate (smooth case).** For `u ∈ C¹`, `N ≥ 1` arcs and `1/2 ≤ r₀ < 1`, there are
values `c_j` with `∑_j ∫_{arc j} (u(e^{iθ}) - c_j)² ≤ (4(1-r₀) + 4h²/(1-r₀)) ∫_𝔻 |∇u|²`,
`h = 2π/N`. -/
theorem step_sum_le {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) {N : ℕ} (hN : 0 < N) {r₀ : ℝ}
    (hr0 : 1 / 2 ≤ r₀) (hr1 : r₀ < 1) :
    ∃ c : Fin N → ℝ, ∑ j : Fin N, ∫ θ in gridPt N j..gridPt N (j + 1),
        (u (Complex.exp (θ * Complex.I)) - c j) ^ 2 ≤
      (4 * (1 - r₀) + 4 * (2 * π / N) ^ 2 / (1 - r₀)) *
        ∫ z in Metric.ball (0:ℂ) 1, ‖fderiv ℝ u z‖ ^ 2 := by
  set H : ℂ → ℝ := fun z => ‖fderiv ℝ u z‖ ^ 2 with hHdef
  have hcD : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  have hHc : Continuous H := hcD.norm.pow 2
  have hH0 : ∀ z, 0 ≤ H z := fun z => by positivity
  set h : ℝ := 2 * π / N with hh
  have hpos : 0 < h := by positivity
  have h1r : 0 < 1 - r₀ := by linarith
  set R : ℝ → ℝ := fun θ => ∫ σ in r₀..1, H (σ * Complex.exp (θ * Complex.I)) with hR
  set E : ℝ → ℝ := fun ρ => ∫ ψ in (0:ℝ)..(2 * π), H (ρ * Complex.exp (ψ * Complex.I)) with hE
  have hRc : Continuous R :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (θ σ : ℝ) => H (σ * Complex.exp (θ * Complex.I))) (by fun_prop) r₀ 1
  have hEc : Continuous E :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (ρ ψ : ℝ) => H (ρ * Complex.exp (ψ * Complex.I))) (by fun_prop) 0 (2 * π)
  set X : ℝ := ∫ θ in (0:ℝ)..(2 * π), R θ with hX
  have hXle : X ≤ 2 * ∫ z in Metric.ball (0:ℂ) 1, H z := polar_annulus_le hHc hH0 hr0 hr1.le
  have hY : ∫ ρ in r₀..1, E ρ = X := by
    simp only [hE, hX, hR]
    exact intervalIntegral_swap (F := fun ρ ψ => H (ρ * Complex.exp (ψ * Complex.I)))
      (by fun_prop) hr1.le (by positivity)
  -- choose the radius minimizing `E`
  obtain ⟨ρ, hρmem, hρmin⟩ := (isCompact_Icc (a := r₀) (b := 1)).exists_isMinOn
    ⟨r₀, left_mem_Icc.2 hr1.le⟩ hEc.continuousOn
  have hEρ : E ρ * (1 - r₀) ≤ X := by
    rw [← hY]
    have : ∫ _ in r₀..1, E ρ ≤ ∫ x in r₀..1, E x :=
      intervalIntegral.integral_mono_on hr1.le (continuous_const.intervalIntegrable _ _)
        (hEc.intervalIntegrable _ _) (fun x hx => hρmin hx)
    simpa [mul_comm] using this
  have hρ0 : 0 ≤ ρ := by linarith [hρmem.1]
  refine ⟨fun j => u (ρ * Complex.exp (gridPt N j * Complex.I)), ?_⟩
  -- pointwise bound on each arc
  have hpt : ∀ j : ℕ, ∀ θ ∈ Icc (gridPt N j) (gridPt N (j + 1)),
      (u (Complex.exp (θ * Complex.I)) - u (ρ * Complex.exp (gridPt N j * Complex.I))) ^ 2 ≤
        2 * (1 - r₀) * R θ +
          2 * h * ∫ ψ in gridPt N j..gridPt N (j + 1), H (ρ * Complex.exp (ψ * Complex.I)) := by
    intro j θ hθ
    have hθ' : θ ∈ Icc (gridPt N j) (gridPt N j + h) := by rwa [gridPt_succ] at hθ
    have hrad := radial_sq_le hu θ hρmem.2
    have hang := angular_sq_le hu hρ0 hρmem.2 hθ'
    rw [← gridPt_succ] at hang
    have hRmono : ∫ σ in ρ..1, ‖fderiv ℝ u (σ * Complex.exp (θ * Complex.I))‖ ^ 2 ≤ R θ := by
      refine intervalIntegral.integral_mono_interval hρmem.1 hρmem.2 le_rfl ?_ ?_
      · exact Eventually.of_forall (fun _ => by positivity)
      · exact (by fun_prop : Continuous fun σ : ℝ => H (σ * Complex.exp (θ * Complex.I))).intervalIntegrable _ _
    have hR0 : 0 ≤ ∫ σ in ρ..1, ‖fderiv ℝ u (σ * Complex.exp (θ * Complex.I))‖ ^ 2 :=
      intervalIntegral.integral_nonneg hρmem.2 (fun _ _ => by positivity)
    have h1 : (u (Complex.exp (θ * Complex.I)) - u (ρ * Complex.exp (θ * Complex.I))) ^ 2 ≤
        (1 - r₀) * R θ := by
      refine hrad.trans ?_
      calc (1 - ρ) * ∫ σ in ρ..1, ‖fderiv ℝ u (σ * Complex.exp (θ * Complex.I))‖ ^ 2
          ≤ (1 - r₀) * ∫ σ in ρ..1, ‖fderiv ℝ u (σ * Complex.exp (θ * Complex.I))‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (by linarith [hρmem.1]) hR0
        _ ≤ (1 - r₀) * R θ := mul_le_mul_of_nonneg_left hRmono h1r.le
    set a := u (Complex.exp (θ * Complex.I))
    set m := u (ρ * Complex.exp (θ * Complex.I))
    set b := u (ρ * Complex.exp (gridPt N j * Complex.I))
    have hsq : (a - b) ^ 2 ≤ 2 * (a - m) ^ 2 + 2 * (m - b) ^ 2 := by
      nlinarith [sq_nonneg (a - 2 * m + b)]
    have hang' : (m - b) ^ 2 ≤ h * ∫ ψ in gridPt N j..gridPt N (j + 1),
        H (ρ * Complex.exp (ψ * Complex.I)) := hang
    nlinarith
  -- integrate on each arc
  have hgle : ∀ j : ℕ, gridPt N j ≤ gridPt N (j + 1) := fun j => gridPt_mono N (Nat.le_succ j)
  have hEj : ∀ j : ℕ, Continuous fun θ : ℝ =>
      (u (Complex.exp (θ * Complex.I)) - u (ρ * Complex.exp (gridPt N j * Complex.I))) ^ 2 := by
    intro j; have := hu.continuous; fun_prop
  have harc : ∀ j : ℕ, ∫ θ in gridPt N j..gridPt N (j + 1),
      (u (Complex.exp (θ * Complex.I)) - u (ρ * Complex.exp (gridPt N j * Complex.I))) ^ 2 ≤
        2 * (1 - r₀) * (∫ θ in gridPt N j..gridPt N (j + 1), R θ) +
          2 * h * h * ∫ ψ in gridPt N j..gridPt N (j + 1), H (ρ * Complex.exp (ψ * Complex.I)) := by
    intro j
    set Ej := ∫ ψ in gridPt N j..gridPt N (j + 1), H (ρ * Complex.exp (ψ * Complex.I))
    have hRi : IntervalIntegrable (fun θ => 2 * (1 - r₀) * R θ) volume
        (gridPt N j) (gridPt N (j + 1)) := (continuous_const.mul hRc).intervalIntegrable _ _
    have hci : IntervalIntegrable (fun _ : ℝ => 2 * h * Ej) volume
        (gridPt N j) (gridPt N (j + 1)) := continuous_const.intervalIntegrable _ _
    have := intervalIntegral.integral_mono_on (hgle j) ((hEj j).intervalIntegrable (μ := volume) _ _)
      (hRi.add hci) (fun θ hθ => hpt j θ hθ)
    refine this.trans (le_of_eq ?_)
    rw [intervalIntegral.integral_add hRi hci, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, smul_eq_mul, gridPt_succ]
    ring
  -- sum over the arcs
  have hsumR : ∑ j : Fin N, ∫ θ in gridPt N j..gridPt N (j + 1), R θ = X := by
    rw [Fin.sum_univ_eq_sum_range (fun j => ∫ θ in gridPt N j..gridPt N (j + 1), R θ),
      intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hRc.intervalIntegrable _ _),
      gridPt_zero, gridPt_N hN]
  have hsumE : ∑ j : Fin N, ∫ ψ in gridPt N j..gridPt N (j + 1),
      H (ρ * Complex.exp (ψ * Complex.I)) = E ρ := by
    have hc : Continuous fun ψ : ℝ => H (ρ * Complex.exp (ψ * Complex.I)) := by fun_prop
    rw [Fin.sum_univ_eq_sum_range
      (fun j => ∫ ψ in gridPt N j..gridPt N (j + 1), H (ρ * Complex.exp (ψ * Complex.I))),
      intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hc.intervalIntegrable _ _),
      gridPt_zero, gridPt_N hN]
  calc ∑ j : Fin N, ∫ θ in gridPt N j..gridPt N (j + 1),
        (u (Complex.exp (θ * Complex.I)) - u (ρ * Complex.exp (gridPt N j * Complex.I))) ^ 2
      ≤ ∑ j : Fin N, (2 * (1 - r₀) * (∫ θ in gridPt N j..gridPt N (j + 1), R θ) +
          2 * h * h * ∫ ψ in gridPt N j..gridPt N (j + 1),
            H (ρ * Complex.exp (ψ * Complex.I))) :=
        Finset.sum_le_sum (fun j _ => harc j)
    _ = 2 * (1 - r₀) * X + 2 * h * h * E ρ := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsumR, hsumE]
    _ ≤ (2 * (1 - r₀) + 2 * h ^ 2 / (1 - r₀)) * X := by
        have : E ρ ≤ X / (1 - r₀) := by rw [le_div_iff₀ h1r]; exact hEρ
        have h2 : 2 * h * h * E ρ ≤ 2 * h * h * (X / (1 - r₀)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        calc 2 * (1 - r₀) * X + 2 * h * h * E ρ ≤ 2 * (1 - r₀) * X + 2 * h * h * (X / (1 - r₀)) :=
              by linarith
          _ = (2 * (1 - r₀) + 2 * h ^ 2 / (1 - r₀)) * X := by ring
    _ ≤ (2 * (1 - r₀) + 2 * h ^ 2 / (1 - r₀)) * (2 * ∫ z in Metric.ball (0:ℂ) 1, H z) :=
        mul_le_mul_of_nonneg_left hXle (by positivity)
    _ = (4 * (1 - r₀) + 4 * h ^ 2 / (1 - r₀)) * ∫ z in Metric.ball (0:ℂ) 1, H z := by ring

/-! ### From the arc estimate to the `L²` distance -/

lemma measurableSet_arc (N j : ℕ) : MeasurableSet (arc N j) := measurableSet_Ioc

lemma lintegral_Ioc_eq_sum_arc {N : ℕ} (hN : 0 < N) (f : ℝ → ℝ≥0∞) :
    ∫⁻ θ in Ioc 0 (2 * π), f θ = ∑ j : Fin N, ∫⁻ θ in arc N j, f θ := by
  rw [← iUnion_arc hN, lintegral_iUnion (s := fun j : Fin N => arc N j)
    (fun j => measurableSet_arc N j)
    (fun i j hij => arc_disjoint hN (fun h => hij (Fin.ext h))), tsum_fintype]

lemma enorm_traceSmooth_sub_step_sq {N : ℕ} (hN : 0 < N) (u : smoothFns) (c : Fin N → ℝ) :
    ‖traceSmooth u - stepMap N c‖ₑ ^ 2 = ENNReal.ofReal (∑ j : Fin N,
      ∫ θ in gridPt N j..gridPt N (j + 1), ((u : ℂ → ℝ) (Complex.exp (θ * Complex.I)) - c j) ^ 2) := by
  have hcu := continuous_of_mem u.2
  have heq : traceSmooth u - stepMap N c = ((memLp_bdry u).sub (memLp_stepFn N c)).toLp _ :=
    (MemLp.toLp_sub (memLp_bdry u) (memLp_stepFn N c)).symm
  rw [heq, enorm_toLp_sq, lintegral_Ioc_eq_sum_arc hN, ENNReal.ofReal_sum_of_nonneg]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    have hc : Continuous fun θ : ℝ => ((u : ℂ → ℝ) (Complex.exp (θ * Complex.I)) - c j) ^ 2 := by
      fun_prop
    rw [setLIntegral_congr_fun (measurableSet_arc N j) (g := fun θ : ℝ =>
      ENNReal.ofReal (((u : ℂ → ℝ) (Complex.exp (θ * Complex.I)) - c j) ^ 2))]
    · rw [intervalIntegral.integral_of_le (gridPt_mono N (Nat.le_succ j)),
        ofReal_integral_eq_lintegral_ofReal]
      · rfl
      · exact hc.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set Ioc_subset_Icc_self
      · exact Eventually.of_forall (fun _ => sq_nonneg _)
    · intro θ hθ
      simp only [Pi.sub_apply]
      rw [stepFn_eq hN c hθ, enorm_sq_real]
  · intro j _
    exact intervalIntegral.integral_nonneg (gridPt_mono N (Nat.le_succ j)) (fun _ _ => sq_nonneg _)

/-- The constant in the step approximation. -/
def stepConst (N : ℕ) (r₀ : ℝ) : ℝ := 4 * (1 - r₀) + 4 * (2 * π / N) ^ 2 / (1 - r₀)

lemma energy_le_norm_embed_sq (u : smoothFns) :
    ∫ z in Metric.ball (0:ℂ) 1, ‖fderiv ℝ (u : ℂ → ℝ) z‖ ^ 2 ≤ ‖embedH u‖ ^ 2 := by
  have hcf : Continuous (fderiv ℝ (u : ℂ → ℝ)) :=
    (contDiff_one_of_mem u.2).continuous_fderiv one_ne_zero
  have h1 : ENNReal.ofReal (∫ z in Metric.ball (0:ℂ) 1, ‖fderiv ℝ (u : ℂ → ℝ) z‖ ^ 2) =
      ENNReal.ofReal (‖gradL2 u‖ ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm_eq_enorm, enorm_gradL2_sq]
    · congr 1; ext z
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
    · exact (memLp_disk (f := fun z => ‖fderiv ℝ (u : ℂ → ℝ) z‖ ^ 2) (by fun_prop)).integrable
        one_le_two
    · exact Eventually.of_forall (fun _ => by positivity)
  have h2 := (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (fun _ => by positivity))
    (by positivity)).1 h1
  rw [h2]
  show ‖gradL2 u‖ ^ 2 ≤ ‖embed u‖ ^ 2
  rw [← embed_snd]
  have := WithLp.prod_norm_sq_eq_of_L2 (embed u)
  nlinarith [sq_nonneg ‖(embed u).fst‖]

/-- Smooth case of the step approximation, as an `L²` distance bound. -/
lemma infDist_traceSmooth_sq_le {N : ℕ} (hN : 0 < N) {r₀ : ℝ} (hr0 : 1 / 2 ≤ r₀) (hr1 : r₀ < 1)
    (u : smoothFns) :
    Metric.infDist (trace (embedH u)) (stepSpace N) ^ 2 ≤ stepConst N r₀ * ‖embedH u‖ ^ 2 := by
  obtain ⟨c, hc⟩ := step_sum_le (contDiff_one_of_mem u.2) hN hr0 hr1
  have hS0 : 0 ≤ ∑ j : Fin N, ∫ θ in gridPt N j..gridPt N (j + 1),
      ((u : ℂ → ℝ) (Complex.exp (θ * Complex.I)) - c j) ^ 2 :=
    Finset.sum_nonneg (fun j _ =>
      intervalIntegral.integral_nonneg (gridPt_mono N (Nat.le_succ j)) (fun _ _ => sq_nonneg _))
  have hnorm : ‖traceSmooth u - stepMap N c‖ ^ 2 = ∑ j : Fin N, ∫ θ in gridPt N j..gridPt N (j + 1),
      ((u : ℂ → ℝ) (Complex.exp (θ * Complex.I)) - c j) ^ 2 := by
    have := enorm_traceSmooth_sub_step_sq hN u c
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)] at this
    exact (ENNReal.ofReal_eq_ofReal_iff (by positivity) hS0).1 this
  have hK0 : 0 ≤ stepConst N r₀ := by
    unfold stepConst
    have : 0 < 1 - r₀ := by linarith
    positivity
  have hd : Metric.infDist (trace (embedH u)) (stepSpace N) ≤ ‖traceSmooth u - stepMap N c‖ := by
    rw [trace_embed, ← dist_eq_norm]
    exact Metric.infDist_le_dist_of_mem (LinearMap.mem_range_self _ c)
  calc Metric.infDist (trace (embedH u)) (stepSpace N) ^ 2 ≤ ‖traceSmooth u - stepMap N c‖ ^ 2 :=
        pow_le_pow_left₀ Metric.infDist_nonneg hd 2
    _ ≤ stepConst N r₀ * ∫ z in Metric.ball (0:ℂ) 1, ‖fderiv ℝ (u : ℂ → ℝ) z‖ ^ 2 := by
        rw [hnorm]; exact hc
    _ ≤ stepConst N r₀ * ‖embedH u‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (energy_le_norm_embed_sq u) hK0

/-- The step approximation on all of `H¹(𝔻)` (by density). -/
lemma infDist_trace_sq_le {N : ℕ} (hN : 0 < N) {r₀ : ℝ} (hr0 : 1 / 2 ≤ r₀) (hr1 : r₀ < 1)
    (x : H1) :
    Metric.infDist (trace x) (stepSpace N) ^ 2 ≤ stepConst N r₀ * ‖x‖ ^ 2 := by
  refine denseRange_embedH.induction_on x ?_ (infDist_traceSmooth_sq_le hN hr0 hr1)
  exact isClosed_le (((Metric.continuous_infDist_pt _).comp trace.continuous).pow 2)
    (continuous_const.mul (continuous_norm.pow 2))

lemma exists_stepConst_le {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, 0 < N ∧ ∃ r₀ : ℝ, 1 / 2 ≤ r₀ ∧ r₀ < 1 ∧ stepConst N r₀ ≤ η := by
  set δ : ℝ := min (1 / 2) (η / 8) with hδ
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 2 := min_le_left _ _
  have hδ2 : δ ≤ η / 8 := min_le_right _ _
  set m : ℝ := min 1 (η * δ / 8) with hm
  have hm0 : 0 < m := lt_min one_pos (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * π / m)
  have hNpos : (0:ℝ) < N := lt_trans (by positivity) hN
  refine ⟨N, by exact_mod_cast hNpos, 1 - δ, by linarith, by linarith, ?_⟩
  have hh : 2 * π / N ≤ m := by
    rw [div_le_iff₀ hNpos]; rw [div_lt_iff₀ hm0] at hN; linarith
  have hh0 : 0 ≤ 2 * π / N := by positivity
  have hsq : (2 * π / N) ^ 2 ≤ η * δ / 8 := by
    have h1 : 2 * π / N ≤ 1 := hh.trans (min_le_left _ _)
    have h2 : 2 * π / N ≤ η * δ / 8 := hh.trans (min_le_right _ _)
    nlinarith
  unfold stepConst
  rw [sub_sub_cancel]
  have : 4 * (2 * π / N) ^ 2 / δ ≤ η / 2 := by
    rw [div_le_iff₀ hδ0]; nlinarith
  linarith

/-- **Compactness of the trace** `H¹(𝔻) → L²(𝕋)`. -/
theorem isCompactOperator_trace : IsCompactOperator trace := by
  refine isCompactOperator_of_approx trace (fun ε hε => ?_)
  obtain ⟨N, hN, r₀, hr0, hr1, hK⟩ := exists_stepConst_le (η := (ε / 2) ^ 2) (by positivity)
  refine ⟨stepSpace N, inferInstance, fun x hx => ?_⟩
  have hK0 : 0 ≤ stepConst N r₀ := by
    unfold stepConst
    have : 0 < 1 - r₀ := by linarith
    positivity
  have h1 := infDist_trace_sq_le hN hr0 hr1 x
  have h2 : Metric.infDist (trace x) (stepSpace N) ^ 2 ≤ (ε / 2) ^ 2 := by
    refine h1.trans ?_
    have : ‖x‖ ^ 2 ≤ 1 := by
      have := norm_nonneg x
      nlinarith
    nlinarith
  have h3 : Metric.infDist (trace x) (stepSpace N) < ε := by
    have := (pow_le_pow_iff_left₀ Metric.infDist_nonneg (by positivity) two_ne_zero).1 h2
    linarith
  obtain ⟨y, hy, hdy⟩ := (Metric.infDist_lt_iff ⟨0, (stepSpace N).zero_mem⟩).1 h3
  exact ⟨y, hy, by rw [← dist_eq_norm]; exact hdy.le⟩

end SteklovH1
