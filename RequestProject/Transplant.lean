module

public import RequestProject.CircleFibre
public import RequestProject.AreaFormula
public import RequestProject.SingularTransfer

/-!
# Transplantation along a pair of branched covers of the disk

Let `B₁, B₂` be finite Blaschke products.  Given a real kernel `K(z', p)` defined for
`B₂ z' = B₁ p`, the *transplantation* of `u` is
`(T u)(z') = ∑_{p ∈ W₁, B₁ p = B₂ z'} K(z', p) u(p)`.
If `K` is fibrewise orthogonal (`∑_{z' ∈ B₂⁻¹ w} K(z',p) K(z',p') = δ_{p p'}`), then `T`
preserves the weighted boundary form with weights `|B₂'|` and `|B₁'|`
(`weightedBoundaryMass_transplant`), by the circle fibre formula.  This file also contains the
algebraic orthogonality identities used for the Dirichlet energy.
-/

@[expose] public section

open Complex Metric Set MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace SteklovTransplant

open SteklovBlaschke Steklov

/-- The transplantation operator `(T u)(z') = ∑_{p ∈ W₁, B₁ p = B₂ z'} K(z', p) u(p)`. -/
def transplant (W₁ : Set ℂ) (B₁ B₂ : ℂ → ℂ) (K : ℂ → ℂ → ℝ) (u : ℂ → ℝ) (z' : ℂ) : ℝ :=
  ∑ᶠ p ∈ {p | p ∈ W₁ ∧ B₁ p = B₂ z'}, K z' p * u p

/-! ### Fibrewise orthogonality -/

lemma sum_sq_orth {α β : Type*} [DecidableEq β] (A : Finset α) (P : Finset β) (K : α → β → ℝ)
    (hK : ∀ p ∈ P, ∀ p' ∈ P, ∑ a ∈ A, K a p * K a p' = if p = p' then 1 else 0) (x : β → ℝ) :
    ∑ a ∈ A, (∑ p ∈ P, K a p * x p) ^ 2 = ∑ p ∈ P, x p ^ 2 := by
  simp_rw [sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_comm]
  have : ∀ p' ∈ P, ∑ a ∈ A, K a p * x p * (K a p' * x p') =
      x p * x p' * (if p = p' then 1 else 0) := by
    intro p' hp'
    rw [← hK p hp p' hp', Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => by ring
  rw [Finset.sum_congr rfl this]
  simp [Finset.sum_ite_eq, hp]

/-- The operator norm of a real functional on `ℂ` is Euclidean. -/
lemma norm_sq_clm (L : ℂ →L[ℝ] ℝ) : ‖L‖ ^ 2 = L 1 ^ 2 + L I ^ 2 := by
  have hL : ∀ z : ℂ, L z = z.re * L 1 + z.im * L I := by
    intro z
    conv_lhs => rw [← Complex.re_add_im z]
    rw [map_add]
    have h1 : ((z.re : ℂ)) = z.re • (1:ℂ) := by simp
    have h2 : (z.im : ℂ) * I = z.im • I := by simp
    rw [h1, h2, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have hnorm : ‖L‖ = Real.sqrt (L 1 ^ 2 + L I ^ 2) := by
    apply le_antisymm
    · refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun z => ?_
      rw [hL, Real.norm_eq_abs, Complex.norm_eq_sqrt_sq_add_sq, ← Real.sqrt_mul (by positivity)]
      rw [← Real.sqrt_sq_eq_abs]
      apply Real.sqrt_le_sqrt
      nlinarith [sq_nonneg (z.re * L I - z.im * L 1)]
    · rcases eq_or_ne (L 1 ^ 2 + L I ^ 2) 0 with h | h
      · rw [h]; simp
      have hpos : 0 < L 1 ^ 2 + L I ^ 2 := lt_of_le_of_ne (by positivity) (Ne.symm h)
      set z : ℂ := L 1 + L I * I
      have hz : ‖z‖ = Real.sqrt (L 1 ^ 2 + L I ^ 2) := by
        rw [Complex.norm_eq_sqrt_sq_add_sq]; simp [z]
      have hLz : L z = L 1 ^ 2 + L I ^ 2 := by
        rw [hL]; simp [z]; ring
      have := L.le_opNorm z
      rw [hLz, hz, Real.norm_eq_abs, abs_of_pos hpos] at this
      have hs := Real.sqrt_pos.2 hpos
      have hsq := Real.sq_sqrt hpos.le
      nlinarith
  rw [hnorm, Real.sq_sqrt (by positivity)]

/-- Vector-valued fibrewise orthogonality for real functionals on `ℂ`. -/
lemma sum_norm_sq_orth {α β : Type*} [DecidableEq β] (A : Finset α) (P : Finset β)
    (K : α → β → ℝ)
    (hK : ∀ p ∈ P, ∀ p' ∈ P, ∑ a ∈ A, K a p * K a p' = if p = p' then 1 else 0)
    (v : β → (ℂ →L[ℝ] ℝ)) :
    ∑ a ∈ A, ‖∑ p ∈ P, K a p • v p‖ ^ 2 = ∑ p ∈ P, ‖v p‖ ^ 2 := by
  simp_rw [norm_sq_clm, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    smul_eq_mul, Finset.sum_add_distrib]
  rw [sum_sq_orth A P K hK (fun p => v p 1), sum_sq_orth A P K hK (fun p => v p I)]

/-! ### Finite sums -/

lemma circFibreSum_eq_sum_toFinset {B : ℂ → ℂ} {w : ℂ} (hA : {z : ℂ | ‖z‖ = 1 ∧ B z = w}.Finite)
    (F : ℂ → ℝ≥0∞) : circFibreSum B F w = ∑ z ∈ hA.toFinset, F z := by
  unfold circFibreSum
  change ∑' z : ({z : ℂ | ‖z‖ = 1 ∧ B z = w} : Set ℂ), F z = _
  conv_lhs => rw [← hA.coe_toFinset]
  exact Finset.tsum_subtype' hA.toFinset F

lemma enorm_sq_eq_ofReal (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

lemma sum_enorm_sq {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ∑ i ∈ s, ‖x i‖ₑ ^ 2 = ENNReal.ofReal (∑ i ∈ s, x i ^ 2) := by
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (x i))]
  simp_rw [enorm_sq_eq_ofReal]

/-- The set of parameters `s` with `e^{is}` in a countable set is countable. -/
lemma countable_preimage_exp {C : Set ℂ} (hC : C.Countable) :
    {s : ℝ | exp (s * I) ∈ C}.Countable := by
  have : {s : ℝ | exp (s * I) ∈ C} ⊆ ⋃ w ∈ C, {s : ℝ | exp (s * I) = w} := by
    intro s hs; exact mem_biUnion hs rfl
  refine (hC.biUnion fun w _ => ?_).mono this
  by_cases h : ∃ s₀ : ℝ, exp (s₀ * I) = w
  · obtain ⟨s₀, rfl⟩ := h
    refine (Set.countable_range fun m : ℤ => s₀ + 2 * Real.pi * m).mono fun s hs => ?_
    obtain ⟨m, hm⟩ := (exp_mul_I_eq_exp_mul_I_iff s s₀).1 hs
    exact ⟨m, hm.symm⟩
  · push_neg at h
    refine Set.countable_empty.mono fun s hs => h s hs

/-! ### Preservation of the weighted boundary form -/

/-- **Transplantation preserves the weighted boundary form.**  Let `B₁, B₂` be finite Blaschke
products of positive degree, `W₁ ⊇ 𝔻̄` a set such that a point of `W₁` mapped by `B₁` to the
circle lies on the circle, and `K` a kernel that is fibrewise orthogonal over all points of the
circle outside a countable set `C`.  Then
`∫_𝕋 |T u|² |B₂'| = ∫_𝕋 |u|² |B₁'|` (stated for any measurable `g` equal to `T u` on `𝕋`). -/
theorem weightedBoundaryMass_transplant {B₁ B₂ : ℂ → ℂ} {n₁ n₂ : ℕ}
    (hB₁ : IsFiniteBlaschke B₁ n₁) (hn₁ : 0 < n₁) (hB₂ : IsFiniteBlaschke B₂ n₂) (hn₂ : 0 < n₂)
    {W₁ : Set ℂ} (hW₁ : closedBall (0:ℂ) 1 ⊆ W₁) (hin₁ : ∀ p ∈ W₁, ‖B₁ p‖ = 1 → ‖p‖ = 1)
    (K : ℂ → ℂ → ℝ) {C : Set ℂ} (hC : C.Countable)
    (horth : ∀ w, ‖w‖ = 1 → w ∉ C → ∀ p p', ‖p‖ = 1 → B₁ p = w → ‖p'‖ = 1 → B₁ p' = w →
      ∑ᶠ z' ∈ {z' : ℂ | ‖z'‖ = 1 ∧ B₂ z' = w}, K z' p * K z' p' = if p = p' then 1 else 0)
    (u : ℂ → ℝ) (hu : Measurable u) (g : ℂ → ℝ) (hg : Measurable g)
    (hgT : ∀ z, ‖z‖ = 1 → g z = transplant W₁ B₁ B₂ K u z) :
    weightedBoundaryMass (fun z => ‖deriv B₂ z‖) g =
      weightedBoundaryMass (fun z => ‖deriv B₁ z‖) u := by
  classical
  unfold weightedBoundaryMass
  have h₂ := lintegral_circle_norm_deriv_eq_circFibreSum hB₂ hn₂
    (fun z => ‖g z‖ₑ ^ 2) (hg.enorm.pow_const 2)
  have h₁ := lintegral_circle_norm_deriv_eq_circFibreSum hB₁ hn₁
    (fun z => ‖u z‖ₑ ^ 2) (hu.enorm.pow_const 2)
  simp only at h₁ h₂ ⊢
  rw [h₂, h₁]
  refine setLIntegral_congr_fun_ae measurableSet_Ioc ?_
  have hcount := countable_preimage_exp hC
  filter_upwards [hcount.ae_notMem volume] with s hs _
  set w := exp (s * I) with hw
  have hwC : w ∉ C := hs
  have hw1 : ‖w‖ = 1 := norm_exp_ofReal_mul_I s
  have hA := circFibre_finite hB₂ hn₂ w
  have hP := circFibre_finite hB₁ hn₁ w
  have hPW : ∀ z', ‖z'‖ = 1 → B₂ z' = w →
      {p | p ∈ W₁ ∧ B₁ p = B₂ z'} = {p : ℂ | ‖p‖ = 1 ∧ B₁ p = w} := by
    intro z' _ hz'
    ext p
    simp only [mem_setOf_eq, hz']
    constructor
    · rintro ⟨hpW, hp⟩; exact ⟨hin₁ p hpW (by rw [hp, hw1]), hp⟩
    · rintro ⟨hp1, hp⟩; exact ⟨hW₁ (by rw [mem_closedBall, dist_zero_right, hp1]), hp⟩
  rw [circFibreSum_eq_sum_toFinset hA, circFibreSum_eq_sum_toFinset hP]
  have hT : ∀ z' ∈ hA.toFinset, g z' =
      ∑ p ∈ hP.toFinset, K z' p * u p := by
    intro z' hz'
    rw [Set.Finite.mem_toFinset] at hz'
    rw [hgT z' hz'.1]
    unfold transplant
    rw [hPW z' hz'.1 hz'.2, finsum_mem_eq_finite_toFinset_sum _ hP]
  rw [Finset.sum_congr rfl fun z' hz' => by rw [hT z' hz'], sum_enorm_sq, sum_enorm_sq]
  congr 1
  refine sum_sq_orth _ _ K (fun p hp p' hp' => ?_) u
  rw [Set.Finite.mem_toFinset] at hp hp'
  rw [← horth w hw1 hwC p p' hp.1 hp.2 hp'.1 hp'.2, finsum_mem_eq_finite_toFinset_sum _ hA]

end SteklovTransplant

end
