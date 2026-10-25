module

public import RequestProject.TransplantEnergy

/-!
# Spectral comparison by transplantation

Combining the energy and boundary-form identities for the transplantation operator
(`dirichletEnergy_transplant`, `weightedBoundaryMass_transplant`) with the min–max transfer for
test functions that are singular at finitely many interior points
(`SteklovBranch.minMax_le_of_singular_transfer`), we obtain
`σ_k(𝔻, |B₂'|) ≤ σ_k(𝔻, |B₁'|)` for every `k` (`weightedSteklovEigenvalue_le_of_transplant`).

All hypotheses are geometric data of the pair of branched covers `B₁, B₂ : 𝔻 → 𝔻` and of the
kernel `K` (finite fibres, critical values, local branches along which `K` is constant,
fibrewise orthogonality); no spectral information is assumed.
-/

@[expose] public section

open Complex Metric Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace SteklovTransplant

open SteklovBlaschke Steklov SteklovArea ConformalPullback SteklovBranch

lemma transplant_eq_sum {W₁ : Set ℂ} {B₁ B₂ : ℂ → ℂ} (K : ℂ → ℂ → ℝ)
    (hfinW : ∀ w, {p | p ∈ W₁ ∧ B₁ p = w}.Finite) (u : ℂ → ℝ) (z' : ℂ) :
    transplant W₁ B₁ B₂ K u z' = ∑ p ∈ (hfinW (B₂ z')).toFinset, K z' p * u p := by
  unfold transplant
  rw [finsum_mem_eq_finite_toFinset_sum _ (hfinW (B₂ z'))]

/-- The cut-off transplantation `u ↦ χ · T u` as a linear map. -/
def transplantL (χ : ℂ → ℝ) (W₁ : Set ℂ) (B₁ B₂ : ℂ → ℂ) (K : ℂ → ℂ → ℝ)
    (hfinW : ∀ w, {p | p ∈ W₁ ∧ B₁ p = w}.Finite) : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ) where
  toFun u := fun z => χ z * transplant W₁ B₁ B₂ K u z
  map_add' u v := by
    ext z
    simp only [transplant_eq_sum K hfinW, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a u := by
    ext z
    simp only [transplant_eq_sum K hfinW, Pi.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => by ring

lemma transplantL_apply (χ : ℂ → ℝ) (W₁ : Set ℂ) (B₁ B₂ : ℂ → ℂ) (K : ℂ → ℂ → ℝ)
    (hfinW : ∀ w, {p | p ∈ W₁ ∧ B₁ p = w}.Finite) (u : ℂ → ℝ) (z : ℂ) :
    transplantL χ W₁ B₁ B₂ K hfinW u z = χ z * transplant W₁ B₁ B₂ K u z := rfl

/-- Smooth functions have finite Dirichlet energy on `𝔻`. -/
lemma dirichletEnergy_ball_ne_top {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u) :
    dirichletEnergy (ball 0 1) u ≠ ⊤ := by
  have hc : Continuous (fderiv ℝ u) := hu.continuous_fderiv one_ne_zero
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn hc.continuousOn
  unfold dirichletEnergy
  refine ne_top_of_le_ne_top (b := ∫⁻ _ in ball (0:ℂ) 1, ENNReal.ofReal (M ^ 2)) ?_ ?_
  · rw [setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne
  · refine setLIntegral_mono measurable_const fun z hz => ?_
    have h := hM z (ball_subset_closedBall hz)
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) h 2)

lemma contDiffAt_of_eventually_differentiableAt {f : ℂ → ℂ} {x : ℂ}
    (h : ∀ᶠ y in 𝓝 x, DifferentiableAt ℂ f y) : ContDiffAt ℝ ∞ f x := by
  obtain ⟨t, ht, hto, hxt⟩ := _root_.eventually_nhds_iff.1 h
  exact (contDiffOn_of_differentiableOn hto
    (fun y hy => (ht y hy).differentiableWithinAt)).contDiffAt (hto.mem_nhds hxt)

lemma IsFiniteBlaschke.norm_lt_one {B : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n) {z : ℂ}
    (hz : ‖z‖ < 1) : ‖B z‖ < 1 ∨ n = 0 := by
  obtain ⟨η, a, hη, ha, rfl⟩ := hB
  rcases Nat.eq_zero_or_pos n with h | h
  · exact Or.inr h
  left
  have hfac : ∀ l, ‖bfac (a l) z‖ < 1 := fun l => by
    have hd := denom_ne_zero (ha l) hz.le
    rw [bfac, norm_div, div_lt_one (norm_pos_iff.2 hd)]
    have h1 : normSq (a l) < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg (a l), ha l]
    have h2 : normSq z < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
    have := normSq_denom_sub (a l) z
    have h3 : normSq (z - a l) < normSq (1 - (starRingEnd ℂ) (a l) * z) := by nlinarith
    rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at h3
    nlinarith [norm_nonneg (z - a l), norm_nonneg (1 - (starRingEnd ℂ) (a l) * z)]
  simp only [norm_mul, hη, one_mul, norm_prod]
  haveI : Nonempty (Fin n) := ⟨⟨0, h⟩⟩
  calc ∏ l, ‖bfac (a l) z‖ ≤ ‖bfac (a ⟨0, h⟩) z‖ := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ⟨0, h⟩)]
        refine mul_le_of_le_one_right (norm_nonneg _) ?_
        exact Finset.prod_le_one (fun l _ => norm_nonneg _) fun l _ => (hfac l).le
    _ < 1 := hfac _

/-- **Spectral comparison by transplantation.**  Let `B₁, B₂` be finite Blaschke products of
positive degree, `K` a bounded kernel on the fibre product, and `S ⊆ 𝔻` a finite set (the
branch locus) such that
* the fibres `{p ∈ W₁ | B₁ p = w}` are finite with bounded cardinality (`W₁ ⊇ 𝔻̄` is a
  neighbourhood on which `B₁` maps exactly `𝔻` into `𝔻` and `𝕋` into `𝕋`);
* away from `B₂(S)` both maps have nonvanishing derivative on `𝔻`;
* `K` is fibrewise orthogonal over `𝔻 \ B₂(S)` and over `𝕋`;
* near every point `z' ∈ U \ S` (`U ⊇ 𝔻̄` open) the `B₁`-fibres over `B₂(z'')` are parametrized
  by holomorphic local inverses `σ_p` of `B₁`, along which `K` is constant.
Then `σ_k(𝔻, |B₂'|) ≤ σ_k(𝔻, |B₁'|)` for all `k`. -/
theorem weightedSteklovEigenvalue_le_of_transplant {B₁ B₂ : ℂ → ℂ} {n₁ n₂ : ℕ}
    (hB₁ : IsFiniteBlaschke B₁ n₁) (hn₁ : 0 < n₁) (hB₂ : IsFiniteBlaschke B₂ n₂) (hn₂ : 0 < n₂)
    {U : Set ℂ} (hU : IsOpen U) (hcbU : closedBall (0:ℂ) 1 ⊆ U)
    (hB₂U : DifferentiableOn ℂ B₂ U)
    {W₁ : Set ℂ} (hW₁ : closedBall (0:ℂ) 1 ⊆ W₁) (hin₁ : ∀ p ∈ W₁, ‖B₁ p‖ = 1 → ‖p‖ = 1)
    (hin₁' : ∀ p ∈ W₁, ‖B₁ p‖ < 1 → ‖p‖ < 1)
    (hfinW : ∀ w, {p | p ∈ W₁ ∧ B₁ p = w}.Finite)
    (hfin₂ : ∀ w, {z : ℂ | ‖z‖ < 1 ∧ B₂ z = w}.Finite)
    (K : ℂ → ℂ → ℝ) (hKb : ∃ M, ∀ z' p, |K z' p| ≤ M)
    (hcard : ∃ N : ℕ, ∀ w, (hfinW w).toFinset.card ≤ N)
    (S : Finset ℂ) (hS : ∀ s ∈ S, ‖s‖ < 1)
    (hcrit₁ : ∀ p, ‖p‖ < 1 → B₁ p ∉ B₂ '' ↑S → deriv B₁ p ≠ 0)
    (hcrit₂ : ∀ z, ‖z‖ < 1 → B₂ z ∉ B₂ '' ↑S → deriv B₂ z ≠ 0)
    (horth : ∀ w, ‖w‖ < 1 → w ∉ B₂ '' ↑S → ∀ p p', ‖p‖ < 1 → B₁ p = w → ‖p'‖ < 1 →
      B₁ p' = w →
      ∑ᶠ z' ∈ {z' : ℂ | ‖z'‖ < 1 ∧ B₂ z' = w}, K z' p * K z' p' = if p = p' then 1 else 0)
    (horthT : ∀ w, ‖w‖ = 1 → ∀ p p', ‖p‖ = 1 → B₁ p = w → ‖p'‖ = 1 → B₁ p' = w →
      ∑ᶠ z' ∈ {z' : ℂ | ‖z'‖ = 1 ∧ B₂ z' = w}, K z' p * K z' p' = if p = p' then 1 else 0)
    (hlocU : ∀ z' ∈ U, z' ∉ S → ∃ σ : ℂ → ℂ → ℂ,
      (∀ p ∈ {p | p ∈ W₁ ∧ B₁ p = B₂ z'}, σ p (B₂ z') = p ∧
        HasDerivAt (σ p) (deriv B₁ p)⁻¹ (B₂ z') ∧
        ∀ᶠ w'' in 𝓝 (B₂ z'), DifferentiableAt ℂ (σ p) w'') ∧
      ∀ᶠ z'' in 𝓝 z', {p | p ∈ W₁ ∧ B₁ p = B₂ z''} =
          (fun p => σ p (B₂ z'')) '' {p | p ∈ W₁ ∧ B₁ p = B₂ z'} ∧
        InjOn (fun p => σ p (B₂ z'')) {p | p ∈ W₁ ∧ B₁ p = B₂ z'} ∧
        ∀ p ∈ {p | p ∈ W₁ ∧ B₁ p = B₂ z'}, K z'' (σ p (B₂ z'')) = K z' p)
    (k : ℕ) :
    weightedSteklovEigenvalue (fun z => ‖deriv B₂ z‖) k ≤
      weightedSteklovEigenvalue (fun z => ‖deriv B₁ z‖) k := by
  classical
  obtain ⟨χ, hχ, ⟨W, -, hcbW, hχ1⟩, hsupp⟩ := exists_cutoff (isCompact_closedBall (0:ℂ) 1) hU hcbU
  have hχb : ∀ z, ‖z‖ ≤ 1 → χ z = 1 := fun z hz =>
    hχ1 z (hcbW (by rwa [mem_closedBall, dist_zero_right]))
  set T := transplantL χ W₁ B₁ B₂ K hfinW with hTdef
  have hmaps₁ : ∀ z, ‖z‖ < 1 → ‖B₁ z‖ < 1 := fun z hz =>
    (IsFiniteBlaschke.norm_lt_one hB₁ hz).resolve_right hn₁.ne'
  have hmaps₂ : ∀ z, ‖z‖ < 1 → ‖B₂ z‖ < 1 := fun z hz =>
    (IsFiniteBlaschke.norm_lt_one hB₂ hz).resolve_right hn₂.ne'
  have hB₁b : DifferentiableOn ℂ B₁ (ball 0 1) := fun z hz =>
    (hB₁.differentiableAt (by simpa using (mem_ball_zero_iff.1 hz).le)).differentiableWithinAt
  have hB₂b : DifferentiableOn ℂ B₂ (ball 0 1) := fun z hz =>
    (hB₂.differentiableAt (by simpa using (mem_ball_zero_iff.1 hz).le)).differentiableWithinAt
  have hPset : ∀ z', ‖z'‖ < 1 →
      {p | p ∈ W₁ ∧ B₁ p = B₂ z'} = {p : ℂ | ‖p‖ < 1 ∧ B₁ p = B₂ z'} := by
    intro z' hz'
    ext p
    simp only [mem_setOf_eq]
    constructor
    · rintro ⟨hpW, hp⟩; exact ⟨hin₁' p hpW (by rw [hp]; exact hmaps₂ z' hz'), hp⟩
    · rintro ⟨hp1, hp⟩
      exact ⟨hW₁ (by rw [mem_closedBall, dist_zero_right]; exact hp1.le), hp⟩
  obtain ⟨q, hq, -, -, -, -, -, hnormd⟩ := blaschke_circle_data hB₂ hn₂
  have hρ : Continuous fun t : ℝ => ‖deriv B₂ (circ t)‖ := by
    have : (fun t : ℝ => ‖deriv B₂ (circ t)‖) = q := funext fun t => hnormd t
    rw [this]; exact hq
  obtain ⟨M, hM⟩ := hKb
  obtain ⟨N, hN⟩ := hcard
  -- smoothness of `T u` off `S`
  have hsmooth : ∀ u, ContDiff ℝ ∞ u → ContDiffOn ℝ ∞ (T u) (↑S)ᶜ := by
    intro u hu z hz
    refine ContDiffAt.contDiffWithinAt ?_
    by_cases hzU : z ∈ U
    · obtain ⟨σ, hσ, hev⟩ := hlocU z hzU hz
      have hP := hfinW (B₂ z)
      have heq := transplant_eventuallyEq hP hev u
      have hloc : ContDiffAt ℝ ∞
          (fun z'' => ∑ p ∈ hP.toFinset, K z p * u (σ p (B₂ z''))) z := by
        refine ContDiffAt.sum fun p hp => contDiffAt_const.mul ?_
        have hp' := (Set.Finite.mem_toFinset hP).1 hp
        obtain ⟨-, -, hσd⟩ := hσ p hp'
        have hB : ContDiffAt ℝ ∞ B₂ z :=
          (contDiffOn_of_differentiableOn hU hB₂U).contDiffAt (hU.mem_nhds hzU)
        exact hu.contDiffAt.comp z ((contDiffAt_of_eventually_differentiableAt hσd).comp z hB)
      have hTz : ContDiffAt ℝ ∞ (transplant W₁ B₁ B₂ K u) z :=
        hloc.congr_of_eventuallyEq heq
      exact hχ.contDiffAt.mul hTz
    · have hz' : z ∉ tsupport χ := fun h => hzU (hsupp h)
      rw [notMem_tsupport_iff_eventuallyEq] at hz'
      refine contDiffAt_const (c := (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [hz'] with x hx
      simp [hTdef, transplantL_apply, hx]
  have hTball : ∀ u z, ‖z‖ ≤ 1 → T u z = transplant W₁ B₁ B₂ K u z := fun u z hz => by
    rw [hTdef, transplantL_apply, hχb z hz, one_mul]
  refine minMax_le_of_singular_transfer hρ S hS T (fun u hu => ⟨?_, hsmooth u hu, ?_, ?_⟩)
    (fun u hu => dirichletEnergy_ball_ne_top (hu.of_le (by exact_mod_cast le_top))) k
  · -- boundedness on `𝔻`
    obtain ⟨Mu, hMu⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn
      hu.continuous.continuousOn
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 0)
    have hMu0 : 0 ≤ Mu := (norm_nonneg _).trans (hMu 0 (by simp))
    refine ⟨N * (M * Mu), fun z hz => ?_⟩
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    rw [hTball u z hz1.le, transplant_eq_sum K hfinW]
    calc |∑ p ∈ (hfinW (B₂ z)).toFinset, K z p * u p|
        ≤ ∑ p ∈ (hfinW (B₂ z)).toFinset, |K z p * u p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ (hfinW (B₂ z)).toFinset, M * Mu := by
          refine Finset.sum_le_sum fun p hp => ?_
          rw [Set.Finite.mem_toFinset] at hp
          have hp1 : ‖p‖ < 1 := hin₁' p hp.1 (by rw [hp.2]; exact hmaps₂ z hz1)
          rw [abs_mul]
          have := hMu p (by rw [mem_closedBall, dist_zero_right]; exact hp1.le)
          rw [Real.norm_eq_abs] at this
          exact mul_le_mul (hM z p) this (abs_nonneg _) hM0
      _ = (hfinW (B₂ z)).toFinset.card * (M * Mu) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ N * (M * Mu) := by
          gcongr
          exact_mod_cast hN _
  · -- energy
    rw [dirichletEnergy_ball_congr (w₂ := transplant W₁ B₁ B₂ K u)
      (fun z hz => hTball u z (mem_ball_zero_iff.1 hz).le)]
    refine dirichletEnergy_transplant hB₁b hB₂b hmaps₁ hmaps₂ K
      ((S.finite_toSet.image B₂).countable)
      (fun w => (hfinW w).subset fun p ⟨hp1, hp⟩ =>
        ⟨hW₁ (by rw [mem_closedBall, dist_zero_right]; exact hp1.le), hp⟩)
      hfin₂ hcrit₁ hcrit₂ horth ?_ u (hu.differentiable (by simp))
    intro z' hz' hz'C
    have hz'S : z' ∉ S := fun h => hz'C ⟨z', h, rfl⟩
    have hz'U : z' ∈ U := hcbU (by rw [mem_closedBall, dist_zero_right]; exact hz'.le)
    obtain ⟨σ, hσ, hev⟩ := hlocU z' hz'U hz'S
    rw [hPset z' hz'] at hσ hev
    exact ⟨σ, fun p hp => ⟨(hσ p hp).1, (hσ p hp).2.1⟩, hev⟩
  · -- boundary form
    exact weightedBoundaryMass_transplant hB₁ hn₁ hB₂ hn₂ hW₁ hin₁ K countable_empty
      (fun w hw _ => horthT w hw) u hu.continuous.measurable (T u)
      (measurable_of_contDiffOn_compl (hsmooth u hu)) (fun z hz => hTball u z hz.le)

end SteklovTransplant

end
