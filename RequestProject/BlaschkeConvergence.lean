module

public import Mathlib
public import RequestProject.Blaschke
public import RequestProject.OuterConvergence

/-!
# Convergence of finite Blaschke products with coalescing zeros (Proposition 3.4.1)

* `tendstoUniformlyOn_of_continuousOn_prod`: a jointly continuous family converges uniformly on a
  compact set when the parameter converges.
* `iteratedDeriv_tendstoLocallyUniformlyOn_zero` (Weierstrass, iterated) and
  `eventually_norm_iteratedFDeriv_lt`: locally uniform convergence of holomorphic functions to `0`
  gives uniform convergence of all real derivatives on compact subsets.
* `blaschke_cinfty_convergence`: if `η → 1` and all zeros `a_j → 0`, then
  `η ∏ (z - a_j)/(1 - ā_j z) → zⁿ` in `C^∞(𝔻̄)`.
* `blaschke_weight_ck_close`: under the same hypotheses the boundary weight `|B'|` on `𝕋`
  tends to the constant `n` in every `C^k(𝕋)` norm (in the sense of `CkClose`).
-/

@[expose] public section

open Complex Metric Set Filter Topology SteklovBlaschke

noncomputable section

namespace SteklovCoalescence

/-! ### Parametric uniform convergence -/

theorem tendstoUniformlyOn_of_continuousOn_prod {ι α β E : Type*} [TopologicalSpace α]
    [TopologicalSpace β] [UniformSpace E] {f : α → β → E} {s : Set α} {k : Set β} {q : α}
    (hk : IsCompact k) (hf : ContinuousOn f.uncurry (s ×ˢ k)) (hq : q ∈ s) {p : ι → α}
    {l : Filter ι} (hp : Tendsto p l (𝓝[s] q)) :
    TendstoUniformlyOn (fun i => f (p i)) (f q) l k := by
  intro u hu
  obtain ⟨v, hv, hvu⟩ := hk.mem_uniformity_of_prod hf hq (symm_le_uniformity hu)
  filter_upwards [hp hv] with i hi x hx
  exact hvu (p i) hi x hx

/-! ### Iterated Weierstrass theorem -/

theorem iteratedDeriv_tendstoLocallyUniformlyOn_zero {ι : Type*} {l : Filter ι} {U : Set ℂ}
    (hU : IsOpen U) {G : ι → ℂ → ℂ} (hG : TendstoLocallyUniformlyOn G 0 l U)
    (hd : ∀ᶠ i in l, DifferentiableOn ℂ (G i) U) (k : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv k (G i)) 0 l U ∧
      ∀ᶠ i in l, DifferentiableOn ℂ (iteratedDeriv k (G i)) U := by
  induction k with
  | zero => simpa using ⟨hG, hd⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · have := h1.deriv h2 hU
      simp only [iteratedDeriv_succ]
      have h0 : deriv (0 : ℂ → ℂ) = 0 := by ext; simp
      rw [h0] at this
      exact this
    · filter_upwards [h2] with i hi
      rw [iteratedDeriv_succ]
      exact (hi.analyticOnNhd hU).deriv.differentiableOn

theorem eventually_norm_iteratedFDeriv_lt {ι : Type*} {l : Filter ι} {U K : Set ℂ}
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) {G : ι → ℂ → ℂ}
    (hG : TendstoLocallyUniformlyOn G 0 l U) (hd : ∀ᶠ i in l, DifferentiableOn ℂ (G i) U)
    (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ i in l, ∀ z ∈ K, ‖iteratedFDeriv ℝ k (G i) z‖ < η := by
  obtain ⟨h1, h2⟩ := iteratedDeriv_tendstoLocallyUniformlyOn_zero hU hG hd k
  have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 h1 K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at hu
  filter_upwards [hu η hη, hd] with i hi hdi z hz
  rw [OuterConvergence.norm_iteratedFDeriv_real_eq hU hdi (hKU hz)]
  simpa [dist_eq_norm] using hi z hz

/-! ### Blaschke products with coalescing zeros -/

lemma bfac_zero (z : ℂ) : bfac 0 z = z := by simp [bfac]

lemma bfac_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1 / 2) (hz : ‖z‖ ≤ 3 / 2) :
    1 - (starRingEnd ℂ) a * z ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * z = 1 := (sub_eq_zero.1 h).symm
  have h2 := congrArg norm h1
  rw [norm_mul, Complex.norm_conj, norm_one] at h2
  nlinarith [norm_nonneg a, norm_nonneg z]

/-- The parameter set `{(η, a) : |a_j| < 1/2}`. -/
def paramSet (n : ℕ) : Set (ℂ × (Fin n → ℂ)) := {p | ∀ j, ‖p.2 j‖ < 1 / 2}

lemma isOpen_paramSet (n : ℕ) : IsOpen (paramSet n) := by
  simp only [paramSet, setOf_forall]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (continuous_norm.comp ((continuous_apply j).comp continuous_snd)) continuous_const

lemma blaschke_continuousOn (n : ℕ) :
    ContinuousOn (fun x : (ℂ × (Fin n → ℂ)) × ℂ =>
      x.1.1 * ∏ j, bfac (x.1.2 j) x.2 - x.2 ^ n) (paramSet n ×ˢ closedBall 0 (3 / 2)) := by
  refine ContinuousOn.sub (ContinuousOn.mul (continuous_fst.comp continuous_fst).continuousOn
    (continuousOn_finset_prod _ fun j _ => ?_)) (by fun_prop)
  refine ContinuousOn.div (f := fun x : (ℂ × (Fin n → ℂ)) × ℂ => x.2 - x.1.2 j)
    (g := fun x : (ℂ × (Fin n → ℂ)) × ℂ => 1 - (starRingEnd ℂ) (x.1.2 j) * x.2)
    (Continuous.continuousOn (by fun_prop)) (Continuous.continuousOn (by fun_prop))
    fun x hx => ?_
  exact bfac_den_ne_zero (hx.1 j) (mem_closedBall_zero_iff.1 hx.2)

lemma blaschke_differentiableOn {n : ℕ} {η : ℂ} {a : Fin n → ℂ} (ha : ∀ j, ‖a j‖ < 1 / 2) :
    DifferentiableOn ℂ (fun w => η * ∏ j, bfac (a j) w - w ^ n) (ball 0 (3 / 2)) := by
  intro w hw
  have hw' : ‖w‖ ≤ 3 / 2 := (mem_ball_zero_iff.1 hw).le
  refine DifferentiableWithinAt.sub (DifferentiableWithinAt.mul (differentiableWithinAt_const _)
    ?_) (by fun_prop)
  have h : DifferentiableAt ℂ (∏ j, bfac (a j)) w := by
    refine DifferentiableAt.finset_prod (𝕜 := ℂ) (𝔸' := ℂ) fun j _ => ?_
    exact DifferentiableAt.div (c := fun w : ℂ => w - a j)
      (d := fun w : ℂ => 1 - (starRingEnd ℂ) (a j) * w) (by fun_prop) (by fun_prop)
      (bfac_den_ne_zero (ha j) hw')
  have : (∏ j, bfac (a j)) = fun w => ∏ j, bfac (a j) w := by ext; simp [Finset.prod_apply]
  rw [this] at h
  exact h.differentiableWithinAt

/-- **Blaschke products with coalescing zeros converge to `zⁿ` in `C^∞(𝔻̄)`.** -/
theorem blaschke_cinfty_convergence {ι : Type*} {l : Filter ι} {n : ℕ} (η : ι → ℂ)
    (a : ι → Fin n → ℂ) (hη : Tendsto η l (𝓝 1)) (ha : ∀ j, Tendsto (fun i => a i j) l (𝓝 0))
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ k (fun w => η i * ∏ j, bfac (a i j) w - w ^ n) z‖ < ε := by
  have hp : Tendsto (fun i => (η i, a i)) l (𝓝 ((1 : ℂ), (0 : Fin n → ℂ))) :=
    hη.prodMk_nhds (tendsto_pi_nhds.2 ha)
  have hq : ((1 : ℂ), (0 : Fin n → ℂ)) ∈ paramSet n := fun j => by simp
  have hev : ∀ᶠ i in l, (η i, a i) ∈ paramSet n := hp ((isOpen_paramSet n).mem_nhds hq)
  have hp' : Tendsto (fun i => (η i, a i)) l (𝓝[paramSet n] ((1 : ℂ), (0 : Fin n → ℂ))) :=
    tendsto_nhdsWithin_iff.2 ⟨hp, hev⟩
  have hU := tendstoUniformlyOn_of_continuousOn_prod (isCompact_closedBall 0 (3 / 2))
    (f := fun p w => p.1 * ∏ j, bfac (p.2 j) w - w ^ n) (blaschke_continuousOn n) hq hp'
  have h0 : (fun w : ℂ => (1 : ℂ) * ∏ j : Fin n, bfac ((0 : Fin n → ℂ) j) w - w ^ n) = 0 := by
    ext w; simp [bfac_zero]
  simp only [h0] at hU
  have hloc : TendstoLocallyUniformlyOn
      (fun i w => η i * ∏ j, bfac (a i j) w - w ^ n) 0 l (ball 0 (3 / 2)) :=
    (hU.mono ball_subset_closedBall).tendstoLocallyUniformlyOn
  refine eventually_norm_iteratedFDeriv_lt isOpen_ball (isCompact_closedBall 0 1)
    (closedBall_subset_ball (by norm_num)) hloc ?_ k hε
  filter_upwards [hev] with i hi
  exact blaschke_differentiableOn hi

end SteklovCoalescence
