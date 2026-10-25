module

public import Mathlib
public import RequestProject.SchwarzTrapping
public import RequestProject.PolyTrapping
public import RequestProject.BlaschkeWeight
public import RequestProject.CriticalValues

/-!
# Proposition 3.4.1 (coalescence), from the polynomial-cover data

Setting.  `Q_i(z) = zⁿ + ∑_{k<n} q_{i,k} z^k` with `q_{i,k} → 0` (along any filter); `D_i` is the
connected component of `Q_i⁻¹(𝔻)` containing `0`; `ψ_i : 𝔻 → D_i` is the normalized conformal
map (`ψ_i(0) = 0`, `ψ_i'(0) > 0`) and `B_i = Q_i ∘ ψ_i` is a finite Blaschke product of degree
`n`.  The existence of `ψ_i` (Riemann mapping theorem for `D_i`) and the fact that `Q_i ∘ ψ_i` is
a degree-`n` Blaschke product (a proper holomorphic self-map of `𝔻`) are **explicit inputs**,
packaged in `IsNormalizedDiskCover`; everything else is proved:

* **disk trapping** `B(0,1-θ) ⊆ D_i ⊆ B(0,1+θ)` eventually (`coalescence_trapping`);
* **normalized maps converge**: `ψ_i → id` uniformly on every `|z| ≤ ρ < 1`
  (`coalescence_map_tendsto_id`, via the quantitative Schwarz–Pick estimate);
* **zeros coalesce**: all zeros of `B_i` in `𝔻` tend to `0` (`coalescence_zeros`, via root
  localization for `Q_i` and the inverse Schwarz estimate);
* **`B_i → zⁿ` in `C^∞(𝔻̄)`** (`coalescence_cinfty`), and the boundary weights `|B_i'|` tend to
  the constant `n` in every `C^k(𝕋)` norm (`coalescence_weight`).

`coalescence` collects all conclusions; `prop_3_4_1` specializes to the paper's polynomials
`Q_ε(z) = ε + (λ_* - 1) ε · P(z/τ_ε)` with `P` monic of degree `n` and `τ_ε^n = (λ_* - 1) ε`.
-/

@[expose] public section

open Complex Metric Set Filter Topology SteklovBlaschke

noncomputable section

namespace SteklovCoalescence

/-- **Cover data (explicit input).** `ψ` is the normalized conformal map of `𝔻` onto the
connected component of `Q⁻¹(𝔻)` containing `0` (holomorphic and injective on `𝔻`, `ψ 0 = 0`,
`ψ'(0) > 0`), and `B = Q ∘ ψ` on `𝔻` is a finite Blaschke product of degree `n`. -/
def IsNormalizedDiskCover (Q : ℂ → ℂ) (n : ℕ) (ψ B : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ ψ (ball 0 1) ∧ InjOn ψ (ball 0 1) ∧ ψ 0 = 0 ∧
    0 < (deriv ψ 0).re ∧ (deriv ψ 0).im = 0 ∧
    ψ '' ball 0 1 = connectedComponentIn (Q ⁻¹' ball 0 1) 0 ∧
    IsFiniteBlaschke B n ∧ ∀ z ∈ ball (0 : ℂ) 1, B z = Q (ψ z)

variable {ι : Type*} {l : Filter ι} {n : ℕ}

lemma eventually_coeff_small {q : ι → Fin n → ℂ} (hq : ∀ k, Tendsto (fun i => q i k) l (𝓝 0))
    {s : ℝ} (hs : 0 < s) : ∀ᶠ i in l, ∀ k, ‖q i k‖ ≤ s :=
  Filter.eventually_all.2 fun k =>
    ((hq k).eventually (closedBall_mem_nhds 0 hs)).mono fun _ hi => mem_closedBall_zero_iff.1 hi

/-- **Disk trapping.** -/
theorem coalescence_trapping (hn : 1 ≤ n) {q : ι → Fin n → ℂ}
    (hq : ∀ k, Tendsto (fun i => q i k) l (𝓝 0)) {ψ B : ι → ℂ → ℂ}
    (hcov : ∀ᶠ i in l, IsNormalizedDiskCover (polyQ n (q i)) n (ψ i) (B i))
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    ∀ᶠ i in l, ball 0 (1 - θ) ⊆ ψ i '' ball 0 1 ∧ ψ i '' ball 0 1 ⊆ ball 0 (1 + θ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (1 - θ) ^ n < 1 := pow_lt_one₀ (by linarith) (by linarith) (by omega)
  set m := min θ (1 - (1 - θ) ^ n)
  have hm : 0 < m := lt_min hθ0 (by linarith)
  set s := m / (2 * n)
  have hs : 0 < s := by positivity
  have hns : n * s = m / 2 := by simp only [s]; field_simp
  filter_upwards [hcov, eventually_coeff_small hq hs] with i hi hqi
  rw [hi.2.2.2.2.2.1]
  refine ⟨ball_subset_component hqi (by linarith) (by linarith) ?_,
    component_subset_ball hn hqi ?_ hs.le⟩
  · have : m ≤ 1 - (1 - θ) ^ n := min_le_right _ _
    linarith
  · have : m ≤ θ := min_le_left _ _
    linarith

/-- **The normalized maps tend to the identity**, uniformly on `|z| ≤ ρ` for each `ρ < 1`. -/
theorem coalescence_map_tendsto_id (hn : 1 ≤ n) {q : ι → Fin n → ℂ}
    (hq : ∀ k, Tendsto (fun i => q i k) l (𝓝 0)) {ψ B : ι → ℂ → ℂ}
    (hcov : ∀ᶠ i in l, IsNormalizedDiskCover (polyQ n (q i)) n (ψ i) (B i))
    {ρ : ℝ} (hρ : ρ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ z ∈ closedBall (0 : ℂ) ρ, ‖ψ i z - z‖ < ε := by
  have hρ' : 0 < 1 - ρ := by linarith
  set C := 6 / (1 - ρ) + 2
  have hC : 0 < C := by positivity
  set θ := min (1 / 2) (ε / (2 * C))
  have hθ0 : 0 < θ := lt_min (by norm_num) (by positivity)
  have hθ1 : θ < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hθC : θ * C < ε := by
    have : θ ≤ ε / (2 * C) := min_le_right _ _
    calc θ * C ≤ ε / (2 * C) * C := by gcongr
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  filter_upwards [hcov, coalescence_trapping hn hq hcov hθ0 hθ1] with i hi htr z hz
  obtain ⟨hd, hinj, h0, hre, him, -⟩ := hi
  have hz' : ‖z‖ ≤ ρ := mem_closedBall_zero_iff.1 hz
  have hz1 : ‖z‖ < 1 := hz'.trans_lt hρ
  have ha : deriv (ψ i) 0 = ((deriv (ψ i) 0).re : ℂ) := by
    apply Complex.ext <;> simp [him]
  have hb := trapped_map_close_to_id hd hinj h0 ha hre (by linarith) htr.1 htr.2
    (show 1 + θ < 1 + 2 * θ by linarith) hz1
  have hzn := norm_nonneg z
  have h1 : (1 + 2 * θ) * (1 - (1 - θ) / (1 + 2 * θ)) = 3 * θ := by
    field_simp; ring
  have h2 : |1 + 2 * θ - 1| = 2 * θ := by rw [abs_of_pos (by linarith)]; ring
  have h3 : ‖z‖ * ((1 + ‖z‖) / (1 - ‖z‖)) ≤ 2 / (1 - ρ) := by
    rw [← mul_div_assoc, div_le_div_iff₀ (by linarith) hρ']
    have h4 : ‖z‖ * (1 + ‖z‖) ≤ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h4 hρ'.le]
  calc ‖ψ i z - z‖
      ≤ (1 + 2 * θ) * (‖z‖ * ((1 - (1 - θ) / (1 + 2 * θ)) * (1 + ‖z‖) / (1 - ‖z‖))) +
          |1 + 2 * θ - 1| * ‖z‖ := hb
    _ = 3 * θ * (‖z‖ * ((1 + ‖z‖) / (1 - ‖z‖))) + 2 * θ * ‖z‖ := by
        rw [h2, ← h1]; ring
    _ ≤ 3 * θ * (2 / (1 - ρ)) + 2 * θ * 1 := by gcongr
    _ = θ * C := by simp only [C]; ring
    _ < ε := hθC

/-- **Coalescence of zeros**: all zeros of `B_i` in `𝔻` tend to `0`. -/
theorem coalescence_zeros (hn : 1 ≤ n) {q : ι → Fin n → ℂ}
    (hq : ∀ k, Tendsto (fun i => q i k) l (𝓝 0)) {ψ B : ι → ℂ → ℂ}
    (hcov : ∀ᶠ i in l, IsNormalizedDiskCover (polyQ n (q i)) n (ψ i) (B i))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ z ∈ ball (0 : ℂ) 1, B i z = 0 → ‖z‖ < ε := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set ρ := min (ε / 4) (1 / 4)
  have hρ0 : 0 < ρ := lt_min (by positivity) (by norm_num)
  have hρ1 : ρ ≤ 1 / 4 := min_le_right _ _
  have hρε : ρ ≤ ε / 4 := min_le_left _ _
  set s := ρ ^ n / (2 * n)
  have hs : 0 < s := by positivity
  have hns : n * s < ρ ^ n := by
    simp only [s]; rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [pow_pos hρ0 n]
  filter_upwards [hcov, eventually_coeff_small hq hs,
    coalescence_trapping hn hq hcov (θ := 1 / 2) (by norm_num) (by norm_num)]
    with i hi hqi htr z hz hBz
  obtain ⟨hd, hinj, h0, -, -, -, -, hBQ⟩ := hi
  have hroot : polyQ n (q i) (ψ i z) = 0 := by rw [← hBQ z hz, hBz]
  have hsmall := polyQ_root_small hn hqi hρ0 (by linarith) hns hroot
  have hball : ball (0 : ℂ) (1 / 2) ⊆ ψ i '' ball 0 1 := by
    have := htr.1; norm_num at this ⊢; exact this
  have := inverse_schwarz hd hinj h0 (by norm_num) hball hz (by linarith)
  have h2 : ‖ψ i z‖ / (1 / 2) = 2 * ‖ψ i z‖ := by ring
  linarith

/-! ### Blaschke parameters -/

lemma bfac_self (a : ℂ) : bfac a a = 0 := by simp [bfac]

/-- The zeros of a Blaschke product `η ∏ bfac (a j)` include every `a j`. -/
lemma blaschke_zero_at {η : ℂ} {a : Fin n → ℂ} (j : Fin n) :
    η * ∏ m, bfac (a m) (a j) = 0 := by
  rw [Finset.prod_eq_zero (Finset.mem_univ j) (bfac_self _), mul_zero]

/-- Choice of Blaschke parameters along the filter. -/
lemma exists_blaschke_params {B : ι → ℂ → ℂ} (hB : ∀ᶠ i in l, IsFiniteBlaschke (B i) n) :
    ∃ (η : ι → ℂ) (a : ι → Fin n → ℂ), ∀ᶠ i in l, ‖η i‖ = 1 ∧ (∀ j, ‖a i j‖ < 1) ∧
      B i = fun z => η i * ∏ j, bfac (a i j) z := by
  classical
  refine ⟨fun i => if h : IsFiniteBlaschke (B i) n then h.choose else 1,
    fun i => if h : IsFiniteBlaschke (B i) n then h.choose_spec.choose else 0, ?_⟩
  filter_upwards [hB] with i hi
  simp only [dif_pos hi]
  exact hi.choose_spec.choose_spec

lemma polyQ_continuous₂ (n : ℕ) :
    Continuous (fun p : (Fin n → ℂ) × ℂ => polyQ n p.1 p.2) := by
  unfold polyQ; fun_prop

/-- **`B_i → zⁿ` in `C^∞(𝔻̄)`.** -/
theorem coalescence_cinfty (hn : 1 ≤ n) {q : ι → Fin n → ℂ}
    (hq : ∀ k, Tendsto (fun i => q i k) l (𝓝 0)) {ψ B : ι → ℂ → ℂ}
    (hcov : ∀ᶠ i in l, IsNormalizedDiskCover (polyQ n (q i)) n (ψ i) (B i))
    (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ k (fun w => B i w - w ^ n) z‖ < ε := by
  obtain ⟨η, a, hηa⟩ := exists_blaschke_params (hcov.mono fun i hi => hi.2.2.2.2.2.2.1)
  -- zeros tend to `0`
  have ha : ∀ j, Tendsto (fun i => a i j) l (𝓝 0) := by
    intro j
    rw [Metric.tendsto_nhds]
    intro e he
    filter_upwards [coalescence_zeros hn hq hcov he, hηa] with i hi hpar
    rw [dist_zero_right]
    refine hi (a i j) (mem_ball_zero_iff.2 (hpar.2.1 j)) ?_
    rw [hpar.2.2]; exact blaschke_zero_at j
  -- `η_i → 1`, by evaluating at `1/2`
  have hψhalf : Tendsto (fun i => ψ i (1 / 2)) l (𝓝 (1 / 2)) := by
    rw [Metric.tendsto_nhds]
    intro e he
    filter_upwards [coalescence_map_tendsto_id hn hq hcov (ρ := 1 / 2) (by norm_num) he]
      with i hi
    rw [dist_eq_norm]
    exact hi _ (by rw [mem_closedBall_zero_iff]; norm_num)
  have hqt : Tendsto q l (𝓝 0) := tendsto_pi_nhds.2 hq
  have hBhalf : Tendsto (fun i => polyQ n (q i) (ψ i (1 / 2))) l
      (𝓝 (polyQ n 0 (1 / 2))) :=
    ((polyQ_continuous₂ n).tendsto ((0 : Fin n → ℂ), (1 / 2 : ℂ))).comp
      (hqt.prodMk_nhds hψhalf)
  have hP0 : polyQ n 0 (1 / 2) = (1 / 2 : ℂ) ^ n := by simp [polyQ]
  have hcont : ∀ j, Tendsto (fun i => bfac (a i j) (1 / 2)) l (𝓝 (1 / 2)) := by
    intro j
    have hc : ContinuousAt (fun b : ℂ => bfac b (1 / 2)) 0 := by
      unfold bfac
      refine ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)
    have := hc.tendsto.comp (ha j)
    first
      | simpa [bfac, Function.comp_def] using this
      | (rw [show bfac 0 (1 / 2 : ℂ) = 1 / 2 by simp [bfac]] at this; exact this)
  have hprod : Tendsto (fun i => ∏ j, bfac (a i j) (1 / 2)) l (𝓝 ((1 / 2 : ℂ) ^ n)) := by
    have := tendsto_finset_prod (Finset.univ : Finset (Fin n)) fun j _ => hcont j
    simpa using this
  have hne : (1 / 2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  have hη : Tendsto η l (𝓝 1) := by
    have hdiv := hBhalf.div hprod hne
    rw [hP0, div_self hne] at hdiv
    refine hdiv.congr' ?_
    filter_upwards [hcov, hηa, hprod.eventually_ne hne] with i hi hpar hpne
    simp only [Pi.div_apply]
    rw [← hi.2.2.2.2.2.2.2 (1 / 2) (by rw [mem_ball_zero_iff]; norm_num), hpar.2.2]
    field_simp
  filter_upwards [blaschke_cinfty_convergence η a hη ha k hε, hηa] with i hi hpar
  rw [hpar.2.2]
  exact hi

/-- **The boundary weights `|B_i'|` tend to the constant `n` in every `C^k(𝕋)` norm.** -/
theorem coalescence_weight (hn : 1 ≤ n) {q : ι → Fin n → ℂ}
    (hq : ∀ k, Tendsto (fun i => q i k) l (𝓝 0)) {ψ B : ι → ℂ → ℂ}
    (hcov : ∀ᶠ i in l, IsNormalizedDiskCover (polyQ n (q i)) n (ψ i) (B i))
    (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ i in l, CkClose k δ (fun z => ‖deriv (B i) z‖) n := by
  obtain ⟨η, a, hηa⟩ := exists_blaschke_params (hcov.mono fun i hi => hi.2.2.2.2.2.2.1)
  have ha : ∀ j, Tendsto (fun i => a i j) l (𝓝 0) := by
    intro j
    rw [Metric.tendsto_nhds]
    intro e he
    filter_upwards [coalescence_zeros hn hq hcov he, hηa] with i hi hpar
    rw [dist_zero_right]
    refine hi (a i j) (mem_ball_zero_iff.2 (hpar.2.1 j)) ?_
    rw [hpar.2.2]; exact blaschke_zero_at j
  filter_upwards [blaschke_weight_ck_close η a (hηa.mono fun i h => h.1) ha k hδ, hηa]
    with i hi hpar
  rw [hpar.2.2]
  exact hi

/-! ### All conclusions of Proposition 3.4.1 -/

/-- The conclusions of Proposition 3.4.1 for a family of cover data `(ψ_i, B_i)` along `l`. -/
def CoalescenceConclusions {ι : Type*} (l : Filter ι) (n : ℕ) (ψ B : ι → ℂ → ℂ) : Prop :=
  -- disk trapping of the cover domains `ψ_i(𝔻)`
  (∀ θ : ℝ, 0 < θ → θ < 1 →
    ∀ᶠ i in l, ball 0 (1 - θ) ⊆ ψ i '' ball 0 1 ∧ ψ i '' ball 0 1 ⊆ ball 0 (1 + θ)) ∧
  -- normalized maps converge to the identity locally uniformly on `𝔻`
  (∀ ρ : ℝ, ρ < 1 → ∀ ε > (0 : ℝ),
    ∀ᶠ i in l, ∀ z ∈ closedBall (0 : ℂ) ρ, ‖ψ i z - z‖ < ε) ∧
  -- coalescence of the zeros of `B_i`
  (∀ ε > (0 : ℝ), ∀ᶠ i in l, ∀ z ∈ ball (0 : ℂ) 1, B i z = 0 → ‖z‖ < ε) ∧
  -- `B_i → zⁿ` in `C^∞(𝔻̄)`
  (∀ k : ℕ, ∀ ε > (0 : ℝ), ∀ᶠ i in l, ∀ z ∈ closedBall (0 : ℂ) 1,
    ‖iteratedFDeriv ℝ k (fun w => B i w - w ^ n) z‖ < ε) ∧
  -- `|B_i'| → n` in `C^∞(𝕋)`
  (∀ k : ℕ, ∀ δ > (0 : ℝ), ∀ᶠ i in l, CkClose k δ (fun z => ‖deriv (B i) z‖) n)

/-- **Proposition 3.4.1 (coalescence), general nearly-monomial form.** -/
theorem coalescence (hn : 1 ≤ n) {q : ι → Fin n → ℂ}
    (hq : ∀ k, Tendsto (fun i => q i k) l (𝓝 0)) {ψ B : ι → ℂ → ℂ}
    (hcov : ∀ᶠ i in l, IsNormalizedDiskCover (polyQ n (q i)) n (ψ i) (B i)) :
    CoalescenceConclusions l n ψ B :=
  ⟨fun _ h0 h1 => coalescence_trapping hn hq hcov h0 h1,
    fun _ hρ _ hε => coalescence_map_tendsto_id hn hq hcov hρ hε,
    fun _ hε => coalescence_zeros hn hq hcov hε,
    fun k _ hε => coalescence_cinfty hn hq hcov k hε,
    fun k _ hδ => coalescence_weight hn hq hcov k hδ⟩

/-! ### The paper's polynomials `Q_ε(z) = ε + (λ_* - 1) ε P(z/τ_ε)` -/

open SteklovCritical in
/-- The paper's rescaled polynomial `Q_ε(z) = ε + δ_ε P(z/τ_ε)`, `δ_ε = (λ_* - 1) ε`; its critical
values are `ε` and `λ_* ε` when those of `P` are `0` and `1`. -/
def paperQ (P : Polynomial ℂ) (τ : ℝ → ℂ) (ε : ℝ) (z : ℂ) : ℂ :=
  ε + (lamStar - 1) * ε * P.eval (z / τ ε)

open SteklovCritical in
/-- Its coefficients below the leading one: `q_0 = ε + δ_ε c_0`, `q_k = c_k δ_ε τ_ε^{-k}`. -/
def paperCoeff (P : Polynomial ℂ) (τ : ℝ → ℂ) (n : ℕ) (ε : ℝ) (k : Fin n) : ℂ :=
  (if (k : ℕ) = 0 then (ε : ℂ) else 0) + P.coeff k * ((lamStar - 1) * ε * (τ ε)⁻¹ ^ (k : ℕ))

open SteklovCritical in
lemma lamStar_sub_one_ne_zero : lamStar - 1 ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp [lamStar] at this

open SteklovCritical in
lemma eval_monic {P : Polynomial ℂ} (hP : P.Monic) {n : ℕ} (hdeg : P.natDegree = n) (w : ℂ) :
    P.eval w = w ^ n + ∑ k : Fin n, P.coeff k * w ^ (k : ℕ) := by
  conv_lhs => rw [hP.as_sum]
  rw [hdeg, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_finset_sum, Finset.sum_range]
  simp

open SteklovCritical in
/-- **Link with the paper's polynomial data**: `Q_ε = zⁿ + ∑_{k<n} q_{ε,k} z^k`. -/
theorem paperQ_eq_polyQ {P : Polynomial ℂ} (hP : P.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : P.natDegree = n) {τ : ℝ → ℂ} {ε : ℝ} (hε : ε ≠ 0)
    (hτ : τ ε ^ n = (lamStar - 1) * ε) :
    paperQ P τ ε = polyQ n (paperCoeff P τ n ε) := by
  have hδ : (lamStar - 1) * (ε : ℂ) ≠ 0 :=
    mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast hε)
  have hτ0 : τ ε ≠ 0 := by
    intro h; rw [h, zero_pow (by omega)] at hτ; exact hδ hτ.symm
  ext z
  rw [paperQ, eval_monic hP hdeg, polyQ]
  simp only [paperCoeff, add_mul, Finset.sum_add_distrib]
  have h1 : ∑ k : Fin n, (if (k : ℕ) = 0 then (ε : ℂ) else 0) * z ^ (k : ℕ) = ε := by
    rw [Finset.sum_eq_single ⟨0, by omega⟩]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  have h2 : ∀ k : Fin n, (lamStar - 1) * (ε : ℂ) * (P.coeff k * (z / τ ε) ^ (k : ℕ)) =
      P.coeff k * ((lamStar - 1) * ε * (τ ε)⁻¹ ^ (k : ℕ)) * z ^ (k : ℕ) := by
    intro k; rw [div_pow, inv_pow]; ring
  have h3 : (lamStar - 1) * (ε : ℂ) * (z / τ ε) ^ n = z ^ n := by
    rw [div_pow, ← hτ]; field_simp
  rw [h1, mul_add, h3, Finset.mul_sum, Finset.sum_congr rfl fun k _ => h2 k]
  ring

open SteklovCritical in
lemma paperCoeff_tendsto {P : Polynomial ℂ} {n : ℕ} {τ : ℝ → ℂ}
    (hτ : ∀ ε, τ ε ^ n = (lamStar - 1) * ε) (k : Fin n) :
    Tendsto (fun ε => paperCoeff P τ n ε k) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun ε : ℝ => (if (k : ℕ) = 0 then (ε : ℂ) else 0)) (𝓝[>] 0) (𝓝 0) := by
    split_ifs
    · exact (Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · exact tendsto_const_nhds
  have h2 := (coalescence_coeff_tendsto_zero n k k.2 τ hτ).const_mul (P.coeff k)
  rw [mul_zero] at h2
  simpa [paperCoeff] using h1.add h2

open SteklovCritical in
/-- **Proposition 3.4.1 (coalescence) for the paper's polynomial covers.**  Let `P` be monic of
degree `n ≥ 1` (the polynomial of Lemma 3.2.1), `τ_ε^n = (λ_* - 1) ε`, and
`Q_ε(z) = ε + (λ_* - 1) ε P(z/τ_ε)`.  If for small `ε > 0` the maps `ψ_ε` are normalized
conformal maps of `𝔻` onto the component of `Q_ε⁻¹(𝔻)` containing `0` and
`B_ε = Q_ε ∘ ψ_ε` are finite Blaschke products of degree `n` (explicit cover input), then the
cover domains are trapped between disks of radii `→ 1`, `ψ_ε → id`, the zeros of `B_ε`
coalesce at `0`, `B_ε → zⁿ` in `C^∞(𝔻̄)` and `|B_ε'| → n` in `C^∞(𝕋)`. -/
theorem prop_3_4_1 {P : Polynomial ℂ} (hP : P.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : P.natDegree = n) {τ : ℝ → ℂ} (hτ : ∀ ε, τ ε ^ n = (lamStar - 1) * ε)
    {ψ B : ℝ → ℂ → ℂ}
    (hcov : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsNormalizedDiskCover (paperQ P τ ε) n (ψ ε) (B ε)) :
    CoalescenceConclusions (𝓝[>] (0 : ℝ)) n ψ B := by
  refine coalescence hn (paperCoeff_tendsto (P := P) hτ) ?_
  filter_upwards [hcov, self_mem_nhdsWithin] with ε hε hpos
  rwa [← paperQ_eq_polyQ hP hn hdeg (ne_of_gt hpos) (hτ ε)]

end SteklovCoalescence
