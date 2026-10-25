module

public import Mathlib
public import RequestProject.BlaschkeConvergence
public import RequestProject.PaperStatements

/-!
# The boundary weight `|B'|` of a Blaschke product with coalescing zeros

For `B = η ∏_j (z - a_j)/(1 - ā_j z)` with `|η| = 1`, on the unit circle
`|B'(z)| = ∑_j (1 - |a_j|²)/|z - a_j|² = n + Re ∑_j 2 a_j/(z - a_j)`.
If `a_j → 0`, the holomorphic functions `∑_j 2 a_j/(z - a_j)` tend to `0` locally uniformly on
an annulus around `𝕋`; since `d/dt h(e^{it}) = (i z h'(z))|_{z = e^{it}}`, all `t`-derivatives
of `|B'(e^{it})| - n` tend to `0` uniformly (`blaschke_weight_ck_close`).
-/

@[expose] public section

open Complex Metric Set Filter Topology SteklovBlaschke

noncomputable section

namespace SteklovCoalescence

/-- The operator `g ↦ i z g'(z)`, so that `d/dt g(e^{it}) = (Dop g)(e^{it})`. -/
def Dop (g : ℂ → ℂ) : ℂ → ℂ := fun z => I * z * deriv g z

lemma differentiableOn_Dop {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) : DifferentiableOn ℂ (Dop g) U := by
  have := (hg.analyticOnNhd hU).deriv.differentiableOn
  exact (differentiableOn_const _ |>.mul differentiableOn_id).mul this

lemma differentiableOn_Dop_iter {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hg : DifferentiableOn ℂ g U) (j : ℕ) : DifferentiableOn ℂ (Dop^[j] g) U := by
  induction j with
  | zero => simpa using hg
  | succ j ih => rw [Function.iterate_succ_apply']; exact differentiableOn_Dop hU ih

lemma hasDerivAt_re_circle {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hS : sphere (0 : ℂ) 1 ⊆ U)
    (hg : DifferentiableOn ℂ g U) (t : ℝ) :
    HasDerivAt (fun s : ℝ => (g (exp (s * I))).re) ((Dop g (exp (t * I))).re) t := by
  have hz : exp (t * I) ∈ U := hS (by simp [norm_exp_ofReal_mul_I])
  have he : HasDerivAt (fun s : ℝ => exp (s * I)) (I * exp (t * I)) t := by
    have := ((hasDerivAt_id (t : ℂ)).mul_const I).cexp
    have := this.comp_ofReal
    simpa [mul_comm] using this
  have hgd : HasDerivAt g (deriv g (exp (t * I))) (exp (t * I)) :=
    (hg.differentiableAt (hU.mem_nhds hz)).hasDerivAt
  have h2 := hgd.comp t he
  have h3 := reCLM.hasFDerivAt.comp_hasDerivAt t h2
  convert h3 using 1
  all_goals first
    | rfl
    | (funext s; simp [Function.comp_apply, reCLM_apply])
    | (simp only [Dop, reCLM_apply]; ring_nf)

/-- `t`-derivatives of `Re g(e^{it})` are `Re (Dop^j g)(e^{it})`. -/
theorem iteratedDeriv_re_circle {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hS : sphere (0 : ℂ) 1 ⊆ U) (hg : DifferentiableOn ℂ g U) (j : ℕ) :
    iteratedDeriv j (fun s : ℝ => (g (exp (s * I))).re) =
      fun t : ℝ => ((Dop^[j] g) (exp (t * I))).re := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    ext t
    rw [(hasDerivAt_re_circle hU hS (differentiableOn_Dop_iter hU hg j) t).deriv,
      Function.iterate_succ_apply']

/-- `Dop` preserves locally uniform convergence to `0` of holomorphic functions on a bounded
open set. -/
theorem Dop_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} {U : Set ℂ} (hU : IsOpen U)
    {M : ℝ} (hM : ∀ z ∈ U, ‖z‖ ≤ M) {G : ι → ℂ → ℂ} (hG : TendstoLocallyUniformlyOn G 0 l U)
    (hd : ∀ᶠ i in l, DifferentiableOn ℂ (G i) U) :
    TendstoLocallyUniformlyOn (fun i => Dop (G i)) 0 l U ∧
      ∀ᶠ i in l, DifferentiableOn ℂ (Dop (G i)) U := by
  refine ⟨?_, hd.mono fun i hi => differentiableOn_Dop hU hi⟩
  have hD := hG.deriv hd hU
  have h0 : deriv (0 : ℂ → ℂ) = 0 := by ext; simp
  rw [h0] at hD
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hD ⊢
  intro ε hε x hx
  obtain ⟨t, ht, hev⟩ := hD (ε / (|M| + 1)) (by positivity) x hx
  refine ⟨t ∩ U, inter_mem ht self_mem_nhdsWithin, ?_⟩
  filter_upwards [hev] with i hi y hy
  have h1 := hi y hy.1
  simp only [Pi.zero_apply, dist_zero_left, Function.comp_apply] at h1 ⊢
  simp only [Dop, norm_mul, norm_I, one_mul]
  have hMy : ‖y‖ ≤ |M| + 1 := (hM y hy.2).trans ((le_abs_self M).trans (by linarith))
  calc ‖y‖ * ‖deriv (G i) y‖ ≤ (|M| + 1) * ‖deriv (G i) y‖ := by gcongr
    _ < (|M| + 1) * (ε / (|M| + 1)) := by gcongr
    _ = ε := by field_simp

theorem Dop_iter_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} {U : Set ℂ}
    (hU : IsOpen U) {M : ℝ} (hM : ∀ z ∈ U, ‖z‖ ≤ M) {G : ι → ℂ → ℂ}
    (hG : TendstoLocallyUniformlyOn G 0 l U) (hd : ∀ᶠ i in l, DifferentiableOn ℂ (G i) U)
    (j : ℕ) :
    TendstoLocallyUniformlyOn (fun i => Dop^[j] (G i)) 0 l U ∧
      ∀ᶠ i in l, DifferentiableOn ℂ (Dop^[j] (G i)) U := by
  induction j with
  | zero => simpa using ⟨hG, hd⟩
  | succ j ih =>
    simp only [Function.iterate_succ_apply']
    exact Dop_tendstoLocallyUniformlyOn hU hM ih.1 ih.2

/-! ### The boundary weight of a Blaschke product -/

/-- On the circle, `|B'| = ∑_j (1 - |a_j|²)/|z - a_j|²`. -/
lemma norm_deriv_blaschke_circle {n : ℕ} {η : ℂ} (hη : ‖η‖ = 1) {a : Fin n → ℂ}
    (ha : ∀ j, ‖a j‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    ‖deriv (fun w => η * ∏ j, bfac (a j) w) z‖ = ∑ j, bdens (a j) z := by
  obtain ⟨h1, h2, h3⟩ := bdryArg_prod Finset.univ a ha z hz
  have := (h3.const_mul η).deriv
  rw [this, norm_mul, hη, one_mul, norm_div, norm_mul, h1, one_mul, hz, div_one, norm_real,
    Real.norm_eq_abs, abs_of_nonneg h2]

lemma bdens_sub_one {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) :
    bdens a z - 1 = (2 * a / (z - a)).re := by
  have hza : z - a ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; subst h; rw [hz] at ha; exact lt_irrefl _ ha
  have hn : normSq (z - a) ≠ 0 := (normSq_pos.2 hza).ne'
  have hz2 : z.re * z.re + z.im * z.im = 1 := by
    have := normSq_eq_norm_sq z; rw [hz, normSq_apply] at this; linarith
  rw [bdens, div_re]
  simp only [mul_re, mul_im, sub_re, sub_im, normSq_apply] at hn ⊢
  norm_num
  rw [← add_div, div_sub_one hn]
  congr 1
  linear_combination -hz2

/-- The holomorphic function `∑_j 2 a_j/(z - a_j)`. -/
def hsum {n : ℕ} (a : Fin n → ℂ) (z : ℂ) : ℂ := ∑ j, 2 * a j / (z - a j)

lemma weight_sub_eq {n : ℕ} {η : ℂ} (hη : ‖η‖ = 1) {a : Fin n → ℂ} (ha : ∀ j, ‖a j‖ < 1) :
    (fun s : ℝ => ‖deriv (fun w => η * ∏ j, bfac (a j) w) (exp (s * I))‖ - (n : ℝ)) =
      fun s : ℝ => (hsum a (exp (s * I))).re := by
  ext s
  have hz : ‖exp (s * I)‖ = 1 := norm_exp_ofReal_mul_I s
  rw [norm_deriv_blaschke_circle hη ha hz, hsum, re_sum]
  have : (n : ℝ) = ∑ _j : Fin n, (1 : ℝ) := by simp
  rw [this, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => bdens_sub_one (ha j) hz

/-- The annulus `3/4 < |z| < 3/2`. -/
def annulus : Set ℂ := {z | 3 / 4 < ‖z‖ ∧ ‖z‖ < 3 / 2}

lemma isOpen_annulus : IsOpen annulus :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

lemma sphere_subset_annulus : sphere (0 : ℂ) 1 ⊆ annulus := fun z hz => by
  have : ‖z‖ = 1 := by simpa using hz
  constructor <;> linarith

/-- The closed annulus `3/4 ≤ |z| ≤ 3/2`. -/
def cannulus : Set ℂ := {z | 3 / 4 ≤ ‖z‖ ∧ ‖z‖ ≤ 3 / 2}

lemma isCompact_cannulus : IsCompact cannulus := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_const continuous_norm).inter
      (isClosed_le continuous_norm continuous_const)
  · exact (isBounded_closedBall (x := (0 : ℂ)) (r := 3 / 2)).subset fun z hz => by
      simpa using hz.2

lemma sub_ne_zero_of_annulus {a z : ℂ} (ha : ‖a‖ < 1 / 2) (hz : 3 / 4 ≤ ‖z‖) : z - a ≠ 0 := by
  intro h; rw [sub_eq_zero] at h; subst h; linarith

/-- The zero-parameter set `{a : |a_j| < 1/2}`. -/
def zeroSet (n : ℕ) : Set (Fin n → ℂ) := {a | ∀ j, ‖a j‖ < 1 / 2}

lemma isOpen_zeroSet (n : ℕ) : IsOpen (zeroSet n) := by
  simp only [zeroSet, setOf_forall]
  exact isOpen_iInter_of_finite fun j =>
    isOpen_lt (continuous_norm.comp (continuous_apply j)) continuous_const

lemma hsum_continuousOn (n : ℕ) :
    ContinuousOn (fun x : (Fin n → ℂ) × ℂ => hsum x.1 x.2) (zeroSet n ×ˢ cannulus) := by
  simp only [hsum]
  refine continuousOn_finset_sum _ fun j _ => ?_
  refine ContinuousOn.div (f := fun x : (Fin n → ℂ) × ℂ => 2 * x.1 j)
    (g := fun x : (Fin n → ℂ) × ℂ => x.2 - x.1 j)
    (Continuous.continuousOn (by fun_prop)) (Continuous.continuousOn (by fun_prop))
    fun x hx => sub_ne_zero_of_annulus (hx.1 j) hx.2.1

lemma hsum_differentiableOn {n : ℕ} {a : Fin n → ℂ} (ha : ∀ j, ‖a j‖ < 1 / 2) :
    DifferentiableOn ℂ (hsum a) annulus := by
  intro z hz
  have h : DifferentiableAt ℂ (∑ j, fun w => 2 * a j / (w - a j)) z := by
    refine DifferentiableAt.sum fun j _ => ?_
    exact DifferentiableAt.div (c := fun w : ℂ => 2 * a j) (d := fun w : ℂ => w - a j)
      (by fun_prop) (by fun_prop) (sub_ne_zero_of_annulus (ha j) hz.1.le)
  have : (∑ j, fun w => 2 * a j / (w - a j)) = hsum a := by ext; simp [hsum, Finset.sum_apply]
  rw [this] at h
  exact h.differentiableWithinAt

/-- **The boundary weights `|B'|` of Blaschke products with coalescing zeros tend to `n` in every
`C^k(𝕋)` norm.** -/
theorem blaschke_weight_ck_close {ι : Type*} {l : Filter ι} {n : ℕ} (η : ι → ℂ)
    (a : ι → Fin n → ℂ) (hη : ∀ᶠ i in l, ‖η i‖ = 1)
    (ha : ∀ j, Tendsto (fun i => a i j) l (𝓝 0)) (k : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ i in l, CkClose k δ (fun z => ‖deriv (fun w => η i * ∏ j, bfac (a i j) w) z‖) n := by
  have hp : Tendsto a l (𝓝 0) := tendsto_pi_nhds.2 ha
  have hq : (0 : Fin n → ℂ) ∈ zeroSet n := fun j => by simp
  have hev : ∀ᶠ i in l, a i ∈ zeroSet n := hp ((isOpen_zeroSet n).mem_nhds hq)
  have hp' : Tendsto a l (𝓝[zeroSet n] 0) := tendsto_nhdsWithin_iff.2 ⟨hp, hev⟩
  have hU := tendstoUniformlyOn_of_continuousOn_prod isCompact_cannulus
    (f := fun b z => hsum b z) (hsum_continuousOn n) hq hp'
  have h0 : (fun z : ℂ => hsum (0 : Fin n → ℂ) z) = 0 := by ext z; simp [hsum]
  simp only [h0] at hU
  have hloc : TendstoLocallyUniformlyOn (fun i => hsum (a i)) 0 l annulus :=
    (hU.mono fun z hz => ⟨hz.1.le, hz.2.le⟩).tendstoLocallyUniformlyOn
  have hdiff : ∀ᶠ i in l, DifferentiableOn ℂ (hsum (a i)) annulus :=
    hev.mono fun i hi => hsum_differentiableOn hi
  have hM : ∀ z ∈ annulus, ‖z‖ ≤ 3 / 2 := fun z hz => hz.2.le
  have hall : ∀ j ∈ Finset.range (k + 1), ∀ᶠ i in l, ∀ z ∈ sphere (0 : ℂ) 1,
      ‖(Dop^[j] (hsum (a i))) z‖ < δ := by
    intro j _
    obtain ⟨h1, h2⟩ := Dop_iter_tendstoLocallyUniformlyOn isOpen_annulus hM hloc hdiff j
    have hu := (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_annulus).1 h1 _
      sphere_subset_annulus (isCompact_sphere 0 1)
    rw [Metric.tendstoUniformlyOn_iff] at hu
    filter_upwards [hu δ hδ] with i hi z hz
    simpa [dist_eq_norm] using hi z hz
  rw [← Finset.eventually_all] at hall
  filter_upwards [hall, hev, hη] with i hi hai hηi
  intro j hj t
  have ha1 : ∀ m, ‖a i m‖ < 1 := fun m => (hai m).trans (by norm_num)
  rw [weight_sub_eq hηi ha1, iteratedDeriv_re_circle isOpen_annulus sphere_subset_annulus
    (hsum_differentiableOn hai) j]
  refine (abs_re_le_norm _).trans_lt ?_
  exact hi j (Finset.mem_range.2 (by omega)) _ (by simp [norm_exp_ofReal_mul_I])

end SteklovCoalescence
