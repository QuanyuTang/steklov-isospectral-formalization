module

public import Mathlib
public import RequestProject.Blaschke
public import RequestProject.Montel
public import RequestProject.Hurwitz

/-!
# The Riemann mapping theorem (Koebe's extremal proof)

Let `U ⊆ ℂ` be a bounded connected open set containing `0` on which every zero-free holomorphic
function has a holomorphic square root.  Then there is a holomorphic bijection `φ : U → 𝔻` with
`φ(0) = 0` and `φ'(0) > 0` (`riemann_mapping`).

Proof (Koebe): among injective holomorphic `f : U → 𝔻` with `f(0) = 0` maximize `|f'(0)|`
(bounded by the Cauchy estimate).  A maximizing sequence has a locally uniform cluster point `g`
(Montel, `montel`), which is holomorphic with `|g'(0)| = sup > 0`, hence injective (Hurwitz,
`hurwitz_injOn`) and with values in `𝔻` (maximum modulus).  If `g` missed a point `a ∈ 𝔻`, the
square-root trick `G = m_b ∘ √(m_a ∘ g)` (`m_a(z) = (z-a)/(1-āz)`) would give an admissible map
with `|G'(0)| = (1+|b|²)/(2|b|) |g'(0)| > |g'(0)|` (`koebe_step`).
-/

@[expose] public section

open Set Filter Topology Metric Complex SteklovBlaschke

noncomputable section

namespace SteklovRiemann

/-! ### Möbius maps of the disk -/

lemma norm_bfac_lt {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖bfac a z‖ < 1 := by
  have hd := denom_ne_zero ha hz.le
  rw [bfac, norm_div, div_lt_one (norm_pos_iff.2 hd)]
  have h1 : normSq a < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have h2 : normSq z < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have := normSq_denom_sub a z
  have h3 : normSq (z - a) < normSq (1 - (starRingEnd ℂ) a * z) := by nlinarith
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at h3
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]

lemma bfac_injOn {a : ℂ} (ha : ‖a‖ < 1) : InjOn (bfac a) (closedBall 0 1) := by
  intro z hz w hw h
  have hz' := denom_ne_zero ha (mem_closedBall_zero_iff.1 hz)
  have hw' := denom_ne_zero ha (mem_closedBall_zero_iff.1 hw)
  rw [bfac, bfac, div_eq_div_iff hz' hw'] at h
  have ha2 : (1 - (starRingEnd ℂ) a * a) ≠ 0 := by
    rw [Complex.conj_mul']
    intro h0
    have : ((‖a‖ ^ 2 : ℝ) : ℂ) = 1 := by push_cast; linear_combination -h0
    have : ‖a‖ ^ 2 = 1 := by exact_mod_cast this
    nlinarith [norm_nonneg a]
  have : (z - w) * (1 - (starRingEnd ℂ) a * a) = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h1 | h1
  · exact sub_eq_zero.1 h1
  · exact absurd h1 ha2

lemma bfac_eq_zero_iff {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) : bfac a z = 0 ↔ z = a := by
  rw [bfac, div_eq_zero_iff, sub_eq_zero]
  exact ⟨fun h => h.resolve_right (denom_ne_zero ha hz), Or.inl⟩

lemma bfac_zero (a : ℂ) : bfac a 0 = -a := by simp [bfac]

lemma bfac_self (a : ℂ) : bfac a a = 0 := by simp [bfac]

lemma differentiableOn_bfac_comp {a : ℂ} (ha : ‖a‖ < 1) {U : Set ℂ} {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g U) (hgU : MapsTo g U (ball 0 1)) :
    DifferentiableOn ℂ (fun z => bfac a (g z)) U := fun z hz =>
  (differentiableAt_bfac ha (mem_ball_zero_iff.1 (hgU hz)).le).comp_differentiableWithinAt z
    (hg z hz)

/-- The admissible family: injective holomorphic maps `U → 𝔻` fixing `0`. -/
def Admissible (U : Set ℂ) (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ InjOn f U ∧ MapsTo f U (ball 0 1) ∧ f 0 = 0

/-- Every zero-free holomorphic function on `U` has a holomorphic square root. -/
def HasSqrtProperty (U : Set ℂ) : Prop :=
  ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U → (∀ z ∈ U, f z ≠ 0) →
    ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ ∀ z ∈ U, g z ^ 2 = f z

/-- **Koebe's square-root step.** -/
theorem koebe_step {U : Set ℂ} (hU : IsOpen U) (h0 : (0 : ℂ) ∈ U) (hsq : HasSqrtProperty U)
    {g : ℂ → ℂ} (hg : Admissible U g) (hg' : deriv g 0 ≠ 0) {a : ℂ} (ha : ‖a‖ < 1)
    (hna : a ∉ g '' U) : ∃ G, Admissible U G ∧ ‖deriv g 0‖ < ‖deriv G 0‖ := by
  obtain ⟨hgd, hginj, hgU, hg0⟩ := hg
  have ha0 : a ≠ 0 := fun h => hna ⟨0, h0, by rw [hg0, h]⟩
  set F : ℂ → ℂ := fun z => bfac a (g z) with hF
  have hFd : DifferentiableOn ℂ F U := differentiableOn_bfac_comp ha hgd hgU
  have hF0 : ∀ z ∈ U, F z ≠ 0 := by
    intro z hz h
    rw [hF, bfac_eq_zero_iff ha (mem_ball_zero_iff.1 (hgU hz)).le] at h
    exact hna ⟨z, hz, h⟩
  obtain ⟨S, hSd, hS2⟩ := hsq F hFd hF0
  have hSU : MapsTo S U (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff]
    have h1 : ‖S z‖ ^ 2 < 1 := by
      rw [← norm_pow, hS2 z hz]
      exact norm_bfac_lt ha (mem_ball_zero_iff.1 (hgU hz))
    nlinarith [norm_nonneg (S z)]
  have hSinj : InjOn S U := by
    intro z hz w hw h
    have : F z = F w := by rw [← hS2 z hz, ← hS2 w hw, h]
    have := bfac_injOn ha (ball_subset_closedBall (hgU hz)) (ball_subset_closedBall (hgU hw)) this
    exact hginj hz hw this
  set b := S 0 with hb
  have hbU : ‖b‖ < 1 := mem_ball_zero_iff.1 (hSU h0)
  have hb2 : b ^ 2 = -a := by rw [hb, hS2 0 h0, hF]; simp only [hg0, bfac_zero]
  have hbn : ‖b‖ ^ 2 = ‖a‖ := by rw [← norm_pow, hb2, norm_neg]
  have hb0 : b ≠ 0 := by
    intro h; rw [h] at hb2; exact ha0 (by linear_combination hb2)
  set G : ℂ → ℂ := fun z => bfac b (S z) with hG
  refine ⟨G, ⟨differentiableOn_bfac_comp hbU hSd hSU, ?_, ?_, ?_⟩, ?_⟩
  · intro z hz w hw h
    exact hSinj hz hw (bfac_injOn hbU (ball_subset_closedBall (hSU hz))
      (ball_subset_closedBall (hSU hw)) h)
  · intro z hz
    exact mem_ball_zero_iff.2 (norm_bfac_lt hbU (mem_ball_zero_iff.1 (hSU hz)))
  · simp only [hG, ← hb, bfac_self]
  -- derivative computation
  set s' := deriv S 0 with hs'
  set d := deriv g 0 with hd
  have hS0 : HasDerivAt S s' 0 := (hSd.differentiableAt (hU.mem_nhds h0)).hasDerivAt
  have hg0' : HasDerivAt g d 0 := (hgd.differentiableAt (hU.mem_nhds h0)).hasDerivAt
  have hFa : HasDerivAt F ((1 - (normSq a : ℂ)) / (1 - (starRingEnd ℂ) a * g 0) ^ 2 * d) 0 :=
    (hasDerivAt_bfac ha (by rw [hg0, norm_zero]; exact zero_le_one)).comp 0 hg0'
  have hFb : HasDerivAt F (2 * b * s') 0 := by
    have := hS0.pow 2
    refine (this.congr_of_eventuallyEq ?_).congr_deriv (by simp [hb])
    filter_upwards [hU.mem_nhds h0] with z hz
    exact (hS2 z hz).symm
  have E1 : 2 * b * s' = (1 - (normSq a : ℂ)) * d := by
    have := hFb.unique hFa
    rw [this, hg0]; simp
  have hGd : HasDerivAt G ((1 - (normSq b : ℂ)) / (1 - (starRingEnd ℂ) b * S 0) ^ 2 * s') 0 :=
    (hasDerivAt_bfac hbU (mem_ball_zero_iff.1 (hSU h0)).le).comp 0 hS0
  have hcb : (starRingEnd ℂ) b * S 0 = (normSq b : ℂ) := by
    rw [← hb, Complex.normSq_eq_conj_mul_self]
  rw [hGd.deriv, hcb]
  have hnb : (1 - (normSq b : ℂ)) ≠ 0 := by
    rw [normSq_eq_norm_sq]; intro h
    have : ((‖b‖ ^ 2 : ℝ) : ℂ) = 1 := by linear_combination -h
    have : ‖b‖ ^ 2 = 1 := by exact_mod_cast this
    nlinarith [norm_nonneg b]
  have hGval : (1 - (normSq b : ℂ)) / (1 - (normSq b : ℂ)) ^ 2 * s' =
      s' / (1 - (normSq b : ℂ)) := by field_simp
  rw [hGval]
  -- norms
  set β := ‖b‖ with hβ
  have hβ0 : 0 < β := norm_pos_iff.2 hb0
  have hnormSq_b : (1 - (normSq b : ℂ)) = ((1 - β ^ 2 : ℝ) : ℂ) := by
    rw [normSq_eq_norm_sq]; push_cast; ring
  have hnormSq_a : (1 - (normSq a : ℂ)) = ((1 - β ^ 4 : ℝ) : ℂ) := by
    rw [normSq_eq_norm_sq, ← hbn]; push_cast; ring
  have h1β : 0 < 1 - β ^ 2 := by nlinarith
  have hE1n : 2 * β * ‖s'‖ = (1 - β ^ 4) * ‖d‖ := by
    have := congrArg norm E1
    rw [hnormSq_a, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by nlinarith : 0 < 1 - β ^ 4)] at this
    simpa using this
  rw [hnormSq_b, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1β,
    lt_div_iff₀ h1β]
  have hdpos : 0 < ‖d‖ := norm_pos_iff.2 hg'
  -- `2β ‖s'‖ = (1-β²)(1+β²)‖d‖`, so `‖s'‖ = (1-β²)(1+β²)/(2β) ‖d‖ > (1-β²)‖d‖`
  have key : (1 - β ^ 2) * ‖d‖ * (2 * β) < ‖s'‖ * (2 * β) := by
    have : ‖s'‖ * (2 * β) = (1 - β ^ 2) * (1 + β ^ 2) * ‖d‖ := by nlinarith
    rw [this]
    have : 0 < (1 - β ^ 2) * ‖d‖ * (1 - β) ^ 2 := by
      have : 0 < 1 - β := by nlinarith
      positivity
    nlinarith
  have := lt_of_mul_lt_mul_right key (by positivity)
  linarith

/-- **Riemann mapping theorem** for bounded connected open sets with the square-root property. -/
theorem riemann_mapping {U : Set ℂ} (hU : IsOpen U) (hUc : IsPreconnected U)
    (hUb : Bornology.IsBounded U) (h0 : (0 : ℂ) ∈ U) (hsq : HasSqrtProperty U) :
    ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ U ∧ InjOn φ U ∧ φ '' U = ball 0 1 ∧ φ 0 = 0 ∧
      0 < (deriv φ 0).re ∧ (deriv φ 0).im = 0 := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU 0 h0
  obtain ⟨R, hRU⟩ := hUb.subset_ball (0 : ℂ)
  have hR : 0 < R := by have := hRU h0; rw [mem_ball, dist_self] at this; exact this
  -- the Cauchy bound
  have hbound : ∀ f, Admissible U f → ‖deriv f 0‖ ≤ 2 / r := by
    rintro f ⟨hfd, -, hfU, -⟩
    have hsub : closedBall (0 : ℂ) (r / 2) ⊆ U :=
      (closedBall_subset_ball (by linarith)).trans hrU
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := r / 2) (C := 1)
      (by positivity) (hfd.diffContOnCl_ball hsub)
      (fun z hz => (mem_ball_zero_iff.1 (hfU (hsub (sphere_subset_closedBall hz)))).le)
    calc ‖deriv f 0‖ ≤ 1 / (r / 2) := this
      _ = 2 / r := by field_simp
  -- a first admissible map
  have hadm0 : Admissible U (fun z => z / R) := by
    refine ⟨(differentiable_id.div_const _).differentiableOn, ?_, ?_, by simp⟩
    · intro z _ w _ h
      have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
      simpa [div_left_inj' hR'] using h
    · intro z hz
      rw [mem_ball_zero_iff, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR,
        div_lt_one hR]
      exact mem_ball_zero_iff.1 (hRU hz)
  have hderiv0 : ‖deriv (fun z : ℂ => z / R) 0‖ = 1 / R := by
    rw [deriv_div_const, deriv_id'', norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]
  set S : Set ℝ := {x | ∃ f, Admissible U f ∧ ‖deriv f 0‖ = x} with hS
  have hSbdd : BddAbove S := ⟨2 / r, by rintro _ ⟨f, hf, rfl⟩; exact hbound f hf⟩
  have hSne : S.Nonempty := ⟨_, _, hadm0, rfl⟩
  set M := sSup S with hM
  have hle : ∀ f, Admissible U f → ‖deriv f 0‖ ≤ M := fun f hf => le_csSup hSbdd ⟨f, hf, rfl⟩
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) (hderiv0 ▸ hle _ hadm0)
  -- maximizing sequence
  have hseq : ∀ k : ℕ, ∃ f, Admissible U f ∧ M - 1 / ((k : ℝ) + 1) < ‖deriv f 0‖ := by
    intro k
    obtain ⟨_, ⟨f, hf, rfl⟩, hlt⟩ := exists_lt_of_lt_csSup hSne
      (show M - 1 / ((k : ℝ) + 1) < M by
        have : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith)
    exact ⟨f, hf, hlt⟩
  choose f hfadm hflt using hseq
  obtain ⟨l, g, hlne, hlle, hlim⟩ := montel hU f (fun k => (hfadm k).1)
    (fun k z hz => (mem_ball_zero_iff.1 ((hfadm k).2.2.1 hz)).le)
  have hfd : ∀ᶠ k in l, DifferentiableOn ℂ (f k) U := Eventually.of_forall fun k => (hfadm k).1
  have hgd : DifferentiableOn ℂ g U := hlim.differentiableOn hfd hU
  -- `|g'(0)| = M`
  have hdlim : Tendsto (fun k => deriv (f k) 0) l (𝓝 (deriv g 0)) :=
    (hlim.deriv hfd hU).tendsto_at h0
  have hMlim : Tendsto (fun k => ‖deriv (f k) 0‖) atTop (𝓝 M) := by
    have h1 : Tendsto (fun k : ℕ => M - 1 / ((k : ℝ) + 1)) atTop (𝓝 M) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      simpa using (tendsto_const_nhds (x := M)).sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds
      (fun k => (hflt k).le) (fun k => hle _ (hfadm k))
  have hgM : ‖deriv g 0‖ = M := tendsto_nhds_unique hdlim.norm (hMlim.mono_left hlle)
  have hg'0 : deriv g 0 ≠ 0 := by
    intro h; rw [h, norm_zero] at hgM; linarith
  have hg0 : g 0 = 0 := by
    refine tendsto_nhds_unique (hlim.tendsto_at h0) ?_
    simp only [(hfadm _).2.2.2]
    exact tendsto_const_nhds
  have hgle : ∀ z ∈ U, ‖g z‖ ≤ 1 := fun z hz =>
    le_of_tendsto (hlim.tendsto_at hz).norm
      (Eventually.of_forall fun k => (mem_ball_zero_iff.1 ((hfadm k).2.2.1 hz)).le)
  have hginj : InjOn g U := hurwitz_injOn hU hUc hfd
    (Eventually.of_forall fun k => (hfadm k).2.1) hlim h0 hg'0
  have hgU : MapsTo g U (ball 0 1) := by
    intro z hz
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_ne (hgle z hz) fun heq => ?_
    have hmax : IsMaxOn (norm ∘ g) U z := fun w hw => by
      simp only [mem_setOf_eq, Function.comp]; rw [heq]; exact hgle w hw
    have := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hUc hU hgd hz hmax h0
    simp only [Function.const_apply] at this
    rw [hg0] at this
    rw [← this, norm_zero] at heq
    exact zero_ne_one heq
  have hgadm : Admissible U g := ⟨hgd, hginj, hgU, hg0⟩
  have hgsurj : g '' U = ball 0 1 := by
    refine Subset.antisymm (image_subset_iff.2 hgU) fun a ha => ?_
    by_contra hna
    obtain ⟨G, hG, hGlt⟩ := koebe_step hU h0 hsq hgadm hg'0 (mem_ball_zero_iff.1 ha) hna
    have := hle G hG
    linarith
  -- rotate so that `φ'(0) > 0`
  set c := deriv g 0 with hc
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hg'0
  set u : ℂ := (starRingEnd ℂ) c / (‖c‖ : ℂ) with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcn,
      div_self hcn.ne']
  have hu0 : u ≠ 0 := by intro h; rw [h, norm_zero] at hu1; exact zero_ne_one hu1
  have hgdiff0 : DifferentiableAt ℂ g 0 := hgd.differentiableAt (hU.mem_nhds h0)
  have hderφ : deriv (fun z => u * g z) 0 = (‖c‖ : ℂ) := by
    rw [deriv_const_mul _ hgdiff0, ← hc, hu, div_mul_eq_mul_div, Complex.conj_mul']
    have : (‖c‖ : ℂ) ≠ 0 := by exact_mod_cast hcn.ne'
    field_simp
  refine ⟨fun z => u * g z, hgd.const_mul u, ?_, ?_, by simp [hg0], ?_, ?_⟩
  · intro z hz w hw h
    exact hginj hz hw (mul_left_cancel₀ hu0 h)
  · ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [mem_ball_zero_iff, norm_mul, hu1, one_mul]
      exact mem_ball_zero_iff.1 (hgU hz)
    · intro hw
      have : u⁻¹ * w ∈ g '' U := by
        rw [hgsurj, mem_ball_zero_iff, norm_mul, norm_inv, hu1, inv_one, one_mul]
        exact mem_ball_zero_iff.1 hw
      obtain ⟨z, hz, hzw⟩ := this
      exact ⟨z, hz, by simp only; rw [hzw, ← mul_assoc, mul_inv_cancel₀ hu0, one_mul]⟩
  · rw [hderφ]; simpa using hcn
  · rw [hderφ]; simp

end SteklovRiemann
