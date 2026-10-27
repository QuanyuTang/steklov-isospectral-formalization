module

public import RequestProject.OuterFunction
public import RequestProject.CompositionBounds
public import RequestProject.Prop231Reduction
public import RequestProject.Univalence
public import RequestProject.HolomorphicInverse

/-!
# Proposition 2.3.1, first part: realization of weights near a constant

For a positive real-analytic weight `ρ` on `𝕋` and `c > 0` let
`h(t) = log ρ(e^{it}) - log c` (`OuterRealization.logWeight`), `H` its Schwarz series
(`OuterFunction.H`), `O = c·e^{H}` the normalized outer function and `F` the primitive of `O`
with `F(0) = 0`.

* `exists_outer_primitive` — `H` is holomorphic on a disk of radius `R > 1` and `F` exists there;
* `norm_outer_eq` — `|O| = ρ` on `𝕋`; `outer_zero_re_pos`, `outer_zero_im` — `O(0) > 0`;
* `prop_2_3_1_realization : Prop_2_3_1_realization` (with `k = 2`): if `‖ρ - c‖_{C²} < δ(c)`,
  then `Re O > 0` on `𝔻̄`, hence `F` is injective on `𝔻̄` (Noshiro–Warschawski);
* `prop_2_3_1 : Prop_2_3_1` — with the spectral identity, via Proposition 2.1.1;
* `deriv_eq_outer` — **uniqueness**: every normalized realizing map has `F' = O` near `𝔻̄`.
-/

@[expose] public section

open Real Complex Set Metric Filter Topology OuterFunction
open scoped Nat ContDiff

noncomputable section

namespace OuterRealization

/-- The logarithmic weight `h(t) = log ρ(e^{it}) - log c`. -/
def logWeight (c : ℝ) (ρ : ℂ → ℝ) : ℝ → ℝ := fun t => Real.log (ρ (exp (t * I))) - Real.log c

/-- The normalized outer function `O_ρ = c · exp H`, with `|O_ρ| = ρ` on `𝕋`. -/
def outer (c : ℝ) (ρ : ℂ → ℝ) (z : ℂ) : ℂ := c * exp (H (logWeight c ρ) z)

lemma exp_periodic_circle (t : ℝ) : exp (((t + 2 * π : ℝ) : ℂ) * I) = exp (t * I) := by
  rw [show (((t + 2 * π : ℝ) : ℂ) * I) = t * I + 2 * π * I by push_cast; ring, Complex.exp_add,
    Complex.exp_two_pi_mul_I, mul_one]

lemma logWeight_periodic (c : ℝ) (ρ : ℂ → ℝ) : Function.Periodic (logWeight c ρ) (2 * π) := by
  intro t; simp only [logWeight]; rw [exp_periodic_circle]

lemma logWeight_analytic {c : ℝ} {ρ : ℂ → ℝ} (hρ : IsPosRealAnalyticWeight ρ) :
    AnalyticOnNhd ℝ (logWeight c ρ) univ := by
  intro t _
  have h1 : AnalyticAt ℝ (fun s : ℝ => ρ (exp (s * I))) t := hρ.1 t (mem_univ t)
  have h2 : AnalyticAt ℝ Real.log (ρ (exp (t * I))) := analyticAt_log (hρ.2 t)
  exact (AnalyticAt.comp (f := fun s : ℝ => ρ (exp (s * I))) h2 h1).sub analyticAt_const

lemma logWeight_contDiff {c : ℝ} {ρ : ℂ → ℝ} (hρ : IsPosRealAnalyticWeight ρ) :
    ContDiff ℝ ∞ (logWeight c ρ) := (logWeight_analytic hρ).contDiff

/-- **The construction**: `H` is holomorphic on a disk of radius `R > 1` (with `H^{(j)} = H_j`
there) and the outer function `O = c e^H` has a primitive `F` with `F(0) = 0` on it. -/
theorem exists_outer_primitive (c : ℝ) {ρ : ℂ → ℝ} (hρ : IsPosRealAnalyticWeight ρ) :
    ∃ R > (1 : ℝ), DifferentiableOn ℂ (H (logWeight c ρ)) (ball 0 R) ∧
      (∀ j, ∀ z ∈ ball (0 : ℂ) R, iteratedDeriv j (H (logWeight c ρ)) z =
        Hj (logWeight c ρ) j z) ∧
      ∃ F : ℂ → ℂ, (∀ z ∈ ball (0 : ℂ) R, HasDerivAt F (outer c ρ z) z) ∧ F 0 = 0 := by
  obtain ⟨A, q, hq0, hq1, hdec⟩ := exists_decay (logWeight_analytic (c := c) hρ)
    (logWeight_periodic c ρ)
  have hHd := differentiableOn_H hdec hq0.le hq1
  have hOd : DifferentiableOn ℂ (outer c ρ) (ball 0 (radius q)) := by
    intro z hz
    exact ((differentiableAt_const _).mul
      ((hHd z hz).differentiableAt (isOpen_ball.mem_nhds hz)).cexp).differentiableWithinAt
  obtain ⟨G, hG⟩ := hOd.isExactOn_ball
  refine ⟨radius q, one_lt_radius hq0.le hq1, hHd, fun j z hz =>
    iteratedDeriv_H hdec hq0.le hq1 j z hz, fun z => G z - G 0, fun z hz => ?_, by simp⟩
  exact (hG z hz).sub_const _

lemma norm_outer_exp {c : ℝ} (hc : 0 < c) {ρ : ℂ → ℝ} (hρ : IsPosRealAnalyticWeight ρ) (t : ℝ) :
    ‖outer c ρ (exp (t * I))‖ = ρ (exp (t * I)) := by
  rw [outer, norm_mul, Complex.norm_exp, re_H_exp (logWeight_contDiff hρ)
    (logWeight_periodic c ρ), Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, logWeight,
    Real.exp_sub, Real.exp_log (hρ.2 t), Real.exp_log hc]
  field_simp

/-- `|O_ρ| = ρ` on the unit circle. -/
theorem norm_outer_eq {c : ℝ} (hc : 0 < c) {ρ : ℂ → ℝ} (hρ : IsPosRealAnalyticWeight ρ)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : ‖outer c ρ z‖ = ρ z := by
  obtain ⟨t, rfl⟩ := Prop231Reduction.exists_exp_eq_of_mem_sphere hz
  exact norm_outer_exp hc hρ t

lemma outer_zero (c : ℝ) (ρ : ℂ → ℝ) :
    outer c ρ 0 = ((c * Real.exp (coef (logWeight c ρ) 0).re : ℝ) : ℂ) := by
  rw [outer, H_zero]
  have : coef (logWeight c ρ) 0 = ((coef (logWeight c ρ) 0).re : ℂ) := by
    apply Complex.ext <;> simp [coef_zero_im]
  rw [this, ← Complex.ofReal_exp]; push_cast; simp

lemma outer_zero_re_pos {c : ℝ} (hc : 0 < c) (ρ : ℂ → ℝ) : 0 < (outer c ρ 0).re := by
  rw [outer_zero, Complex.ofReal_re]; positivity

lemma outer_zero_im (c : ℝ) (ρ : ℂ → ℝ) : (outer c ρ 0).im = 0 := by
  rw [outer_zero, Complex.ofReal_im]

lemma outer_ne_zero {c : ℝ} (hc : 0 < c) (ρ : ℂ → ℝ) (z : ℂ) : outer c ρ z ≠ 0 :=
  mul_ne_zero (by exact_mod_cast hc.ne') (Complex.exp_ne_zero _)

/-- If `‖H‖ < π/2` then `Re O > 0`. -/
lemma re_outer_pos {c : ℝ} (hc : 0 < c) {ρ : ℂ → ℝ} {z : ℂ}
    (hH : ‖H (logWeight c ρ) z‖ < π / 2) : 0 < (outer c ρ z).re := by
  rw [outer, Complex.re_ofReal_mul, Complex.exp_re]
  have him : |(H (logWeight c ρ) z).im| < π / 2 := (Complex.abs_im_le_norm _).trans_lt hH
  have hcos : 0 < Real.cos (H (logWeight c ρ) z).im :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le (H (logWeight c ρ) z).im],
      by linarith [le_abs_self (H (logWeight c ρ) z).im]⟩
  positivity

/-- The `C^k` closeness hypothesis gives non-strict bounds on `ρ(e^{it}) - c`. -/
lemma bounds_of_ckClose {k : ℕ} {δ : ℝ} {ρ : ℂ → ℝ} {c : ℝ} (h : CkClose k δ ρ c) :
    ∀ j ≤ k, ∀ t, |iteratedDeriv j (fun s : ℝ => ρ (exp (s * I)) - c) t| ≤ δ :=
  fun j hj t => (h j hj t).le

lemma logWeight_eq (c : ℝ) (ρ : ℂ → ℝ) :
    logWeight c ρ = fun s : ℝ => Real.log (c + (ρ (exp (s * I)) - c)) - Real.log c := by
  funext s; simp [logWeight]

/-- Bounds on the derivatives of the logarithmic weight from `C^n`-closeness of `ρ` to `c`. -/
lemma logWeight_deriv_bound {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ∃ K, 0 ≤ K ∧ ∀ ρ : ℂ → ℝ, IsPosRealAnalyticWeight ρ → ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 → δ ≤ c / 2 →
      (∀ j ≤ n, ∀ t, |iteratedDeriv j (fun s : ℝ => ρ (exp (s * I)) - c) t| ≤ δ) →
      ∀ i ≤ n, ∀ t, |iteratedDeriv i (logWeight c ρ) t| ≤ K * δ := by
  choose K hK0 hK using fun i : ℕ => CompositionBounds.log_comp_bound hc i
  refine ⟨∑ i ∈ Finset.range (n + 1), K i, Finset.sum_nonneg fun i _ => hK0 i,
    fun ρ hρ δ hδ0 hδ1 hδc hbd i hi t => ?_⟩
  have hg : ContDiff ℝ ∞ (fun s : ℝ => ρ (exp (s * I)) - c) :=
    (AnalyticOnNhd.contDiff (fun s _ => hρ.1 s (mem_univ s))).sub contDiff_const
  rw [logWeight_eq]
  calc |iteratedDeriv i (fun s : ℝ => Real.log (c + (ρ (exp (s * I)) - c)) - Real.log c) t|
      ≤ K i * δ := hK i _ hg δ hδ0 hδ1 hδc (fun j hj t => hbd j (hj.trans hi) t) t
    _ ≤ (∑ i ∈ Finset.range (n + 1), K i) * δ := by
        gcongr
        exact Finset.single_le_sum (fun i _ => hK0 i) (Finset.mem_range.2 (by omega))

/-- Uniform bound for `H_j` on the closed disk from `C^{j+2}`-bounds of the weight. -/
lemma norm_Hj_le_of_bound {c : ℝ} {ρ : ℂ → ℝ} (hρ : IsPosRealAnalyticWeight ρ) {j : ℕ} {B : ℝ}
    (hB : ∀ i ≤ j + 2, ∀ t, |iteratedDeriv i (logWeight c ρ) t| ≤ B) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖Hj (logWeight c ρ) j z‖ ≤ 5 * B := by
  have h1 := norm_Hj_le (logWeight_contDiff hρ) (logWeight_periodic c ρ) j
    (hB (j + 2) le_rfl) hz
  have h2 := norm_coef_zero_le (logWeight c ρ) (M := B) (fun x => by
    simpa using hB 0 (Nat.zero_le _) x)
  linarith

/-- **Proposition 2.3.1, realization part** (proved with `k = 2`). -/
theorem prop_2_3_1_realization : Prop_2_3_1_realization := by
  intro c hc
  obtain ⟨K, hK0, hK⟩ := logWeight_deriv_bound hc 2
  set δ : ℝ := min (min 1 (c / 2)) (1 / (16 * (K + 1))) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδc : δ ≤ c / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hKδ : K * δ ≤ 1 / 16 := by
    have : δ ≤ 1 / (16 * (K + 1)) := min_le_right _ _
    calc K * δ ≤ (K + 1) * δ := by nlinarith
      _ ≤ (K + 1) * (1 / (16 * (K + 1))) := by gcongr
      _ = 1 / 16 := by field_simp
  refine ⟨2, δ, hδpos, fun ρ hρ hck => ?_⟩
  obtain ⟨R, hR1, hHd, hiter, F, hF, hF0⟩ := exists_outer_primitive c hρ
  have hbd := hK ρ hρ δ hδpos.le hδ1 hδc (bounds_of_ckClose hck)
  have hsub : closedBall (0 : ℂ) 1 ⊆ ball 0 R := closedBall_subset_ball hR1
  have hderiv : ∀ z ∈ ball (0 : ℂ) R, deriv F z = outer c ρ z := fun z hz => (hF z hz).deriv
  have hHsmall : ∀ z ∈ closedBall (0 : ℂ) 1, ‖H (logWeight c ρ) z‖ < π / 2 := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 := by simpa using hz
    have := norm_Hj_le_of_bound hρ (j := 0) (B := K * δ) (fun i hi t => hbd i hi t) hz'
    have hpi := Real.pi_gt_three
    unfold H; linarith
  refine ⟨F, ⟨ball 0 R, isOpen_ball, hsub, fun z hz => (hF z hz).differentiableAt.differentiableWithinAt⟩,
    ?_, hF0, ?_, ?_, ?_⟩
  · refine SteklovAnalytic.injOn_of_re_deriv_pos (convex_closedBall 0 1)
      (fun z hz => (hF z (hsub hz)).differentiableAt) fun z hz => ?_
    rw [hderiv z (hsub hz)]
    exact re_outer_pos hc (hHsmall z hz)
  · rw [hderiv 0 (mem_ball_self (by linarith))]; exact outer_zero_re_pos hc ρ
  · rw [hderiv 0 (mem_ball_self (by linarith))]; exact outer_zero_im c ρ
  · intro z hz
    rw [hderiv z (hsub (sphere_subset_closedBall hz))]
    exact norm_outer_eq hc hρ hz

/-- **Proposition 2.3.1, first part with the spectral identity**, proved
(realization above + Proposition 2.1.1). -/
theorem prop_2_3_1 : Prop_2_3_1 :=
  Prop231Reduction.prop_2_3_1_of_realization prop_2_3_1_realization

/-- A compact subset of an open set containing `𝔻̄` contains a disk of radius `> 1`. -/
lemma exists_ball_subset_of_closedBall_subset {U : Set ℂ} (hU : IsOpen U)
    (h : closedBall (0 : ℂ) 1 ⊆ U) : ∃ r > (1 : ℝ), ball (0 : ℂ) r ⊆ U := by
  obtain ⟨ε, hε, hth⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_thickening_subset_open hU h
  refine ⟨ε + 1, by linarith, ?_⟩
  rw [← thickening_closedBall hε zero_le_one]
  exact hth

/-- **Uniqueness of normalized realizing maps**: if `F` is holomorphic near `𝔻̄`, injective on
`𝔻̄`, `F'(0) > 0` and `|F'| = ρ` on `𝕋`, then `F' = O_ρ` on a disk of radius `> 1`. -/
theorem deriv_eq_outer {c : ℝ} (hc : 0 < c) {ρ : ℂ → ℝ} (hρ : IsPosRealAnalyticWeight ρ)
    {F : ℂ → ℂ}
    (hFU : ∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ F U)
    (hinj : InjOn F (closedBall 0 1)) (hre : 0 < (deriv F 0).re) (him : (deriv F 0).im = 0)
    (hnorm : ∀ z ∈ sphere (0 : ℂ) 1, ‖deriv F z‖ = ρ z) :
    ∃ r > (1 : ℝ), DifferentiableOn ℂ F (ball 0 r) ∧
      ∀ z ∈ ball (0 : ℂ) r, deriv F z = outer c ρ z := by
  obtain ⟨U, hUo, hUc, hFd⟩ := hFU
  have hρpos : ∀ z ∈ sphere (0 : ℂ) 1, 0 < ρ z := by
    intro z hz
    obtain ⟨t, rfl⟩ := Prop231Reduction.exists_exp_eq_of_mem_sphere hz
    exact hρ.2 t
  have hF' : ∀ z ∈ sphere (0 : ℂ) 1, deriv F z ≠ 0 := by
    intro z hz h0
    have := hnorm z hz
    rw [h0, norm_zero] at this
    exact (hρpos z hz).ne this
  obtain ⟨U', hU'o, hU'c, hU'U, -, hU'ne⟩ :=
    HolInv.exists_open_nbhd_injOn_deriv_ne_zero hUo hUc hFd hinj hF'
  obtain ⟨R, hR1, hHd, -, G, hG, -⟩ := exists_outer_primitive c hρ
  obtain ⟨r, hr1, hrsub⟩ := exists_ball_subset_of_closedBall_subset (hU'o.inter isOpen_ball)
    (subset_inter hU'c (closedBall_subset_ball hR1))
  set V := ball (0 : ℂ) r with hV
  have hVU : V ⊆ U := fun z hz => hU'U (hrsub hz).1
  have hVR : V ⊆ ball 0 R := fun z hz => (hrsub hz).2
  have hFdV : DifferentiableOn ℂ F V := hFd.mono hVU
  have hF'd : DifferentiableOn ℂ (deriv F) V := (hFd.deriv hUo).mono hVU
  have hOd : DifferentiableOn ℂ (outer c ρ) V := by
    intro z hz
    have := (hG z (hVR hz))
    refine DifferentiableAt.differentiableWithinAt ?_
    have hHd' := (hHd z (hVR hz)).differentiableAt (isOpen_ball.mem_nhds (hVR hz))
    exact (differentiableAt_const _).mul hHd'.cexp
  have hF'ne : ∀ z ∈ V, deriv F z ≠ 0 := fun z hz => hU'ne z (hrsub hz).1
  have hOne : ∀ z, outer c ρ z ≠ 0 := outer_ne_zero hc ρ
  set q : ℂ → ℂ := fun z => deriv F z / outer c ρ z with hq
  set q' : ℂ → ℂ := fun z => outer c ρ z / deriv F z with hq'
  have hqd : DifferentiableOn ℂ q V := hF'd.div hOd fun z _ => hOne z
  have hq'd : DifferentiableOn ℂ q' V := hOd.div hF'd hF'ne
  have hclV : closure (ball (0 : ℂ) 1) ⊆ V := by
    rw [closure_ball _ one_ne_zero]; exact closedBall_subset_ball hr1
  have hsphere_q : ∀ z ∈ sphere (0 : ℂ) 1, ‖q z‖ = 1 := by
    intro z hz
    rw [hq, norm_div, hnorm z hz, norm_outer_eq hc hρ hz, div_self (hρpos z hz).ne']
  have hsphere_q' : ∀ z ∈ sphere (0 : ℂ) 1, ‖q' z‖ = 1 := by
    intro z hz
    rw [hq', norm_div, hnorm z hz, norm_outer_eq hc hρ hz, div_self (hρpos z hz).ne']
  have hmax : ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f V → (∀ z ∈ sphere (0 : ℂ) 1, ‖f z‖ = 1) →
      ∀ z ∈ closedBall (0 : ℂ) 1, ‖f z‖ ≤ 1 := by
    intro f hf hfs z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball
      (hf.mono hclV).diffContOnCl (fun w hw => ?_) (by rwa [closure_ball _ one_ne_zero])
    rw [frontier_ball _ one_ne_zero] at hw
    exact (hfs w hw).le
  have hq1 : ∀ z ∈ ball (0 : ℂ) 1, ‖q z‖ = 1 := by
    intro z hz
    have h1 := hmax q hqd hsphere_q z (ball_subset_closedBall hz)
    have h2 := hmax q' hq'd hsphere_q' z (ball_subset_closedBall hz)
    have hprod : q z * q' z = 1 := by
      rw [hq, hq']
      have := hF'ne z (closedBall_subset_ball hr1 (ball_subset_closedBall hz))
      field_simp [hOne z, this]
    have : ‖q z‖ * ‖q' z‖ = 1 := by rw [← norm_mul, hprod, norm_one]
    nlinarith [norm_nonneg (q z), norm_nonneg (q' z)]
  have hconst : EqOn q (Function.const ℂ (q 0)) (ball 0 1) := by
    refine Complex.eqOn_of_isPreconnected_of_isMaxOn_norm (convex_ball 0 1).isPreconnected
      isOpen_ball (hqd.mono fun z hz => closedBall_subset_ball hr1 (ball_subset_closedBall hz))
      (mem_ball_self one_pos) fun z hz => ?_
    simp only [mem_setOf_eq, Function.comp_apply]
    rw [hq1 z hz, hq1 0 (mem_ball_self one_pos)]
  have hq0 : q 0 = 1 := by
    have hF0 : deriv F 0 = ((deriv F 0).re : ℂ) := by
      apply Complex.ext <;> simp [him]
    have hO0 := outer_zero c ρ
    have hn := hq1 0 (mem_ball_self one_pos)
    have hpos : 0 < (outer c ρ 0).re := outer_zero_re_pos hc ρ
    rw [hq] at hn ⊢
    simp only at hn ⊢
    rw [hF0, hO0] at hn ⊢
    rw [hO0, Complex.ofReal_re] at hpos
    rw [← Complex.ofReal_div] at hn ⊢
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hre hpos)] at hn
    rw [hn, Complex.ofReal_one]
  have heq1 : EqOn (deriv F) (outer c ρ) (ball 0 1) := by
    intro z hz
    have := hconst hz
    simp only [Function.const_apply, hq0] at this
    rw [hq] at this
    simp only at this
    exact (div_eq_one_iff_eq (hOne z)).1 this
  have heqV : EqOn (deriv F) (outer c ρ) V := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq (hF'd.analyticOnNhd isOpen_ball)
      (hOd.analyticOnNhd isOpen_ball) (convex_ball 0 r).isPreconnected
      (mem_ball_self (by linarith)) ?_
    exact Filter.eventually_of_mem (isOpen_ball.mem_nhds (mem_ball_self one_pos)) heq1
  exact ⟨r, hr1, hFdV, fun z hz => heqV hz⟩

end OuterRealization

end
