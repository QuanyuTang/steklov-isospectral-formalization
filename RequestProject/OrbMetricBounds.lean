module

public import RequestProject.OrbSobolev
public import RequestProject.Friedrichs

/-!
# Metric comparison estimates for disk-type orbisurfaces

For a `SteklovOrb.DiskOrbisurface` `O` with conformal factor `λ` (metric `g = λ|dz|²`), all
derived from the cone-chart data of `O` (smooth positive pulled-back factor `μ` in each chart
`w ↦ p + w^m`):

* `cone_lintegral_ge`: reverse area formula for the `m`-to-`1` cone chart;
* `exists_lam_lower`: `λ ≥ c > 0` on `𝔻` minus the cone points;
* `exists_weighted_bound`: **weighted Sobolev estimate**
  `∫_𝔻 u² λ dA ≤ C (∫_𝔻 u² dA + ∫_𝔻 |∇u|² dA)` for all orbifold-smooth `u`
  (via the Friedrichs inequality in each cone chart);
* `area_lt_top`: the metric area `∫_𝔻 λ dA` of `O` is finite.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Real ComplexConjugate

noncomputable section

namespace SteklovOrb

open Steklov SteklovH1

/-- **Reverse area formula for a cone chart**: each point has at most `m` preimages, so
`∫_{|w|<r} |m w^{m-1}|² G(p + w^m) ≤ m ∫_{|z-p|<r^m} G`. -/
theorem cone_lintegral_ge (p : ℂ) {m : ℕ} (hm : m ≠ 0) (r : ℝ) (G : ℂ → ℝ≥0∞)
    (hG : Measurable G) :
    ∫⁻ w in ball (0 : ℂ) r, ‖(m : ℂ) * w ^ (m - 1)‖ₑ ^ 2 * G (coneChart p m w) ≤
      m * ∫⁻ z in ball p (r ^ m), G z := by
  classical
  set B := coneChart p m
  have hBd : DifferentiableOn ℂ B univ := fun w _ =>
    (hasDerivAt_coneChart p m w).differentiableAt.differentiableWithinAt
  have hcrit : {w ∈ ball (0 : ℂ) r | deriv B w = 0}.Countable := by
    refine (Set.countable_singleton (0 : ℂ)).mono ?_
    rintro w ⟨-, hw⟩
    rw [deriv_coneChart, mul_eq_zero] at hw
    rcases hw with h | h
    · exact absurd (Nat.cast_eq_zero.1 h) hm
    · exact eq_zero_of_pow_eq_zero h
  have hA := SteklovArea.lintegral_deriv_sq_mul_eq_fibreSum isOpen_univ hBd measurableSet_ball
    (subset_univ _) hcrit (G ∘ B) (hG.comp (contDiff_coneChart p m).continuous.measurable)
  rw [show deriv B = fun w => (m : ℂ) * w ^ (m - 1) from funext (deriv_coneChart p m)] at hA
  simp only [Function.comp] at hA
  rw [hA, ← lintegral_indicator measurableSet_ball, ← lintegral_const_mul _
    (hG.indicator measurableSet_ball)]
  refine lintegral_mono fun z => ?_
  unfold SteklovArea.fibreSum
  set S : Set ℂ := {w | w ∈ ball (0 : ℂ) r ∧ B w = z}
  have hsub : S ⊆ ((Polynomial.nthRoots m (z - p)).toFinset : Set ℂ) := by
    rintro w ⟨-, hw⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_nthRoots (Nat.pos_of_ne_zero hm)]
    simp only [B, coneChart] at hw
    rw [← hw]; ring
  have h1 : ∑' w : S, G (B w) = ∑' w : S, G z :=
    tsum_congr fun w => by rw [w.2.2]
  change ∑' w : S, G (B w) ≤ _
  rw [h1]
  by_cases hz : z ∈ ball p (r ^ m)
  · rw [indicator_of_mem hz]
    refine (ENNReal.tsum_mono_subtype (fun _ => G z) hsub).trans ?_
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    gcongr
    simp only [Finset.coe_sort_coe, Fintype.card_coe]
    exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots m (z - p))
  · have hS : S = ∅ := by
      ext w
      simp only [S, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
      intro hw hBw
      apply hz
      rw [← hBw, mem_ball, dist_eq_norm]
      simp only [B, coneChart, add_sub_cancel_left, norm_pow]
      exact pow_lt_pow_left₀ (mem_ball_zero_iff.1 hw) (norm_nonneg _) hm
    have : IsEmpty S := by rw [hS]; exact Set.isEmpty_coe_sort.2 rfl
    simp

namespace DiskOrbisurface

variable (O : DiskOrbisurface)

/-- The conformal factor, set to `0` outside its domain `U \ {cone points}` (a measurable
version of `λ`; it agrees with `λ` on `𝔻` minus the cone points). -/
def lamI : ℂ → ℝ := (O.U \ range O.pt).indicator O.lam

lemma isOpen_U_diff : IsOpen (O.U \ range O.pt) :=
  O.isOpen_U.sdiff (Set.finite_range O.pt).isClosed

lemma measurable_lamI : Measurable O.lamI := by
  classical
  unfold lamI
  rw [← piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise O.lam_smooth.continuousOn continuousOn_const
    O.isOpen_U_diff.measurableSet

lemma lamI_eq {z : ℂ} (hz : z ∈ O.U \ range O.pt) : O.lamI z = O.lam z := indicator_of_mem hz _

/-- Separation of the cone points. -/
lemma exists_sep (i : Fin O.n) : ∃ δ > 0, ∀ z ∈ ball (O.pt i) δ, z ∈ range O.pt → z = O.pt i := by
  have hcl : IsClosed (range O.pt \ {O.pt i}) := ((Set.finite_range O.pt).diff).isClosed
  have hp : O.pt i ∈ (range O.pt \ {O.pt i})ᶜ := by simp
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl _ hp
  exact ⟨δ, hδ, fun z hz hzP => by
    by_contra hne
    exact hball hz ⟨hzP, hne⟩⟩

/-- **Normalized cone-chart data** at the cone point `i`: a radius `a ≤ 1/4` such that the smooth
positive pulled-back metric factor `μ` is available on `|w| < 2a`, the chart image of `|w| < 2a` lies
in `𝔻` and meets no other cone point. -/
theorem exists_cone_radius (i : Fin O.n) :
    ∃ a > 0, a ≤ 1 / 4 ∧ ∃ μ : ℂ → ℝ, ContinuousOn μ (closedBall 0 a) ∧
      (∀ w ∈ closedBall (0 : ℂ) a, 0 < μ w) ∧
      (∀ w ∈ ball (0 : ℂ) (2 * a), w ≠ 0 → μ w = chartFactor O.lam (O.pt i) (O.ord i) w) ∧
      ball (O.pt i) ((2 * a) ^ O.ord i) ⊆ ball 0 1 ∧
      (∀ w ∈ ball (0 : ℂ) (2 * a), w ≠ 0 →
        coneChart (O.pt i) (O.ord i) w ∈ ball (0 : ℂ) 1 \ range O.pt) := by
  obtain ⟨r, hr, μ, hμs, hμp, hμe⟩ := O.cone_metric i
  obtain ⟨δ, hδ, hsep⟩ := O.exists_sep i
  set p := O.pt i
  set m := O.ord i
  have hm : m ≠ 0 := O.ord_ne_zero i
  have hp1 : ‖p‖ < 1 := O.pt_mem i
  set a := min (r / 4) (min (1 / 8) (min (δ / 2) ((1 - ‖p‖) / 4))) with ha_def
  have ha : 0 < a := by
    refine lt_min (by linarith) (lt_min (by norm_num) (lt_min (by linarith) (by linarith)))
  have har : a ≤ r / 4 := min_le_left _ _
  have ha8 : a ≤ 1 / 8 := (min_le_right _ _).trans (min_le_left _ _)
  have haδ : a ≤ δ / 2 := ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hap : a ≤ (1 - ‖p‖) / 4 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have h2a1 : 2 * a ≤ 1 := by linarith
  have hpow : (2 * a) ^ m ≤ 2 * a := pow_le_of_le_one (by positivity) h2a1 hm
  have hball : ball p ((2 * a) ^ m) ⊆ ball 0 1 := fun z hz => by
    rw [mem_ball, dist_eq_norm] at hz
    rw [mem_ball_zero_iff]
    calc ‖z‖ = ‖p + (z - p)‖ := by rw [add_sub_cancel]
      _ ≤ ‖p‖ + ‖z - p‖ := norm_add_le _ _
      _ < 1 := by linarith
  refine ⟨a, ha, by linarith, μ, ?_, ?_, ?_, hball, ?_⟩
  · exact hμs.continuousOn.mono (closedBall_subset_ball (by linarith))
  · exact fun w hw => hμp w (closedBall_subset_ball (by linarith) hw)
  · exact fun w hw hw0 => hμe w (ball_subset_ball (by linarith) hw) hw0
  · intro w hw hw0
    have hmem : coneChart p m w ∈ ball p ((2 * a) ^ m) := by
      rw [mem_ball, dist_eq_norm]
      simp only [coneChart, add_sub_cancel_left, norm_pow]
      exact pow_lt_pow_left₀ (mem_ball_zero_iff.1 hw) (norm_nonneg _) hm
    refine ⟨hball hmem, fun hP => ?_⟩
    have hδmem : coneChart p m w ∈ ball p δ :=
      ball_subset_ball (by linarith) hmem
    have := hsep _ hδmem hP
    simp only [coneChart, add_eq_left] at this
    exact hw0 (eq_zero_of_pow_eq_zero this)

/-- Composition of an orbifold-smooth function with the cone chart is `C¹` on the normalized chart
disk. -/
lemma contDiffOn_comp_coneChart {u : ℂ → ℝ} (hu : O.IsOrbSmooth u) (i : Fin O.n) {a : ℝ}
    (hch : ∀ w ∈ ball (0 : ℂ) (2 * a), w ≠ 0 →
        coneChart (O.pt i) (O.ord i) w ∈ ball (0 : ℂ) 1 \ range O.pt) :
    ContDiffOn ℝ 1 (fun w => u (coneChart (O.pt i) (O.ord i) w)) (ball 0 (2 * a)) := by
  intro w hw
  refine ContDiffAt.contDiffWithinAt ?_
  by_cases hw0 : w = 0
  · subst hw0; exact (hu.2 i).of_le (by exact_mod_cast le_top)
  · have hc := (hch w hw hw0).2
    have h1 : ContDiffAt ℝ 1 u (coneChart (O.pt i) (O.ord i) w) :=
      ((hu.1.contDiffAt (O.isOpen_compl_S.mem_nhds hc))).of_le (by exact_mod_cast le_top)
    exact h1.comp w ((contDiff_coneChart _ _).contDiffAt.of_le (by exact_mod_cast le_top))

/-- Gradient norm of a function composed with the cone chart. -/
lemma norm_fderiv_comp_coneChart {u : ℂ → ℝ} (p : ℂ) (m : ℕ) {w : ℂ}
    (hud : DifferentiableAt ℝ u (coneChart p m w)) :
    ‖fderiv ℝ (fun w => u (coneChart p m w)) w‖ =
      ‖(m : ℂ) * w ^ (m - 1)‖ * ‖fderiv ℝ u (coneChart p m w)‖ := by
  have hg := SteklovH1.grad_comp_holo hud (hasDerivAt_coneChart p m w)
  rw [← SteklovH1.norm_grad, ← SteklovH1.norm_grad, hg, norm_mul, Complex.norm_conj]

/-- **Local estimates at a cone point**, derived from the cone-chart data: on a small chart image
`B(p, a^m)`, the conformal factor is bounded below, and the weighted `L²` norm of an orbifold-smooth
function is controlled by its Euclidean `H¹` norm on `B(p, (2a)^m) ⊆ 𝔻`. -/
theorem cone_estimates (i : Fin O.n) :
    ∃ a > 0, ∃ c > 0, ∃ C : ℝ≥0∞, ball (O.pt i) ((2 * a) ^ O.ord i) ⊆ ball 0 1 ∧
      (∀ z ∈ ball (O.pt i) (a ^ O.ord i), z ∉ range O.pt → c ≤ O.lam z) ∧
      C ≠ ⊤ ∧ ∀ u, O.IsOrbSmooth u →
        ∫⁻ z in ball (O.pt i) (a ^ O.ord i), ENNReal.ofReal (O.lamI z) * ‖u z‖ₑ ^ 2 ≤
          C * ((∫⁻ z in ball (O.pt i) ((2 * a) ^ O.ord i), ‖u z‖ₑ ^ 2) +
            ∫⁻ z in ball (O.pt i) ((2 * a) ^ O.ord i), ‖fderiv ℝ u z‖ₑ ^ 2) := by
  obtain ⟨a, ha, ha4, μ, hμc, hμp, hμe, hball, hch⟩ := O.exists_cone_radius i
  set p := O.pt i
  set m := O.ord i
  have hm : m ≠ 0 := O.ord_ne_zero i
  have hm2 : 2 ≤ m := O.two_le_ord i
  obtain ⟨w₀, hw₀, hmin⟩ := (isCompact_closedBall (0 : ℂ) a).exists_isMinOn
    (nonempty_closedBall.2 ha.le) hμc
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) a).exists_bound_of_continuousOn hμc
  set K : ℝ := (m : ℝ) ^ 2 * a ^ (2 * (m - 1)) with hK
  have hKpos : 0 < K := by positivity
  have hnormsq : ∀ w : ℂ, ‖(m : ℂ) * w ^ (m - 1)‖ ^ 2 = (m : ℝ) ^ 2 * ‖w‖ ^ (2 * (m - 1)) := by
    intro w
    rw [norm_mul, norm_pow, Complex.norm_natCast, mul_pow, ← pow_mul, mul_comm (m - 1) 2]
  set N : ℝ≥0∞ := ENNReal.ofReal (1 / K)
  refine ⟨a, ha, μ w₀ / K, div_pos (hμp w₀ hw₀) hKpos,
    ENNReal.ofReal M * (9 * N * m + ENNReal.ofReal (4 * a) * m), hball, ?_, ?_, fun u hu => ?_⟩
  · intro z hz hzP
    obtain ⟨w, hw, rfl⟩ := exists_coneChart_eq hm ha.le hz
    have hw0 : w ≠ 0 := by
      rintro rfl
      exact hzP ⟨i, by simp [coneChart, zero_pow hm, p]⟩
    have hwb : w ∈ ball (0 : ℂ) (2 * a) := ball_subset_ball (by linarith) hw
    have he := hμe w hwb hw0
    unfold chartFactor at he
    have hlam : 0 < O.lam (coneChart p m w) :=
      O.lam_pos _ ⟨O.cb (ball_subset_closedBall (hch w hwb hw0).1), (hch w hwb hw0).2⟩
    have hN : 0 < ‖(m : ℂ) * w ^ (m - 1)‖ ^ 2 := by
      have : (m : ℂ) * w ^ (m - 1) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.2 hm) (pow_ne_zero _ hw0)
      positivity
    have hNK : ‖(m : ℂ) * w ^ (m - 1)‖ ^ 2 ≤ K := by
      rw [hnormsq, hK]
      gcongr
      exact (mem_ball_zero_iff.1 hw).le
    have hmw : μ w₀ ≤ μ w := hmin (ball_subset_closedBall hw)
    rw [div_le_iff₀ hKpos]
    calc μ w₀ ≤ μ w := hmw
      _ = O.lam (coneChart p m w) * ‖(m : ℂ) * w ^ (m - 1)‖ ^ 2 := he
      _ ≤ O.lam (coneChart p m w) * K := mul_le_mul_of_nonneg_left hNK hlam.le
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2
      ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)
        (ENNReal.natCast_ne_top m),
       ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top m)⟩)
  set v : ℂ → ℝ := fun w => u (coneChart p m w) with hv_def
  have hvc : Continuous v := hu.continuous.comp (contDiff_coneChart p m).continuous
  have hvd : ContDiffOn ℝ 1 v (ball 0 (2 * a)) := O.contDiffOn_comp_coneChart hu i hch
  have hF := SteklovFriedrichs.friedrichs_ball hvc ha ha4 hvd
  have hum : Measurable fun z => ‖u z‖ₑ ^ 2 := hu.continuous.measurable.enorm.pow_const 2
  have hm1 : m - 1 ≠ 0 := by omega
  -- the weighted integral, computed in the chart
  have hb : ∫⁻ z in ball p (a ^ m), ENNReal.ofReal (O.lamI z) * ‖u z‖ₑ ^ 2 ≤
      ENNReal.ofReal M * ∫⁻ w in ball (0 : ℂ) a, ‖v w‖ₑ ^ 2 := by
    refine (cone_lintegral_le p hm ha.le _
      ((O.measurable_lamI.ennreal_ofReal).mul hum)).trans ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun w hw => ?_
    by_cases hw0 : w = 0
    · subst hw0; simp [zero_pow hm1]
    · have hwb : w ∈ ball (0 : ℂ) (2 * a) := ball_subset_ball (by linarith) hw
      have hc := hch w hwb hw0
      have hlam : 0 < O.lam (coneChart p m w) :=
        O.lam_pos _ ⟨O.cb (ball_subset_closedBall hc.1), hc.2⟩
      rw [O.lamI_eq ⟨O.cb (ball_subset_closedBall hc.1), hc.2⟩]
      have he := hμe w hwb hw0
      unfold chartFactor at he
      calc ‖(m : ℂ) * w ^ (m - 1)‖ₑ ^ 2 *
            (ENNReal.ofReal (O.lam (coneChart p m w)) * ‖u (coneChart p m w)‖ₑ ^ 2)
          = ENNReal.ofReal (O.lam (coneChart p m w) * ‖(m : ℂ) * w ^ (m - 1)‖ ^ 2) *
              ‖v w‖ₑ ^ 2 := by
            rw [ENNReal.ofReal_mul hlam.le, ← ofReal_norm_eq_enorm,
              ← ENNReal.ofReal_pow (norm_nonneg _)]
            ring
        _ = ENNReal.ofReal (μ w) * ‖v w‖ₑ ^ 2 := by rw [← he]
        _ ≤ ENNReal.ofReal M * ‖v w‖ₑ ^ 2 := by
            gcongr
            exact (le_abs_self _).trans (hM w (ball_subset_closedBall hw))
  -- the annulus term
  have hd : ∫⁻ w in ball (0 : ℂ) (2 * a) \ ball 0 a, ‖v w‖ₑ ^ 2 ≤
      N * (m * ∫⁻ z in ball p ((2 * a) ^ m), ‖u z‖ₑ ^ 2) := by
    calc ∫⁻ w in ball (0 : ℂ) (2 * a) \ ball 0 a, ‖v w‖ₑ ^ 2
        ≤ ∫⁻ w in ball (0 : ℂ) (2 * a) \ ball 0 a,
            N * (‖(m : ℂ) * w ^ (m - 1)‖ₑ ^ 2 * ‖u (coneChart p m w)‖ₑ ^ 2) := by
          refine setLIntegral_mono' (measurableSet_ball.diff measurableSet_ball)
            fun w hw => ?_
          have hwa : a ≤ ‖w‖ := by
            have := hw.2; rwa [mem_ball_zero_iff, not_lt] at this
          have hKw : K ≤ ‖(m : ℂ) * w ^ (m - 1)‖ ^ 2 := by
            rw [hnormsq, hK]; gcongr
          have h1 : (1 : ℝ≥0∞) ≤ N * ‖(m : ℂ) * w ^ (m - 1)‖ₑ ^ 2 := by
            rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
              ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
            refine ENNReal.ofReal_le_ofReal ?_
            rw [one_div, inv_mul_eq_div, le_div_iff₀ hKpos, one_mul]
            exact hKw
          calc ‖v w‖ₑ ^ 2 = 1 * ‖v w‖ₑ ^ 2 := (one_mul _).symm
            _ ≤ (N * ‖(m : ℂ) * w ^ (m - 1)‖ₑ ^ 2) * ‖v w‖ₑ ^ 2 := by gcongr
            _ = _ := by rw [mul_assoc]
      _ ≤ ∫⁻ w in ball (0 : ℂ) (2 * a),
            N * (‖(m : ℂ) * w ^ (m - 1)‖ₑ ^ 2 * ‖u (coneChart p m w)‖ₑ ^ 2) :=
          lintegral_mono_set diff_subset
      _ = N * ∫⁻ w in ball (0 : ℂ) (2 * a),
            ‖(m : ℂ) * w ^ (m - 1)‖ₑ ^ 2 * ‖u (coneChart p m w)‖ₑ ^ 2 :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ N * (m * ∫⁻ z in ball p ((2 * a) ^ m), ‖u z‖ₑ ^ 2) := by
          gcongr
          exact cone_lintegral_ge p hm _ _ hum
  -- the gradient term
  have he : ∫⁻ w in ball (0 : ℂ) (2 * a), ‖fderiv ℝ v w‖ₑ ^ 2 ≤
      m * ∫⁻ z in ball p ((2 * a) ^ m), ‖fderiv ℝ u z‖ₑ ^ 2 := by
    refine le_trans ?_ (cone_lintegral_ge p hm _ _
      ((measurable_fderiv ℝ u).enorm.pow_const 2))
    refine lintegral_mono_ae ?_
    have h0 : volume ({0} : Set ℂ) = 0 := measure_singleton 0
    filter_upwards [ae_restrict_mem measurableSet_ball,
      ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 h0)] with w hw hw0
    have hw0' : w ≠ 0 := hw0
    have hc := hch w hw hw0'
    have hud : DifferentiableAt ℝ u (coneChart p m w) :=
      (hu.1.contDiffAt (O.isOpen_compl_S.mem_nhds hc.2)).differentiableAt (by simp)
    have hn := norm_fderiv_comp_coneChart p m hud
    apply le_of_eq
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity), hv_def, hn,
      mul_pow]
  set A := ∫⁻ z in ball p ((2 * a) ^ m), ‖u z‖ₑ ^ 2
  set B := ∫⁻ z in ball p ((2 * a) ^ m), ‖fderiv ℝ u z‖ₑ ^ 2
  calc ∫⁻ z in ball p (a ^ m), ENNReal.ofReal (O.lamI z) * ‖u z‖ₑ ^ 2
      ≤ ENNReal.ofReal M * ∫⁻ w in ball (0 : ℂ) a, ‖v w‖ₑ ^ 2 := hb
    _ ≤ ENNReal.ofReal M * (9 * (∫⁻ w in ball (0 : ℂ) (2 * a) \ ball 0 a, ‖v w‖ₑ ^ 2) +
          ENNReal.ofReal (4 * a) * ∫⁻ w in ball (0 : ℂ) (2 * a), ‖fderiv ℝ v w‖ₑ ^ 2) := by
        gcongr
    _ ≤ ENNReal.ofReal M * (9 * (N * (m * A)) + ENNReal.ofReal (4 * a) * (m * B)) := by
        gcongr
    _ ≤ ENNReal.ofReal M * ((9 * N * m + ENNReal.ofReal (4 * a) * m) * (A + B)) := by
        gcongr
        calc 9 * (N * (m * A)) + ENNReal.ofReal (4 * a) * (m * B)
            = (9 * N * m) * A + (ENNReal.ofReal (4 * a) * m) * B := by ring
          _ ≤ (9 * N * m) * (A + B) + (ENNReal.ofReal (4 * a) * m) * (A + B) := by
              gcongr
              · exact le_self_add
              · exact le_add_self
          _ = _ := by ring
    _ = _ := by ring

lemma exists_pos_le_all {ι : Type*} [Finite ι] (f : ι → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c > 0, ∀ i, c ≤ f i := by
  by_cases h : Nonempty ι
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_min f
    exact ⟨f i₀, hf i₀, hi₀⟩
  · exact ⟨1, one_pos, fun i => (h ⟨i⟩).elim⟩

/-- Data for the decomposition of `𝔻` into small cone neighbourhoods and a compact part away from
the cone points. -/
theorem exists_decomposition :
    ∃ (a : Fin O.n → ℝ) (c : Fin O.n → ℝ) (C : Fin O.n → ℝ≥0∞),
      (∀ i, 0 < a i) ∧ (∀ i, ball (O.pt i) ((2 * a i) ^ O.ord i) ⊆ ball 0 1) ∧
      (∀ i, 0 < c i) ∧
      (∀ i, ∀ z ∈ ball (O.pt i) (a i ^ O.ord i), z ∉ range O.pt → c i ≤ O.lam z) ∧
      (∀ i, C i ≠ ⊤) ∧
      (∀ i u, O.IsOrbSmooth u →
        ∫⁻ z in ball (O.pt i) (a i ^ O.ord i), ENNReal.ofReal (O.lamI z) * ‖u z‖ₑ ^ 2 ≤
          C i * ((∫⁻ z in ball (O.pt i) ((2 * a i) ^ O.ord i), ‖u z‖ₑ ^ 2) +
            ∫⁻ z in ball (O.pt i) ((2 * a i) ^ O.ord i), ‖fderiv ℝ u z‖ₑ ^ 2)) := by
  choose a ha c hc C hball hcl hC hCb using O.cone_estimates
  exact ⟨a, c, C, ha, hball, hc, hcl, hC, hCb⟩

/-- **The conformal factor is bounded below** on `𝔻` minus the cone points (it blows up at the cone
points, where `λ(p + w^m) = μ(w) / |m w^{m-1}|²`). -/
theorem exists_lam_lower : ∃ c > 0, ∀ z ∈ ball (0 : ℂ) 1 \ range O.pt, c ≤ O.lam z := by
  obtain ⟨a, c, C, ha, hball, hc, hcl, -, -⟩ := O.exists_decomposition
  set V := ⋃ i, ball (O.pt i) (a i ^ O.ord i)
  set K := closedBall (0 : ℂ) 1 \ V
  have hK : IsCompact K := (isCompact_closedBall 0 1).diff (isOpen_iUnion fun i => isOpen_ball)
  have hKU : K ⊆ O.U \ range O.pt := by
    rintro z ⟨hz, hzV⟩
    refine ⟨O.cb hz, ?_⟩
    rintro ⟨i, rfl⟩
    exact hzV (mem_iUnion.2 ⟨i, mem_ball_self (pow_pos (ha i) _)⟩)
  obtain ⟨c₀, hc₀, hc₀K⟩ : ∃ c₀ > 0, ∀ z ∈ K, c₀ ≤ O.lam z := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, fun z hz => by rw [hKe] at hz; exact hz.elim⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hKne
        (O.lam_smooth.continuousOn.mono hKU)
      exact ⟨O.lam z₀, O.lam_pos _ (hKU hz₀), fun z hz => hmin hz⟩
  obtain ⟨c₁, hc₁, hc₁i⟩ := exists_pos_le_all c hc
  refine ⟨min c₀ c₁, lt_min hc₀ hc₁, fun z ⟨hz, hzP⟩ => ?_⟩
  by_cases hzV : z ∈ V
  · obtain ⟨i, hi⟩ := mem_iUnion.1 hzV
    exact (min_le_right _ _).trans ((hc₁i i).trans (hcl i z hi hzP))
  · exact (min_le_left _ _).trans (hc₀K z ⟨ball_subset_closedBall hz, hzV⟩)

/-- **Weighted Sobolev estimate.** For every orbifold-smooth `u`,
`∫_𝔻 u² λ dA ≤ C (∫_𝔻 u² dA + ∫_𝔻 |∇u|² dA)`, with `C` depending only on `O`. -/
theorem exists_weighted_bound : ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ u, O.IsOrbSmooth u →
    ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (O.lamI z) * ‖u z‖ₑ ^ 2 ≤
      C * ((∫⁻ z in ball (0 : ℂ) 1, ‖u z‖ₑ ^ 2) +
        ∫⁻ z in ball (0 : ℂ) 1, ‖fderiv ℝ u z‖ₑ ^ 2) := by
  obtain ⟨a, c, C, ha, hball, -, -, hC, hCb⟩ := O.exists_decomposition
  set V := ⋃ i, ball (O.pt i) (a i ^ O.ord i)
  set K := closedBall (0 : ℂ) 1 \ V
  have hK : IsCompact K := (isCompact_closedBall 0 1).diff (isOpen_iUnion fun i => isOpen_ball)
  have hKU : K ⊆ O.U \ range O.pt := by
    rintro z ⟨hz, hzV⟩
    refine ⟨O.cb hz, ?_⟩
    rintro ⟨i, rfl⟩
    exact hzV (mem_iUnion.2 ⟨i, mem_ball_self (pow_pos (ha i) _)⟩)
  obtain ⟨Λ, hΛ⟩ := hK.exists_bound_of_continuousOn (O.lam_smooth.continuousOn.mono hKU)
  refine ⟨ENNReal.ofReal Λ + ∑ i, C i, ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
    ENNReal.sum_ne_top.2 fun i _ => hC i⟩, fun u hu => ?_⟩
  set A := ∫⁻ z in ball (0 : ℂ) 1, ‖u z‖ₑ ^ 2
  set B := ∫⁻ z in ball (0 : ℂ) 1, ‖fderiv ℝ u z‖ₑ ^ 2
  set G : ℂ → ℝ≥0∞ := fun z => ENNReal.ofReal (O.lamI z) * ‖u z‖ₑ ^ 2
  have hsub : ball (0 : ℂ) 1 ⊆ (ball 0 1 \ V) ∪ V := fun z hz => by
    by_cases h : z ∈ V
    · exact Or.inr h
    · exact Or.inl ⟨hz, h⟩
  have h1 : ∫⁻ z in ball (0 : ℂ) 1 \ V, G z ≤ ENNReal.ofReal Λ * A := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (setLIntegral_mono' (measurableSet_ball.diff
      (MeasurableSet.iUnion fun i => measurableSet_ball)) fun z hz => ?_).trans
      (lintegral_mono_set diff_subset)
    have hzK : z ∈ K := ⟨ball_subset_closedBall hz.1, hz.2⟩
    simp only [G]
    rw [O.lamI_eq (hKU hzK)]
    gcongr
    exact (le_abs_self _).trans (by simpa using hΛ z hzK)
  have h2 : ∀ i, ∫⁻ z in ball (O.pt i) (a i ^ O.ord i), G z ≤ C i * (A + B) := fun i =>
    (hCb i u hu).trans (by
      gcongr
      · exact lintegral_mono_set (hball i)
      · exact lintegral_mono_set (hball i))
  calc ∫⁻ z in ball (0 : ℂ) 1, G z
      ≤ ∫⁻ z in (ball 0 1 \ V) ∪ V, G z := lintegral_mono_set hsub
    _ ≤ (∫⁻ z in ball (0 : ℂ) 1 \ V, G z) + ∫⁻ z in V, G z := lintegral_union_le _ _ _
    _ ≤ ENNReal.ofReal Λ * A + ∑ i, C i * (A + B) := by
        gcongr
        refine (lintegral_iUnion_le _ _).trans ?_
        rw [tsum_fintype]
        exact Finset.sum_le_sum fun i _ => h2 i
    _ ≤ (ENNReal.ofReal Λ + ∑ i, C i) * (A + B) := by
        rw [add_mul, Finset.sum_mul]
        gcongr
        exact le_self_add

/-- **The orbisurface has finite area**: `Area_g(O) = ∫_𝔻 λ dA < ∞`. -/
theorem area_lt_top : O.areaMeasure univ < ⊤ := by
  obtain ⟨C, hC, hb⟩ := O.exists_weighted_bound
  have h1 := hb (fun _ => 1) (O.isOrbSmooth_of_contDiff contDiff_const)
  have hfd : ∀ z, fderiv ℝ (fun _ : ℂ => (1 : ℝ)) z = 0 := fun z => fderiv_const_apply _
  simp only [hfd, enorm_one, one_pow, mul_one] at h1
  rw [areaMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have heq : ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (O.lam z) =
      ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (O.lamI z) := by
    refine lintegral_congr_ae ?_
    filter_upwards [O.ae_ball_not_cone] with z hz
    rw [O.lamI_eq ⟨O.cb (ball_subset_closedBall hz.1), hz.2⟩]
  rw [heq]
  refine h1.trans_lt (ENNReal.mul_lt_top hC.lt_top ?_)
  simp [← ofReal_norm_eq_enorm]

end DiskOrbisurface

end SteklovOrb
