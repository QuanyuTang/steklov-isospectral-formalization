module

public import RequestProject.OuterRealization
public import RequestProject.ConformalImage

/-!
# Proposition 2.3.1, convergence part: `F_ρ → c·id` in `C^∞(𝔻̄)`

* `main_estimate` — for every order `k` and `η > 0` there is `δ > 0` such that every normalized
  realizing map `F` of a positive real-analytic weight `ρ` with `‖ρ - c‖_{C^{k+2}} < δ`
  satisfies `‖D^k (F - c·id)‖ < η` on `𝔻̄`.  Proof: by uniqueness (`deriv_eq_outer`)
  `F' = c e^{H}`; `|H^{(j)}| ≤ 5 · max_{i ≤ j+2} ‖h^{(i)}‖_∞` on `𝔻̄` (Fourier estimate);
  `‖h^{(i)}‖_∞ ≤ K δ` (`log_comp_bound`); and Faà di Bruno for `e^{H}`.
* `prop_2_3_1_convergence : Prop_2_3_1_convergence` (parameter formulation, for *all* normalized
  realizing maps);
* `prop_2_3_1_convergence_seq : Prop_2_3_1_convergence_seq` (the paper's sequence formulation);
* `prop_2_3_1_complete : Prop_2_3_1_complete` — the whole proposition.
-/

@[expose] public section

open Real Complex Set Metric Filter Topology OuterFunction OuterRealization
open scoped Nat ContDiff

noncomputable section

namespace OuterConvergence

/-- For a holomorphic map, the real `k`-th derivative has the norm of the complex one. -/
lemma norm_iteratedFDeriv_real_eq {Φ : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hd : DifferentiableOn ℂ Φ V) {z : ℂ} (hz : z ∈ V) (k : ℕ) :
    ‖iteratedFDeriv ℝ k Φ z‖ = ‖iteratedDeriv k Φ z‖ := by
  have hcd : ContDiffAt ℂ k Φ z := (hd.contDiffOn hV).contDiffAt (hV.mem_nhds hz)
  rw [← hcd.restrictScalars_iteratedFDeriv (𝕜 := ℝ), Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]

lemma iteratedDeriv_cexp (i : ℕ) : iteratedDeriv i Complex.exp = Complex.exp := by
  rw [iteratedDeriv_eq_iterate]; exact Complex.iter_deriv_exp i

/-- Faà di Bruno bound for `e^{H}` when the derivatives of `H` are small. -/
lemma norm_iteratedDeriv_exp_comp_le {Hf : ℂ → ℂ} {V : Set ℂ} (hV : IsOpen V)
    (hd : DifferentiableOn ℂ Hf V) {z : ℂ} (hz : z ∈ V) {m : ℕ} (hm : 1 ≤ m) {S : ℝ}
    (hS0 : 0 ≤ S) (hS1 : S ≤ 1) (hval : ‖Hf z‖ ≤ 1)
    (hder : ∀ i, 1 ≤ i → i ≤ m → ‖iteratedDeriv i Hf z‖ ≤ S) :
    ‖iteratedDeriv m (fun w => Complex.exp (Hf w)) z‖ ≤ m ! * 3 * S := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv, ← iteratedFDerivWithin_of_isOpen m hV hz]
  have hexp : ContDiffOn ℂ ∞ Complex.exp univ := Complex.contDiff_exp.contDiffOn
  refine CompositionBounds.norm_iteratedFDerivWithin_comp_le_small (g := Complex.exp) (f := Hf)
    hexp (hd.contDiffOn hV) (WithTop.coe_le_coe.2 le_top) uniqueDiffOn_univ hV.uniqueDiffOn
    (mapsTo_univ _ _) hz hm hS0 hS1 (fun i _ => ?_) (fun i hi1 him => ?_)
  · rw [iteratedFDerivWithin_univ, norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp,
      Complex.norm_exp]
    calc Real.exp (Hf z).re ≤ Real.exp 1 :=
          Real.exp_le_exp.2 ((Complex.re_le_norm _).trans hval)
      _ ≤ 3 := (Real.exp_one_lt_d9.trans (by norm_num)).le
  · rw [iteratedFDerivWithin_of_isOpen i hV hz, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hder i hi1 him

/-- **The main `C^k` estimate** behind the convergence part of Proposition 2.3.1. -/
theorem main_estimate {c : ℝ} (hc : 0 < c) (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∃ δ > (0 : ℝ), ∀ (ρ : ℂ → ℝ) (F : ℂ → ℂ), IsPosRealAnalyticWeight ρ →
      CkClose (k + 2) δ ρ c → IsNormalizedRealizing F ρ →
      ∀ z ∈ closedBall (0 : ℂ) 1, ‖iteratedFDeriv ℝ k (fun w => F w - (c : ℂ) * w) z‖ < η := by
  obtain ⟨K, hK0, hK⟩ := logWeight_deriv_bound hc (k + 2)
  set T : ℝ := 30 * c * k ! * (K + 1) with hT
  have hTpos : 0 < T := by positivity
  set δ : ℝ := min (min 1 (c / 2)) (min (1 / (5 * (K + 1))) (η / (2 * T))) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hδc : δ ≤ c / 2 := (min_le_left _ _).trans (min_le_right _ _)
  have hδK : δ ≤ 1 / (5 * (K + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hδη : δ ≤ η / (2 * T) := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨δ, hδpos, fun ρ F hρ hck hF z hz => ?_⟩
  obtain ⟨hFU, hinj, hF0, hre, him, hnorm⟩ := hF
  have hbd := hK ρ hρ δ hδpos.le hδ1 hδc (bounds_of_ckClose hck)
  set S : ℝ := 5 * (K * δ) with hS
  have hS0 : 0 ≤ S := by positivity
  have hS1 : S ≤ 1 := by
    have : 5 * (K + 1) * δ ≤ 1 := by
      calc 5 * (K + 1) * δ ≤ 5 * (K + 1) * (1 / (5 * (K + 1))) := by gcongr
        _ = 1 := by field_simp
    nlinarith
  have hST : 5 * c * k ! * S ≤ η / 2 := by
    have h1 : 5 * c * k ! * S ≤ T * δ := by
      rw [hS, hT]
      have : (0 : ℝ) ≤ c * k ! := by positivity
      nlinarith
    calc 5 * c * k ! * S ≤ T * δ := h1
      _ ≤ T * (η / (2 * T)) := by gcongr
      _ = η / 2 := by field_simp
  -- the analytic data
  obtain ⟨R, hR1, hHd, hiter, -⟩ := exists_outer_primitive c hρ
  obtain ⟨r, hr1, hFdV, hderiv⟩ := deriv_eq_outer hc hρ hFU hinj hre him hnorm
  set V := ball (0 : ℂ) (min r R) with hV
  have hV1 : 1 < min r R := lt_min hr1 hR1
  have hVr : V ⊆ ball 0 r := ball_subset_ball (min_le_left _ _)
  have hVR : V ⊆ ball 0 R := ball_subset_ball (min_le_right _ _)
  have hcl : closedBall (0 : ℂ) 1 ⊆ V := closedBall_subset_ball hV1
  have hzV : z ∈ V := hcl hz
  have hHj : ∀ j ≤ k, ∀ w ∈ closedBall (0 : ℂ) 1, ‖iteratedDeriv j (H (logWeight c ρ)) w‖ ≤ S := by
    intro j hj w hw
    rw [hiter j w (hVR (hcl hw))]
    exact norm_Hj_le_of_bound hρ (j := j) (fun i hi t => hbd i (by omega) t)
      (by simpa using hw)
  have hH0 : ∀ w ∈ closedBall (0 : ℂ) 1, ‖H (logWeight c ρ) w‖ ≤ S := fun w hw => by
    simpa using hHj 0 (Nat.zero_le _) w hw
  set Φ : ℂ → ℂ := fun w => F w - (c : ℂ) * w with hΦ
  have hΦd : DifferentiableOn ℂ Φ V :=
    (hFdV.mono hVr).sub ((differentiableOn_const _).mul differentiableOn_id)
  have hderivΦ : ∀ w ∈ V, deriv Φ w = (c : ℂ) * (Complex.exp (H (logWeight c ρ) w) - 1) := by
    intro w hw
    have hFw : DifferentiableAt ℂ F w := (hFdV w (hVr hw)).differentiableAt
      (isOpen_ball.mem_nhds (hVr hw))
    have := (hFw.hasDerivAt.fun_sub ((hasDerivAt_id' w).const_mul (c : ℂ))).deriv
    rw [hΦ, this, hderiv w (hVr hw), outer]
    ring
  have hexp1 : ∀ w ∈ closedBall (0 : ℂ) 1,
      ‖(c : ℂ) * (Complex.exp (H (logWeight c ρ) w) - 1)‖ ≤ 2 * c * S := by
    intro w hw
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    have := Complex.norm_exp_sub_one_le ((hH0 w hw).trans hS1)
    nlinarith [hH0 w hw]
  have hk1 : (1 : ℝ) ≤ k ! := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (Nat.factorial_ne_zero k)
  have hbound : ‖iteratedDeriv k Φ z‖ ≤ 5 * c * k ! * S := by
    rcases k with _ | m
    · -- order 0: mean value inequality on the closed disk
      simp only [iteratedDeriv_zero]
      have hmv := Convex.norm_image_sub_le_of_norm_deriv_le (f := Φ) (s := closedBall (0 : ℂ) 1)
        (C := 2 * c * S) (fun w hw => (hΦd w (hcl hw)).differentiableAt
          (isOpen_ball.mem_nhds (hcl hw)))
        (fun w hw => by rw [hderivΦ w (hcl hw)]; exact hexp1 w hw) (convex_closedBall 0 1)
        (mem_closedBall_self zero_le_one) hz
      have hΦ0 : Φ 0 = 0 := by simp [hΦ, hF0]
      rw [hΦ0, sub_zero, sub_zero] at hmv
      have hz1 : ‖z‖ ≤ 1 := by simpa using hz
      calc ‖Φ z‖ ≤ 2 * c * S * ‖z‖ := hmv
        _ ≤ 2 * c * S * 1 := by gcongr
        _ ≤ 5 * c * (Nat.factorial 0 : ℝ) * S := by simp; nlinarith
    · rw [iteratedDeriv_succ']
      have hev : deriv Φ =ᶠ[𝓝 z] fun w => (c : ℂ) * (Complex.exp (H (logWeight c ρ) w) - 1) :=
        Filter.eventually_of_mem (isOpen_ball.mem_nhds hzV) hderivΦ
      rw [hev.iteratedDeriv_eq]
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp only [iteratedDeriv_zero]
        refine (hexp1 z hz).trans ?_
        simp only [zero_add, Nat.factorial_one, Nat.cast_one, mul_one]
        nlinarith
      · rw [iteratedDeriv_const_mul_field]
        have hfun : (fun w => Complex.exp (H (logWeight c ρ) w) - 1) =
            fun w => (-1 : ℂ) + Complex.exp (H (logWeight c ρ) w) := by
          funext w; ring
        rw [hfun, iteratedDeriv_const_add hm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hc]
        have hexpb := norm_iteratedDeriv_exp_comp_le (Hf := H (logWeight c ρ)) isOpen_ball
          (hHd.mono hVR) hzV hm hS0 hS1 ((hH0 z hz).trans hS1)
          (fun i _ hi => hHj i (by omega) z hz)
        have hmf : (m ! : ℝ) ≤ (m + 1)! := by exact_mod_cast Nat.factorial_le (Nat.le_succ m)
        calc c * ‖iteratedDeriv m (fun w => Complex.exp (H (logWeight c ρ) w)) z‖
            ≤ c * (m ! * 3 * S) := by gcongr
          _ ≤ c * ((m + 1)! * 3 * S) := by gcongr
          _ ≤ 5 * c * ((m + 1)! : ℝ) * S := by nlinarith
  rw [norm_iteratedFDeriv_real_eq isOpen_ball hΦd hzV]
  linarith

/-- **Proposition 2.3.1, convergence part (parameter formulation), proved.** -/
theorem prop_2_3_1_convergence : Prop_2_3_1_convergence := by
  intro c hc ρ F hgood hclose hF k η hη
  obtain ⟨δ, hδ, hmain⟩ := main_estimate hc k hη
  filter_upwards [hgood, hclose (k + 2) δ hδ, hF] with ε h1 h2 h3
  exact hmain (ρ ε) (F ε) h1 h2 h3

/-- **Proposition 2.3.1, convergence part (the paper's sequence formulation), proved.** -/
theorem prop_2_3_1_convergence_seq : Prop_2_3_1_convergence_seq := by
  intro c hc ρ hgood hclose
  obtain ⟨k₀, δ₀, hδ₀, hreal⟩ := prop_2_3_1_realization c hc
  classical
  let F : ℕ → ℂ → ℂ := fun n =>
    if h : ∃ G : ℂ → ℂ, IsNormalizedRealizing G (ρ n) then h.choose else fun _ => 0
  have hF : ∀ᶠ n in atTop, IsNormalizedRealizing (F n) (ρ n) := by
    filter_upwards [hclose k₀ δ₀ hδ₀] with n hn
    have hex : ∃ G : ℂ → ℂ, IsNormalizedRealizing G (ρ n) := by
      obtain ⟨G, hG⟩ := hreal (ρ n) (hgood n) hn
      exact ⟨G, hG⟩
    simp only [F, dif_pos hex]
    exact hex.choose_spec
  refine ⟨F, hF, fun k η hη => ?_⟩
  obtain ⟨δ, hδ, hmain⟩ := main_estimate hc k hη
  filter_upwards [hclose (k + 2) δ hδ, hF] with n h2 h3
  exact hmain (ρ n) (F n) (hgood n) h2 h3

/-- **Proposition 2.3.1 (complete statement), proved**: realization with all geometric and
spectral conclusions, and convergence in the paper's sequence formulation. -/
theorem prop_2_3_1_complete : Prop_2_3_1_complete := by
  refine ⟨fun c hc => ?_, prop_2_3_1_convergence_seq⟩
  obtain ⟨k, δ, hδ, h⟩ := prop_2_3_1_realization c hc
  refine ⟨k, δ, hδ, fun ρ hρ hck => ?_⟩
  obtain ⟨F, hFU, hinj, h0, hre, him, hnorm⟩ := h ρ hρ hck
  obtain ⟨U, hUo, hUc, hFd⟩ := hFU
  have hF' : ∀ z ∈ sphere (0 : ℂ) 1, deriv F z ≠ 0 := by
    intro z hz h0'
    obtain ⟨t, rfl⟩ := Prop231Reduction.exists_exp_eq_of_mem_sphere hz
    have := hρ.2 t
    rw [← hnorm _ hz, h0', norm_zero] at this
    exact lt_irrefl _ this
  refine ⟨F, ⟨⟨U, hUo, hUc, hFd⟩, hinj, h0, hre, him, hnorm⟩,
    ConformalImage.isDomain_image_ball hUc hFd hinj,
    ConformalImage.isBounded_image_ball hUc hFd,
    ConformalImage.simplyConnected_image_ball hUc hFd hinj,
    ConformalImage.realAnalyticJordan_image_ball hUo hUc hFd hinj hF', ?_⟩
  rw [ConformalPullback.prop_2_1_1 F ⟨U, hUo, hUc, hFd⟩ hinj hF']
  exact Prop231Reduction.weightedSteklovSpectrum_congr hnorm

end OuterConvergence

end
