module

public import Mathlib
public import RequestProject.Coalescence
public import RequestProject.BoundaryLength

/-!
# Feeding Proposition 3.4.1 into Proposition 2.3.1 (§3.5, conclusions (iv) and (v))

* `blaschke_weight_posAnalytic`: for a finite Blaschke product `B` of degree `n ≥ 1`, the
  boundary weight `|B'|` is positive and real-analytic on `𝕋`.
* `coalescence_realization`: under the hypotheses of `prop_3_4_1` (paper polynomial data and the
  explicit cover input), for all small `ε > 0` the weights `|B_ε'|` are realized by normalized
  maps `F_ε` (holomorphic near `𝔻̄`, injective on `𝔻̄`, `F_ε(0) = 0`, `F_ε'(0) > 0`), the domains
  `F_ε(𝔻)` are bounded simply connected domains with real-analytic Jordan boundary and
  `Spec_St(F_ε(𝔻)) = Spec_St(𝔻, |B_ε'|)`, the rescaled domains `(1/n) F_ε(𝔻)` have boundary
  length `2π`, and `F_ε → n·id` in `C^∞(𝔻̄)`.
-/

@[expose] public section

open Complex Metric Set Filter Topology SteklovBlaschke PlaneDomain Steklov

noncomputable section

namespace SteklovCoalescence

lemma bdens_pos {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ = 1) : 0 < bdens a z := by
  have hza : z - a ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; subst h; rw [hz] at ha; exact lt_irrefl _ ha
  have : normSq a < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  exact div_pos (by linarith) (normSq_pos.2 hza)

lemma hsum_analyticAt {n : ℕ} {a : Fin n → ℂ} {w : ℂ} (hw : ∀ j, w - a j ≠ 0) :
    AnalyticAt ℂ (hsum a) w := by
  have h : AnalyticAt ℂ (∑ j, fun z => 2 * a j / (z - a j)) w :=
    Finset.analyticAt_sum _ fun j _ =>
      analyticAt_const.div (analyticAt_id.sub analyticAt_const) (hw j)
  have : (∑ j, fun z => 2 * a j / (z - a j)) = hsum a := by
    ext; simp [hsum, Finset.sum_apply]
  rwa [this] at h

lemma analyticAt_re_circle {g : ℂ → ℂ} {t : ℝ} (hg : AnalyticAt ℂ g (exp (t * I))) :
    AnalyticAt ℝ (fun s : ℝ => (g (exp (s * I))).re) t := by
  have he : AnalyticAt ℝ (fun s : ℝ => exp ((s : ℂ) * I)) t := by
    have h1 : AnalyticAt ℝ (fun s : ℝ => (s : ℂ) * I) t :=
      (ofRealCLM.analyticAt t).mul analyticAt_const
    exact (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp h1
  have : AnalyticAt ℝ (fun s : ℝ => g (exp ((s : ℂ) * I))) t :=
    (hg.restrictScalars (𝕜 := ℝ)).comp (f := fun s : ℝ => exp ((s : ℂ) * I)) he
  exact (reCLM.analyticAt _).comp (f := fun s : ℝ => g (exp ((s : ℂ) * I))) this

/-- **The boundary weight `|B'|` of a finite Blaschke product of degree `n ≥ 1` is positive and
real-analytic on `𝕋`.** -/
theorem blaschke_weight_posAnalytic {B : ℂ → ℂ} {n : ℕ} (hn : 1 ≤ n)
    (hB : IsFiniteBlaschke B n) : IsPosRealAnalyticWeight (fun z => ‖deriv B z‖) := by
  obtain ⟨η, a, hη, ha, rfl⟩ := hB
  have heq := weight_sub_eq hη ha
  refine ⟨fun t _ => ?_, fun t => ?_⟩
  · have hfun : (fun s : ℝ => ‖deriv (fun w => η * ∏ j, bfac (a j) w) (exp (s * I))‖) =
        fun s : ℝ => (n : ℝ) + (hsum a (exp (s * I))).re := by
      ext s
      have := congrFun heq s
      try simp only at this
      linarith
    try simp only
    rw [hfun]
    refine analyticAt_const.add (analyticAt_re_circle (hsum_analyticAt fun j h => ?_))
    have h1 : exp (t * I) = a j := sub_eq_zero.1 h
    have := ha j
    rw [← h1, norm_exp_ofReal_mul_I] at this
    exact lt_irrefl _ this
  · have hz : ‖exp (t * I)‖ = 1 := norm_exp_ofReal_mul_I t
    try simp only
    rw [norm_deriv_blaschke_circle hη ha hz]
    haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    exact Finset.sum_pos (fun j _ => bdens_pos (ha j) hz) Finset.univ_nonempty

open SteklovCritical in
/-- **Proposition 3.4.1 feeds Proposition 2.3.1** (§3.5, conclusions (iv), (v) and the transfer
part of (ii)), conditional only on the explicit cover input of `prop_3_4_1`. -/
theorem coalescence_realization {P : Polynomial ℂ} (hP : P.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : P.natDegree = n) {τ : ℝ → ℂ} (hτ : ∀ ε, τ ε ^ n = (lamStar - 1) * ε)
    {ψ B : ℝ → ℂ → ℂ}
    (hcov : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsNormalizedDiskCover (paperQ P τ ε) n (ψ ε) (B ε)) :
    ∃ F : ℝ → ℂ → ℂ,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ),
        IsNormalizedRealizing (F ε) (fun z => ‖deriv (B ε) z‖) ∧
        IsDomain (F ε '' ball 0 1) ∧ Bornology.IsBounded (F ε '' ball 0 1) ∧
        SimplyConnectedSpace (F ε '' ball 0 1) ∧ IsRealAnalyticJordanBoundary (F ε '' ball 0 1) ∧
        steklovSpectrum (F ε '' ball 0 1) = weightedSteklovSpectrum (fun z => ‖deriv (B ε) z‖) ∧
        boundaryLength ((fun z : ℂ => ((n : ℝ)⁻¹) • z) '' (F ε '' ball 0 1)) =
          ENNReal.ofReal (2 * Real.pi)) ∧
      ∀ k : ℕ, ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ closedBall (0 : ℂ) 1,
        ‖iteratedFDeriv ℝ k (fun w => F ε w - (n : ℂ) * w) z‖ < η := by
  have hconc := prop_3_4_1 hP hn hdeg hτ hcov
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set ρ : ℝ → ℂ → ℝ := fun ε z => ‖deriv (B ε) z‖ with hρ
  have hgood : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsPosRealAnalyticWeight (ρ ε) :=
    hcov.mono fun ε h => blaschke_weight_posAnalytic hn h.2.2.2.2.2.2.1
  obtain ⟨k₀, δ₀, hδ₀, hreal⟩ := OuterConvergence.prop_2_3_1_complete.1 n hn0
  classical
  set Good : ℝ → (ℂ → ℂ) → Prop := fun ε G =>
    IsNormalizedRealizing G (ρ ε) ∧ IsDomain (G '' ball 0 1) ∧
      Bornology.IsBounded (G '' ball 0 1) ∧ SimplyConnectedSpace (G '' ball 0 1) ∧
      IsRealAnalyticJordanBoundary (G '' ball 0 1) ∧
      steklovSpectrum (G '' ball 0 1) = weightedSteklovSpectrum (ρ ε) with hGood
  let F : ℝ → ℂ → ℂ := fun ε => if h : ∃ G, Good ε G then h.choose else fun _ => 0
  have hF : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Good ε (F ε) := by
    filter_upwards [hgood, hconc.2.2.2.2 k₀ δ₀ hδ₀] with ε h1 h2
    have hex : ∃ G, Good ε G := hreal (ρ ε) h1 h2
    simp only [F, dif_pos hex]
    exact hex.choose_spec
  refine ⟨F, ?_, ?_⟩
  · filter_upwards [hF, hcov] with ε hε hc
    refine ⟨hε.1, hε.2.1, hε.2.2.1, hε.2.2.2.1, hε.2.2.2.2.1, hε.2.2.2.2.2, ?_⟩
    obtain ⟨⟨U, hUo, hUc, hFd⟩, hinj, -, -, -, hnorm⟩ := hε.1
    exact BoundaryLength.boundaryLength_rescaled_blaschke (by omega) hc.2.2.2.2.2.2.1 hUo hUc hFd
      hinj hnorm
  · intro k η hη
    exact OuterConvergence.prop_2_3_1_convergence n hn0 ρ F hgood
      (fun k δ hδ => hconc.2.2.2.2 k δ hδ) (hF.mono fun ε h => h.1) k η hη

end SteklovCoalescence
