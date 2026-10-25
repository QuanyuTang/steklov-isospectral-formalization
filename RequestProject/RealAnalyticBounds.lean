module

public import Mathlib

/-!
# Uniform Cauchy estimates for real-analytic functions

For `f : ℝ → ℂ` real-analytic on `ℝ` and a compact set `K`, there are `C, r > 0` with
`‖f^{(m)}(y)‖ ≤ C · m! / r^m` for all `y ∈ K` and all `m`
(`RealAnalyticBounds.exists_iteratedDeriv_bound`).  For a periodic function this holds on all of
`ℝ` (`RealAnalyticBounds.exists_iteratedDeriv_bound_periodic`).

Proof: near each point the power series of `f` defines a holomorphic function `g` on a complex
disk with `f = g` on the real diameter (`exists_complexification`); the real derivatives of `f`
are the complex derivatives of `g`, which satisfy Cauchy's estimate uniformly near the centre.
A compactness argument then gives uniform constants.
-/

@[expose] public section

open Set Metric Filter Topology Complex
open scoped Nat NNReal ENNReal

noncomputable section

namespace RealAnalyticBounds

/-- **Local complexification** of a real-analytic function `ℝ → ℂ`. -/
lemma exists_complexification {f : ℝ → ℂ} {x₀ : ℝ} (hf : AnalyticAt ℝ f x₀) :
    ∃ ρ > (0 : ℝ), ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball (x₀ : ℂ) ρ) ∧
      ∀ y : ℝ, |y - x₀| < ρ → f y = g y := by
  obtain ⟨p, R, hp⟩ := hf
  obtain ⟨ρ', hρ'0, hρ'R⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp.r_pos
  set a : ℕ → ℂ := fun n => p n (fun _ => 1) with ha
  set q : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a with hq_def
  have hpr : (ρ' : ℝ≥0∞) < p.radius := hρ'R.trans_le hp.r_le
  obtain ⟨C, -, hC⟩ := p.norm_mul_pow_le_of_lt_radius hpr
  have hqr : (ρ' : ℝ≥0∞) ≤ q.radius := by
    refine q.le_radius_of_bound C fun n => ?_
    rw [hq_def, FormalMultilinearSeries.ofScalars_norm]
    refine le_trans ?_ (hC n)
    gcongr
    calc ‖a n‖ ≤ ‖p n‖ * ∏ i : Fin n, ‖(fun _ => (1 : ℝ)) i‖ := (p n).le_opNorm _
      _ = ‖p n‖ := by simp
  have hρ'pos : (0 : ℝ) < ρ' := by exact_mod_cast hρ'0
  have hq := q.hasFPowerSeriesOnBall (lt_of_lt_of_le hρ'0 hqr)
  refine ⟨ρ', hρ'pos, fun z => q.sum (z - x₀), ?_, ?_⟩
  · intro z hz
    have hz' : z - x₀ ∈ Metric.eball (0 : ℂ) q.radius := by
      refine lt_of_lt_of_le ?_ hqr
      rw [edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _)
        ENNReal.coe_ne_top]
      simpa [dist_eq_norm] using hz
    have := hq.analyticAt_of_mem hz'
    have h2 : AnalyticAt ℂ (fun w : ℂ => w - (x₀ : ℂ)) z := by fun_prop
    exact AnalyticAt.comp (f := fun w : ℂ => w - (x₀ : ℂ)) this h2
  · intro y hy
    have hy' : ((y - x₀ : ℝ)) ∈ Metric.eball (0 : ℝ) R := by
      refine lt_of_lt_of_le ?_ hρ'R.le
      rw [edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _)
        ENNReal.coe_ne_top]
      simpa [Real.norm_eq_abs] using hy
    have h1 := hp.hasSum hy'
    rw [add_sub_cancel] at h1
    have hz' : ((y : ℂ) - x₀) ∈ Metric.eball (0 : ℂ) q.radius := by
      refine lt_of_lt_of_le ?_ hqr
      rw [edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _)
        ENNReal.coe_ne_top]
      rw [← Complex.ofReal_sub, Complex.norm_real]
      simpa [Real.norm_eq_abs] using hy
    have h2 := hq.hasSum hz'
    rw [zero_add] at h2
    refine h1.unique ?_
    convert h2 using 1
    funext n
    rw [hq_def, FormalMultilinearSeries.ofScalars_apply_eq]
    have : (fun _ : Fin n => (y - x₀ : ℝ)) = fun i => (y - x₀) • (fun _ : Fin n => (1 : ℝ)) i := by
      funext i; simp
    rw [this, ContinuousMultilinearMap.map_smul_univ]
    simp [ha, Complex.real_smul, smul_eq_mul, mul_comm]

/-- Real derivatives of `f` are complex derivatives of a complexification `g`. -/
lemma iteratedDeriv_eq_of_complexification {f : ℝ → ℂ} {g : ℂ → ℂ} {x₀ ρ : ℝ}
    (hg : AnalyticOnNhd ℂ g (ball (x₀ : ℂ) ρ)) (hfg : ∀ y : ℝ, |y - x₀| < ρ → f y = g y) (m : ℕ) :
    ∀ y : ℝ, |y - x₀| < ρ → iteratedDeriv m f y = iteratedDeriv m g y := by
  have hmem : ∀ y : ℝ, |y - x₀| < ρ → (y : ℂ) ∈ ball (x₀ : ℂ) ρ := by
    intro y hy
    rw [mem_ball, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hy
  have hopen : IsOpen {y : ℝ | |y - x₀| < ρ} :=
    isOpen_lt (continuous_abs.comp (continuous_id.sub continuous_const)) continuous_const
  induction m with
  | zero => simpa using hfg
  | succ m ih =>
    intro y hy
    have hev : iteratedDeriv m f =ᶠ[𝓝 y] fun s : ℝ => iteratedDeriv m g s :=
      Filter.eventually_of_mem (hopen.mem_nhds hy) fun s hs => ih s hs
    rw [iteratedDeriv_succ, hev.deriv_eq, iteratedDeriv_succ]
    have han : AnalyticOnNhd ℂ (iteratedDeriv m g) (ball (x₀ : ℂ) ρ) := by
      rw [iteratedDeriv_eq_iterate]; exact hg.iterated_deriv m
    have hd := ((han _ (hmem y hy)).differentiableAt).hasDerivAt
    exact hd.comp_ofReal.deriv

/-- **Local uniform Cauchy estimate.** -/
lemma local_bound {f : ℝ → ℂ} {x₀ : ℝ} (hf : AnalyticAt ℝ f x₀) :
    ∃ C > (0 : ℝ), ∃ r > (0 : ℝ), ∃ ε > (0 : ℝ), ∀ y : ℝ, |y - x₀| < ε → ∀ m : ℕ,
      ‖iteratedDeriv m f y‖ ≤ C * m ! / r ^ m := by
  obtain ⟨ρ, hρ, g, hg, hfg⟩ := exists_complexification hf
  have hK : IsCompact (closedBall (x₀ : ℂ) (3 * ρ / 4)) := isCompact_closedBall _ _
  have hsub : closedBall (x₀ : ℂ) (3 * ρ / 4) ⊆ ball (x₀ : ℂ) ρ :=
    closedBall_subset_ball (by linarith)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (hg.continuousOn.mono hsub)
  refine ⟨max M 1, by positivity, ρ / 2, by positivity, ρ / 4, by positivity, ?_⟩
  intro y hy m
  have hy' : |y - x₀| < ρ := by linarith
  rw [iteratedDeriv_eq_of_complexification hg hfg m y hy']
  have hball : closedBall (y : ℂ) (ρ / 2) ⊆ closedBall (x₀ : ℂ) (3 * ρ / 4) := by
    intro z hz
    rw [mem_closedBall] at hz ⊢
    have : dist (y : ℂ) x₀ = |y - x₀| := by
      rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    linarith [dist_triangle z (y : ℂ) x₀]
  have hdc : DiffContOnCl ℂ g (ball (y : ℂ) (ρ / 2)) := by
    refine DifferentiableOn.diffContOnCl ?_
    have hρ2' : ρ / 2 ≠ 0 := by positivity
    rw [closure_ball _ hρ2']
    exact fun z hz => (hg z (hsub (hball hz))).differentiableAt.differentiableWithinAt
  have hρ2 : 0 < ρ / 2 := by positivity
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (C := max M 1) m hρ2
    hdc (fun z hz =>
      (hM z (hball (sphere_subset_closedBall hz))).trans (le_max_left _ _))
  rw [mul_comm (max M 1)]
  exact this

/-- **Uniform Cauchy estimate on a compact set** for a real-analytic `f : ℝ → ℂ`. -/
theorem exists_iteratedDeriv_bound {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f univ) {K : Set ℝ}
    (hK : IsCompact K) :
    ∃ C > (0 : ℝ), ∃ r > (0 : ℝ), ∀ y ∈ K, ∀ m : ℕ, ‖iteratedDeriv m f y‖ ≤ C * m ! / r ^ m := by
  refine hK.induction_on (p := fun s => ∃ C > (0 : ℝ), ∃ r > (0 : ℝ), ∀ y ∈ s, ∀ m : ℕ,
    ‖iteratedDeriv m f y‖ ≤ C * m ! / r ^ m) ?_ ?_ ?_ ?_
  · exact ⟨1, one_pos, 1, one_pos, fun y hy => absurd hy (notMem_empty y)⟩
  · intro s t hst ⟨C, hC, r, hr, h⟩
    exact ⟨C, hC, r, hr, fun y hy => h y (hst hy)⟩
  · intro s t ⟨C₁, hC₁, r₁, hr₁, h₁⟩ ⟨C₂, hC₂, r₂, hr₂, h₂⟩
    refine ⟨max C₁ C₂, by positivity, min r₁ r₂, lt_min hr₁ hr₂, ?_⟩
    have key : ∀ C r m, 0 < C → 0 < r → C ≤ max C₁ C₂ → min r₁ r₂ ≤ r →
        C * (m ! : ℝ) / r ^ m ≤ max C₁ C₂ * m ! / (min r₁ r₂) ^ m := by
      intro C r m hC hr hCle hrle
      have h0 : 0 < min r₁ r₂ := lt_min hr₁ hr₂
      gcongr
    rintro y (hy | hy) m
    · exact (h₁ y hy m).trans (key _ _ _ hC₁ hr₁ (le_max_left _ _) (min_le_left _ _))
    · exact (h₂ y hy m).trans (key _ _ _ hC₂ hr₂ (le_max_right _ _) (min_le_right _ _))
  · intro x _
    obtain ⟨C, hC, r, hr, ε, hε, h⟩ := local_bound (hf x (mem_univ x))
    refine ⟨Ioo (x - ε) (x + ε), mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by linarith)
      (by linarith)), C, hC, r, hr, fun y hy m => h y ?_ m⟩
    rw [abs_lt]; constructor <;> linarith [hy.1, hy.2]

lemma periodic_deriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F} {T : ℝ} (hper : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  rw [← deriv_comp_add_const]
  congr 1
  funext y; exact hper y

lemma periodic_iteratedDeriv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : ℝ → F}
    {T : ℝ} (hper : Function.Periodic f T) (m : ℕ) :
    Function.Periodic (iteratedDeriv m f) T := by
  induction m with
  | zero => simpa using hper
  | succ m ih => rw [iteratedDeriv_succ]; exact periodic_deriv ih

/-- **Uniform Cauchy estimate on `ℝ`** for a real-analytic periodic `f : ℝ → ℂ`. -/
theorem exists_iteratedDeriv_bound_periodic {f : ℝ → ℂ} (hf : AnalyticOnNhd ℝ f univ) {T : ℝ}
    (hT : 0 < T) (hper : Function.Periodic f T) :
    ∃ C > (0 : ℝ), ∃ r > (0 : ℝ), ∀ y : ℝ, ∀ m : ℕ, ‖iteratedDeriv m f y‖ ≤ C * m ! / r ^ m := by
  obtain ⟨C, hC, r, hr, h⟩ := exists_iteratedDeriv_bound hf (isCompact_Icc (a := 0) (b := T))
  refine ⟨C, hC, r, hr, fun y m => ?_⟩
  obtain ⟨z, hz, hyz⟩ := (periodic_iteratedDeriv hper m).exists_mem_Ico₀ hT y
  rw [hyz]
  exact h z (Ico_subset_Icc_self hz) m

end RealAnalyticBounds

end
