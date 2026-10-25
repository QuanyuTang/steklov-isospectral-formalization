module

public import Mathlib
public import RequestProject.OuterConvergence

/-!
# Strict convexity from `C²`-closeness to a dilation (§3.5, conclusion (i))

`strictConvex_closure_image`: let `F` be holomorphic on a neighbourhood of `𝔻̄` with
`|F' - c| ≤ ε c` and `|F''| ≤ M c` on `𝔻̄` (`c > 0`), where `4M < 1 - ε`.  Then the closure of
`F(𝔻)` is strictly convex.

Proof.  For `z₁ ≠ z₂` in `𝔻̄`, `a, b > 0`, `a + b = 1`, put `m = a z₁ + b z₂` and
`s = ab|z₁ - z₂|² > 0`; then `|m| ≤ 1 - s/2`.  With `h = F - c·id`, second-order Taylor bounds give
`a F(z₁) + b F(z₂) = F(m) + d` with `|d| ≤ M c s`.  Since `F` approximates the linear map `c·id`
on `B̄(m, s/4) ⊆ 𝔻` with constant `ε c`, `F(B̄(m, s/4)) ⊇ B̄(F(m), c(1-ε)s/4)`, an open ball
around `a F(z₁) + b F(z₂)` inside `F(𝔻)`.

`eventually_strictConvex_of_cinfty`: a family of maps tending to `c·id` in `C²(𝔻̄)` eventually has
strictly convex image domains.
-/

@[expose] public section

open Complex Metric Set Filter Topology

noncomputable section

namespace SteklovConvexity

variable {F : ℂ → ℂ} {U : Set ℂ} {c ε M : ℝ}

/-- The identity `|a z₁ + b z₂|² = a|z₁|² + b|z₂|² - ab|z₁ - z₂|²` for `a + b = 1`. -/
lemma norm_sq_convex_comb (z₁ z₂ : ℂ) {a b : ℝ} (hab : a + b = 1) :
    ‖(a : ℂ) * z₁ + (b : ℂ) * z₂‖ ^ 2 =
      a * ‖z₁‖ ^ 2 + b * ‖z₂‖ ^ 2 - a * b * ‖z₁ - z₂‖ ^ 2 := by
  simp only [← normSq_eq_norm_sq, normSq_apply, add_re, add_im, mul_re, mul_im, ofReal_re,
    ofReal_im, sub_re, sub_im, zero_mul, sub_zero, add_zero]
  have hb : b = 1 - a := by linarith
  subst hb
  ring

section estimates

variable (hU : IsOpen U) (hcb : closedBall (0 : ℂ) 1 ⊆ U) (hd : DifferentiableOn ℂ F U)
include hU hcb hd

lemma differentiableAt_of_mem {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    DifferentiableAt ℂ F z := hd.differentiableAt (hU.mem_nhds (hcb hz))

lemma differentiableAt_deriv_of_mem {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    DifferentiableAt ℂ (deriv F) z :=
  ((hd.analyticOnNhd hU).deriv.differentiableOn).differentiableAt (hU.mem_nhds (hcb hz))

/-- First-order estimate: `F` approximates `c·id` on `𝔻̄`. -/
lemma lipschitz_sub_linear (h1 : ∀ z ∈ closedBall (0 : ℂ) 1, ‖deriv F z - c‖ ≤ ε * c)
    {x y : ℂ} (hx : x ∈ closedBall (0 : ℂ) 1) (hy : y ∈ closedBall (0 : ℂ) 1) :
    ‖F x - F y - c * (x - y)‖ ≤ ε * c * ‖x - y‖ := by
  have hdiff : ∀ w ∈ closedBall (0 : ℂ) 1, DifferentiableAt ℂ (fun w => F w - c * w) w :=
    fun w hw => (differentiableAt_of_mem hU hcb hd hw).sub (by fun_prop)
  have hder : ∀ w ∈ closedBall (0 : ℂ) 1, ‖deriv (fun w => F w - c * w) w‖ ≤ ε * c := by
    intro w hw
    have : HasDerivAt (fun w => F w - c * w) (deriv F w - c) w := by
      have := (differentiableAt_of_mem hU hcb hd hw).hasDerivAt.sub
        ((hasDerivAt_id w).const_mul (c : ℂ))
      first
        | exact this.congr_deriv (by simp)
        | simpa [Function.comp_def, Pi.sub_def] using this
    rw [this.deriv]
    exact h1 w hw
  have := (convex_closedBall (0 : ℂ) 1).norm_image_sub_le_of_norm_deriv_le hdiff hder hy hx
  calc ‖F x - F y - c * (x - y)‖ = ‖(F x - c * x) - (F y - c * y)‖ := by ring_nf
    _ ≤ ε * c * ‖x - y‖ := this

/-- Second-order Taylor estimate on `𝔻̄`. -/
lemma taylor_two (h2 : ∀ z ∈ closedBall (0 : ℂ) 1, ‖deriv (deriv F) z‖ ≤ M * c)
    {m z : ℂ} (hm : m ∈ closedBall (0 : ℂ) 1) (hz : z ∈ closedBall (0 : ℂ) 1) :
    ‖F z - F m - deriv F m * (z - m)‖ ≤ M * c * ‖z - m‖ ^ 2 := by
  have hseg : segment ℝ m z ⊆ closedBall (0 : ℂ) 1 :=
    (convex_closedBall (0 : ℂ) 1).segment_subset hm hz
  have hdiff : ∀ w ∈ segment ℝ m z,
      DifferentiableAt ℂ (fun w => F w - deriv F m * (w - m)) w :=
    fun w hw => (differentiableAt_of_mem hU hcb hd (hseg hw)).sub (by fun_prop)
  have hder : ∀ w ∈ segment ℝ m z,
      ‖deriv (fun w => F w - deriv F m * (w - m)) w‖ ≤ M * c * ‖z - m‖ := by
    intro w hw
    have hdw : deriv (fun w => F w - deriv F m * (w - m)) w = deriv F w - deriv F m := by
      have := (differentiableAt_of_mem hU hcb hd (hseg hw)).hasDerivAt.sub
        (((hasDerivAt_id w).sub_const m).const_mul (deriv F m))
      have h' : HasDerivAt (fun w => F w - deriv F m * (w - m)) (deriv F w - deriv F m) w := by
        first
          | exact this.congr_deriv (by simp)
          | simpa [Pi.sub_def] using this
      exact h'.deriv
    rw [hdw]
    have hdd : ∀ v ∈ segment ℝ m z, DifferentiableAt ℂ (deriv F) v :=
      fun v hv => differentiableAt_deriv_of_mem hU hcb hd (hseg hv)
    have hbd : ∀ v ∈ segment ℝ m z, ‖deriv (deriv F) v‖ ≤ M * c := fun v hv => h2 v (hseg hv)
    have := (convex_segment m z).norm_image_sub_le_of_norm_deriv_le hdd hbd
      (left_mem_segment ℝ m z) hw
    have hMc : 0 ≤ M * c := (norm_nonneg _).trans (h2 m hm)
    calc ‖deriv F w - deriv F m‖ ≤ M * c * ‖w - m‖ := this
      _ ≤ M * c * ‖z - m‖ := by gcongr; exact norm_sub_le_of_mem_segment hw
  have := (convex_segment m z).norm_image_sub_le_of_norm_deriv_le hdiff hder
    (left_mem_segment ℝ m z) (right_mem_segment ℝ m z)
  calc ‖F z - F m - deriv F m * (z - m)‖
      = ‖(F z - deriv F m * (z - m)) - (F m - deriv F m * (m - m))‖ := by ring_nf
    _ ≤ M * c * ‖z - m‖ * ‖z - m‖ := this
    _ = M * c * ‖z - m‖ ^ 2 := by ring

end estimates

/-- **Strict convexity from `C²`-closeness to the dilation `z ↦ c z`.** -/
theorem strictConvex_closure_image (hc : 0 < c) (hU : IsOpen U)
    (hcb : closedBall (0 : ℂ) 1 ⊆ U) (hd : DifferentiableOn ℂ F U)
    (h1 : ∀ z ∈ closedBall (0 : ℂ) 1, ‖deriv F z - c‖ ≤ ε * c)
    (h2 : ∀ z ∈ closedBall (0 : ℂ) 1, ‖deriv (deriv F) z‖ ≤ M * c) (hεM : 4 * M < 1 - ε) :
    StrictConvex ℝ (closure (F '' ball 0 1)) := by
  have h0 : (0 : ℂ) ∈ closedBall (0 : ℂ) 1 := mem_closedBall_self zero_le_one
  have hε0 : 0 ≤ ε := by
    have := (norm_nonneg _).trans (h1 0 h0)
    exact nonneg_of_mul_nonneg_left this hc
  have hM0 : 0 ≤ M := by
    have := (norm_nonneg _).trans (h2 0 h0)
    exact nonneg_of_mul_nonneg_left this hc
  -- the closure is contained in `F(𝔻̄)`
  have hcont : ContinuousOn F (closedBall 0 1) :=
    (hd.mono hcb).continuousOn
  have hclos : closure (F '' ball 0 1) ⊆ F '' closedBall 0 1 :=
    closure_minimal (image_mono ball_subset_closedBall)
      ((isCompact_closedBall 0 1).image_of_continuousOn hcont).isClosed
  intro x hx y hy hxy a b ha hb hab
  obtain ⟨z₁, hz₁, rfl⟩ := hclos hx
  obtain ⟨z₂, hz₂, rfl⟩ := hclos hy
  have hz12 : z₁ ≠ z₂ := fun h => hxy (by rw [h])
  set m : ℂ := (a : ℂ) * z₁ + (b : ℂ) * z₂ with hm_def
  set s : ℝ := a * b * ‖z₁ - z₂‖ ^ 2 with hs_def
  have hs : 0 < s := by
    have : 0 < ‖z₁ - z₂‖ := norm_pos_iff.2 (sub_ne_zero.2 hz12)
    positivity
  have hn1 : ‖z₁‖ ≤ 1 := mem_closedBall_zero_iff.1 hz₁
  have hn2 : ‖z₂‖ ≤ 1 := mem_closedBall_zero_iff.1 hz₂
  -- `|m| ≤ 1 - s/2`
  have hmsq : ‖m‖ ^ 2 ≤ 1 - s := by
    rw [hm_def, norm_sq_convex_comb z₁ z₂ hab]
    have h1' : ‖z₁‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z₁]
    have h2' : ‖z₂‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z₂]
    nlinarith
  have hs1 : s ≤ 1 := by nlinarith [sq_nonneg ‖m‖]
  have hm : ‖m‖ ≤ 1 - s / 2 := by
    nlinarith [norm_nonneg m, sq_nonneg (‖m‖ - (1 - s / 2))]
  have hmb : m ∈ closedBall (0 : ℂ) 1 := mem_closedBall_zero_iff.2 (by linarith)
  -- the defect `d`
  set d : ℂ := (a : ℂ) * F z₁ + (b : ℂ) * F z₂ - F m with hd_def
  have hdbound : ‖d‖ ≤ M * c * s := by
    have t1 := taylor_two hU hcb hd h2 hmb hz₁
    have t2 := taylor_two hU hcb hd h2 hmb hz₂
    have e1 : z₁ - m = (b : ℂ) * (z₁ - z₂) := by
      rw [hm_def]
      have h := congrArg (fun r : ℝ => (r : ℂ)) hab
      push_cast at h
      linear_combination (-z₁) * h
    have e2 : z₂ - m = -(a : ℂ) * (z₁ - z₂) := by
      rw [hm_def]
      have h := congrArg (fun r : ℝ => (r : ℂ)) hab
      push_cast at h
      linear_combination (-z₂) * h
    have hdeq : d = (a : ℂ) * (F z₁ - F m - deriv F m * (z₁ - m)) +
        (b : ℂ) * (F z₂ - F m - deriv F m * (z₂ - m)) := by
      rw [hd_def, e1, e2]
      have : (a : ℂ) + b = 1 := by exact_mod_cast hab
      linear_combination (F m) * this
    rw [hdeq]
    calc _ ≤ ‖(a : ℂ) * (F z₁ - F m - deriv F m * (z₁ - m))‖ +
          ‖(b : ℂ) * (F z₂ - F m - deriv F m * (z₂ - m))‖ := norm_add_le _ _
      _ ≤ a * (M * c * ‖z₁ - m‖ ^ 2) + b * (M * c * ‖z₂ - m‖ ^ 2) := by
          rw [norm_mul, norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
            abs_of_pos ha, abs_of_pos hb]
          gcongr
      _ = M * c * s := by
          rw [e1, e2, norm_mul, norm_mul, norm_neg, norm_real, norm_real, Real.norm_eq_abs,
            Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb, hs_def]
          have : a + b = 1 := hab
          linear_combination (M * c * a * b * ‖z₁ - z₂‖ ^ 2) * this
  -- local surjectivity of `F` near `m`
  set ρ : ℝ := s / 4
  have hρ : 0 ≤ ρ := by positivity
  have hball : closedBall m ρ ⊆ closedBall (0 : ℂ) 1 := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    have := mem_closedBall.1 hw
    calc ‖w‖ = ‖(w - m) + m‖ := by ring_nf
      _ ≤ ‖w - m‖ + ‖m‖ := norm_add_le _ _
      _ ≤ ρ + (1 - s / 2) := by rw [← dist_eq_norm]; linarith
      _ ≤ 1 := by simp only [ρ]; linarith
  have hball' : closedBall m ρ ⊆ ball (0 : ℂ) 1 := by
    intro w hw
    rw [mem_ball_zero_iff]
    have := mem_closedBall.1 hw
    calc ‖w‖ = ‖(w - m) + m‖ := by ring_nf
      _ ≤ ‖w - m‖ + ‖m‖ := norm_add_le _ _
      _ ≤ ρ + (1 - s / 2) := by rw [← dist_eq_norm]; linarith
      _ < 1 := by simp only [ρ]; linarith
  set L : ℂ →L[ℝ] ℂ := c • ContinuousLinearMap.id ℝ ℂ
  have hcε : 0 ≤ ε * c := by positivity
  have happrox : ApproximatesLinearOn F L (closedBall m ρ) ⟨ε * c, hcε⟩ := by
    intro x hx y hy
    have := lipschitz_sub_linear hU hcb hd h1 (hball hx) (hball hy)
    simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, NNReal.coe_mk]
    rw [real_smul]
    exact this
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let Linv : L.NonlinearRightInverse :=
    { toFun := fun y => y / c
      nnnorm := ⟨c⁻¹, inv_nonneg.2 hc.le⟩
      bound' := fun y => by
        simp only [NNReal.coe_mk, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hc]
        rw [div_eq_inv_mul]
        all_goals exact le_of_eq rfl
      right_inv' := fun y => by
        simp only [L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, real_smul]
        field_simp }
  have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse Linv hρ subset_rfl
  replace hsurj : SurjOn F (closedBall m ρ) (closedBall (F m) (c * (1 - ε) * ρ)) := by
    convert hsurj using 2
    first
      | (simp only [Linv, NNReal.coe_mk, inv_inv]; ring)
      | (show c * (1 - ε) * ρ = ((c⁻¹ : ℝ)⁻¹ - ε * c) * ρ; rw [inv_inv]; ring)
      | (simp only [Linv]; show c * (1 - ε) * ρ = ((c⁻¹ : ℝ)⁻¹ - ε * c) * ρ; rw [inv_inv]; ring)
  -- conclude
  have hopen : ball (F m) (c * (1 - ε) * ρ) ⊆ F '' ball 0 1 := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := hsurj (ball_subset_closedBall hw)
    exact ⟨v, hball' hv, rfl⟩
  have hmem : (a : ℂ) * F z₁ + (b : ℂ) * F z₂ ∈ ball (F m) (c * (1 - ε) * ρ) := by
    rw [mem_ball, dist_eq_norm]
    have : (a : ℂ) * F z₁ + (b : ℂ) * F z₂ - F m = d := rfl
    rw [this]
    calc ‖d‖ ≤ M * c * s := hdbound
      _ < c * (1 - ε) * ρ := by simp only [ρ]; nlinarith [mul_pos hc hs]
  have hint : ball (F m) (c * (1 - ε) * ρ) ⊆ interior (closure (F '' ball 0 1)) :=
    interior_maximal (hopen.trans subset_closure) isOpen_ball
  rw [Complex.real_smul, Complex.real_smul]
  exact hint hmem

/-- For a holomorphic map, the first two real derivatives of `F - c·id` are `F' - c` and `F''`. -/
lemma norm_iteratedFDeriv_one_two {F : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hd : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U) (c : ℂ) :
    ‖iteratedFDeriv ℝ 1 (fun w => F w - c * w) z‖ = ‖deriv F z - c‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun w => F w - c * w) z‖ = ‖deriv (deriv F) z‖ := by
  have hg : DifferentiableOn ℂ (fun w => F w - c * w) U := hd.sub (by fun_prop)
  have hderiv : ∀ w ∈ U, deriv (fun w => F w - c * w) w = deriv F w - c := by
    intro w hw
    have := (hd.differentiableAt (hU.mem_nhds hw)).hasDerivAt.sub
      ((hasDerivAt_id w).const_mul c)
    have h' : HasDerivAt (fun w => F w - c * w) (deriv F w - c) w := by
      first
        | exact this.congr_deriv (by simp)
        | simpa [Pi.sub_def] using this
    exact h'.deriv
  refine ⟨?_, ?_⟩
  · rw [OuterConvergence.norm_iteratedFDeriv_real_eq hU hg hz 1, iteratedDeriv_one, hderiv z hz]
  · rw [OuterConvergence.norm_iteratedFDeriv_real_eq hU hg hz 2, iteratedDeriv_succ,
      iteratedDeriv_one]
    have heq : deriv (fun w => F w - c * w) =ᶠ[𝓝 z] fun w => deriv F w - c :=
      Filter.eventually_of_mem (hU.mem_nhds hz) hderiv
    rw [heq.deriv_eq]
    have hdd : DifferentiableAt ℂ (deriv F) z :=
      ((hd.analyticOnNhd hU).deriv.differentiableOn).differentiableAt (hU.mem_nhds hz)
    rw [(hdd.hasDerivAt.sub_const c).deriv]

/-- **Maps converging to `c·id` in `C²(𝔻̄)` eventually have strictly convex image domains.** -/
theorem eventually_strictConvex_of_C2 {ι : Type*} {l : Filter ι} {F : ι → ℂ → ℂ} {c : ℝ}
    (hc : 0 < c)
    (hF : ∀ᶠ i in l, ∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ (F i) U)
    (hconv : ∀ k : ℕ, ∀ η > (0 : ℝ), ∀ᶠ i in l, ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ k (fun w => F i w - (c : ℂ) * w) z‖ < η) :
    ∀ᶠ i in l, PlaneDomain.IsStrictlyConvexDomain (F i '' ball 0 1) := by
  filter_upwards [hF, hconv 1 (c / 2) (by positivity), hconv 2 (c / 10) (by positivity)]
    with i hi h1 h2
  obtain ⟨U, hU, hcb, hd⟩ := hi
  refine strictConvex_closure_image (ε := 1 / 2) (M := 1 / 10) hc hU hcb hd
    (fun z hz => ?_) (fun z hz => ?_) (by norm_num)
  · have := (norm_iteratedFDeriv_one_two hU hd (hcb hz) c).1
    rw [← this]; linarith [h1 z hz]
  · have := (norm_iteratedFDeriv_one_two hU hd (hcb hz) c).2
    rw [← this]; linarith [h2 z hz]

end SteklovConvexity
