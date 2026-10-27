module

public import RequestProject.Orbisurface

/-!
# Local analysis of pulled-back cone metrics

Two local facts used to pull an orbifold metric back through a branched holomorphic map.

* `exists_local_root` (**local normal form**): if `F(w) = p + (w - w₀)^m g(w)` near `w₀` with `g`
  analytic and `g(w₀) ≠ 0`, then `F = p + h^m` near `w₀` for an analytic `h` with `h(w₀) = 0`,
  `h'(w₀) ≠ 0` (an analytic `m`-th root of `g` times `w - w₀`).
* `pullback_factor_eq`: if `F = p + h^m` near `w`, then
  `λ(F w) |F'(w)|² = chartFactor λ p m (h w) · |h'(w)|²` — the pull-back of `λ|dz|²` by `F` is
  the pull-back by `h` of the metric of the cone chart of order `m` at `p`.
* `exists_smooth_pullback`: consequently, if the cone-chart factor `chartFactor λ p m` extends to a
  smooth positive `μ` near `0` (the cone condition of a `DiskOrbisurface`), then
  `w ↦ λ(F w)|F'(w)|²` extends smoothly and positively across `w₀`: it equals the smooth positive
  `Λ = (μ ∘ h)|h'|²` on a punctured neighbourhood of `w₀`.
-/

@[expose] public section

open Set Filter Topology Metric
open scoped ContDiff

noncomputable section

namespace SteklovOrb

/-- **Local normal form** of a holomorphic map with a zero of exact order `m`. -/
theorem exists_local_root {F g : ℂ → ℂ} {p w₀ : ℂ} {m : ℕ} (hm : 0 < m) (hg : AnalyticAt ℂ g w₀)
    (hg0 : g w₀ ≠ 0) (hF : ∀ᶠ w in 𝓝 w₀, F w = p + (w - w₀) ^ m * g w) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h w₀ ∧ h w₀ = 0 ∧ deriv h w₀ ≠ 0 ∧
      ∀ᶠ w in 𝓝 w₀, F w = p + h w ^ m := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (g w₀) hm
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_pow hm.ne'] at hc; exact hg0 hc.symm
  set q : ℂ → ℂ := fun w => g w / g w₀
  have hq : AnalyticAt ℂ q w₀ := hg.div analyticAt_const hg0
  have hq1 : q w₀ = 1 := div_self hg0
  have hqs : q w₀ ∈ Complex.slitPlane := by rw [hq1]; exact Complex.one_mem_slitPlane
  set r : ℂ → ℂ := fun w => c * Complex.exp (Complex.log (q w) / m)
  have hr : AnalyticAt ℂ r w₀ := by
    have h1 : AnalyticAt ℂ (fun w => Complex.log (q w) / m) w₀ :=
      (hq.clog hqs).div analyticAt_const (by exact_mod_cast hm.ne')
    exact analyticAt_const.mul (h1.cexp)
  have hr0 : r w₀ = c := by simp [r, hq1]
  set h : ℂ → ℂ := fun w => (w - w₀) * r w
  have hh : AnalyticAt ℂ h w₀ := (analyticAt_id.sub analyticAt_const).mul hr
  have hderiv : HasDerivAt h (r w₀) w₀ := by
    have h1 : HasDerivAt (fun w : ℂ => w - w₀) 1 w₀ := (hasDerivAt_id w₀).sub_const w₀
    have := h1.mul hr.differentiableAt.hasDerivAt
    first
      | simpa using this
      | simpa [Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.neg_def, Function.comp_def] using this
      | exact (this.congr_deriv (by first | rfl | simp | (simp; ring))).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => by first | rfl | simp | (simp; ring))
  refine ⟨h, hh, by simp [h], by rw [hderiv.deriv, hr0]; exact hc0, ?_⟩
  have hgne : ∀ᶠ w in 𝓝 w₀, g w ≠ 0 := hg.continuousAt.eventually_ne hg0
  filter_upwards [hF, hgne] with w hw hgw
  rw [hw]
  congr 1
  have hrm : r w ^ m = g w := by
    simp only [r, mul_pow, ← Complex.exp_nat_mul]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hm.ne' : (m : ℂ) ≠ 0),
      Complex.exp_log (div_ne_zero hgw hg0), hc]
    field_simp
  simp only [h, mul_pow, hrm]

/-- The pulled-back conformal factor through `F = p + h^m`. -/
theorem pullback_factor_eq {lam : ℂ → ℝ} {p : ℂ} {m : ℕ} {F h : ℂ → ℂ} {w : ℂ}
    (hF : F =ᶠ[𝓝 w] fun x => p + h x ^ m) (hh : DifferentiableAt ℂ h w) :
    lam (F w) * ‖deriv F w‖ ^ 2 = chartFactor lam p m (h w) * ‖deriv h w‖ ^ 2 := by
  have hFw : F w = p + h w ^ m := hF.eq_of_nhds
  have hd : deriv F w = (m : ℂ) * h w ^ (m - 1) * deriv h w := by
    rw [hF.deriv_eq]
    exact ((hh.hasDerivAt.pow m).const_add p).deriv
  rw [hFw, hd, chartFactor, coneChart, norm_mul, norm_mul]
  ring

/-- **Smooth positive extension of a pulled-back cone metric.**  Let `μ` be smooth and positive on
`ball 0 r₀`, equal to `chartFactor λ p m` off `0` (the cone condition), and let `F = p + h^m` near
`w₀` with `h` analytic, `h(w₀) = 0`, `h'(w₀) ≠ 0`.  Then there are `δ > 0` and a function `Λ`,
smooth and positive on `ball w₀ δ`, with `λ(F w)|F'(w)|² = Λ w` for `w ∈ ball w₀ δ`, `w ≠ w₀`. -/
theorem exists_smooth_pullback {lam μ : ℂ → ℝ} {p : ℂ} {m : ℕ} {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hμ : ContDiffOn ℝ ∞ μ (ball 0 r₀)) (hμpos : ∀ x ∈ ball (0 : ℂ) r₀, 0 < μ x)
    (hμeq : ∀ x ∈ ball (0 : ℂ) r₀, x ≠ 0 → μ x = chartFactor lam p m x)
    {F h : ℂ → ℂ} {w₀ : ℂ} (hh : AnalyticAt ℂ h w₀) (hh0 : h w₀ = 0) (hh' : deriv h w₀ ≠ 0)
    (hF : ∀ᶠ w in 𝓝 w₀, F w = p + h w ^ m) :
    ∃ δ > 0, ∃ Λ : ℂ → ℝ, ContDiffOn ℝ ∞ Λ (ball w₀ δ) ∧ (∀ w ∈ ball w₀ δ, 0 < Λ w) ∧
      ∀ w ∈ ball w₀ δ, w ≠ w₀ → lam (F w) * ‖deriv F w‖ ^ 2 = Λ w := by
  set Λ : ℂ → ℝ := fun w => μ (h w) * ‖deriv h w‖ ^ 2
  have E1 : ∀ᶠ w in 𝓝 w₀, AnalyticAt ℂ h w := hh.eventually_analyticAt
  have E2 : ∀ᶠ w in 𝓝 w₀, ∀ᶠ x in 𝓝 w, F x = p + h x ^ m := hF.eventually_nhds
  have E3 : ∀ᶠ w in 𝓝 w₀, h w ∈ ball (0 : ℂ) r₀ :=
    hh.continuousAt.preimage_mem_nhds (by rw [hh0]; exact ball_mem_nhds 0 hr₀)
  have E4 : ∀ᶠ w in 𝓝 w₀, deriv h w ≠ 0 := hh.deriv.continuousAt.eventually_ne hh'
  have E5 : ∀ᶠ w in 𝓝 w₀, w ≠ w₀ → h w ≠ 0 := by
    rcases hh.eventually_eq_zero_or_eventually_ne_zero with hz | hz
    · exfalso
      have : deriv h w₀ = deriv (fun _ : ℂ => (0 : ℂ)) w₀ :=
        Filter.EventuallyEq.deriv_eq (show h =ᶠ[𝓝 w₀] fun _ : ℂ => (0 : ℂ) from hz)
      rw [deriv_const] at this
      exact hh' this
    · exact eventually_nhdsWithin_iff.1 hz
  obtain ⟨δ, hδ, H⟩ := Metric.eventually_nhds_iff_ball.1 (E1.and (E2.and (E3.and (E4.and E5))))
  refine ⟨δ, hδ, Λ, fun w hw => ?_, fun w hw => ?_, fun w hw hne => ?_⟩
  · obtain ⟨e1, -, e3, -, -⟩ := H w hw
    have hμh : ContDiffAt ℝ ∞ (fun x => μ (h x)) w :=
      (hμ.contDiffAt (isOpen_ball.mem_nhds e3)).comp w (e1.contDiffAt.restrict_scalars ℝ)
    have hd : ContDiffAt ℝ ∞ (fun x => ‖deriv h x‖ ^ 2) w :=
      (contDiff_norm_sq ℝ).contDiffAt.comp w (e1.deriv.contDiffAt.restrict_scalars ℝ)
    exact (hμh.mul hd).contDiffWithinAt
  · obtain ⟨-, -, e3, e4, -⟩ := H w hw
    exact mul_pos (hμpos _ e3) (pow_pos (norm_pos_iff.2 e4) 2)
  · obtain ⟨e1, e2, e3, -, e5⟩ := H w hw
    rw [pullback_factor_eq e2 e1.differentiableAt, ← hμeq _ e3 (e5 hne)]

end SteklovOrb
