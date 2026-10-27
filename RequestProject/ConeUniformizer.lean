module

public import RequestProject.PullbackLocal

/-!
# Equivariant change of cone uniformizer

`exists_equivariant_uniformizer`: if `K` is holomorphic at `z₀` with `K'(z₀) ≠ 0` and `m > 0`, then
near `t = 0`

  `K(z₀ + t^m) = K(z₀) + h(t)^m`

for a holomorphic `h` with `h(0) = 0`, `h'(0) ≠ 0`, which is **exactly equivariant** under all the
rotations `t ↦ ζ t`, `ζ^m = 1`:  `h(ζ t) = ζ h(t)`.  (Concretely `h(t) = t · R(t^m)` with `R` a
holomorphic `m`-th root of the difference quotient `(K(z₀ + s) - K(z₀))/s`; this is the same
root construction as `SteklovOrb.exists_local_root`, applied in the variable `s = t^m` so that the
rotation compatibility holds identically.)

`metric_eq_at_filled_point`: if `λ_X` is a conformal factor whose cone-chart factor at `p` (order
`m`) extends to a smooth `μ`, `F = p + h^m` near `0` with `h` holomorphic, `h(0)=0`, `h'(0) ≠ 0`,
and a continuous `g` satisfies `g t = λ_X(F t)|F'(t)|²` for small `t ≠ 0`, then
`g t = μ(h t)|h'(t)|²` for all small `t`, **including `t = 0`** (continuity and density).
-/

@[expose] public section

open Set Filter Topology Metric SteklovOrb
open scoped ContDiff

noncomputable section

namespace ConeUnif

/-- **Equivariant change of uniformizer.** -/
theorem exists_equivariant_uniformizer {K : ℂ → ℂ} {z₀ : ℂ} {m : ℕ} (hm : 0 < m)
    (hK : AnalyticAt ℂ K z₀) (hK' : deriv K z₀ ≠ 0) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = 0 ∧ deriv h 0 ≠ 0 ∧
      (∀ ζ t : ℂ, ζ ^ m = 1 → h (ζ * t) = ζ * h t) ∧
      ∀ᶠ t in 𝓝 (0 : ℂ), K (z₀ + t ^ m) = K z₀ + h t ^ m := by
  set k : ℂ → ℂ := fun s => dslope K z₀ (z₀ + s)
  have hk : AnalyticAt ℂ k 0 := by
    obtain ⟨p, hp⟩ := hK
    have h1 : AnalyticAt ℂ (dslope K z₀) z₀ := ⟨_, hp.has_fpower_series_dslope_fslope⟩
    have h2 : AnalyticAt ℂ (fun s : ℂ => z₀ + s) 0 := analyticAt_const.add analyticAt_id
    exact AnalyticAt.comp_of_eq h1 h2 (by simp)
  have hk0 : k 0 = deriv K z₀ := by simp [k, dslope_same]
  have hkK : ∀ s, K (z₀ + s) = K z₀ + s * k s := by
    intro s
    have := sub_smul_dslope K z₀ (z₀ + s)
    simp only [add_sub_cancel_left, smul_eq_mul] at this
    simp only [k, this]; ring
  have hk0' : k 0 ≠ 0 := by rw [hk0]; exact hK'
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (k 0) hm
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_pow hm.ne'] at hc; exact hk0' hc.symm
  set q : ℂ → ℂ := fun s => k s / k 0
  have hq : AnalyticAt ℂ q 0 := hk.div analyticAt_const hk0'
  have hq1 : q 0 = 1 := div_self hk0'
  have hqs : q 0 ∈ Complex.slitPlane := by rw [hq1]; exact Complex.one_mem_slitPlane
  set R : ℂ → ℂ := fun s => c * Complex.exp (Complex.log (q s) / m)
  have hR : AnalyticAt ℂ R 0 := by
    have h1 : AnalyticAt ℂ (fun s => Complex.log (q s) / m) 0 :=
      (hq.clog hqs).div analyticAt_const (by exact_mod_cast hm.ne')
    exact analyticAt_const.mul (h1.cexp)
  have hR0 : R 0 = c := by simp [R, hq1]
  set h : ℂ → ℂ := fun t => t * R (t ^ m)
  have hRm : AnalyticAt ℂ (fun t : ℂ => R (t ^ m)) 0 :=
    AnalyticAt.comp_of_eq (g := R) (f := fun t : ℂ => t ^ m) hR (analyticAt_id.pow m) (by simp [zero_pow hm.ne'])
  have hh : AnalyticAt ℂ h 0 := analyticAt_id.mul hRm
  have hderiv : HasDerivAt h (R ((0 : ℂ) ^ m)) 0 := by
    have := (hasDerivAt_id (0 : ℂ)).mul hRm.differentiableAt.hasDerivAt
    first
      | simpa using this
      | simpa [Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.neg_def, Function.comp_def] using this
      | exact (this.congr_deriv (by first | rfl | simp | (simp; ring))).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => by first | rfl | simp | (simp; ring))
  refine ⟨h, hh, by simp [h], ?_, ?_, ?_⟩
  · rw [hderiv.deriv, zero_pow hm.ne', hR0]; exact hc0
  · intro ζ t hζ
    simp only [h, mul_pow, hζ, one_mul]; ring
  · have hkne : ∀ᶠ s in 𝓝 (0 : ℂ), k s ≠ 0 := hk.continuousAt.eventually_ne hk0'
    have hcont : Tendsto (fun t : ℂ => t ^ m) (𝓝 0) (𝓝 0) := by
      have := ((continuous_pow m).tendsto (0 : ℂ)); simpa [zero_pow hm.ne'] using this
    filter_upwards [hcont.eventually hkne] with t ht
    rw [hkK]
    congr 1
    have hrm : R (t ^ m) ^ m = k (t ^ m) := by
      simp only [R, mul_pow, ← Complex.exp_nat_mul]
      rw [mul_div_cancel₀ _ (by exact_mod_cast hm.ne' : (m : ℂ) ≠ 0),
        Complex.exp_log (div_ne_zero ht hk0'), hc]
      field_simp
    simp only [h, mul_pow, hrm]

/-- **The metric identity at the filled point.**  Let `h` be holomorphic at `0` with `h 0 = 0`,
`h'(0) ≠ 0`, `F = p + h^m` near `0`, `μ` continuous on `ball 0 r` and equal to the cone-chart
factor `chartFactor λ p m` off `0`, and `g` continuous at `0` with `g t = λ(F t)|F'(t)|²` for all
small `t ≠ 0`.  Then `g t = μ(h t)|h'(t)|²` for all small `t`, **including `t = 0`**. -/
theorem metric_eq_at_filled_point {lam : ℂ → ℝ} {p : ℂ} {m : ℕ} {F h : ℂ → ℂ} {g μ : ℂ → ℝ}
    {r : ℝ} (hh : AnalyticAt ℂ h 0) (hh0 : h 0 = 0) (hh' : deriv h 0 ≠ 0)
    (hF : ∀ᶠ t in 𝓝 (0 : ℂ), F t = p + h t ^ m) (hr : 0 < r)
    (hμc : ContinuousOn μ (ball 0 r))
    (hμ : ∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → μ w = chartFactor lam p m w)
    (hg : ContinuousAt g 0)
    (hgF : ∀ᶠ t in 𝓝[≠] (0 : ℂ), g t = lam (F t) * ‖deriv F t‖ ^ 2) :
    ∀ᶠ t in 𝓝 (0 : ℂ), h t ∈ ball (0 : ℂ) r ∧ g t = μ (h t) * ‖deriv h t‖ ^ 2 := by
  set φ : ℂ → ℝ := fun t => μ (h t) * ‖deriv h t‖ ^ 2
  have hball : ∀ᶠ t in 𝓝 (0 : ℂ), h t ∈ ball (0 : ℂ) r :=
    hh.continuousAt.preimage_mem_nhds (by rw [hh0]; exact ball_mem_nhds 0 hr)
  have hne : ∀ᶠ t in 𝓝[≠] (0 : ℂ), h t ≠ 0 := by
    have := hh.differentiableAt.hasDerivAt.eventually_ne (c := 0) hh'
    exact this
  have hφc : ContinuousAt φ 0 := by
    have h1 : ContinuousAt (fun t => μ (h t)) 0 := by
      have : ContinuousAt μ (h 0) := hμc.continuousAt (by rw [hh0]; exact ball_mem_nhds 0 hr)
      exact this.comp hh.continuousAt
    have h2 : ContinuousAt (deriv h) 0 := hh.deriv.continuousAt
    exact h1.mul ((continuous_norm.continuousAt.comp h2).pow 2)
  have hpunct : ∀ᶠ t in 𝓝[≠] (0 : ℂ), g t = φ t := by
    filter_upwards [hgF, hne, nhdsWithin_le_nhds hball, nhdsWithin_le_nhds hF.eventually_nhds,
      nhdsWithin_le_nhds (hh.eventually_analyticAt)] with t hgt hht hbt hFt hat
    rw [hgt, SteklovOrb.pullback_factor_eq hFt hat.differentiableAt, ← hμ _ hbt hht]
  have h0 : g 0 = φ 0 := by
    have t1 : Tendsto g (𝓝[≠] (0 : ℂ)) (𝓝 (g 0)) := hg.tendsto.mono_left nhdsWithin_le_nhds
    have t2 : Tendsto φ (𝓝[≠] (0 : ℂ)) (𝓝 (φ 0)) := hφc.tendsto.mono_left nhdsWithin_le_nhds
    exact tendsto_nhds_unique (t1.congr' hpunct) t2
  have hall : ∀ᶠ t in 𝓝 (0 : ℂ), g t = φ t := by
    have := eventually_nhdsWithin_iff.1 hpunct
    filter_upwards [this] with t ht
    by_cases ht0 : t = 0
    · rw [ht0]; exact h0
    · exact ht ht0
  filter_upwards [hball, hall] with t h1 h2 using ⟨h1, h2⟩

end ConeUnif
