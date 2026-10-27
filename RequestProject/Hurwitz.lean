module

public import Mathlib

/-!
# Hurwitz's theorem for injective maps

If injective holomorphic maps `f_i` on a connected open set `U` converge locally uniformly
(along any nontrivial filter) to `g`, and `g' (z₀) ≠ 0` at one point of `U`, then `g` is
injective on `U`.

Proof: if `g a = g b` with `a ≠ b`, the zeros of `g - g b` are isolated at `a` (otherwise `g` is
constant on `U` by the identity theorem), so `|g - g b| ≥ m > 0` on a small circle around `a`.
For `i` far along the filter, `k = f_i - f_i(b)` has no zeros on the closed disk (injectivity),
`|k| ≥ 3m/5` on the circle and `|k(a)| < 2m/5`, contradicting the maximum modulus principle for
`1/k`.
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace SteklovRiemann

/-- **Hurwitz's theorem** (injective limits). -/
theorem hurwitz_injOn {ι : Type*} {l : Filter ι} [l.NeBot] {U : Set ℂ} (hU : IsOpen U)
    (hUc : IsPreconnected U) {f : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (hf : ∀ᶠ i in l, DifferentiableOn ℂ (f i) U) (hinj : ∀ᶠ i in l, InjOn (f i) U)
    (hlim : TendstoLocallyUniformlyOn f g l U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (hg' : deriv g z₀ ≠ 0) : InjOn g U := by
  have hgd : DifferentiableOn ℂ g U := hlim.differentiableOn hf hU
  intro a ha b hb hab
  by_contra hne
  set h : ℂ → ℂ := fun z => g z - g b with hh
  have hhA : AnalyticOnNhd ℂ h U := (hgd.sub_const (g b)).analyticOnNhd hU
  by_cases hfreq : ∃ᶠ z in 𝓝[≠] a, h z = 0
  · -- `g` is constant on `U`
    have hzero := hhA.eqOn_zero_of_preconnected_of_frequently_eq_zero hUc ha hfreq
    have hconst : g =ᶠ[𝓝 z₀] fun _ => g b := by
      filter_upwards [hU.mem_nhds hz₀] with z hz
      have := hzero hz
      simp only [hh, Pi.zero_apply] at this
      exact sub_eq_zero.1 this
    rw [hconst.deriv_eq, deriv_const] at hg'
    exact hg' rfl
  rw [not_frequently] at hfreq
  obtain ⟨r, hr, hrh⟩ := Metric.eventually_nhds_iff.1 (eventually_nhdsWithin_iff.1 hfreq)
  obtain ⟨r', hr', hr'U⟩ := Metric.isOpen_iff.1 hU a ha
  have hab' : 0 < dist a b := dist_pos.2 hne
  set ρ := min (min r r') (dist a b) / 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρr : ρ < r := by
    have := min_le_left (min r r') (dist a b); have := min_le_left r r'; rw [hρ]; linarith
  have hρr' : ρ < r' := by
    have := min_le_left (min r r') (dist a b); have := min_le_right r r'; rw [hρ]; linarith
  have hρb : ρ < dist a b := by
    have := min_le_right (min r r') (dist a b); rw [hρ]; linarith
  have hcbU : closedBall a ρ ⊆ U := (closedBall_subset_ball hρr').trans hr'U
  have hbout : b ∉ closedBall a ρ := by
    rw [mem_closedBall, dist_comm]; linarith
  have hsph : ∀ z ∈ sphere a ρ, h z ≠ 0 := by
    intro z hz
    refine hrh ?_ ?_
    · rw [mem_sphere] at hz; rw [hz]; exact hρr
    · intro hza; rw [mem_sphere, hza, dist_self] at hz; linarith
  obtain ⟨zm, hzm, hmin⟩ := (isCompact_sphere a ρ).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 hρ0.le) (f := fun z => ‖h z‖)
    ((hgd.continuousOn.mono (sphere_subset_closedBall.trans hcbU)).sub
      continuousOn_const).norm
  set m := ‖h zm‖ with hm
  have hm0 : 0 < m := norm_pos_iff.2 (hsph zm hzm)
  have hunif : TendstoUniformlyOn f g l (closedBall a ρ) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hlim _ hcbU (isCompact_closedBall a ρ)
  have hptb := hlim.tendsto_at hb
  obtain ⟨i, hi1, hi2, hi3, hi4⟩ :=
    ((Metric.tendstoUniformlyOn_iff.1 hunif (m / 5) (by positivity)).and
      ((Metric.tendsto_nhds.1 hptb (m / 5) (by positivity)).and (hf.and hinj))).exists
  set k : ℂ → ℂ := fun z => f i z - f i b with hk
  have hk0 : ∀ z ∈ closedBall a ρ, k z ≠ 0 := by
    intro z hz hkz
    have : f i z = f i b := sub_eq_zero.1 hkz
    have := hi4 (hcbU hz) hb this
    exact hbout (this ▸ hz)
  have hkd : DifferentiableOn ℂ (fun z => (k z)⁻¹) (closedBall a ρ) :=
    ((hi3.mono hcbU).sub_const _).inv hk0
  have hkcl : DiffContOnCl ℂ (fun z => (k z)⁻¹) (ball a ρ) := by
    refine ⟨hkd.mono ball_subset_closedBall, ?_⟩
    rw [closure_ball a hρ0.ne']
    exact hkd.continuousOn
  have hbd : ∀ z ∈ frontier (ball a ρ), ‖(k z)⁻¹‖ ≤ (3 * m / 5)⁻¹ := by
    intro z hz
    rw [frontier_ball a hρ0.ne'] at hz
    have hzc : z ∈ closedBall a ρ := sphere_subset_closedBall hz
    have h1 : m ≤ ‖h z‖ := hmin hz
    have h2 := hi1 z hzc
    rw [dist_eq_norm] at h2 hi2
    have h3 : 3 * m / 5 ≤ ‖k z‖ := by
      have : k z = h z - (g z - f i z) + (g b - f i b) := by simp only [hk, hh]; ring
      rw [this]
      have := norm_sub_norm_le (h z - (g z - f i z)) (-(g b - f i b))
      rw [sub_neg_eq_add, norm_neg] at this
      have := norm_sub_norm_le (h z) (g z - f i z)
      have : ‖g b - f i b‖ < m / 5 := by rw [norm_sub_rev]; exact hi2
      linarith
    rw [norm_inv]
    exact inv_anti₀ (by positivity) h3
  have hka := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hkcl hbd
    (subset_closure (mem_ball_self hρ0))
  have hka' : ‖k a‖ < 2 * m / 5 := by
    have h2 := hi1 a (mem_closedBall_self hρ0.le)
    rw [dist_eq_norm] at h2 hi2
    have : k a = (f i a - g a) + (g b - f i b) := by simp [hk, hab]
    rw [this]
    calc ‖(f i a - g a) + (g b - f i b)‖ ≤ ‖f i a - g a‖ + ‖g b - f i b‖ := norm_add_le _ _
      _ < m / 5 + m / 5 := by
          rw [norm_sub_rev (f i a), norm_sub_rev (g b)]
          exact add_lt_add h2 hi2
      _ = 2 * m / 5 := by ring
  rw [norm_inv] at hka
  have hkapos : 0 < ‖k a‖ := norm_pos_iff.2 (hk0 a (mem_closedBall_self hρ0.le))
  have : 3 * m / 5 ≤ ‖k a‖ := by
    have := (inv_le_inv₀ hkapos (by positivity)).1 hka
    exact this
  linarith

end SteklovRiemann
