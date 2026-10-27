module

public import RequestProject.PullbackOrbisurface

/-!
# Local pull-backs of base orbifold metrics and their transformation law

For a base orbifold metric `L : BaseOrbMetric u v mu mv` (cone orders `mu`, `mv` at `u`, `v`) and a
holomorphic map `F` on an open set `W` which is **ramified of order exactly `mu` (resp. `mv`) at
every point over `u` (resp. `v`)** and unramified elsewhere (`IsLocalBranched L F W`), the pulled
back conformal factor `pbLam L F` (the continuous extension of `λ₀(F z)|F'(z)|²`) is smooth and
positive on all of `W` (`IsLocalBranched.smooth`): the cone singularities of the base are exactly
resolved.  This is the situation of the completed covering surface, where every point over a
branch value has the full inertia order.

`pullback_law`: if `F₁ = F₂ ∘ T` near `z` with `T` holomorphic, and both pulled-back factors are
continuous at `z`, `T z` and given by the formula at nearby generic points, then
`pbLam L F₁ z = pbLam L F₂ (T z) · |T'(z)|²` — the conformal transformation law, valid also at
the branch points (by continuity).  It gives the chart-transition law, the isometry property of
deck transformations, and the descent of metrics to quotients.
-/

@[expose] public section

open Set Filter Topology Metric Steklov
open scoped ContDiff ENNReal

noncomputable section

namespace SteklovOrb

variable {u v : ℂ} {mu mv : ℕ}

/-- `F` is holomorphic on `W`, maps into the domain of `L`, is unramified off `F⁻¹{u, v}` and has
ramification exactly `mu` (resp. `mv`) at every point over `u` (resp. `v`). -/
structure IsLocalBranched (L : BaseOrbMetric u v mu mv) (F : ℂ → ℂ) (W : Set ℂ) : Prop where
  isOpen : IsOpen W
  analytic : AnalyticOnNhd ℂ F W
  mapsTo : MapsTo F W L.U
  crit : ∀ z ∈ W, F z ≠ u → F z ≠ v → deriv F z ≠ 0
  ram_u : ∀ z ∈ W, F z = u →
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ ∀ᶠ x in 𝓝 z, F x = u + (x - z) ^ mu * g x
  ram_v : ∀ z ∈ W, F z = v →
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ ∀ᶠ x in 𝓝 z, F x = v + (x - z) ^ mv * g x

variable {L : BaseOrbMetric u v mu mv} {F : ℂ → ℂ} {W : Set ℂ}

lemma eventually_ne_of_ram {F g : ℂ → ℂ} {p z : ℂ} {m : ℕ} (hm : 0 < m) (hg : AnalyticAt ℂ g z)
    (hg0 : g z ≠ 0) (hF : ∀ᶠ x in 𝓝 z, F x = p + (x - z) ^ m * g x) :
    ∀ᶠ x in 𝓝 z, x ≠ z → F x ≠ p := by
  filter_upwards [hF, hg.continuousAt.eventually_ne hg0] with x hx hgx hne
  rw [hx]
  intro h
  have : (x - z) ^ m * g x = 0 := by linear_combination h
  rcases mul_eq_zero.1 this with h1 | h1
  · exact hne (sub_eq_zero.1 ((pow_eq_zero_iff hm.ne').1 h1))
  · exact hgx h1

/-- Near any point of `W`, all other points are generic. -/
lemma IsLocalBranched.eventually_good (h : IsLocalBranched L F W) {z : ℂ} (hz : z ∈ W) :
    ∀ᶠ x in 𝓝 z, x ≠ z → x ∈ W ∧ F x ≠ u ∧ F x ≠ v := by
  have hc : ContinuousAt F z := (h.analytic z hz).continuousAt
  by_cases hu : F z = u
  · obtain ⟨g, hg, hg0, hF⟩ := h.ram_u z hz hu
    have hv : F z ≠ v := hu ▸ L.u_ne_v
    filter_upwards [h.isOpen.mem_nhds hz,
      eventually_ne_of_ram (by have := L.two_le_mu; omega) hg hg0 hF,
      hc.eventually_ne hv] with x h1 h2 h3 hne
    exact ⟨h1, h2 hne, h3⟩
  by_cases hv : F z = v
  · obtain ⟨g, hg, hg0, hF⟩ := h.ram_v z hz hv
    filter_upwards [h.isOpen.mem_nhds hz,
      eventually_ne_of_ram (by have := L.two_le_mv; omega) hg hg0 hF,
      hc.eventually_ne hu] with x h1 h2 h3 hne
    exact ⟨h1, h3, h2 hne⟩
  · filter_upwards [h.isOpen.mem_nhds hz, hc.eventually_ne hu, hc.eventually_ne hv] with
      x h1 h2 h3 _
    exact ⟨h1, h2, h3⟩

/-- At a generic point the formula is smooth and positive and equals `pbLam` nearby. -/
lemma IsLocalBranched.generic_point (h : IsLocalBranched L F W) {z : ℂ} (hz : z ∈ W)
    (hu : F z ≠ u) (hv : F z ≠ v) :
    pbLam L F =ᶠ[𝓝 z] pbFml L F ∧ ContDiffAt ℝ ∞ (pbFml L F) z ∧ 0 < pbFml L F z := by
  set W' : Set ℂ := W ∩ F ⁻¹' (L.U \ {u, v})
  have hWo : IsOpen W' := by
    refine ContinuousOn.isOpen_inter_preimage ?_ h.isOpen isOpen_base_good
    exact fun x hx => (h.analytic x hx).continuousAt.continuousWithinAt
  have hcd : ∀ x ∈ W', ContDiffAt ℝ ∞ (pbFml L F) x := by
    intro x hx
    have hFx := h.analytic x hx.1
    have h1 : ContDiffAt ℝ ∞ (fun y => L.lam (F y)) x :=
      (L.lam_smooth.contDiffAt (isOpen_base_good.mem_nhds hx.2)).comp x
        (hFx.contDiffAt.restrict_scalars ℝ)
    have h2 : ContDiffAt ℝ ∞ (fun y => ‖deriv F y‖ ^ 2) x :=
      (contDiff_norm_sq ℝ).contDiffAt.comp x (hFx.deriv.contDiffAt.restrict_scalars ℝ)
    exact h1.mul h2
  have hzW : z ∈ W' := ⟨hz, h.mapsTo hz, by simp [hu, hv]⟩
  refine ⟨?_, hcd z hzW, ?_⟩
  · filter_upwards [hWo.mem_nhds hzW] with x hx
    exact ((hcd x hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  · have hpos := L.lam_pos _ hzW.2
    exact mul_pos hpos (pow_pos (norm_pos_iff.2 (h.crit z hz hu hv)) 2)

lemma IsLocalBranched.pbLam_eq (h : IsLocalBranched L F W) {x : ℂ} (hx : x ∈ W) (hu : F x ≠ u)
    (hv : F x ≠ v) : pbLam L F x = pbFml L F x :=
  (h.generic_point hx hu hv).1.eq_of_nhds

/-- At a point over `p ∈ {u, v}` with the exact ramification, `pbLam` is smooth and positive. -/
lemma IsLocalBranched.critical_point (h : IsLocalBranched L F W) {p : ℂ} {m : ℕ} (hm : 0 < m)
    {r₀ : ℝ} (hr₀ : 0 < r₀) {μ : ℂ → ℝ} (hμ : ContDiffOn ℝ ∞ μ (ball 0 r₀))
    (hμpos : ∀ w ∈ ball (0 : ℂ) r₀, 0 < μ w)
    (hμeq : ∀ w ∈ ball (0 : ℂ) r₀, w ≠ 0 → μ w = chartFactor L.lam p m w)
    {z : ℂ} (hz : z ∈ W) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g z)
    (hg0 : g z ≠ 0) (hFg : ∀ᶠ x in 𝓝 z, F x = p + (x - z) ^ m * g x) :
    ContDiffAt ℝ ∞ (pbLam L F) z ∧ 0 < pbLam L F z := by
  obtain ⟨hh₁, hh, hh0, hh', hF⟩ := exists_local_root hm hg hg0 hFg
  obtain ⟨δ₁, hδ₁, Λ, hΛ, hΛpos, hΛeq⟩ := exists_smooth_pullback hr₀ hμ hμpos hμeq hh hh0 hh' hF
  obtain ⟨δ₂, hδ₂, hgood⟩ := Metric.eventually_nhds_iff_ball.1 (h.eventually_good hz)
  set δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hsub₁ : ball z δ ⊆ ball z δ₁ := ball_subset_ball (min_le_left _ _)
  have hsub₂ : ball z δ ⊆ ball z δ₂ := ball_subset_ball (min_le_right _ _)
  have hoff : ∀ x ∈ ball z δ, x ≠ z → pbLam L F x = Λ x := by
    intro x hx hne
    obtain ⟨hxW, hxu, hxv⟩ := hgood x (hsub₂ hx) hne
    rw [h.pbLam_eq hxW hxu hxv]
    exact hΛeq x (hsub₁ hx) hne
  have hcont : ContinuousAt Λ z :=
    (hΛ.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hδ₁)))
  have hz_eq : pbLam L F z = Λ z := by
    have hev : pbFml L F =ᶠ[𝓝[≠] z] Λ := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z hδ), self_mem_nhdsWithin]
        with y hy hyne
      obtain ⟨hyW, hyu, hyv⟩ := hgood y (hsub₂ hy) hyne
      rw [← h.pbLam_eq hyW hyu hyv]
      exact hoff y hy hyne
    exact ((hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm).limUnder_eq
  have hevΛ : pbLam L F =ᶠ[𝓝 z] Λ := by
    filter_upwards [ball_mem_nhds z hδ] with x hx
    by_cases hne : x = z
    · subst hne; exact hz_eq
    · exact hoff x hx hne
  exact ⟨((hΛ.contDiffAt (ball_mem_nhds z hδ₁))).congr_of_eventuallyEq hevΛ,
    by rw [hz_eq]; exact hΛpos z (mem_ball_self hδ₁)⟩

/-- **The pulled-back factor is smooth and positive on all of `W`.** -/
theorem IsLocalBranched.smooth (h : IsLocalBranched L F W) {z : ℂ} (hz : z ∈ W) :
    ContDiffAt ℝ ∞ (pbLam L F) z ∧ 0 < pbLam L F z := by
  by_cases hu : F z = u
  · obtain ⟨r, hr, μ, hμ, hμpos, hμeq⟩ := L.cone_u
    obtain ⟨g, hg, hg0, hFg⟩ := h.ram_u z hz hu
    exact h.critical_point (by have := L.two_le_mu; omega) hr hμ hμpos hμeq hz hg hg0 hFg
  by_cases hv : F z = v
  · obtain ⟨r, hr, μ, hμ, hμpos, hμeq⟩ := L.cone_v
    obtain ⟨g, hg, hg0, hFg⟩ := h.ram_v z hz hv
    exact h.critical_point (by have := L.two_le_mv; omega) hr hμ hμpos hμeq hz hg hg0 hFg
  obtain ⟨hev, hcd, hpos⟩ := h.generic_point hz hu hv
  exact ⟨hcd.congr_of_eventuallyEq hev, by rw [hev.eq_of_nhds]; exact hpos⟩

/-- The chain rule for the pulled-back formula. -/
lemma pbFml_comp {F₁ F₂ T : ℂ → ℂ} {x : ℂ} (hF : F₁ =ᶠ[𝓝 x] F₂ ∘ T) (hT : DifferentiableAt ℂ T x)
    (hF₂ : DifferentiableAt ℂ F₂ (T x)) :
    pbFml L F₁ x = pbFml L F₂ (T x) * ‖deriv T x‖ ^ 2 := by
  have hd : deriv F₁ x = deriv F₂ (T x) * deriv T x := by
    rw [hF.deriv_eq]
    exact (hF₂.hasDerivAt.comp x hT.hasDerivAt).deriv
  simp only [pbFml, hF.eq_of_nhds, Function.comp, hd, norm_mul]
  ring

/-- **The conformal transformation law of pulled-back metrics**, including at branch points. -/
theorem pullback_law {F₁ F₂ T : ℂ → ℂ} {z : ℂ} (hF : F₁ =ᶠ[𝓝 z] F₂ ∘ T) (hT : AnalyticAt ℂ T z)
    (hc₁ : ContinuousAt (pbLam L F₁) z) (hc₂ : ContinuousAt (pbLam L F₂) (T z))
    (hgood : ∀ᶠ x in 𝓝[≠] z, pbLam L F₁ x = pbFml L F₁ x ∧
      pbLam L F₂ (T x) = pbFml L F₂ (T x) ∧ DifferentiableAt ℂ F₂ (T x)) :
    pbLam L F₁ z = pbLam L F₂ (T z) * ‖deriv T z‖ ^ 2 := by
  have hTd : ∀ᶠ x in 𝓝 z, AnalyticAt ℂ T x := hT.eventually_analyticAt
  have hFF : ∀ᶠ x in 𝓝 z, F₁ =ᶠ[𝓝 x] F₂ ∘ T := hF.eventually_nhds
  have heq : ∀ᶠ x in 𝓝[≠] z, pbLam L F₁ x = pbLam L F₂ (T x) * ‖deriv T x‖ ^ 2 := by
    filter_upwards [hgood, nhdsWithin_le_nhds hTd, nhdsWithin_le_nhds hFF] with x ⟨h1, h2, h3⟩
      hTx hFx
    rw [h1, h2]
    exact pbFml_comp hFx hTx.differentiableAt h3
  have hcR : ContinuousAt (fun x => pbLam L F₂ (T x) * ‖deriv T x‖ ^ 2) z :=
    (hc₂.comp hT.continuousAt).mul
      ((continuous_pow 2).continuousAt.comp (continuous_norm.continuousAt.comp
        hT.deriv.continuousAt))
  exact tendsto_nhds_unique ((hc₁.tendsto.mono_left nhdsWithin_le_nhds))
    ((hcR.tendsto.mono_left nhdsWithin_le_nhds).congr' (EventuallyEq.symm heq))

/-- Variant of the law between two locally branched maps. -/
theorem IsLocalBranched.law {F₁ F₂ T : ℂ → ℂ} {W₁ W₂ : Set ℂ} (h₁ : IsLocalBranched L F₁ W₁)
    (h₂ : IsLocalBranched L F₂ W₂) {z : ℂ} (hz : z ∈ W₁) (hTz : T z ∈ W₂)
    (hF : F₁ =ᶠ[𝓝 z] F₂ ∘ T) (hT : AnalyticAt ℂ T z) :
    pbLam L F₁ z = pbLam L F₂ (T z) * ‖deriv T z‖ ^ 2 := by
  refine pullback_law hF hT (h₁.smooth hz).1.continuousAt (h₂.smooth hTz).1.continuousAt ?_
  have hTW : ∀ᶠ x in 𝓝 z, T x ∈ W₂ := hT.continuousAt.preimage_mem_nhds (h₂.isOpen.mem_nhds hTz)
  filter_upwards [nhdsWithin_le_nhds (h₁.eventually_good hz), self_mem_nhdsWithin,
    nhdsWithin_le_nhds hTW, nhdsWithin_le_nhds hF] with x hg hne hx hFx
  obtain ⟨hxW, hxu, hxv⟩ := hg hne
  have hFx' : F₂ (T x) = F₁ x := hFx.symm
  refine ⟨h₁.pbLam_eq hxW hxu hxv, h₂.pbLam_eq hx (by rwa [hFx']) (by rwa [hFx']),
    (h₂.analytic _ hx).differentiableAt⟩

end SteklovOrb
