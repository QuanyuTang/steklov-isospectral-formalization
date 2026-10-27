module

public import RequestProject.PullbackLocal
public import RequestProject.OrbMetricSpectrum

/-!
# Pulling an orbifold metric on the disk back through a branched disk map

* `BaseOrbMetric u v mu mv`: a Riemannian orbifold metric `λ₀|dw|²` on (a neighbourhood of) the
  closed unit disk, smooth and positive off two cone points `u` (order `mu`) and `v` (order
  `mv`), with the cone-chart condition of `DiskOrbisurface` at `u`, `v`, and **Euclidean in a
  boundary collar** (`λ₀ = 1` on `{ρ < |w|}` for some `ρ < 1`).  This is the structural hypothesis
  on the paper's base metric; it is a general class, not a particular choice.
* `IsBranchedDiskMap B V u v mu mv U₀`: `B` is holomorphic on an open `V ⊇ closed disk`, maps
  `V` into the domain `U₀` of the base metric and the circle into the circle, its points over `u`,
  `v` are finitely many and lie in the open disk, it is unramified off `B⁻¹{u, v}`, and at each
  critical point over `u` (resp. `v`) it is ramified of order exactly `mu` (resp. `mv`).
* `pullbackOrb L hB : DiskOrbisurface`: the **pulled-back orbisurface**.  Its metric is
  `λ(z) = λ₀(B z)|B'(z)|²` off `B⁻¹{u, v}`, extended continuously (`pbLam`, a limit) across the
  critical points over `u, v` (which become smooth points: `λ₀(u + h^m)|m h^{m-1} h'|²` is smooth
  positive by the cone condition, `exists_smooth_pullback`); its cone points are exactly the
  unramified points over `u` (order `mu`) and over `v` (order `mv`) (`range_pt`, `ord_eq`), and
  the cone condition is derived from the local normal form `B(z₀ + w^m) = p + h(w)^m`.
* `lineDensity_pullbackOrb`: on the circle the metric line element is `|B'|`, because the base
  metric is Euclidean near the circle and `B` maps the circle to the circle.
* `pullback_spectra_eq`: for two such maps with `Spec_St(𝔻, |B₁'|) = Spec_St(𝔻, |B₂'|)` the
  Riemannian orbifold Steklov spectra of the two pulled-back orbisurfaces agree, with
  multiplicities (via the metric Proposition 2.2.1 `prop_2_2_1_metric`).
-/

@[expose] public section

open Set Filter Topology Metric Steklov
open scoped ContDiff ENNReal

noncomputable section

namespace SteklovOrb

/-- The paper's base orbifold metric on the closed unit disk. -/
structure BaseOrbMetric (u v : ℂ) (mu mv : ℕ) where
  lam : ℂ → ℝ
  U : Set ℂ
  isOpen_U : IsOpen U
  cb : closedBall (0 : ℂ) 1 ⊆ U
  u_mem : ‖u‖ < 1
  v_mem : ‖v‖ < 1
  u_ne_v : u ≠ v
  two_le_mu : 2 ≤ mu
  two_le_mv : 2 ≤ mv
  lam_smooth : ContDiffOn ℝ ∞ lam (U \ {u, v})
  lam_pos : ∀ z ∈ U \ {u, v}, 0 < lam z
  cone_u : ∃ r > 0, ∃ μ : ℂ → ℝ, ContDiffOn ℝ ∞ μ (ball 0 r) ∧ (∀ w ∈ ball (0 : ℂ) r, 0 < μ w) ∧
    ∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → μ w = chartFactor lam u mu w
  cone_v : ∃ r > 0, ∃ μ : ℂ → ℝ, ContDiffOn ℝ ∞ μ (ball 0 r) ∧ (∀ w ∈ ball (0 : ℂ) r, 0 < μ w) ∧
    ∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → μ w = chartFactor lam v mv w
  collar : ∃ ρ < 1, ∀ z ∈ U, ρ < ‖z‖ → lam z = 1

/-- The geometric properties of a branched disk map used for the pull-back. -/
structure IsBranchedDiskMap (B : ℂ → ℂ) (V : Set ℂ) (u v : ℂ) (mu mv : ℕ) (U₀ : Set ℂ) :
    Prop where
  isOpen : IsOpen V
  cb : closedBall (0 : ℂ) 1 ⊆ V
  analytic : AnalyticOnNhd ℂ B V
  mapsTo : MapsTo B V U₀
  sphere : MapsTo B (sphere 0 1) (sphere 0 1)
  branch_mem : ∀ z ∈ V, (B z = u ∨ B z = v) → ‖z‖ < 1
  finite : (V ∩ B ⁻¹' {u, v}).Finite
  crit : ∀ z ∈ V, B z ≠ u → B z ≠ v → deriv B z ≠ 0
  ram_u : ∀ z ∈ V, B z = u → deriv B z = 0 →
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ ∀ᶠ x in 𝓝 z, B x = u + (x - z) ^ mu * g x
  ram_v : ∀ z ∈ V, B z = v → deriv B z = 0 →
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ ∀ᶠ x in 𝓝 z, B x = v + (x - z) ^ mv * g x

variable {u v : ℂ} {mu mv : ℕ} (L : BaseOrbMetric u v mu mv) {B : ℂ → ℂ} {V : Set ℂ}

/-- The pulled-back conformal factor `λ₀(B x)|B'(x)|²`. -/
def pbFml (B : ℂ → ℂ) (x : ℂ) : ℝ := L.lam (B x) * ‖deriv B x‖ ^ 2

/-- Its continuous extension (the value at `z` is the limit along `𝓝[≠] z`). -/
def pbLam (B : ℂ → ℂ) (z : ℂ) : ℝ := limUnder (𝓝[≠] z) (pbFml L B)

variable {L}

lemma isOpen_base_good : IsOpen (L.U \ {u, v}) :=
  L.isOpen_U.sdiff (Set.toFinite _).isClosed

/-- At a point not over `u, v`, the formula is smooth and positive, and equals `pbLam` nearby. -/
lemma generic_point (hB : IsBranchedDiskMap B V u v mu mv L.U) {z : ℂ} (hz : z ∈ V)
    (hu : B z ≠ u) (hv : B z ≠ v) :
    pbLam L B =ᶠ[𝓝 z] pbFml L B ∧ ContDiffAt ℝ ∞ (pbFml L B) z ∧ 0 < pbFml L B z := by
  -- the open set of good points
  set W : Set ℂ := V ∩ B ⁻¹' (L.U \ {u, v})
  have hWo : IsOpen W := by
    refine ContinuousOn.isOpen_inter_preimage ?_ hB.isOpen isOpen_base_good
    exact fun x hx => (hB.analytic x hx).continuousAt.continuousWithinAt
  have hcd : ∀ x ∈ W, ContDiffAt ℝ ∞ (pbFml L B) x := by
    intro x hx
    have hBx := hB.analytic x hx.1
    have h1 : ContDiffAt ℝ ∞ (fun y => L.lam (B y)) x :=
      (L.lam_smooth.contDiffAt (isOpen_base_good.mem_nhds hx.2)).comp x
        (hBx.contDiffAt.restrict_scalars ℝ)
    have h2 : ContDiffAt ℝ ∞ (fun y => ‖deriv B y‖ ^ 2) x :=
      (contDiff_norm_sq ℝ).contDiffAt.comp x (hBx.deriv.contDiffAt.restrict_scalars ℝ)
    exact h1.mul h2
  have hzW : z ∈ W := ⟨hz, hB.mapsTo hz, by simp [hu, hv]⟩
  refine ⟨?_, hcd z hzW, ?_⟩
  · filter_upwards [hWo.mem_nhds hzW] with x hx
    exact ((hcd x hx).continuousAt.tendsto.mono_left nhdsWithin_le_nhds).limUnder_eq
  · have hpos := L.lam_pos _ hzW.2
    exact mul_pos hpos (pow_pos (norm_pos_iff.2 (hB.crit z hz hu hv)) 2)

/-- Near a point over `p ∈ {u, v}`, all other points are good. -/
lemma eventually_good (hB : IsBranchedDiskMap B V u v mu mv L.U) {z : ℂ} (hz : z ∈ V) :
    ∀ᶠ x in 𝓝 z, x ≠ z → x ∈ V ∧ B x ≠ u ∧ B x ≠ v := by
  have hfin : ((V ∩ B ⁻¹' {u, v}) \ {z}).Finite := hB.finite.diff
  have hcl : IsClosed ((V ∩ B ⁻¹' {u, v}) \ {z}) := hfin.isClosed
  have hnot : z ∉ (V ∩ B ⁻¹' {u, v}) \ {z} := fun h => h.2 rfl
  filter_upwards [hB.isOpen.mem_nhds hz, hcl.isOpen_compl.mem_nhds hnot] with x hxV hx hne
  refine ⟨hxV, fun h => hx ⟨⟨hxV, Or.inl h⟩, hne⟩, fun h => hx ⟨⟨hxV, Or.inr h⟩, hne⟩⟩

/-- The value of `pbLam` at a good point is the formula. -/
lemma pbLam_eq (hB : IsBranchedDiskMap B V u v mu mv L.U) {x : ℂ} (hx : x ∈ V) (hu : B x ≠ u)
    (hv : B x ≠ v) : pbLam L B x = pbFml L B x :=
  (generic_point hB hx hu hv).1.eq_of_nhds

/-- **Critical points over `p` become smooth points.** -/
lemma critical_point (hB : IsBranchedDiskMap B V u v mu mv L.U) {p : ℂ} {m : ℕ} (hm : 0 < m)
    {r₀ : ℝ} (hr₀ : 0 < r₀) {μ : ℂ → ℝ} (hμ : ContDiffOn ℝ ∞ μ (ball 0 r₀))
    (hμpos : ∀ w ∈ ball (0 : ℂ) r₀, 0 < μ w)
    (hμeq : ∀ w ∈ ball (0 : ℂ) r₀, w ≠ 0 → μ w = chartFactor L.lam p m w)
    {z : ℂ} (hz : z ∈ V) (hzb : B z = u ∨ B z = v) {g : ℂ → ℂ} (hg : AnalyticAt ℂ g z)
    (hg0 : g z ≠ 0) (hBg : ∀ᶠ x in 𝓝 z, B x = p + (x - z) ^ m * g x) :
    ∃ δ > 0, ∃ Λ : ℂ → ℝ, ContDiffOn ℝ ∞ Λ (ball z δ) ∧ (∀ x ∈ ball z δ, 0 < Λ x) ∧
      ∀ x ∈ ball z δ, pbLam L B x = Λ x := by
  obtain ⟨h, hh, hh0, hh', hF⟩ := exists_local_root hm hg hg0 hBg
  obtain ⟨δ₁, hδ₁, Λ, hΛ, hΛpos, hΛeq⟩ := exists_smooth_pullback hr₀ hμ hμpos hμeq hh hh0 hh' hF
  obtain ⟨δ₂, hδ₂, hgood⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_good hB hz)
  set δ := min δ₁ δ₂
  have hδ : 0 < δ := lt_min hδ₁ hδ₂
  have hsub₁ : ball z δ ⊆ ball z δ₁ := ball_subset_ball (min_le_left _ _)
  have hsub₂ : ball z δ ⊆ ball z δ₂ := ball_subset_ball (min_le_right _ _)
  have hoff : ∀ x ∈ ball z δ, x ≠ z → pbLam L B x = Λ x := by
    intro x hx hne
    obtain ⟨hxV, hxu, hxv⟩ := hgood x (hsub₂ hx) hne
    rw [pbLam_eq hB hxV hxu hxv]
    exact hΛeq x (hsub₁ hx) hne
  refine ⟨δ, hδ, Λ, hΛ.mono hsub₁, fun x hx => hΛpos x (hsub₁ hx), fun x hx => ?_⟩
  by_cases hne : x = z
  · subst hne
    -- the limit along the punctured neighbourhood
    have hcont : ContinuousAt Λ x :=
      (hΛ.continuousOn.continuousAt (isOpen_ball.mem_nhds (mem_ball_self hδ₁)))
    have hev : pbFml L B =ᶠ[𝓝[≠] x] Λ := by
      have : ball x δ ∈ 𝓝 x := ball_mem_nhds x hδ
      filter_upwards [mem_nhdsWithin_of_mem_nhds this, self_mem_nhdsWithin] with y hy hyne
      obtain ⟨hyV, hyu, hyv⟩ := hgood y (hsub₂ hy) hyne
      rw [← pbLam_eq hB hyV hyu hyv]
      exact hoff y hy hyne
    exact ((hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' hev.symm).limUnder_eq
  · exact hoff x hx hne

/-- **The cone condition at an unramified point over `p`.** -/
lemma cone_point (hB : IsBranchedDiskMap B V u v mu mv L.U) {p : ℂ} {m : ℕ} (hm : 0 < m)
    {r₀ : ℝ} (hr₀ : 0 < r₀) {μ : ℂ → ℝ} (hμ : ContDiffOn ℝ ∞ μ (ball 0 r₀))
    (hμpos : ∀ w ∈ ball (0 : ℂ) r₀, 0 < μ w)
    (hμeq : ∀ w ∈ ball (0 : ℂ) r₀, w ≠ 0 → μ w = chartFactor L.lam p m w)
    {z : ℂ} (hz : z ∈ V) (hzp : B z = p) (hd : deriv B z ≠ 0) :
    ∃ r > 0, ∃ μ' : ℂ → ℝ, ContDiffOn ℝ ∞ μ' (ball 0 r) ∧ (∀ w ∈ ball (0 : ℂ) r, 0 < μ' w) ∧
      ∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → μ' w = chartFactor (pbLam L B) z m w := by
  have hBz := hB.analytic z hz
  obtain ⟨P, hP⟩ := hBz
  have hg : AnalyticAt ℂ (dslope B z) z := ⟨_, hP.has_fpower_series_dslope_fslope⟩
  have hg0 : dslope B z z ≠ 0 := by rw [dslope_same]; exact hd
  set F : ℂ → ℂ := fun w => B (coneChart z m w)
  set G : ℂ → ℂ := fun w => dslope B z (coneChart z m w)
  have hcc : AnalyticAt ℂ (coneChart z m) 0 := analyticAt_const.add (analyticAt_id.pow m)
  have hcc0 : coneChart z m 0 = z := by simp [coneChart, zero_pow hm.ne']
  have hG : AnalyticAt ℂ G 0 := by
    have : AnalyticAt ℂ (dslope B z) (coneChart z m 0) := by rw [hcc0]; exact hg
    exact this.comp hcc
  have hG0 : G 0 ≠ 0 := by simp only [G, hcc0]; exact hg0
  have hFG : ∀ᶠ w in 𝓝 (0 : ℂ), F w = p + (w - 0) ^ m * G w := by
    refine Filter.Eventually.of_forall fun w => ?_
    have := sub_smul_dslope B z (coneChart z m w)
    simp only [coneChart, add_sub_cancel_left, smul_eq_mul] at this
    simp only [F, G, coneChart, sub_zero]
    rw [this, hzp]; ring
  obtain ⟨h, hh, hh0, hh', hF⟩ := exists_local_root hm hG hG0 hFG
  obtain ⟨δ₁, hδ₁, Λ, hΛ, hΛpos, hΛeq⟩ := exists_smooth_pullback hr₀ hμ hμpos hμeq hh hh0 hh' hF
  -- points `z + w^m`, `w ≠ 0` small, are good
  obtain ⟨δ₂, hδ₂, hgood⟩ := Metric.eventually_nhds_iff_ball.1 (eventually_good hB hz)
  have hcont : ContinuousAt (coneChart z m) 0 := hcc.continuousAt
  have hpre : coneChart z m ⁻¹' ball z δ₂ ∈ 𝓝 (0 : ℂ) :=
    hcont.preimage_mem_nhds (by rw [hcc0]; exact ball_mem_nhds z hδ₂)
  obtain ⟨δ₃, hδ₃, hδ₃sub⟩ := Metric.mem_nhds_iff.1 hpre
  set r := min δ₁ δ₃
  have hr : 0 < r := lt_min hδ₁ hδ₃
  refine ⟨r, hr, Λ, hΛ.mono (ball_subset_ball (min_le_left _ _)),
    fun w hw => hΛpos w (ball_subset_ball (min_le_left _ _) hw), fun w hw hw0 => ?_⟩
  have hw1 : w ∈ ball (0 : ℂ) δ₁ := ball_subset_ball (min_le_left _ _) hw
  have hw3 : coneChart z m w ∈ ball z δ₂ := hδ₃sub (ball_subset_ball (min_le_right _ _) hw)
  have hne : coneChart z m w ≠ z := by
    simp only [coneChart, ne_eq, add_eq_left]
    exact pow_ne_zero _ hw0
  obtain ⟨hxV, hxu, hxv⟩ := hgood _ hw3 hne
  rw [← hΛeq w hw1 hw0, chartFactor, pbLam_eq hB hxV hxu hxv, pbFml]
  -- chain rule for `F = B ∘ coneChart`
  have hdF : deriv F w = deriv B (coneChart z m w) * ((m : ℂ) * w ^ (m - 1)) := by
    have h1 : HasDerivAt (coneChart z m) ((m : ℂ) * w ^ (m - 1)) w :=
      (hasDerivAt_pow m w).const_add z
    exact ((hB.analytic _ hxV).differentiableAt.hasDerivAt.comp w h1).deriv
  rw [hdF, norm_mul]
  ring

/-- The cone points of the pulled-back orbisurface: the unramified points over `u` and `v`. -/
def coneSet (B : ℂ → ℂ) (V : Set ℂ) (u v : ℂ) : Set ℂ :=
  {z | z ∈ V ∧ (B z = u ∨ B z = v) ∧ deriv B z ≠ 0}

lemma coneSet_finite (hB : IsBranchedDiskMap B V u v mu mv L.U) : (coneSet B V u v).Finite :=
  hB.finite.subset fun _ hz => ⟨hz.1, hz.2.1⟩

/-- Smoothness and positivity of `pbLam` at every non-cone point of `V`. -/
lemma smooth_at_noncone (hB : IsBranchedDiskMap B V u v mu mv L.U) {z : ℂ} (hz : z ∈ V)
    (hzc : z ∉ coneSet B V u v) : ContDiffAt ℝ ∞ (pbLam L B) z ∧ 0 < pbLam L B z := by
  have hcrit : ∀ {p : ℂ} {m : ℕ}, 0 < m → B z = p → (B z = u ∨ B z = v) →
      (∃ r > 0, ∃ μ : ℂ → ℝ, ContDiffOn ℝ ∞ μ (ball 0 r) ∧ (∀ w ∈ ball (0 : ℂ) r, 0 < μ w) ∧
        ∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → μ w = chartFactor L.lam p m w) →
      (∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ ∀ᶠ x in 𝓝 z, B x = p + (x - z) ^ m * g x) →
      ContDiffAt ℝ ∞ (pbLam L B) z ∧ 0 < pbLam L B z := by
    intro p m hm _ hzb ⟨r, hr, μ, hμ, hμpos, hμeq⟩ ⟨g, hg, hg0, hBg⟩
    obtain ⟨δ, hδ, Λ, hΛ, hΛpos, hΛeq⟩ := critical_point hB hm hr hμ hμpos hμeq hz hzb hg hg0 hBg
    have hev : pbLam L B =ᶠ[𝓝 z] Λ := by
      filter_upwards [ball_mem_nhds z hδ] with x hx using hΛeq x hx
    exact ⟨(hΛ.contDiffAt (ball_mem_nhds z hδ)).congr_of_eventuallyEq hev,
      by rw [hΛeq z (mem_ball_self hδ)]; exact hΛpos z (mem_ball_self hδ)⟩
  by_cases hu : B z = u
  · have hd : deriv B z = 0 := by
      by_contra hd; exact hzc ⟨hz, Or.inl hu, hd⟩
    exact hcrit (by have := L.two_le_mu; omega) hu (Or.inl hu) L.cone_u (hB.ram_u z hz hu hd)
  by_cases hv : B z = v
  · have hd : deriv B z = 0 := by
      by_contra hd; exact hzc ⟨hz, Or.inr hv, hd⟩
    exact hcrit (by have := L.two_le_mv; omega) hv (Or.inr hv) L.cone_v (hB.ram_v z hz hv hd)
  obtain ⟨hev, hcd, hpos⟩ := generic_point hB hz hu hv
  exact ⟨hcd.congr_of_eventuallyEq hev, by rw [hev.eq_of_nhds]; exact hpos⟩

variable (L) in
/-- **The pulled-back orbisurface** `(𝔻, B^*(λ₀|dw|²))`, with cone points the unramified points over
`u` (order `mu`) and `v` (order `mv`). -/
def pullbackOrb (hB : IsBranchedDiskMap B V u v mu mv L.U) : DiskOrbisurface where
  n := (coneSet_finite hB).toFinset.card
  pt i := ((coneSet_finite hB).toFinset.equivFin.symm i : ℂ)
  ord i := if B ((coneSet_finite hB).toFinset.equivFin.symm i : ℂ) = u then mu else mv
  pt_inj := Subtype.val_injective.comp (coneSet_finite hB).toFinset.equivFin.symm.injective
  pt_mem i := by
    have h := ((coneSet_finite hB).mem_toFinset.1
      ((coneSet_finite hB).toFinset.equivFin.symm i).2)
    exact hB.branch_mem _ h.1 h.2.1
  two_le_ord i := by
    split_ifs
    · exact L.two_le_mu
    · exact L.two_le_mv
  lam := pbLam L B
  U := V
  isOpen_U := hB.isOpen
  cb := hB.cb
  lam_smooth := by
    intro z ⟨hzV, hzr⟩
    refine (smooth_at_noncone hB hzV fun hzc => hzr ?_).1.contDiffWithinAt
    exact ⟨(coneSet_finite hB).toFinset.equivFin ⟨z, (coneSet_finite hB).mem_toFinset.2 hzc⟩,
      by simp⟩
  lam_pos := by
    intro z ⟨hzV, hzr⟩
    refine (smooth_at_noncone hB hzV fun hzc => hzr ?_).2
    exact ⟨(coneSet_finite hB).toFinset.equivFin ⟨z, (coneSet_finite hB).mem_toFinset.2 hzc⟩,
      by simp⟩
  cone_metric i := by
    set z : ℂ := ((coneSet_finite hB).toFinset.equivFin.symm i : ℂ)
    have h : z ∈ coneSet B V u v := (coneSet_finite hB).mem_toFinset.1
      ((coneSet_finite hB).toFinset.equivFin.symm i).2
    obtain ⟨hzV, hzb, hd⟩ := h
    split_ifs with hu
    · obtain ⟨r, hr, μ, hμ, hμpos, hμeq⟩ := L.cone_u
      exact cone_point hB (by have := L.two_le_mu; omega) hr hμ hμpos hμeq hzV hu hd
    · have hv : B z = v := hzb.resolve_left hu
      obtain ⟨r, hr, μ, hμ, hμpos, hμeq⟩ := L.cone_v
      exact cone_point hB (by have := L.two_le_mv; omega) hr hμ hμpos hμeq hzV hv hd

/-- The metric of the pulled-back orbisurface is `λ₀(B z)|B'(z)|²` off `B⁻¹{u, v}`. -/
theorem pullbackOrb_lam (hB : IsBranchedDiskMap B V u v mu mv L.U) {z : ℂ} (hz : z ∈ V)
    (hu : B z ≠ u) (hv : B z ≠ v) :
    (pullbackOrb L hB).lam z = L.lam (B z) * ‖deriv B z‖ ^ 2 :=
  pbLam_eq hB hz hu hv

/-- The cone points are exactly the unramified points over `u` and `v`. -/
theorem pullbackOrb_range_pt (hB : IsBranchedDiskMap B V u v mu mv L.U) :
    range (pullbackOrb L hB).pt = coneSet B V u v := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact (coneSet_finite hB).mem_toFinset.1 ((coneSet_finite hB).toFinset.equivFin.symm i).2
  · intro hz
    exact ⟨(coneSet_finite hB).toFinset.equivFin ⟨z, (coneSet_finite hB).mem_toFinset.2 hz⟩,
      by simp [pullbackOrb]⟩

/-- Cone orders: `mu` over `u`, `mv` over `v`. -/
theorem pullbackOrb_ord (hB : IsBranchedDiskMap B V u v mu mv L.U)
    (i : Fin (pullbackOrb L hB).n) :
    (B ((pullbackOrb L hB).pt i) = u ∧ (pullbackOrb L hB).ord i = mu) ∨
      (B ((pullbackOrb L hB).pt i) = v ∧ (pullbackOrb L hB).ord i = mv) := by
  have h := (coneSet_finite hB).mem_toFinset.1 ((coneSet_finite hB).toFinset.equivFin.symm i).2
  show (_ ∧ (if _ then mu else mv) = mu) ∨ (_ ∧ (if _ then mu else mv) = mv)
  split_ifs with hu
  · exact Or.inl ⟨hu, rfl⟩
  · exact Or.inr ⟨h.2.1.resolve_left hu, rfl⟩

/-- **The boundary line element of the pulled-back orbisurface is `|B'|`.** -/
theorem lineDensity_pullbackOrb (hB : IsBranchedDiskMap B V u v mu mv L.U) {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) 1) : (pullbackOrb L hB).lineDensity z = ‖deriv B z‖ := by
  have hzV : z ∈ V := hB.cb (sphere_subset_closedBall hz)
  have hBz : ‖B z‖ = 1 := by simpa using hB.sphere hz
  have hu : B z ≠ u := fun h => by have := L.u_mem; rw [← h, hBz] at this; exact lt_irrefl _ this
  have hv : B z ≠ v := fun h => by have := L.v_mem; rw [← h, hBz] at this; exact lt_irrefl _ this
  obtain ⟨ρ, hρ, hcol⟩ := L.collar
  have h1 : L.lam (B z) = 1 := hcol _ (hB.mapsTo hzV) (by rw [hBz]; exact hρ)
  rw [DiskOrbisurface.lineDensity, pullbackOrb_lam hB hzV hu hv, h1, one_mul,
    Real.sqrt_sq (norm_nonneg _)]

/-- The weighted Steklov spectrum only depends on the weight on the circle. -/
theorem weightedSteklovSpectrum_congr {ρ₁ ρ₂ : ℂ → ℝ} (h : ∀ z ∈ sphere (0 : ℂ) 1, ρ₁ z = ρ₂ z) :
    weightedSteklovSpectrum ρ₁ = weightedSteklovSpectrum ρ₂ := by
  have hB : weightedBoundaryMass ρ₁ = weightedBoundaryMass ρ₂ := by
    funext f
    unfold weightedBoundaryMass
    congr 1
    funext t
    rw [h _ (by simp [Complex.norm_exp_ofReal_mul_I])]
  unfold weightedSteklovSpectrum weightedSteklovEigenvalue
  rw [hB]

/-- **Steklov isospectrality of pulled-back orbisurfaces.**  For any base orbifold metric `L` and
two branched disk maps `B₁, B₂` with `Spec_St(𝔻, |B₁'|) = Spec_St(𝔻, |B₂'|)`, the two
pulled-back orbisurfaces have the same Riemannian orbifold Steklov spectrum (min–max over the
metric Sobolev space `H1Met`, and over orbifold-smooth functions), with multiplicities. -/
theorem pullback_spectra_eq {B₁ B₂ : ℂ → ℂ} {V₁ V₂ : Set ℂ}
    (h₁ : IsBranchedDiskMap B₁ V₁ u v mu mv L.U) (h₂ : IsBranchedDiskMap B₂ V₂ u v mu mv L.U)
    (hspec : weightedSteklovSpectrum (fun z => ‖deriv B₁ z‖) =
      weightedSteklovSpectrum (fun z => ‖deriv B₂ z‖)) :
    (pullbackOrb L h₁).metricSteklovEigenvalue = (pullbackOrb L h₂).metricSteklovEigenvalue ∧
      (pullbackOrb L h₁).steklovSpectrum = (pullbackOrb L h₂).steklovSpectrum := by
  obtain ⟨a₁, b₁⟩ := (pullbackOrb L h₁).prop_2_2_1_metric
  obtain ⟨a₂, b₂⟩ := (pullbackOrb L h₂).prop_2_2_1_metric
  have e₁ := weightedSteklovSpectrum_congr (fun z hz => lineDensity_pullbackOrb h₁ hz)
  have e₂ := weightedSteklovSpectrum_congr (fun z hz => lineDensity_pullbackOrb h₂ hz)
  have key : (pullbackOrb L h₁).metricSteklovEigenvalue =
      (pullbackOrb L h₂).metricSteklovEigenvalue := by
    rw [a₁, a₂, e₁, e₂, hspec]
  exact ⟨key, by rw [← b₁, ← b₂, key]⟩

end SteklovOrb

namespace SteklovOrb

/-- The canonical flat cone factor of order `m` at `u`: `(1/m²)|z - u|^{2/m - 2}`. -/
def coneFac (u : ℂ) (m : ℕ) (z : ℂ) : ℝ := (1 / (m : ℝ) ^ 2) * ‖z - u‖ ^ ((2 : ℝ) / m - 2)

lemma chartFactor_coneFac_aux {m : ℕ} (hm : 1 ≤ m) {t : ℝ} (ht : 0 < t) :
    (1 / (m : ℝ) ^ 2) * (t ^ m) ^ ((2 : ℝ) / m - 2) * ((m : ℝ) * t ^ (m - 1)) ^ 2 = 1 := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [← Real.rpow_natCast t m, ← Real.rpow_mul ht.le, mul_pow, ← pow_mul,
    ← Real.rpow_natCast t ((m - 1) * 2)]
  have hexp : (m : ℝ) * (2 / m - 2) = -(((m - 1) * 2 : ℕ) : ℝ) := by
    push_cast [Nat.cast_sub hm]
    field_simp
    ring
  rw [hexp, Real.rpow_neg ht.le]
  have hpos : 0 < t ^ ((((m - 1) * 2 : ℕ)) : ℝ) := Real.rpow_pos_of_pos ht _
  field_simp

/-- **Existence of base orbifold metrics** (so `BaseOrbMetric` is not vacuous): for distinct
`u, v` in the open unit disk and orders `mu, mv ≥ 2`, the metric
`λ₀ = 1 + b_u (coneFac u mu - 1) + b_v (coneFac v mv - 1)` (smooth bump functions `b_u, b_v`
equal to `1` near `u`, `v`, with small disjoint supports) is a base orbifold metric. -/
theorem exists_baseOrbMetric {u v : ℂ} {mu mv : ℕ} (hu : ‖u‖ < 1) (hv : ‖v‖ < 1) (huv : u ≠ v)
    (hmu : 2 ≤ mu) (hmv : 2 ≤ mv) : Nonempty (BaseOrbMetric u v mu mv) := by
  set d := ‖u - v‖
  have hd : 0 < d := norm_pos_iff.2 (sub_ne_zero.2 huv)
  set r₀ := min (d / 3) ((1 - max ‖u‖ ‖v‖) / 3)
  have hmax : max ‖u‖ ‖v‖ < 1 := max_lt hu hv
  have hr₀ : 0 < r₀ := lt_min (by linarith) (by linarith)
  have hr₀d : r₀ ≤ d / 3 := min_le_left _ _
  have hr₀m : r₀ ≤ (1 - max ‖u‖ ‖v‖) / 3 := min_le_right _ _
  let bu : ContDiffBump u := ⟨r₀ / 2, r₀, half_pos hr₀, half_lt_self hr₀⟩
  let bv : ContDiffBump v := ⟨r₀ / 2, r₀, half_pos hr₀, half_lt_self hr₀⟩
  have hbu0 : ∀ z, r₀ ≤ ‖z - u‖ → bu z = 0 := by
    intro z hz
    by_contra h
    have : z ∈ Function.support bu := h
    rw [bu.support_eq, mem_ball, dist_eq_norm] at this
    exact absurd hz (not_le.2 this)
  have hbv0 : ∀ z, r₀ ≤ ‖z - v‖ → bv z = 0 := by
    intro z hz
    by_contra h
    have : z ∈ Function.support bv := h
    rw [bv.support_eq, mem_ball, dist_eq_norm] at this
    exact absurd hz (not_le.2 this)
  -- the two bump supports are far apart
  have hsep : ∀ z, ‖z - u‖ < 2 * r₀ → r₀ ≤ ‖z - v‖ := by
    intro z hz
    have : d ≤ ‖z - u‖ + ‖z - v‖ := by
      calc d = ‖(z - v) - (z - u)‖ := by simp only [d]; congr 1; ring
        _ ≤ ‖z - v‖ + ‖z - u‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    linarith
  set lam : ℂ → ℝ := fun z => 1 + bu z * (coneFac u mu z - 1) + bv z * (coneFac v mv z - 1)
  have hcf_smooth : ∀ (p : ℂ) (m : ℕ) (z : ℂ), z ≠ p → ContDiffAt ℝ ∞ (coneFac p m) z := by
    intro p m z hz
    have h1 : ContDiffAt ℝ ∞ (fun x : ℂ => ‖x - p‖) z :=
      (contDiffAt_norm ℝ (sub_ne_zero.2 hz)).comp z (contDiffAt_id.sub contDiffAt_const)
    have h2 := (Real.contDiffAt_rpow_const_of_ne (n := ∞) (p := (2 : ℝ) / m - 2)
      (norm_ne_zero_iff.2 (sub_ne_zero.2 hz))).comp z h1
    exact contDiffAt_const.mul h2
  have hcf_pos : ∀ (p : ℂ) (m : ℕ) (z : ℂ), 1 ≤ m → z ≠ p → 0 < coneFac p m z := by
    intro p m z hm hz
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    exact mul_pos (by positivity) (Real.rpow_pos_of_pos (norm_pos_iff.2 (sub_ne_zero.2 hz)) _)
  have hconvex : ∀ b c : ℝ, 0 ≤ b → b ≤ 1 → 0 < c → 0 < 1 + b * (c - 1) := by
    intro b c hb0 hb1 hc
    rcases hb0.lt_or_eq with hb | hb
    · nlinarith
    · rw [← hb]; norm_num
  -- the cone condition
  have hcone : ∀ (p : ℂ) (m : ℕ) (b : ContDiffBump p), 1 ≤ m → b.rIn = r₀ / 2 →
      (∀ z, ‖z - p‖ < r₀ → lam z = 1 + b z * (coneFac p m z - 1)) →
      ∃ r > 0, ∃ μ : ℂ → ℝ, ContDiffOn ℝ ∞ μ (ball 0 r) ∧ (∀ w ∈ ball (0 : ℂ) r, 0 < μ w) ∧
        ∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → μ w = chartFactor lam p m w := by
    intro p m b hm hbr hlam
    set r := min 1 (r₀ / 2)
    have hr : 0 < r := lt_min one_pos (half_pos hr₀)
    refine ⟨r, hr, fun _ => 1, contDiffOn_const, fun _ _ => one_pos, fun w hw hw0 => ?_⟩
    have hw1 : ‖w‖ < 1 := lt_of_lt_of_le (mem_ball_zero_iff.1 hw) (min_le_left _ _)
    have hwr : ‖w‖ < r₀ / 2 := lt_of_lt_of_le (mem_ball_zero_iff.1 hw) (min_le_right _ _)
    have hwm : ‖w‖ ^ m ≤ ‖w‖ := pow_le_of_le_one (norm_nonneg _) hw1.le (by omega)
    have hzp : ‖coneChart p m w - p‖ = ‖w‖ ^ m := by simp [coneChart, norm_pow]
    have hb1 : b (coneChart p m w) = 1 := by
      apply b.one_of_mem_closedBall
      rw [mem_closedBall, dist_eq_norm, hzp, hbr]; linarith
    rw [chartFactor, hlam _ (by rw [hzp]; linarith), hb1, coneFac, hzp, norm_mul, norm_pow,
      Complex.norm_natCast]
    have ht : 0 < ‖w‖ := norm_pos_iff.2 hw0
    have := chartFactor_coneFac_aux hm ht
    linarith
  refine ⟨{
    lam := lam
    U := univ
    isOpen_U := isOpen_univ
    cb := subset_univ _
    u_mem := hu
    v_mem := hv
    u_ne_v := huv
    two_le_mu := hmu
    two_le_mv := hmv
    lam_smooth := ?_
    lam_pos := ?_
    cone_u := ?_
    cone_v := ?_
    collar := ?_ }⟩
  · rintro z ⟨-, hz⟩
    have hzu : z ≠ u := fun h => hz (Or.inl h)
    have hzv : z ≠ v := fun h => hz (Or.inr h)
    have hbu' : ContDiffAt ℝ ∞ (fun x => bu x) z := (bu.contDiff (n := ⊤)).contDiffAt
    have hbv' : ContDiffAt ℝ ∞ (fun x => bv x) z := (bv.contDiff (n := ⊤)).contDiffAt
    exact ((contDiffAt_const.add (hbu'.mul ((hcf_smooth u mu z hzu).sub contDiffAt_const))).add
      (hbv'.mul ((hcf_smooth v mv z hzv).sub contDiffAt_const))).contDiffWithinAt
  · rintro z ⟨-, hz⟩
    have hzu : z ≠ u := fun h => hz (Or.inl h)
    have hzv : z ≠ v := fun h => hz (Or.inr h)
    by_cases h1 : ‖z - u‖ < r₀
    · have hbv : bv z = 0 := hbv0 z (hsep z (by linarith))
      show 0 < 1 + bu z * (coneFac u mu z - 1) + bv z * (coneFac v mv z - 1)
      rw [hbv, zero_mul, add_zero]
      exact hconvex _ _ bu.nonneg bu.le_one (hcf_pos u mu z (by omega) hzu)
    · have hbu : bu z = 0 := hbu0 z (not_lt.1 h1)
      show 0 < 1 + bu z * (coneFac u mu z - 1) + bv z * (coneFac v mv z - 1)
      rw [hbu, zero_mul, add_zero]
      exact hconvex _ _ bv.nonneg bv.le_one (hcf_pos v mv z (by omega) hzv)
  · exact hcone u mu bu (by omega) rfl fun z hz => by
      show 1 + bu z * (coneFac u mu z - 1) + bv z * (coneFac v mv z - 1) = _
      rw [hbv0 z (hsep z (by linarith)), zero_mul, add_zero]
  · refine hcone v mv bv (by omega) rfl fun z hz => ?_
    have hsep' : r₀ ≤ ‖z - u‖ := by
      have : d ≤ ‖z - u‖ + ‖z - v‖ := by
        calc d = ‖(z - v) - (z - u)‖ := by simp only [d]; congr 1; ring
          _ ≤ ‖z - v‖ + ‖z - u‖ := norm_sub_le _ _
          _ = _ := add_comm _ _
      linarith
    show 1 + bu z * (coneFac u mu z - 1) + bv z * (coneFac v mv z - 1) = _
    rw [hbu0 z hsep', zero_mul, add_zero]
  · refine ⟨max ‖u‖ ‖v‖ + r₀, by linarith, fun z _ hz => ?_⟩
    have h1 : r₀ ≤ ‖z - u‖ := by
      have := norm_sub_norm_le z u
      have := le_max_left ‖u‖ ‖v‖
      linarith
    have h2 : r₀ ≤ ‖z - v‖ := by
      have := norm_sub_norm_le z v
      have := le_max_right ‖u‖ ‖v‖
      linarith
    show 1 + bu z * (coneFac u mu z - 1) + bv z * (coneFac v mv z - 1) = 1
    rw [hbu0 z h1, hbv0 z h2]; ring

end SteklovOrb
