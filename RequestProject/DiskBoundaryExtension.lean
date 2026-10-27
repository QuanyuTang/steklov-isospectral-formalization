module

public import RequestProject.Coalescence
public import RequestProject.BlaschkeCover
public import RequestProject.HolomorphicInverse

/-!
# Boundary extension of the conformal map of a normalized disk cover

Let `Q` be entire with `Q' ≠ 0` on the level set `{‖Q‖ = 1}` and `{‖Q‖ ≤ 1}` compact (e.g. the
paper's polynomials `paperQ`, whose critical values lie in `𝔻`), and let `ψ : 𝔻 → ℂ` be
holomorphic and injective with `ψ(𝔻) = {‖Q‖ < 1}` and `B = Q ∘ ψ` a finite Blaschke product.

* `local_extension`: at every `z₀ ∈ 𝕋`, `ψ` is the restriction of a holomorphic map `E = G ∘ B`
  (`G` a local inverse of `Q`) on a disk about `z₀`, with `E' ≠ 0` and `Q ∘ E = B`.
* **`closed_disk_extension`**: `ψ` extends to a homeomorphism `Ψ` of the closed unit disk onto
  `{‖Q‖ ≤ 1}`, mapping the circle onto `{‖Q‖ = 1}`, with `Q ∘ Ψ = B` on the closed disk, and which
  near each boundary point is the restriction of a holomorphic map with nonvanishing derivative
  (analytic compatibility at the boundary).

No Carathéodory theorem is used: the extension comes from the local invertibility of `Q` along
the level set and of the Blaschke product `B` along the circle.
-/

@[expose] public section

open Set Filter Topology Metric SteklovBlaschke SteklovCoalescence

noncomputable section

namespace SteklovBordered

variable {Q ψ B : ℂ → ℂ} {n : ℕ}

/-- A sequence in the open disk tending to a boundary point. -/
lemma tendsto_inner_seq {z₀ : ℂ} (hz₀ : ‖z₀‖ = 1) :
    (∀ k : ℕ, (1 - 1 / ((k : ℝ) + 2) : ℂ) * z₀ ∈ ball (0 : ℂ) 1) ∧
      Tendsto (fun k : ℕ => (1 - 1 / ((k : ℝ) + 2) : ℂ) * z₀) atTop (𝓝 z₀) := by
  constructor
  · intro k
    rw [mem_ball_zero_iff, norm_mul, hz₀, mul_one]
    have hk : (0 : ℝ) < (k : ℝ) + 2 := by positivity
    have h1 : (1 - 1 / ((k : ℝ) + 2) : ℂ) = ((1 - 1 / ((k : ℝ) + 2) : ℝ) : ℂ) := by push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · have : 0 < 1 / ((k : ℝ) + 2) := by positivity
      linarith
    · rw [sub_nonneg, div_le_one hk]; linarith
  · have h : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 2))) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 2)) atTop (𝓝 0) := by
        refine squeeze_zero (fun k => by positivity) (fun k => ?_) this
        apply one_div_le_one_div_of_le (by positivity); linarith
      exact h2
    have h' : Tendsto (fun k : ℕ => ((1 - 1 / ((k : ℝ) + 2) : ℝ) : ℂ) * z₀) atTop
        (𝓝 (((1 - 0 : ℝ) : ℂ) * z₀)) :=
      ((Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.sub h)).mul_const z₀
    simp only [sub_zero, Complex.ofReal_one, one_mul] at h'
    refine h'.congr fun k => ?_
    push_cast; ring

variable (hQ : Differentiable ℂ Q) (hQ' : ∀ y, ‖Q y‖ = 1 → deriv Q y ≠ 0)
  (hK : IsCompact {y | ‖Q y‖ ≤ 1})
  (hψd : DifferentiableOn ℂ ψ (ball 0 1)) (hψi : InjOn ψ (ball 0 1))
  (himg : ψ '' ball 0 1 = {y | ‖Q y‖ < 1})
  (hB : IsFiniteBlaschke B n) (hn : 0 < n) (hBQ : ∀ z ∈ ball (0 : ℂ) 1, B z = Q (ψ z))
include hQ hQ' hK hψd hψi himg hB hn hBQ

/-- **Local holomorphic extension across the circle.** -/
theorem local_extension {z₀ : ℂ} (hz₀ : z₀ ∈ sphere (0 : ℂ) 1) :
    ∃ δ > 0, ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (ball z₀ δ) ∧
      (∀ z ∈ ball z₀ δ, deriv E z ≠ 0) ∧ (∀ z ∈ ball z₀ δ, Q (E z) = B z) ∧
      ∀ z ∈ ball z₀ δ ∩ ball 0 1, E z = ψ z := by
  have hz₀n : ‖z₀‖ = 1 := by simpa using hz₀
  obtain ⟨R, R₀, c, hR₀, hR₀R, -, hBd, hBn, -, -, -, hBder⟩ := hB.exists_radii hn
  obtain ⟨hzk, hzt⟩ := tendsto_inner_seq hz₀n
  set zk := fun k : ℕ => (1 - 1 / ((k : ℝ) + 2) : ℂ) * z₀
  have hψK : ∀ k, ψ (zk k) ∈ {y | ‖Q y‖ ≤ 1} := by
    intro k
    have : ψ (zk k) ∈ ψ '' ball 0 1 := mem_image_of_mem _ (hzk k)
    rw [himg] at this
    exact le_of_lt (show ‖Q (ψ (zk k))‖ < 1 from this)
  obtain ⟨y₀, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hψK
  have hz₀R : z₀ ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff, hz₀n]; linarith
  have hBc : ContinuousAt B z₀ := (hBd.differentiableAt (isOpen_ball.mem_nhds hz₀R)).continuousAt
  have hQy₀ : Q y₀ = B z₀ := by
    have h1 : Tendsto (fun k => Q (ψ (zk (φ k)))) atTop (𝓝 (Q y₀)) :=
      (hQ y₀).continuousAt.tendsto.comp hlim
    have h2 : Tendsto (fun k => B (zk (φ k))) atTop (𝓝 (B z₀)) :=
      hBc.tendsto.comp (hzt.comp hφ.tendsto_atTop)
    refine tendsto_nhds_unique (h1.congr fun k => ?_) h2
    exact (hBQ _ (hzk _)).symm
  have hBz₀ : ‖B z₀‖ = 1 := ((hBn z₀ hz₀R).2).2 hz₀n
  have hQ'y₀ : deriv Q y₀ ≠ 0 := hQ' y₀ (by rw [hQy₀, hBz₀])
  -- a ball about `y₀` on which `Q` is injective with nonzero derivative
  have hdQc : ContinuousAt (deriv Q) y₀ := ((hQ.analyticAt y₀).deriv).continuousAt
  obtain ⟨r₁, hr₁, hinj⟩ := HolInv.exists_ball_injOn isOpen_univ hQ.differentiableOn
    (mem_univ y₀) hQ'y₀
  obtain ⟨r₂, hr₂, hr₂d⟩ := Metric.eventually_nhds_iff_ball.1
    (hdQc.eventually (isOpen_ne.mem_nhds hQ'y₀))
  set r := min r₁ r₂
  have hr : 0 < r := lt_min hr₁ hr₂
  set Y := ball y₀ r
  have hYinj : InjOn Q Y := hinj.mono (ball_subset_ball (min_le_left _ _))
  have hYd : ∀ y ∈ Y, deriv Q y ≠ 0 := fun y hy => hr₂d y (ball_subset_ball (min_le_right _ _) hy)
  set W := Q '' Y
  have hWo : IsOpen W := HolInv.isOpen_image hQ.differentiableOn hYinj subset_rfl isOpen_ball
  set G := Function.invFunOn Q Y
  have hGd : ∀ w ∈ W, HasDerivAt G (deriv Q (G w))⁻¹ w := by
    rintro _ ⟨y, hy, rfl⟩
    have hGy : G (Q y) = y := HolInv.invFunOn_apply_self hYinj hy
    rw [hGy]
    exact HolInv.hasDerivAt_invFunOn isOpen_ball hQ.differentiableOn hYinj hy (hYd y hy)
  have hGmem : ∀ w ∈ W, G w ∈ Y := fun w hw => Function.invFunOn_mem hw
  have hQG : ∀ w ∈ W, Q (G w) = w := fun w hw => Function.invFunOn_eq hw
  -- the disk about `z₀`
  have hBW : B z₀ ∈ W := ⟨y₀, mem_ball_self hr, hQy₀⟩
  obtain ⟨δ₁, hδ₁, hδ₁W⟩ := Metric.eventually_nhds_iff_ball.1 (hBc.eventually (hWo.mem_nhds hBW))
  set δ := min δ₁ (min (R₀ - 1) (R - 1))
  have hδ : 0 < δ := lt_min hδ₁ (lt_min (by linarith) (by linarith))
  have hδ1 : ball z₀ δ ⊆ ball z₀ δ₁ := ball_subset_ball (min_le_left _ _)
  have hδR : ∀ z ∈ ball z₀ δ, ‖z‖ < R₀ := by
    intro z hz
    have h1 : dist z z₀ < R₀ - 1 :=
      lt_of_lt_of_le hz ((min_le_right _ _).trans (min_le_left _ _))
    have := norm_le_norm_add_norm_sub' z z₀
    rw [dist_eq_norm] at h1
    linarith [norm_sub_rev z z₀]
  have hδR' : ∀ z ∈ ball z₀ δ, z ∈ ball (0 : ℂ) R := fun z hz =>
    mem_ball_zero_iff.2 (by linarith [hδR z hz])
  have hBWδ : ∀ z ∈ ball z₀ δ, B z ∈ W := fun z hz => hδ₁W z (hδ1 hz)
  set E : ℂ → ℂ := fun z => G (B z)
  have hEd : ∀ z ∈ ball z₀ δ, HasDerivAt E ((deriv Q (G (B z)))⁻¹ * deriv B z) z := by
    intro z hz
    have hBz : HasDerivAt B (deriv B z) z :=
      (hBd.differentiableAt (isOpen_ball.mem_nhds (hδR' z hz))).hasDerivAt
    exact (hGd _ (hBWδ z hz)).comp z hBz
  have hEcont : ContinuousOn E (ball z₀ δ) := fun z hz =>
    (hEd z hz).continuousAt.continuousWithinAt
  -- `E = ψ` on `ball z₀ δ ∩ 𝔻`
  set D := ball z₀ δ ∩ ball (0 : ℂ) 1
  have hDo : IsOpen D := isOpen_ball.inter isOpen_ball
  have hDc : IsPreconnected D := ((convex_ball _ _).inter (convex_ball _ _)).isPreconnected
  have hψc : ContinuousOn ψ D := hψd.continuousOn.mono inter_subset_right
  set u := D ∩ ψ ⁻¹' Y
  have huo : IsOpen u := hψc.isOpen_inter_preimage hDo isOpen_ball
  have hEq_u : EqOn ψ E u := by
    intro z hz
    show ψ z = G (B z)
    rw [hBQ z hz.1.2]
    exact (HolInv.invFunOn_apply_self hYinj hz.2).symm
  have hne : (D ∩ u).Nonempty := by
    have h1 : ∀ᶠ k in atTop, zk (φ k) ∈ ball z₀ δ :=
      (hzt.comp hφ.tendsto_atTop).eventually (ball_mem_nhds z₀ hδ)
    have h2 : ∀ᶠ k in atTop, ψ (zk (φ k)) ∈ Y := hlim.eventually (ball_mem_nhds y₀ hr)
    obtain ⟨k, hk1, hk2⟩ := (h1.and h2).exists
    exact ⟨zk (φ k), ⟨hk1, hzk _⟩, ⟨hk1, hzk _⟩, hk2⟩
  have hsub : D ⊆ u := by
    refine hDc.subset_of_closure_inter_subset huo hne ?_
    rintro z ⟨hzc, hzD⟩
    have heq : EqOn ψ E (D ∩ closure u) := by
      refine Set.EqOn.of_subset_closure hEq_u (hψc.mono inter_subset_left)
        (hEcont.mono (inter_subset_left.trans inter_subset_left)) ?_ inter_subset_right
      intro x hx; exact ⟨hx.1, subset_closure hx⟩
    have hz : ψ z = E z := heq ⟨hzD, hzc⟩
    refine ⟨hzD, ?_⟩
    show ψ z ∈ Y
    rw [hz]; exact hGmem _ (hBWδ z hzD.1)
  refine ⟨δ, hδ, E, fun z hz => (hEd z hz).differentiableAt.differentiableWithinAt,
    fun z hz => ?_, fun z hz => hQG _ (hBWδ z hz), fun z hz => (hEq_u (hsub hz)).symm⟩
  rw [(hEd z hz).deriv]
  refine mul_ne_zero (inv_ne_zero (hYd _ (hGmem _ (hBWδ z hz)))) ?_
  by_cases h1 : 1 ≤ ‖z‖
  · exact hBder z h1 (hδR z hz).le
  · -- inside the disk, `E = ψ` near `z` and `ψ` is injective
    have hz1 : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.2 (not_le.1 h1)
    have hψ' : deriv ψ z ≠ 0 := HolInv.deriv_ne_zero_of_injOn isOpen_ball hψd hψi hz1
    have hev : E =ᶠ[𝓝 z] ψ := by
      filter_upwards [hDo.mem_nhds ⟨hz, hz1⟩] with x hx using (hEq_u (hsub hx)).symm
    have hdE : deriv E z = deriv ψ z := hev.deriv_eq
    rw [(hEd z hz).deriv] at hdE
    intro hBz0
    rw [hBz0, mul_zero] at hdE
    exact hψ' hdE.symm

omit hQ hQ' hK hψd hψi himg hB hn hBQ in
/-- Two functions continuous at a boundary point and agreeing with `ψ` on the inside near it have
the same value there. -/
lemma eq_of_inner_eq {E E' : ℂ → ℂ} {z : ℂ} (hz : ‖z‖ = 1) (hE : ContinuousAt E z)
    (hE' : ContinuousAt E' z) {δ δ' : ℝ} (hδ : 0 < δ) (hδ' : 0 < δ')
    (h : ∀ x ∈ ball z δ ∩ ball 0 1, E x = ψ x) (h' : ∀ x ∈ ball z δ' ∩ ball 0 1, E' x = ψ x) :
    E z = E' z := by
  obtain ⟨hzk, hzt⟩ := tendsto_inner_seq hz
  set zk := fun k : ℕ => (1 - 1 / ((k : ℝ) + 2) : ℂ) * z
  refine tendsto_nhds_unique (hE.tendsto.comp hzt) ((hE'.tendsto.comp hzt).congr' ?_)
  filter_upwards [hzt.eventually (ball_mem_nhds z hδ), hzt.eventually (ball_mem_nhds z hδ')]
    with k hk hk'
  simp only [Function.comp]
  rw [h' _ ⟨hk', hzk k⟩, h _ ⟨hk, hzk k⟩]

/-- **Boundary extension of `ψ` to the closed disk.** -/
theorem closed_disk_extension :
    ∃ Ψ : ℂ → ℂ, (∀ z ∈ ball (0 : ℂ) 1, Ψ z = ψ z) ∧ ContinuousOn Ψ (closedBall 0 1) ∧
      InjOn Ψ (closedBall 0 1) ∧ Ψ '' closedBall 0 1 = {y | ‖Q y‖ ≤ 1} ∧
      Ψ '' sphere 0 1 = {y | ‖Q y‖ = 1} ∧ (∀ z ∈ closedBall (0 : ℂ) 1, Q (Ψ z) = B z) ∧
      ∀ z₀ ∈ sphere (0 : ℂ) 1, ∃ δ > 0, ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (ball z₀ δ) ∧
        (∀ z ∈ ball z₀ δ, deriv E z ≠ 0) ∧ (∀ z ∈ ball z₀ δ, Q (E z) = B z) ∧
        ∀ z ∈ ball z₀ δ ∩ closedBall 0 1, E z = Ψ z := by
  classical
  have hloc := fun (z₀ : ℂ) (h : z₀ ∈ sphere (0 : ℂ) 1) =>
    local_extension hQ hQ' hK hψd hψi himg hB hn hBQ h
  choose δf hδf Ef hEd hEder hQE hEψ using hloc
  obtain ⟨R, R₀, c, hR₀, hR₀R, -, hBd, hBn, -, -, -, -⟩ := hB.exists_radii hn
  set Ψ : ℂ → ℂ := fun z => if h : z ∈ sphere (0 : ℂ) 1 then Ef z h z else ψ z
  have hΨin : ∀ z ∈ ball (0 : ℂ) 1, Ψ z = ψ z := by
    intro z hz
    have : z ∉ sphere (0 : ℂ) 1 := by
      intro h; rw [mem_sphere_zero_iff_norm] at h; rw [mem_ball_zero_iff] at hz; linarith
    simp only [Ψ, dif_neg this]
  -- near a boundary point, `Ψ` is the local extension
  have hΨE : ∀ z₀ (h₀ : z₀ ∈ sphere (0 : ℂ) 1), ∀ z ∈ ball z₀ (δf z₀ h₀) ∩ closedBall 0 1,
      Ef z₀ h₀ z = Ψ z := by
    intro z₀ h₀ z ⟨hz, hzc⟩
    by_cases hzs : z ∈ sphere (0 : ℂ) 1
    · simp only [Ψ, hzs, dite_true]
      have hzn : ‖z‖ = 1 := by simpa using hzs
      obtain ⟨η, hη, hηsub⟩ := Metric.isOpen_iff.1 isOpen_ball z hz
      refine eq_of_inner_eq hzn ((hEd z₀ h₀).differentiableAt (isOpen_ball.mem_nhds hz)).continuousAt
        ((hEd z hzs).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hδf z hzs)))).continuousAt
        hη (hδf z hzs) (fun x hx => hEψ z₀ h₀ x ⟨hηsub hx.1, hx.2⟩) (hEψ z hzs)
    · have hz1 : z ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]; rw [mem_closedBall_zero_iff] at hzc
        rw [mem_sphere_zero_iff_norm] at hzs
        exact lt_of_le_of_ne hzc hzs
      rw [hΨin z hz1]
      exact hEψ z₀ h₀ z ⟨hz, hz1⟩
  have hBQc : ∀ z ∈ closedBall (0 : ℂ) 1, Q (Ψ z) = B z := by
    intro z hz
    by_cases hzs : z ∈ sphere (0 : ℂ) 1
    · rw [← hΨE z hzs z ⟨mem_ball_self (hδf z hzs), hz⟩]
      exact hQE z hzs z (mem_ball_self (hδf z hzs))
    · have hz1 : z ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]; rw [mem_closedBall_zero_iff] at hz
        rw [mem_sphere_zero_iff_norm] at hzs
        exact lt_of_le_of_ne hz hzs
      rw [hΨin z hz1, hBQ z hz1]
  have hcb_R : ∀ z ∈ closedBall (0 : ℂ) 1, z ∈ ball (0 : ℂ) R := fun z hz =>
    mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hz) (by linarith))
  -- continuity
  have hcont : ContinuousOn Ψ (closedBall 0 1) := by
    intro z hz
    by_cases hzs : z ∈ sphere (0 : ℂ) 1
    · have hEc : ContinuousAt (Ef z hzs) z :=
        ((hEd z hzs).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hδf z hzs)))).continuousAt
      refine (hEc.continuousWithinAt).congr_of_eventuallyEq ?_ (hΨE z hzs z
        ⟨mem_ball_self (hδf z hzs), hz⟩).symm
      filter_upwards [mem_nhdsWithin_of_mem_nhds (ball_mem_nhds z (hδf z hzs)),
        self_mem_nhdsWithin] with x hx hxc
      exact (hΨE z hzs x ⟨hx, hxc⟩).symm
    · have hz1 : z ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]; rw [mem_closedBall_zero_iff] at hz
        rw [mem_sphere_zero_iff_norm] at hzs
        exact lt_of_le_of_ne hz hzs
      have hψc : ContinuousAt ψ z := (hψd.differentiableAt (isOpen_ball.mem_nhds hz1)).continuousAt
      refine (hψc.congr ?_).continuousWithinAt
      filter_upwards [isOpen_ball.mem_nhds hz1] with x hx using (hΨin x hx).symm
  -- norms
  have hnorm_lt : ∀ z ∈ closedBall (0 : ℂ) 1, ‖Q (Ψ z)‖ < 1 ↔ z ∈ ball (0 : ℂ) 1 := by
    intro z hz
    rw [hBQc z hz, mem_ball_zero_iff]
    exact (hBn z (hcb_R z hz)).1
  have hnorm_eq : ∀ z ∈ closedBall (0 : ℂ) 1, ‖Q (Ψ z)‖ = 1 ↔ z ∈ sphere (0 : ℂ) 1 := by
    intro z hz
    rw [hBQc z hz, mem_sphere_zero_iff_norm]
    exact (hBn z (hcb_R z hz)).2
  -- every point of the level set is a limit of points of `{‖Q‖ < 1}`, locally near any preimage
  have hlevel_approx : ∀ y, ‖Q y‖ = 1 → ∀ N ∈ 𝓝 y, ∃ y' ∈ N, ‖Q y'‖ < 1 := by
    intro y hy N hN
    have hs : HasStrictDerivAt Q (deriv Q y) y := (hQ.analyticAt y).hasStrictDerivAt
    have hmap : map Q (𝓝 y) = 𝓝 (Q y) := hs.map_nhds_eq (hQ' y hy)
    have hQN : Q '' N ∈ 𝓝 (Q y) := by
      rw [← hmap]; exact image_mem_map hN
    -- points `t Q(y)`, `t < 1`, close to `Q y`
    obtain ⟨η, hη, hηsub⟩ := Metric.mem_nhds_iff.1 hQN
    set t : ℝ := 1 - min (η / 2) (1 / 2)
    have ht0 : 0 < t := by
      have := min_le_right (η / 2) (1 / 2); simp only [t]; linarith
    have ht1 : t < 1 := by
      have := lt_min (half_pos hη) (by norm_num : (0 : ℝ) < 1 / 2); simp only [t]; linarith
    have hmem : (t : ℂ) * Q y ∈ ball (Q y) η := by
      rw [mem_ball, dist_eq_norm]
      have : (t : ℂ) * Q y - Q y = ((t - 1 : ℝ) : ℂ) * Q y := by push_cast; ring
      rw [this, norm_mul, Complex.norm_real, hy, mul_one, Real.norm_eq_abs, abs_of_nonpos
        (by linarith)]
      have := min_le_left (η / 2) (1 / 2)
      simp only [t]; linarith
    obtain ⟨y', hy'N, hy'⟩ := hηsub hmem
    refine ⟨y', hy'N, ?_⟩
    rw [hy', norm_mul, Complex.norm_real, hy, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
    exact ht1
  -- injectivity
  have hinj : InjOn Ψ (closedBall 0 1) := by
    intro z₁ hz₁ z₂ hz₂ heq
    by_cases h1 : z₁ ∈ ball (0 : ℂ) 1 <;> by_cases h2 : z₂ ∈ ball (0 : ℂ) 1
    · rw [hΨin z₁ h1, hΨin z₂ h2] at heq; exact hψi h1 h2 heq
    · exfalso
      have a := (hnorm_lt z₁ hz₁).2 h1
      have b : ¬ ‖Q (Ψ z₂)‖ < 1 := fun h => h2 ((hnorm_lt z₂ hz₂).1 h)
      rw [heq] at a; exact b a
    · exfalso
      have a := (hnorm_lt z₂ hz₂).2 h2
      have b : ¬ ‖Q (Ψ z₁)‖ < 1 := fun h => h1 ((hnorm_lt z₁ hz₁).1 h)
      rw [← heq] at a; exact b a
    · by_contra hne
      have hs1 : z₁ ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm]; rw [mem_closedBall_zero_iff] at hz₁
        rw [mem_ball_zero_iff] at h1; linarith
      have hs2 : z₂ ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm]; rw [mem_closedBall_zero_iff] at hz₂
        rw [mem_ball_zero_iff] at h2; linarith
      set y := Ψ z₁
      have hy1 : ‖Q y‖ = 1 := (hnorm_eq z₁ hz₁).2 hs1
      -- disjoint small disks
      have hd : 0 < dist z₁ z₂ := dist_pos.2 hne
      set ρ := min (dist z₁ z₂ / 2) (min (δf z₁ hs1) (min (δf z₂ hs2) (R - 1)))
      have hρ : 0 < ρ := lt_min (half_pos hd) (lt_min (hδf z₁ hs1)
        (lt_min (hδf z₂ hs2) (by linarith)))
      have hρ1 : ball z₁ ρ ⊆ ball z₁ (δf z₁ hs1) :=
        ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _))
      have hρ2 : ball z₂ ρ ⊆ ball z₂ (δf z₂ hs2) :=
        ball_subset_ball ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      have hρR : ρ ≤ R - 1 :=
        (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
      have hn1 : ‖z₁‖ = 1 := mem_sphere_zero_iff_norm.1 hs1
      have hn2 : ‖z₂‖ = 1 := mem_sphere_zero_iff_norm.1 hs2
      have hdisj : Disjoint (ball z₁ ρ) (ball z₂ ρ) := by
        refine ball_disjoint_ball ?_
        have := min_le_left (dist z₁ z₂ / 2) (min (δf z₁ hs1) (min (δf z₂ hs2) (R - 1)))
        linarith
      -- images are neighbourhoods of `y`
      have himg_nhds : ∀ (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1), Ef z hz z = y →
          Ef z hz '' ball z ρ ∈ 𝓝 y := by
        intro z hz hzy
        have hs : HasStrictDerivAt (Ef z hz) (deriv (Ef z hz) z) z :=
          (((hEd z hz).analyticOnNhd isOpen_ball) z (mem_ball_self (hδf z hz))).hasStrictDerivAt
        have hmap := hs.map_nhds_eq (hEder z hz z (mem_ball_self (hδf z hz)))
        rw [hzy] at hmap
        rw [← hmap]; exact image_mem_map (ball_mem_nhds z hρ)
      have hE1 : Ef z₁ hs1 z₁ = y :=
        hΨE z₁ hs1 z₁ ⟨mem_ball_self (hδf z₁ hs1), hz₁⟩
      have hE2 : Ef z₂ hs2 z₂ = y := by
        rw [hΨE z₂ hs2 z₂ ⟨mem_ball_self (hδf z₂ hs2), hz₂⟩]; exact heq.symm
      obtain ⟨y', ⟨⟨x₁, hx₁, hx₁y⟩, ⟨x₂, hx₂, hx₂y⟩⟩, hy'⟩ :=
        hlevel_approx y hy1 _ (inter_mem (himg_nhds z₁ hs1 hE1) (himg_nhds z₂ hs2 hE2))
      have hx₁in : x₁ ∈ ball (0 : ℂ) 1 := by
        have hB1 : B x₁ = Q y' := by rw [← hx₁y]; exact (hQE z₁ hs1 x₁ (hρ1 hx₁)).symm
        have hx₁R : x₁ ∈ ball (0 : ℂ) R := by
          rw [mem_ball_zero_iff]
          have h3 : dist x₁ z₁ < ρ := hx₁
          rw [dist_eq_norm] at h3
          have := norm_le_norm_add_norm_sub' x₁ z₁
          linarith
        rw [mem_ball_zero_iff]
        exact (hBn x₁ hx₁R).1.1 (by rw [hB1]; exact hy')
      have hx₂in : x₂ ∈ ball (0 : ℂ) 1 := by
        have hB2 : B x₂ = Q y' := by rw [← hx₂y]; exact (hQE z₂ hs2 x₂ (hρ2 hx₂)).symm
        have hx₂R : x₂ ∈ ball (0 : ℂ) R := by
          rw [mem_ball_zero_iff]
          have h3 : dist x₂ z₂ < ρ := hx₂
          rw [dist_eq_norm] at h3
          have := norm_le_norm_add_norm_sub' x₂ z₂
          linarith
        rw [mem_ball_zero_iff]
        exact (hBn x₂ hx₂R).1.1 (by rw [hB2]; exact hy')
      have e1 : ψ x₁ = y' := by rw [← hEψ z₁ hs1 x₁ ⟨hρ1 hx₁, hx₁in⟩]; exact hx₁y
      have e2 : ψ x₂ = y' := by rw [← hEψ z₂ hs2 x₂ ⟨hρ2 hx₂, hx₂in⟩]; exact hx₂y
      have : x₁ = x₂ := hψi hx₁in hx₂in (e1.trans e2.symm)
      exact hdisj.ne_of_mem hx₁ hx₂ this
  -- images
  have himg_cb : Ψ '' closedBall 0 1 = {y | ‖Q y‖ ≤ 1} := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      show ‖Q (Ψ z)‖ ≤ 1
      rw [hBQc z hz]
      have hz' := mem_closedBall_zero_iff.1 hz
      rcases hz'.lt_or_eq with h | h
      · exact ((hBn z (hcb_R z hz)).1.2 h).le
      · exact ((hBn z (hcb_R z hz)).2.2 h).le
    · have hcpt : IsCompact (Ψ '' closedBall 0 1) :=
        (isCompact_closedBall 0 1).image_of_continuousOn hcont
      intro y hy
      have hy' : ‖Q y‖ ≤ 1 := hy
      rcases hy'.lt_or_eq with h | h
      · have : y ∈ ψ '' ball 0 1 := by rw [himg]; exact h
        obtain ⟨z, hz, rfl⟩ := this
        exact ⟨z, ball_subset_closedBall hz, hΨin z hz⟩
      · refine hcpt.isClosed.mem_of_frequently_of_tendsto (f := id) ?_ tendsto_id
        rw [Filter.frequently_iff]
        intro N hN
        obtain ⟨y', hy'N, hy'⟩ := hlevel_approx y h N hN
        have : y' ∈ ψ '' ball 0 1 := by rw [himg]; exact hy'
        obtain ⟨z, hz, rfl⟩ := this
        exact ⟨ψ z, hy'N, z, ball_subset_closedBall hz, hΨin z hz⟩
  have himg_sph : Ψ '' sphere 0 1 = {y | ‖Q y‖ = 1} := by
    apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact (hnorm_eq z (sphere_subset_closedBall hz)).2 hz
    · intro y hy
      have hy' : ‖Q y‖ ≤ 1 := le_of_eq hy
      have : y ∈ Ψ '' closedBall 0 1 := by rw [himg_cb]; exact hy'
      obtain ⟨z, hz, rfl⟩ := this
      exact ⟨z, (hnorm_eq z hz).1 hy, rfl⟩
  refine ⟨Ψ, hΨin, hcont, hinj, himg_cb, himg_sph, hBQc, fun z₀ h₀ => ⟨δf z₀ h₀, hδf z₀ h₀,
    Ef z₀ h₀, hEd z₀ h₀, hEder z₀ h₀, hQE z₀ h₀, hΨE z₀ h₀⟩⟩

/-- **The closed-disk homeomorphism.** -/
theorem closed_disk_homeomorph :
    ∃ Ψ : ℂ → ℂ, ∃ e : closedBall (0 : ℂ) 1 ≃ₜ {y | ‖Q y‖ ≤ 1},
      (∀ z, (e z : ℂ) = Ψ z) ∧ (∀ z ∈ ball (0 : ℂ) 1, Ψ z = ψ z) ∧
      Ψ '' sphere 0 1 = {y | ‖Q y‖ = 1} ∧ (∀ z ∈ closedBall (0 : ℂ) 1, Q (Ψ z) = B z) ∧
      ∀ z₀ ∈ sphere (0 : ℂ) 1, ∃ δ > 0, ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (ball z₀ δ) ∧
        (∀ z ∈ ball z₀ δ, deriv E z ≠ 0) ∧ (∀ z ∈ ball z₀ δ, Q (E z) = B z) ∧
        ∀ z ∈ ball z₀ δ ∩ closedBall 0 1, E z = Ψ z := by
  obtain ⟨Ψ, hin, hc, hinj, hcb, hsph, hQB, hloc⟩ :=
    closed_disk_extension hQ hQ' hK hψd hψi himg hB hn hBQ
  let F : closedBall (0 : ℂ) 1 → {y | ‖Q y‖ ≤ 1} := fun z =>
    ⟨Ψ z, by rw [← hcb]; exact mem_image_of_mem _ z.2⟩
  have hFc : Continuous F :=
    ((continuousOn_iff_continuous_restrict.1 hc)).subtype_mk _
  have hFi : Function.Injective F := fun a b h => Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val h))
  have hFs : Function.Surjective F := by
    rintro ⟨y, hy⟩
    rw [← hcb] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨⟨z, hz⟩, rfl⟩
  haveI : CompactSpace (closedBall (0 : ℂ) 1) := isCompact_iff_compactSpace.1 (isCompact_closedBall 0 1)
  exact ⟨Ψ, hFc.homeoOfEquivCompactToT2 (f := Equiv.ofBijective F ⟨hFi, hFs⟩), fun z => rfl, hin,
    hsph, hQB, hloc⟩

end SteklovBordered
