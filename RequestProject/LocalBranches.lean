module

public import RequestProject.HolomorphicInverse

/-!
# Local branches of a holomorphic map near a regular value

Let `B` be holomorphic on an open set `W`, and `w₀` a value whose fibre `F₀ = B⁻¹(w₀) ∩ W` is
finite and consists of regular points, and assume `B` is proper near `w₀` (fibres over a
neighbourhood of `w₀` stay in a fixed compact subset of `W`).  Then there are holomorphic local
inverses `σ_p` (`p ∈ F₀`), `σ_p(w₀) = p`, `σ_p'(w₀) = 1/B'(p)`, such that for all `w` near `w₀`
the fibre `B⁻¹(w) ∩ W` is exactly `{σ_p(w) : p ∈ F₀}`, with the `σ_p(w)` pairwise distinct
(`exists_local_branches`).  This is the local structure of a branched covering over a regular
value, used to verify the local-branch hypothesis of the transplantation theorem.
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace HolInv

theorem exists_local_branches {B : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hB : DifferentiableOn ℂ B W) {w₀ : ℂ} (hfin : {p | p ∈ W ∧ B p = w₀}.Finite)
    (hreg : ∀ p ∈ {p | p ∈ W ∧ B p = w₀}, deriv B p ≠ 0) {L : Set ℂ} (hL : IsCompact L)
    (hLW : L ⊆ W) (hprop : ∀ᶠ w in 𝓝 w₀, ∀ p ∈ W, B p = w → p ∈ L) :
    ∃ σ : ℂ → ℂ → ℂ,
      (∀ p ∈ {p | p ∈ W ∧ B p = w₀}, σ p w₀ = p ∧ HasDerivAt (σ p) (deriv B p)⁻¹ w₀ ∧
        ContinuousAt (σ p) w₀ ∧ ∀ᶠ w in 𝓝 w₀, DifferentiableAt ℂ (σ p) w) ∧
      ∀ᶠ w in 𝓝 w₀, {p | p ∈ W ∧ B p = w} = (fun p => σ p w) '' {p | p ∈ W ∧ B p = w₀} ∧
        InjOn (fun p => σ p w) {p | p ∈ W ∧ B p = w₀} := by
  classical
  set F₀ := {p | p ∈ W ∧ B p = w₀} with hF₀
  -- radii of injectivity
  have hrad : ∀ p ∈ F₀, ∃ r > 0, ball p r ⊆ W ∧ InjOn B (ball p r) := by
    intro p hp
    obtain ⟨r₁, hr₁, hinj⟩ := exists_ball_injOn hW hB hp.1 (hreg p hp)
    obtain ⟨r₂, hr₂, hsub⟩ := Metric.isOpen_iff.1 hW p hp.1
    exact ⟨min r₁ r₂, lt_min hr₁ hr₂, (ball_subset_ball (min_le_right _ _)).trans hsub,
      hinj.mono (ball_subset_ball (min_le_left _ _))⟩
  choose! r hr hrW hrinj using hrad
  set σ : ℂ → ℂ → ℂ := fun p => Function.invFunOn B (ball p (r p)) with hσ
  have hBd : ∀ p ∈ F₀, DifferentiableOn ℂ B (ball p (r p)) := fun p hp => hB.mono (hrW p hp)
  have hσ0 : ∀ p ∈ F₀, σ p w₀ = p := fun p hp => by
    have := invFunOn_apply_self (hrinj p hp) (mem_ball_self (hr p hp))
    rwa [hp.2] at this
  have hσc : ∀ p ∈ F₀, ContinuousAt (σ p) w₀ := fun p hp => by
    have := continuousAt_invFunOn isOpen_ball (hBd p hp) (hrinj p hp) (mem_ball_self (hr p hp))
    rwa [hp.2] at this
  have himg : ∀ p ∈ F₀, B '' ball p (r p) ∈ 𝓝 w₀ := fun p hp => by
    refine (isOpen_image (hBd p hp) (hrinj p hp) subset_rfl isOpen_ball).mem_nhds ?_
    exact ⟨p, mem_ball_self (hr p hp), hp.2⟩
  refine ⟨σ, fun p hp => ⟨hσ0 p hp, ?_, hσc p hp, ?_⟩, ?_⟩
  · have := hasDerivAt_invFunOn isOpen_ball (hBd p hp) (hrinj p hp) (mem_ball_self (hr p hp))
      (hreg p hp)
    rwa [hp.2] at this
  · filter_upwards [himg p hp] with w ⟨q, hq, hqw⟩
    rw [← hqw]
    exact (hasDerivAt_invFunOn isOpen_ball (hBd p hp) (hrinj p hp) hq
      (deriv_ne_zero_of_injOn isOpen_ball (hBd p hp) (hrinj p hp) hq)).differentiableAt
  -- the fibre over nearby points
  set O := ⋃ p ∈ F₀, ball p (r p) with hO
  have hOo : IsOpen O := isOpen_biUnion fun p _ => isOpen_ball
  have hcK : IsCompact (B '' (L \ O)) :=
    (hL.diff hOo).image_of_continuousOn (hB.continuousOn.mono (diff_subset.trans hLW))
  have hw₀ : w₀ ∉ B '' (L \ O) := by
    rintro ⟨q, ⟨hqL, hqO⟩, hq⟩
    exact hqO (mem_biUnion ⟨hLW hqL, hq⟩ (mem_ball_self (hr q ⟨hLW hqL, hq⟩)))
  have hev1 : ∀ᶠ w in 𝓝 w₀, w ∉ B '' (L \ O) := hcK.isClosed.isOpen_compl.mem_nhds hw₀
  have hev2 : ∀ᶠ w in 𝓝 w₀, ∀ p ∈ F₀, w ∈ B '' ball p (r p) :=
    (eventually_all_finite hfin).2 fun p hp => himg p hp
  have hev3 : ∀ᶠ w in 𝓝 w₀, ∀ p ∈ F₀, ∀ p' ∈ F₀, p ≠ p' → σ p w ≠ σ p' w := by
    refine (eventually_all_finite hfin).2 fun p hp => (eventually_all_finite hfin).2
      fun p' hp' => ?_
    by_cases hpp : p = p'
    · exact Eventually.of_forall fun w h => absurd hpp h
    have hd : 0 < dist p p' := dist_pos.2 hpp
    have ht := (hσc p hp).tendsto.dist (hσc p' hp').tendsto
    rw [hσ0 p hp, hσ0 p' hp'] at ht
    filter_upwards [ht.eventually_const_lt hd] with w hw _
    exact fun h => by rw [h, dist_self] at hw; exact lt_irrefl _ hw
  filter_upwards [hev1, hev2, hev3, hprop] with w h1 h2 h3 h4
  refine ⟨?_, fun p hp p' hp' h => by_contra fun hne => h3 p hp p' hp' hne h⟩
  ext q
  simp only [mem_setOf_eq, mem_image]
  constructor
  · rintro ⟨hqW, hqw⟩
    have hqL := h4 q hqW hqw
    have hqO : q ∈ O := by
      by_contra hn
      exact h1 ⟨q, ⟨hqL, hn⟩, hqw⟩
    obtain ⟨p, hp, hqp⟩ := mem_iUnion₂.1 hqO
    refine ⟨p, hp, ?_⟩
    rw [← hqw]
    exact invFunOn_apply_self (hrinj p hp) hqp
  · rintro ⟨p, hp, rfl⟩
    have hmem : σ p w ∈ ball p (r p) := Function.invFunOn_mem (h2 p hp)
    exact ⟨hrW p hp hmem, Function.invFunOn_eq (h2 p hp)⟩

/-- Local branches pulled back along a continuous map `B₂`, together with local constancy of a
kernel `K` on the fibre product `{(z', p) | B₂ z' = B₁ p}`: this is exactly the local-branch
hypothesis of the transplantation theorem. -/
theorem exists_local_branches_comp {B₁ B₂ : ℂ → ℂ} {W : Set ℂ} (hW : IsOpen W)
    (hB₁ : DifferentiableOn ℂ B₁ W) {z' : ℂ} (hB₂ : ContinuousAt B₂ z')
    (hfin : {p | p ∈ W ∧ B₁ p = B₂ z'}.Finite)
    (hreg : ∀ p ∈ {p | p ∈ W ∧ B₁ p = B₂ z'}, deriv B₁ p ≠ 0) {L : Set ℂ} (hL : IsCompact L)
    (hLW : L ⊆ W) (hprop : ∀ᶠ w in 𝓝 (B₂ z'), ∀ p ∈ W, B₁ p = w → p ∈ L)
    (K : ℂ → ℂ → ℝ)
    (hK : ∀ p ∈ {p | p ∈ W ∧ B₁ p = B₂ z'},
      ∀ᶠ q in 𝓝 (z', p), B₂ q.1 = B₁ q.2 → K q.1 q.2 = K z' p) :
    ∃ σ : ℂ → ℂ → ℂ,
      (∀ p ∈ {p | p ∈ W ∧ B₁ p = B₂ z'}, σ p (B₂ z') = p ∧
        HasDerivAt (σ p) (deriv B₁ p)⁻¹ (B₂ z') ∧
        ∀ᶠ w'' in 𝓝 (B₂ z'), DifferentiableAt ℂ (σ p) w'') ∧
      ∀ᶠ z'' in 𝓝 z', {p | p ∈ W ∧ B₁ p = B₂ z''} =
          (fun p => σ p (B₂ z'')) '' {p | p ∈ W ∧ B₁ p = B₂ z'} ∧
        InjOn (fun p => σ p (B₂ z'')) {p | p ∈ W ∧ B₁ p = B₂ z'} ∧
        ∀ p ∈ {p | p ∈ W ∧ B₁ p = B₂ z'}, K z'' (σ p (B₂ z'')) = K z' p := by
  obtain ⟨σ, hσ, hev⟩ := exists_local_branches hW hB₁ hfin hreg hL hLW hprop
  refine ⟨σ, fun p hp => ⟨(hσ p hp).1, (hσ p hp).2.1, (hσ p hp).2.2.2⟩, ?_⟩
  have hev' := hB₂.eventually hev
  have hKev : ∀ᶠ z'' in 𝓝 z', ∀ p ∈ {p | p ∈ W ∧ B₁ p = B₂ z'},
      B₂ z'' = B₁ (σ p (B₂ z'')) → K z'' (σ p (B₂ z'')) = K z' p := by
    refine (eventually_all_finite hfin).2 fun p hp => ?_
    have ht : Tendsto (fun z'' => (z'', σ p (B₂ z''))) (𝓝 z') (𝓝 (z', p)) := by
      refine (tendsto_id.prodMk_nhds ?_)
      have := ((hσ p hp).2.2.1.tendsto.comp hB₂.tendsto)
      rwa [Function.comp_def, (hσ p hp).1] at this
    exact ht.eventually (hK p hp)
  filter_upwards [hev', hKev] with z'' ⟨hset, hinj⟩ hK'
  refine ⟨hset, hinj, fun p hp => hK' p hp ?_⟩
  have : σ p (B₂ z'') ∈ {q | q ∈ W ∧ B₁ q = B₂ z''} := by
    rw [hset]; exact ⟨p, hp, rfl⟩
  exact this.2.symm

end HolInv

end
