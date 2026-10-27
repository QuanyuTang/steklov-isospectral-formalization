module

public import Mathlib

/-!
# Inverses of injective holomorphic maps

* `HolInv.isOpen_image`: an injective holomorphic map on an open set is an open map.
* `HolInv.hasDerivAt_invFunOn`: the inverse is complex differentiable at points with `F' ≠ 0`.
* `HolInv.deriv_ne_zero_of_injOn`: an injective holomorphic map has nonvanishing derivative
  (proved via the removable singularity theorem applied to the inverse).
* `HolInv.exists_open_injOn_of_compact`: injectivity on a compact set plus local injectivity
  extends to injectivity on an open neighbourhood.
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace HolInv

variable {F : ℂ → ℂ} {U : Set ℂ}

lemma not_const_on_ball (hinj : InjOn F U) {z : ℂ} {ε : ℝ} (hε : 0 < ε) (hball : ball z ε ⊆ U) :
    ¬ ∃ w, ∀ x ∈ ball z ε, F x = w := by
  rintro ⟨w, hw⟩
  have h1 : z ∈ ball z ε := mem_ball_self hε
  have h2 : z + (ε / 2 : ℝ) ∈ ball z ε := by
    rw [mem_ball, dist_eq_norm]; simp [abs_of_pos hε]; linarith
  have := hinj (hball h1) (hball h2) ((hw _ h1).trans (hw _ h2).symm)
  have h3 : ((ε / 2 : ℝ) : ℂ) = 0 := by linear_combination -this
  have : (ε / 2 : ℝ) = 0 := by exact_mod_cast h3
  linarith

/-- An injective holomorphic map on an open set maps open subsets to open sets. -/
lemma isOpen_image (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {s : Set ℂ} (hs : s ⊆ U) (hso : IsOpen s) : IsOpen (F '' s) := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hso z hz
  have hA : AnalyticOnNhd ℂ F (ball z ε) :=
    (hF.mono (hball.trans hs)).analyticOnNhd isOpen_ball
  rcases hA.is_constant_or_isOpen (convex_ball z ε).isPreconnected with h | h
  · exact absurd h (not_const_on_ball hinj hε (hball.trans hs))
  · exact ⟨F '' ball z ε, image_mono hball, h _ subset_rfl isOpen_ball, ⟨z, mem_ball_self hε, rfl⟩⟩

lemma invFunOn_apply_self (hinj : InjOn F U) {z : ℂ} (hz : z ∈ U) :
    Function.invFunOn F U (F z) = z := hinj.leftInvOn_invFunOn hz

lemma continuousAt_invFunOn (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : ContinuousAt (Function.invFunOn F U) (F z) := by
  rw [ContinuousAt, invFunOn_apply_self hinj hz]
  intro N hN
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (inter_mem hN (hU.mem_nhds hz))
  have hopen := isOpen_image hF hinj (hball.trans inter_subset_right) isOpen_ball
  refine Filter.mem_map.2 (Filter.mem_of_superset (hopen.mem_nhds ⟨z, mem_ball_self hε, rfl⟩) ?_)
  rintro _ ⟨x, hx, rfl⟩
  show Function.invFunOn F U (F x) ∈ N
  rw [invFunOn_apply_self hinj (hball hx).2]
  exact (hball hx).1

lemma eventually_apply_invFunOn (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : ∀ᶠ y in 𝓝 (F z), F (Function.invFunOn F U y) = y := by
  filter_upwards [(isOpen_image hF hinj subset_rfl hU).mem_nhds ⟨z, hz, rfl⟩] with y hy
  exact Function.invFunOn_eq hy

/-- The inverse of an injective holomorphic map is complex differentiable where `F' ≠ 0`. -/
lemma hasDerivAt_invFunOn (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {z : ℂ} (hz : z ∈ U) (hF' : deriv F z ≠ 0) :
    HasDerivAt (Function.invFunOn F U) (deriv F z)⁻¹ (F z) := by
  refine HasDerivAt.of_local_left_inverse (continuousAt_invFunOn hU hF hinj hz) ?_ hF'
    (eventually_apply_invFunOn hU hF hinj hz)
  rw [invFunOn_apply_self hinj hz]
  exact (hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt

/-- **An injective holomorphic map has nonvanishing derivative.** -/
theorem deriv_ne_zero_of_injOn (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (hinj : InjOn F U)
    {z : ℂ} (hz : z ∈ U) : deriv F z ≠ 0 := by
  intro h0
  have hA : AnalyticAt ℂ (deriv F) z := (hF.analyticOnNhd hU z hz).deriv
  rcases hA.eventually_eq_zero_or_eventually_ne_zero with h | h
  · obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h.and (hU.mem_nhds hz))
    apply not_const_on_ball hinj hr (fun x hx => (hball x hx).2)
    refine ⟨F z, fun x hx => ?_⟩
    exact isOpen_ball.is_const_of_deriv_eq_zero (convex_ball z r).isPreconnected
      (hF.mono fun y hy => (hball y hy).2) (fun y hy => (hball y hy).1) hx (mem_ball_self hr)
  · rw [eventually_nhdsWithin_iff] at h
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (h.and (hU.mem_nhds hz))
    set G := Function.invFunOn F U
    have hBU : ball z r ⊆ U := fun x hx => (hball x hx).2
    set W := F '' ball z r
    have hWo : IsOpen W := isOpen_image hF hinj hBU isOpen_ball
    have hW : W ∈ 𝓝 (F z) := hWo.mem_nhds ⟨z, mem_ball_self hr, rfl⟩
    have hGd : DifferentiableOn ℂ G (W \ {F z}) := by
      rintro _ ⟨⟨x, hx, rfl⟩, hne⟩
      have hxz : x ≠ z := fun e => hne (by rw [e]; rfl)
      exact (hasDerivAt_invFunOn hU hF hinj (hBU hx)
        ((hball x hx).1 hxz)).differentiableAt.differentiableWithinAt
    have hGW : DifferentiableOn ℂ G W :=
      (Complex.differentiableOn_compl_singleton_and_continuousAt_iff hW).1
        ⟨hGd, continuousAt_invFunOn hU hF hinj hz⟩
    have hGz : HasDerivAt G (deriv G (F z)) (F z) :=
      (hGW.differentiableAt hW).hasDerivAt
    have hFz : HasDerivAt F 0 z := by
      rw [← h0]; exact (hF.differentiableAt (hU.mem_nhds hz)).hasDerivAt
    have hcomp := hGz.comp z hFz
    rw [mul_zero] at hcomp
    have hid : HasDerivAt (G ∘ F) 1 z := by
      refine (hasDerivAt_id z).congr_of_eventuallyEq ?_
      filter_upwards [hU.mem_nhds hz] with x hx
      exact invFunOn_apply_self hinj hx
    exact zero_ne_one (hcomp.unique hid)


/-- Injectivity on a compact set together with local injectivity at its points gives injectivity
on an open neighbourhood. -/
theorem exists_open_injOn_of_compact {K : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hFc : ContinuousOn F U) (hinjK : InjOn F K)
    (hloc : ∀ z ∈ K, ∃ r > 0, InjOn F (ball z r)) :
    ∃ V : Set ℂ, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧ InjOn F V := by
  choose r hr hrinj using hloc
  set O : Set (ℂ × ℂ) := ⋃ z, ⋃ (hz : z ∈ K), ball z (r z hz) ×ˢ ball z (r z hz) with hO
  have hOo : IsOpen O := isOpen_iUnion fun z => isOpen_iUnion fun hz =>
    isOpen_ball.prod isOpen_ball
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  set L := cthickening δ₀ K
  have hLU : L ×ˢ L ⊆ U ×ˢ U := prod_mono hsub hsub
  set C : Set (ℂ × ℂ) := ((L ×ˢ L) ∩ (fun p : ℂ × ℂ => F p.1 - F p.2) ⁻¹' {0}) \ O with hC
  have hCc : IsClosed C := by
    refine IsClosed.sdiff ?_ hOo
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_
      (isClosed_cthickening.prod isClosed_cthickening) isClosed_singleton
    refine ContinuousOn.sub ?_ ?_
    · exact (hFc.comp continuousOn_fst fun p hp => (hLU hp).1)
    · exact (hFc.comp continuousOn_snd fun p hp => (hLU hp).2)
  have hKC : K ×ˢ K ⊆ Cᶜ := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨⟨_, hab⟩, hnO⟩
    simp only at ha hb
    have hab' : F a = F b := sub_eq_zero.1 hab
    have := hinjK ha hb hab'
    subst this
    exact hnO (mem_iUnion.2 ⟨a, mem_iUnion.2 ⟨ha, mem_ball_self (hr a ha),
      mem_ball_self (hr a ha)⟩⟩)
  obtain ⟨ε, hε, hth⟩ := (hK.prod hK).exists_thickening_subset_open hCc.isOpen_compl hKC
  refine ⟨thickening (min ε δ₀) K, isOpen_thickening,
    self_subset_thickening (lt_min hε hδ₀) K, ?_, ?_⟩
  · exact (thickening_subset_cthickening _ _).trans
      ((cthickening_mono (min_le_right _ _) K).trans hsub)
  · intro x hx y hy hxy
    have hxL : x ∈ L := (thickening_subset_cthickening _ _).trans
      (cthickening_mono (min_le_right _ _) K) hx
    have hyL : y ∈ L := (thickening_subset_cthickening _ _).trans
      (cthickening_mono (min_le_right _ _) K) hy
    obtain ⟨a, ha, hxa⟩ := mem_thickening_iff.1 hx
    obtain ⟨b, hb, hyb⟩ := mem_thickening_iff.1 hy
    have hxy_th : (x, y) ∈ thickening ε (K ×ˢ K) := by
      refine mem_thickening_iff.2 ⟨(a, b), ⟨ha, hb⟩, ?_⟩
      rw [Prod.dist_eq]
      exact max_lt (hxa.trans_le (min_le_left _ _)) (hyb.trans_le (min_le_left _ _))
    have hnC := hth hxy_th
    by_contra hne
    apply hnC
    refine ⟨⟨⟨hxL, hyL⟩, by simp [hxy]⟩, ?_⟩
    intro hmem
    obtain ⟨z, hz⟩ := mem_iUnion.1 hmem
    obtain ⟨hzK, hz⟩ := mem_iUnion.1 hz
    exact hne (hrinj z hzK hz.1 hz.2 hxy)

/-- A holomorphic map with nonzero derivative is injective on a small ball. -/
lemma exists_ball_injOn (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) {z : ℂ} (hz : z ∈ U)
    (hF' : deriv F z ≠ 0) : ∃ r > 0, InjOn F (ball z r) := by
  have hs : HasStrictDerivAt F (deriv F z) z := (hF.analyticOnNhd hU z hz).hasStrictDerivAt
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (hs.eventually_left_inverse hF')
  refine ⟨r, hr, fun x hx y hy hxy => ?_⟩
  rw [← hball x hx, ← hball y hy, hxy]

/-- **Holomorphic inverse near the closed disk.**  A map holomorphic near `𝔻̄`, injective on `𝔻̄`
with `F' ≠ 0` on `𝕋`, is injective with nonvanishing derivative on an open neighbourhood of
`𝔻̄`. -/
theorem exists_open_nbhd_injOn_deriv_ne_zero (hU : IsOpen U) (hcb : closedBall (0 : ℂ) 1 ⊆ U)
    (hF : DifferentiableOn ℂ F U) (hinj : InjOn F (closedBall 0 1))
    (hF' : ∀ z ∈ sphere (0 : ℂ) 1, deriv F z ≠ 0) :
    ∃ U' : Set ℂ, IsOpen U' ∧ closedBall 0 1 ⊆ U' ∧ U' ⊆ U ∧ InjOn F U' ∧
      ∀ z ∈ U', deriv F z ≠ 0 := by
  have hd : ∀ z ∈ closedBall (0 : ℂ) 1, deriv F z ≠ 0 := by
    intro z hz
    rcases (mem_closedBall.1 hz).lt_or_eq with h | h
    · exact deriv_ne_zero_of_injOn isOpen_ball (hF.mono (ball_subset_closedBall.trans hcb))
        (hinj.mono ball_subset_closedBall) (mem_ball.2 h)
    · exact hF' z (mem_sphere.2 h)
  set U₁ := U ∩ deriv F ⁻¹' {0}ᶜ
  have hU₁ : IsOpen U₁ := ((hF.deriv hU).continuousOn).isOpen_inter_preimage hU
    isClosed_singleton.isOpen_compl
  have hcb₁ : closedBall (0 : ℂ) 1 ⊆ U₁ := fun z hz => ⟨hcb hz, hd z hz⟩
  obtain ⟨V, hV, hKV, hVU, hVinj⟩ := exists_open_injOn_of_compact (isCompact_closedBall 0 1) hU₁
    hcb₁ (hF.continuousOn.mono inter_subset_left) hinj
    (fun z hz => exists_ball_injOn hU hF (hcb hz) (hd z hz))
  exact ⟨V, hV, hKV, hVU.trans inter_subset_left, hVinj, fun z hz => (hVU hz).2⟩

end HolInv
