module

public import RequestProject.Degree7QuotientSpace

/-!
# The quotient interiors are the unit disk with projection `B_j`

For the paper's normalized disk covers `(ψ_j, B_j)` of `Q_j = paperQ (monicP (±s) a_j) τ ε`
(`IsNormalizedDiskCover`: `ψ_j` a normalized injective holomorphic map of `𝔻` onto the component
of `Q_j⁻¹(𝔻)` through `0`, `B_j = Q_j ∘ ψ_j` a Blaschke product), we show
(`quotient_interior_disk`): for all small `ε > 0`,

* `Q_j⁻¹(𝔻)` is connected, so `ψ_j : 𝔻 ≃ₜ Q_j⁻¹(𝔻)` (`exists_homeomorph_of_normalizedDiskCover`,
  using the open mapping theorem);
* hence there is a homeomorphism `Θ_j : (interior M_ε) / H_j ≃ₜ 𝔻` with
  `ψ_j (Θ_j [w]) = τ ε · Ev_j(w) / a_j` and `B_j (Θ_j [w]) = A_ε(π̄ w)`:
  the actual quotient `X_j° = (interior M_ε)/H_j` is the unit disk, on which the projection
  induced by `A_ε ∘ π̄` is exactly the paper's Blaschke product `B_j`.
-/

@[expose] public section

open Polynomial Set PolyCover LocalMonodromy SteklovRegularCover SteklovPunctured SteklovFill
  SteklovRiemann Topology Manifold SteklovCritical SteklovCoalescence GL3F2 Metric Filter

noncomputable section

namespace SteklovBordered

/-- A normalized disk cover whose domain `Q⁻¹(𝔻)` is connected is a homeomorphism of `𝔻` onto
it. -/
theorem exists_homeomorph_of_normalizedDiskCover {Q ψ B : ℂ → ℂ} {n : ℕ}
    (hc : IsNormalizedDiskCover Q n ψ B) (hconn : IsPreconnected (Q ⁻¹' ball 0 1)) :
    ∃ Ψ : ball (0 : ℂ) 1 ≃ₜ (Q ⁻¹' ball 0 1), ∀ z, (Ψ z : ℂ) = ψ z := by
  obtain ⟨hdiff, hinj, h0, -, -, himg, -, -⟩ := hc
  set S := Q ⁻¹' ball (0 : ℂ) 1
  have h0S : (0 : ℂ) ∈ S := by
    have : ψ 0 ∈ ψ '' ball (0 : ℂ) 1 := mem_image_of_mem _ (mem_ball_self one_pos)
    rw [himg, h0] at this
    exact connectedComponentIn_subset _ _ this
  have himg' : ψ '' ball (0 : ℂ) 1 = S := by rw [himg, hconn.connectedComponentIn h0S]
  have hmaps : ∀ z : ball (0 : ℂ) 1, ψ z ∈ S := fun z => himg' ▸ mem_image_of_mem _ z.2
  let F : ball (0 : ℂ) 1 → S := fun z => ⟨ψ z, hmaps z⟩
  have hFinj : Function.Injective F := fun z z' h =>
    Subtype.ext (hinj z.2 z'.2 (congrArg Subtype.val h))
  have hFsurj : Function.Surjective F := by
    rintro ⟨y, hy⟩
    rw [← himg'] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨⟨z, hz⟩, rfl⟩
  have hFc : Continuous F :=
    (continuousOn_iff_continuous_restrict.1 hdiff.continuousOn).subtype_mk _
  have han : AnalyticOnNhd ℂ ψ (ball 0 1) := hdiff.analyticOnNhd isOpen_ball
  have hopen : ∀ s ⊆ ball (0 : ℂ) 1, IsOpen s → IsOpen (ψ '' s) := by
    rcases han.is_constant_or_isOpen (convex_ball (0 : ℂ) 1).isPreconnected with ⟨w, hw⟩ | h
    · exfalso
      have h1 : (1 / 2 : ℂ) ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff]; norm_num
      have := hinj (mem_ball_self one_pos) h1 (by rw [hw 0 (mem_ball_self one_pos), hw _ h1])
      norm_num at this
    · exact h
  have hFo : IsOpenMap F := by
    intro U hU
    obtain ⟨V, hV, rfl⟩ := isOpen_induced_iff.1 hU
    have hsub : V ∩ ball (0 : ℂ) 1 ⊆ ball 0 1 := inter_subset_right
    have hO := hopen _ hsub (hV.inter isOpen_ball)
    refine isOpen_induced_iff.2 ⟨_, hO, ?_⟩
    ext ⟨y, hy⟩
    simp only [mem_preimage, mem_image, Subtype.exists, F, Subtype.mk.injEq]
    constructor
    · rintro ⟨z, ⟨hzV, hz⟩, rfl⟩
      exact ⟨z, hz, hzV, rfl⟩
    · rintro ⟨z, hz, hzV, rfl⟩
      exact ⟨z, ⟨hzV, hz⟩, rfl⟩
  exact ⟨(Equiv.ofBijective F ⟨hFinj, hFsurj⟩).toHomeomorphOfContinuousOpen hFc hFo,
    fun z => rfl⟩

end SteklovBordered

namespace Degree7

variable {s : ℂ}

/-- `Q_j⁻¹(𝔻)` is connected for small `ε` (Lemma 3.2.1 and the scaling `z ↦ τ ε z`). -/
lemma eventually_isPreconnected_paperQ (hs : s ^ 2 = -7) {a : ℂ} (ha : a ^ 7 = -bconst s)
    {τ : ℝ → ℂ} (hτ : ∀ ε, τ ε ^ 7 = (lamStar - 1) * ε) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsPreconnected (paperQ (monicP s a) τ ε ⁻¹' ball 0 1) := by
  filter_upwards [SteklovDiskCovers.lemma_3_2_1 (monicP_monic s a)
    (SteklovDiskCovers.critVals_monicP hs ha), self_mem_nhdsWithin] with ε hε hε0
  have hτ0 : τ ε ≠ 0 := by
    intro h
    have := hτ ε
    rw [h, zero_pow (by norm_num)] at this
    exact mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast (ne_of_gt hε0)) this.symm
  have heq : paperQ (monicP s a) τ ε ⁻¹' ball 0 1 =
      (fun z => τ ε * z) '' SteklovDiskCovers.coverDomain (monicP s a) ε := by
    ext z
    simp only [mem_preimage, mem_image, SteklovDiskCovers.coverDomain]
    constructor
    · intro hz
      refine ⟨z / τ ε, ?_, by field_simp⟩
      show (SteklovDiskCovers.coverPoly (monicP s a) ε).eval (z / τ ε) ∈ ball 0 1
      rw [SteklovDiskCovers.eval_coverPoly]
      exact hz
    · rintro ⟨w, hw, rfl⟩
      show paperQ (monicP s a) τ ε (τ ε * w) ∈ ball 0 1
      have : paperQ (monicP s a) τ ε (τ ε * w) =
          (SteklovDiskCovers.coverPoly (monicP s a) ε).eval w := by
        rw [paperQ, SteklovDiskCovers.eval_coverPoly, mul_div_cancel_left₀ _ hτ0]
      rw [this]
      exact hw
  rw [heq]
  exact hε.1.2.isPreconnected.image _ (continuous_const.mul continuous_id).continuousOn

/-- The open quotient for one label, from the quotient identification and the normalized disk
cover. -/
lemma quotient_disk_of {S : Set ℂ} {Qt : Type*} [TopologicalSpace Qt] {Q ψ B : ℂ → ℂ}
    (hc : IsNormalizedDiskCover Q 7 ψ B) (hconn : IsPreconnected (Q ⁻¹' ball 0 1))
    (hS : S = {z | ‖Q z‖ < 1}) (Φ : Qt ≃ₜ S) :
    ∃ Θ : Qt ≃ₜ ball (0 : ℂ) 1, ∀ x, ψ (Θ x) = Φ x ∧ B (Θ x) = Q (Φ x) := by
  subst hS
  obtain ⟨Ψ, hΨ⟩ := SteklovBordered.exists_homeomorph_of_normalizedDiskCover hc hconn
  have hset : {z | ‖Q z‖ < 1} = Q ⁻¹' ball 0 1 := by ext z; simp
  let Φ' : Qt ≃ₜ Q ⁻¹' ball 0 1 := Φ.trans (Homeomorph.setCongr hset)
  refine ⟨Φ'.trans Ψ.symm, fun x => ⟨?_, ?_⟩⟩
  · rw [Homeomorph.trans_apply, ← hΨ (Ψ.symm (Φ' x)), Homeomorph.apply_symm_apply]; rfl
  · rw [Homeomorph.trans_apply, hc.2.2.2.2.2.2.2 _ (Ψ.symm (Φ' x)).2,
      ← hΨ (Ψ.symm (Φ' x)), Homeomorph.apply_symm_apply]; rfl

/-- **The actual open quotients `X_j° = (interior M_ε)/H_j` are the unit disk, with projection
`B_j`.**  With the ordered fibre `f₀` and quotient maps `Ev₁, Ev₂` of `actual_quotient_spaces`:
for all `a_P, a_L` with `a_P⁷ = -b_s`, `a_L⁷ = -b_{-s}`, every `τ` with `τ(ε)⁷ = (λ_* - 1)ε`, for
all sufficiently small `ε > 0` and all normalized disk covers `(ψ_P, B_P)`, `(ψ_L, B_L)` of
`paperQ (monicP s a_P) τ ε`, `paperQ (monicP (-s) a_L) τ ε` (the paper's family), there are
homeomorphisms `Θ_P : (interior M_ε)/H_P ≃ₜ 𝔻`, `Θ_L : (interior M_ε)/H_L ≃ₜ 𝔻` with
`ψ_j (Θ_j [w]) = τ ε · Ev_j(w) / a_j` and `B_j (Θ_j [w]) = A_ε(π̄ w)`. -/
theorem quotient_interior_disk (hs : s ^ 2 = -7) :
    ∃ f₀ : OrdFib (projSum hs) 13,
      Nonempty (G ≃* deckGroup f₀) ∧ Nat.card (deckGroup f₀) = 168 ∧
      ∃ Ev₁ Ev₂ : RegFill hs f₀ → ℂ,
        (∀ w, (pPoly s).eval (Ev₁ w) = regFillProj hs f₀ w) ∧
        (∀ w, (pPoly (-s)).eval (Ev₂ w) = regFillProj hs f₀ w) ∧
        (∀ w w', Ev₁ w = Ev₁ w' ↔ (orbSetoid hs f₀ (stabSub f₀ 0)) w w') ∧
        (∀ w w', Ev₂ w = Ev₂ w' ↔ (orbSetoid hs f₀ (stabSub f₀ 7)) w w') ∧
        ∀ (aP aL : ℂ), aP ^ 7 = -bconst s → aL ^ 7 = -bconst (-s) →
        ∀ (τ : ℝ → ℂ), (∀ ε, τ ε ^ 7 = (lamStar - 1) * ε) →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ψP BP ψL BL : ℂ → ℂ,
          IsNormalizedDiskCover (paperQ (monicP s aP) τ ε) 7 ψP BP →
          IsNormalizedDiskCover (paperQ (monicP (-s) aL) τ ε) 7 ψL BL →
          (∃ Θ : QuotOn hs f₀ (interior (bordered hs f₀ ε)) (stabSub f₀ 0) ≃ₜ ball (0 : ℂ) 1,
            ∀ w, ψP (Θ (Quotient.mk _ w)) = τ ε * Ev₁ w / aP ∧
              BP (Θ (Quotient.mk _ w)) = bdf hs f₀ ε w) ∧
          (∃ Θ : QuotOn hs f₀ (interior (bordered hs f₀ ε)) (stabSub f₀ 7) ≃ₜ ball (0 : ℂ) 1,
            ∀ w, ψL (Θ (Quotient.mk _ w)) = τ ε * Ev₂ w / aL ∧
              BL (Θ (Quotient.mk _ w)) = bdf hs f₀ ε w) := by
  obtain ⟨f₀, hiso, hcard, Ev₁, Ev₂, e₁, e₂, fib₁, fib₂, H⟩ := actual_quotient_spaces hs
  have hs' : (-s) ^ 2 = -7 := by rw [neg_sq]; exact hs
  refine ⟨f₀, hiso, hcard, Ev₁, Ev₂, e₁, e₂, fib₁, fib₂, fun aP aL haP haL τ hτ => ?_⟩
  filter_upwards [eventually_isPreconnected_paperQ hs haP hτ,
    eventually_isPreconnected_paperQ hs' haL hτ,
    Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 3 by norm_num)] with ε hcP hcL hεI
  intro ψP BP ψL BL hP hL
  obtain ⟨h0, h1⟩ := hεI
  have hτ0 : τ ε ≠ 0 := by
    intro h
    have := hτ ε
    rw [h, zero_pow (by norm_num)] at this
    exact mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast h0.ne') this.symm
  obtain ⟨HP, HL⟩ := H ε h0 h1 τ hτ0
  obtain ⟨qP, -, -, ⟨ΦP, hΦP⟩, -⟩ := HP aP haP
  obtain ⟨qL, -, -, ⟨ΦL, hΦL⟩, -⟩ := HL aL haL
  obtain ⟨ΘP, hΘP⟩ := quotient_disk_of hP hcP rfl ΦP
  obtain ⟨ΘL, hΘL⟩ := quotient_disk_of hL hcL rfl ΦL
  refine ⟨⟨ΘP, fun w => ?_⟩, ⟨ΘL, fun w => ?_⟩⟩
  · obtain ⟨a1, a2⟩ := hΘP (Quotient.mk _ w)
    rw [hΦP] at a1 a2
    exact ⟨a1, by rw [a2, qP]⟩
  · obtain ⟨a1, a2⟩ := hΘL (Quotient.mk _ w)
    rw [hΦL] at a1 a2
    exact ⟨a1, by rw [a2, qL]⟩

end Degree7
