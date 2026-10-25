module

public import RequestProject.Degree7BorderedSurface

/-!
# The actual quotient spaces `R̄ / H` and `M_ε / H`

For a subgroup `H` of the deck group (`≅ GL(3, 𝔽₂)`) of the common regular cover, acting on the
branched completion `R̄ = RegFill hs f₀` by the extended deck transformations, we form the
**actual topological quotients** (`orbSetoid`, `QuotOn`):

* `R̄ / H = Quotient (orbSetoid hs f₀ H)`, and for an `H`-invariant subset `S ⊆ R̄`,
  `S / H = QuotOn hs f₀ S H` (the quotient of the subspace `S` by the restricted orbit relation),
  each with the quotient topology;

and identify them (`actual_quotient_spaces`), for the point stabilizer `H_P = {σ | σ 0 = 0}` and
the line stabilizer `H_L = {σ | σ 7 = 7}`, with the polynomial-cover objects of Lemma 3.2.1:

* `R̄ / H_P ≃ₜ ℂ`, `R̄ / H_L ≃ₜ ℂ` (induced by `Ev₁`, `Ev₂`; `p_{±s} ∘ Ev = π̄`);
* `M_ε / H ≃ₜ q_ε⁻¹(closed unit disk)` (the closure of the disk cover `Y_ε`),
  `(interior M_ε) / H ≃ₜ Y_ε = coverDomain p_{±s} ε`, `∂M_ε / H ≃ₜ q_ε⁻¹(unit circle)`;
* with the **paper's normalisations**: for `a⁷ = -b_{±s}` (the monic polynomial
  `monicP (±s) a = p_{±s}(a ·)`) and any `τ` with `τ ε ≠ 0`,
  `(interior M_ε) / H ≃ₜ paperQ (monicP (±s) a) τ ε ⁻¹' 𝔻` via `[w] ↦ τ ε · Ev(w) / a`, and
  `paperQ (monicP (±s) a) τ ε (τ ε · Ev(w) / a) = A_ε(π̄ w)`; the same for `M_ε` and the closed
  disk.

All the homeomorphisms are induced by the explicit maps (`Φ ⟦w⟧ = Ev w`); nothing about the
quotients is assumed.
-/

@[expose] public section

open Polynomial Set PolyCover LocalMonodromy SteklovRegularCover SteklovPunctured SteklovFill
  SteklovRiemann Topology Manifold SteklovCritical SteklovCoalescence GL3F2

noncomputable section

namespace SteklovBordered

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A continuous closed surjection whose fibres are the classes of `r` induces a homeomorphism
`X / r ≃ₜ Y`. -/
theorem exists_quotient_homeomorph (r : Setoid X) {f : X → Y} (hf : Continuous f)
    (hcl : IsClosedMap f) (hsurj : Function.Surjective f) (hker : ∀ x y, f x = f y ↔ r x y) :
    ∃ Φ : Quotient r ≃ₜ Y, ∀ x, Φ (Quotient.mk r x) = f x := by
  let F : Quotient r → Y := Quotient.lift f fun a b h => (hker a b).2 h
  have hinj : Function.Injective F := by
    intro a b h
    induction a using Quotient.inductionOn
    induction b using Quotient.inductionOn
    exact Quotient.sound ((hker _ _).1 h)
  have hsurjF : Function.Surjective F := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨Quotient.mk r x, rfl⟩
  have hcont : Continuous F := hf.quotient_lift _
  have hclF : IsClosedMap F := by
    intro C hC
    have : F '' C = f '' (Quotient.mk r ⁻¹' C) := by
      ext y
      constructor
      · rintro ⟨q, hq, rfl⟩
        induction q using Quotient.inductionOn with
        | h x => exact ⟨x, hq, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨Quotient.mk r x, hx, rfl⟩
    rw [this]
    exact hcl _ (hC.preimage continuous_quotient_mk')
  exact ⟨(Equiv.ofBijective F ⟨hinj, hsurjF⟩).toHomeomorphOfContinuousClosed hcont hclF,
    fun x => rfl⟩

/-- The restricted version: for a proper surjection `f` whose fibres are the classes of `r`, and
`S = f⁻¹(T)`, the quotient of the subspace `S` by the restricted relation is homeomorphic to `T`,
via `f`. -/
theorem exists_quotient_homeomorph_restrict (r : Setoid X) {f : X → Y} (hf : IsProperMap f)
    (hsurj : Function.Surjective f) (hker : ∀ x y, f x = f y ↔ r x y) (T : Set Y) (S : Set X)
    (hS : S = f ⁻¹' T) :
    ∃ Φ : Quotient (r.comap (Subtype.val : S → X)) ≃ₜ T,
      ∀ x : S, (Φ (Quotient.mk _ x) : Y) = f x := by
  subst hS
  have hp := hf.restrictPreimage T
  obtain ⟨Φ, hΦ⟩ := exists_quotient_homeomorph (r.comap (Subtype.val : f ⁻¹' T → X))
    hp.continuous hp.isClosedMap
    (fun y => by
      obtain ⟨x, hx⟩ := hsurj y.1
      exact ⟨⟨x, show f x ∈ T by rw [hx]; exact y.2⟩, Subtype.ext hx⟩)
    (fun x y => by
      rw [Setoid.comap_rel]
      exact (Subtype.ext_iff.trans (hker x.1 y.1)))
  exact ⟨Φ, fun x => by rw [hΦ]; rfl⟩

end SteklovBordered

namespace Degree7

variable {s : ℂ}

/-- The stabilizer of a label `k` in the deck group. -/
def stabSub {hs : s ^ 2 = -7} (f₀ : OrdFib (projSum hs) 13) (k : Fin 14) : Subgroup (deckGroup f₀) where
  carrier := {σ | σ.1 k = k}
  one_mem' := rfl
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [mem_setOf_eq] at hσ hτ ⊢
    rw [Subgroup.coe_mul, Equiv.Perm.mul_apply, hτ, hσ]
  inv_mem' := by
    intro σ hσ
    simp only [mem_setOf_eq] at hσ ⊢
    rw [Subgroup.coe_inv, Equiv.Perm.inv_eq_iff_eq, hσ]

/-- The orbit relation of a subgroup `H` acting by extended deck transformations. -/
def orbSetoid (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (H : Subgroup (deckGroup f₀)) :
    Setoid (RegFill hs f₀) where
  r w w' := ∃ σ ∈ H, regFillAct hs f₀ σ w = w'
  iseqv := by
    refine ⟨fun w => ⟨1, H.one_mem, by rw [regFillAct_one]; rfl⟩, ?_, ?_⟩
    · rintro w w' ⟨σ, hσ, rfl⟩
      refine ⟨σ⁻¹, H.inv_mem hσ, ?_⟩
      rw [← Function.comp_apply (f := regFillAct hs f₀ σ⁻¹), ← regFillAct_mul, mul_inv_cancel,
        regFillAct_one]
      rfl
    · rintro w w' w'' ⟨σ, hσ, rfl⟩ ⟨τ, hτ, rfl⟩
      exact ⟨σ * τ, H.mul_mem hσ hτ, by rw [regFillAct_mul]; rfl⟩

/-- The quotient `S / H` of an (invariant) subset `S ⊆ R̄`, with the quotient topology. -/
abbrev QuotOn (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (S : Set (RegFill hs f₀))
    (H : Subgroup (deckGroup f₀)) : Type _ :=
  Quotient ((orbSetoid hs f₀ H).comap (Subtype.val : S → RegFill hs f₀))

/-- The quotient `R̄ / H`. -/
abbrev QuotFill (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13)
    (H : Subgroup (deckGroup f₀)) : Type _ :=
  Quotient (orbSetoid hs f₀ H)

/-- The four quotient identifications induced by a map `Ev` with the properties established in
`quotient_ident`, together with the normalised version `w ↦ c · Ev w` (`c ≠ 0`). -/
theorem quotient_spaces_of_ev (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13)
    (H : Subgroup (deckGroup f₀)) {P : ℂ[X]} {Ev : RegFill hs f₀ → ℂ} (hpr : IsProperMap Ev)
    (hsurj : Function.Surjective Ev)
    (hfib : ∀ w w', Ev w = Ev w' ↔ ∃ σ ∈ H, regFillAct hs f₀ σ w = w')
    (hq : ∀ (ε : ℝ) w, (SteklovDiskCovers.coverPoly P ε).eval (Ev w) =
      affA ε (regFillProj hs f₀ w))
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 3) (c : ℂ) (hc : c ≠ 0) :
    (∃ Φ : QuotFill hs f₀ H ≃ₜ ℂ, ∀ w, Φ (Quotient.mk _ w) = c * Ev w) ∧
    (∃ Φ : QuotOn hs f₀ (bordered hs f₀ ε) H ≃ₜ
        {z : ℂ | ‖(SteklovDiskCovers.coverPoly P ε).eval (z / c)‖ ≤ 1},
      ∀ w, (Φ (Quotient.mk _ w) : ℂ) = c * Ev w) ∧
    (∃ Φ : QuotOn hs f₀ (interior (bordered hs f₀ ε)) H ≃ₜ
        {z : ℂ | ‖(SteklovDiskCovers.coverPoly P ε).eval (z / c)‖ < 1},
      ∀ w, (Φ (Quotient.mk _ w) : ℂ) = c * Ev w) ∧
    (∃ Φ : QuotOn hs f₀ (borderedBdry hs f₀ ε) H ≃ₜ
        {z : ℂ | ‖(SteklovDiskCovers.coverPoly P ε).eval (z / c)‖ = 1},
      ∀ w, (Φ (Quotient.mk _ w) : ℂ) = c * Ev w) := by
  set m : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ c hc
  set Ev' : RegFill hs f₀ → ℂ := fun w => c * Ev w
  have hpr' : IsProperMap Ev' := m.isProperMap.comp hpr
  have hsurj' : Function.Surjective Ev' := m.surjective.comp hsurj
  have hker : ∀ w w', Ev' w = Ev' w' ↔ (orbSetoid hs f₀ H) w w' := by
    intro w w'
    change _ ↔ ∃ σ ∈ H, regFillAct hs f₀ σ w = w'
    rw [← hfib]
    exact ⟨fun h => mul_left_cancel₀ hc h, fun h => by simp only [Ev', h]⟩
  have hval : ∀ w, (SteklovDiskCovers.coverPoly P ε).eval (Ev' w / c) = bdf hs f₀ ε w := by
    intro w
    simp only [Ev', mul_div_cancel_left₀ _ hc]
    exact hq ε w
  have hint := (regBorderedSurface hs f₀ h0 h1).2.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact SteklovBordered.exists_quotient_homeomorph _ hpr'.continuous hpr'.isClosedMap hsurj'
      hker
  · refine SteklovBordered.exists_quotient_homeomorph_restrict _ hpr' hsurj' hker _ _ ?_
    ext w; simp only [bordered_eq, mem_setOf_eq, mem_preimage, hval]
  · refine SteklovBordered.exists_quotient_homeomorph_restrict _ hpr' hsurj' hker _ _ ?_
    rw [hint]; ext w; simp only [mem_setOf_eq, mem_preimage, hval]
  · refine SteklovBordered.exists_quotient_homeomorph_restrict _ hpr' hsurj' hker _ _ ?_
    ext w; simp only [borderedBdry_eq, mem_setOf_eq, mem_preimage, hval]

/-- `paperQ` in terms of the normalised coordinate. -/
lemma paperQ_monicP_eq (hs : s ^ 2 = -7) {a : ℂ} (ha : a ^ 7 = -bconst s) (τ : ℝ → ℂ) (ε : ℝ)
    (z : ℂ) : paperQ (monicP s a) τ ε z =
      (SteklovDiskCovers.coverPoly (pPoly s) ε).eval (z / (τ ε / a)) := by
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [zero_pow (by norm_num)] at ha
    exact bconst_ne_zero hs (neg_eq_zero.1 ha.symm)
  rw [paperQ, monicP_eval hs ha, SteklovDiskCovers.eval_coverPoly, pPoly_eval]
  congr 3
  by_cases hτ : τ ε = 0
  · simp [hτ]
  · field_simp

/-- **The actual quotient spaces of the completed cover and of `M_ε`.**  For `s² = -7` there is
an ordered fibre `f₀` (deck group `≅ GL(3, 𝔽₂)`, order `168`) and the two quotient maps
`Ev₁, Ev₂ : R̄ → ℂ` of `completed_quotient_identifications` such that, for `H_P = stabSub f₀ 0`
and `H_L = stabSub f₀ 7`:
* the fibres of `Ev₁`, `Ev₂` are the `H_P`-, resp. `H_L`-orbits, and `p_{±s} ∘ Ev = π̄`;
* for every `0 < ε < 1/3`, every `a` with `a⁷ = -b_{s}` (resp. `a⁷ = -b_{-s}`) and every `τ`
  with `τ ε ≠ 0`, the induced maps `[w] ↦ τ ε · Ev(w) / a` are homeomorphisms
  `R̄ / H ≃ₜ ℂ`, `M_ε / H ≃ₜ {‖paperQ‖ ≤ 1}`, `(interior M_ε) / H ≃ₜ {‖paperQ‖ < 1}`,
  `∂M_ε / H ≃ₜ {‖paperQ‖ = 1}` for `paperQ = paperQ (monicP (±s) a) τ ε` (the paper's
  normalised polynomial disk covers), and `paperQ (τ ε · Ev(w) / a) = A_ε(π̄ w)`. -/
theorem actual_quotient_spaces (hs : s ^ 2 = -7) :
    ∃ f₀ : OrdFib (projSum hs) 13,
      Nonempty (G ≃* deckGroup f₀) ∧ Nat.card (deckGroup f₀) = 168 ∧
      ∃ Ev₁ Ev₂ : RegFill hs f₀ → ℂ,
        (∀ w, (pPoly s).eval (Ev₁ w) = regFillProj hs f₀ w) ∧
        (∀ w, (pPoly (-s)).eval (Ev₂ w) = regFillProj hs f₀ w) ∧
        (∀ w w', Ev₁ w = Ev₁ w' ↔ (orbSetoid hs f₀ (stabSub f₀ 0)) w w') ∧
        (∀ w w', Ev₂ w = Ev₂ w' ↔ (orbSetoid hs f₀ (stabSub f₀ 7)) w w') ∧
        ∀ (ε : ℝ), 0 < ε → ε < 1 / 3 → ∀ (τ : ℝ → ℂ), τ ε ≠ 0 →
        (∀ a : ℂ, a ^ 7 = -bconst s →
          (∀ w, paperQ (monicP s a) τ ε (τ ε * Ev₁ w / a) = bdf hs f₀ ε w) ∧
          (∃ Φ : QuotFill hs f₀ (stabSub f₀ 0) ≃ₜ ℂ,
            ∀ w, Φ (Quotient.mk _ w) = τ ε * Ev₁ w / a) ∧
          (∃ Φ : QuotOn hs f₀ (bordered hs f₀ ε) (stabSub f₀ 0) ≃ₜ
              {z : ℂ | ‖paperQ (monicP s a) τ ε z‖ ≤ 1},
            ∀ w, (Φ (Quotient.mk _ w) : ℂ) = τ ε * Ev₁ w / a) ∧
          (∃ Φ : QuotOn hs f₀ (interior (bordered hs f₀ ε)) (stabSub f₀ 0) ≃ₜ
              {z : ℂ | ‖paperQ (monicP s a) τ ε z‖ < 1},
            ∀ w, (Φ (Quotient.mk _ w) : ℂ) = τ ε * Ev₁ w / a) ∧
          (∃ Φ : QuotOn hs f₀ (borderedBdry hs f₀ ε) (stabSub f₀ 0) ≃ₜ
              {z : ℂ | ‖paperQ (monicP s a) τ ε z‖ = 1},
            ∀ w, (Φ (Quotient.mk _ w) : ℂ) = τ ε * Ev₁ w / a)) ∧
        (∀ a : ℂ, a ^ 7 = -bconst (-s) →
          (∀ w, paperQ (monicP (-s) a) τ ε (τ ε * Ev₂ w / a) = bdf hs f₀ ε w) ∧
          (∃ Φ : QuotFill hs f₀ (stabSub f₀ 7) ≃ₜ ℂ,
            ∀ w, Φ (Quotient.mk _ w) = τ ε * Ev₂ w / a) ∧
          (∃ Φ : QuotOn hs f₀ (bordered hs f₀ ε) (stabSub f₀ 7) ≃ₜ
              {z : ℂ | ‖paperQ (monicP (-s) a) τ ε z‖ ≤ 1},
            ∀ w, (Φ (Quotient.mk _ w) : ℂ) = τ ε * Ev₂ w / a) ∧
          (∃ Φ : QuotOn hs f₀ (interior (bordered hs f₀ ε)) (stabSub f₀ 7) ≃ₜ
              {z : ℂ | ‖paperQ (monicP (-s) a) τ ε z‖ < 1},
            ∀ w, (Φ (Quotient.mk _ w) : ℂ) = τ ε * Ev₂ w / a) ∧
          (∃ Φ : QuotOn hs f₀ (borderedBdry hs f₀ ε) (stabSub f₀ 7) ≃ₜ
              {z : ℂ | ‖paperQ (monicP (-s) a) τ ε z‖ = 1},
            ∀ w, (Φ (Quotient.mk _ w) : ℂ) = τ ε * Ev₂ w / a)) := by
  obtain ⟨f₀, hiso, hcard, Ev₁, Ev₂, -, -, e₁, e₂, fib₁, fib₂, su₁, su₂, pr₁, pr₂, c₁, c₂⟩ :=
    completed_quotient_identifications hs
  have hs' : (-s) ^ 2 = -7 := by rw [neg_sq]; exact hs
  refine ⟨f₀, hiso, hcard, Ev₁, Ev₂, e₁, e₂, fib₁, fib₂, fun ε h0 h1 τ hτ => ⟨?_, ?_⟩⟩
  · intro a ha
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [zero_pow (by norm_num)] at ha
      exact bconst_ne_zero hs (neg_eq_zero.1 ha.symm)
    have hc : τ ε / a ≠ 0 := div_ne_zero hτ ha0
    have hPQ := paperQ_monicP_eq hs ha τ ε
    have hmul : ∀ w, τ ε * Ev₁ w / a = τ ε / a * Ev₁ w := fun w => by ring
    obtain ⟨A1, A2, A3, A4⟩ := quotient_spaces_of_ev hs f₀ (stabSub f₀ 0) pr₁ su₁ fib₁ c₁ h0 h1
      (τ ε / a) hc
    refine ⟨fun w => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hPQ, hmul, mul_div_cancel_left₀ _ hc, c₁]; rfl
    · obtain ⟨Φ, hΦ⟩ := A1; exact ⟨Φ, fun w => by rw [hΦ, hmul]⟩
    · obtain ⟨Φ, hΦ⟩ := A2
      refine ⟨Φ.trans (Homeomorph.setCongr (by ext z; simp only [mem_setOf_eq, hPQ])),
        fun w => ?_⟩
      exact (hΦ w).trans (hmul w).symm
    · obtain ⟨Φ, hΦ⟩ := A3
      refine ⟨Φ.trans (Homeomorph.setCongr (by ext z; simp only [mem_setOf_eq, hPQ])),
        fun w => ?_⟩
      exact (hΦ w).trans (hmul w).symm
    · obtain ⟨Φ, hΦ⟩ := A4
      refine ⟨Φ.trans (Homeomorph.setCongr (by ext z; simp only [mem_setOf_eq, hPQ])),
        fun w => ?_⟩
      exact (hΦ w).trans (hmul w).symm
  · intro a ha
    have ha0 : a ≠ 0 := by
      rintro rfl; rw [zero_pow (by norm_num)] at ha
      exact bconst_ne_zero hs' (neg_eq_zero.1 ha.symm)
    have hc : τ ε / a ≠ 0 := div_ne_zero hτ ha0
    have hPQ := paperQ_monicP_eq hs' ha τ ε
    have hmul : ∀ w, τ ε * Ev₂ w / a = τ ε / a * Ev₂ w := fun w => by ring
    obtain ⟨A1, A2, A3, A4⟩ := quotient_spaces_of_ev hs f₀ (stabSub f₀ 7) pr₂ su₂ fib₂ c₂ h0 h1
      (τ ε / a) hc
    refine ⟨fun w => ?_, ?_, ?_, ?_, ?_⟩
    · rw [hPQ, hmul, mul_div_cancel_left₀ _ hc, c₂]; rfl
    · obtain ⟨Φ, hΦ⟩ := A1; exact ⟨Φ, fun w => by rw [hΦ, hmul]⟩
    · obtain ⟨Φ, hΦ⟩ := A2
      refine ⟨Φ.trans (Homeomorph.setCongr (by ext z; simp only [mem_setOf_eq, hPQ])),
        fun w => ?_⟩
      exact (hΦ w).trans (hmul w).symm
    · obtain ⟨Φ, hΦ⟩ := A3
      refine ⟨Φ.trans (Homeomorph.setCongr (by ext z; simp only [mem_setOf_eq, hPQ])),
        fun w => ?_⟩
      exact (hΦ w).trans (hmul w).symm
    · obtain ⟨Φ, hΦ⟩ := A4
      refine ⟨Φ.trans (Homeomorph.setCongr (by ext z; simp only [mem_setOf_eq, hPQ])),
        fun w => ?_⟩
      exact (hΦ w).trans (hmul w).symm

end Degree7
