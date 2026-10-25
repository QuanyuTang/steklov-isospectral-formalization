module

public import RequestProject.RegularCover
public import RequestProject.FullMonodromy

/-!
# The unbranched regular `GL(3, 𝔽₂)` cover of `ℂ \ {0, 1}` from the degree-seven polynomial

For `s² = -7` let `p_s` be the explicit degree-seven polynomial with critical values `{0, 1}`, and
`proj : p_s⁻¹(ℂ \ {0,1}) → ℂ \ {0,1}` its covering projection. Take an ordering `f₀` of the fibre
over the base point `A` (the labelling `L` of `monodromy_full`) and the path component
`R = RegCov f₀` of the space of ordered complete fibres. We prove (`regular_cover`):

* `R → ℂ \ {0,1}` is a covering map and `R` is path connected;
* the deck group (`deckGroup f₀`, label permutations acting on the right) equals `ρ_L(G)` or
  `ρ_P(G)` (`G = GL(3, 𝔽₂)`), so it is isomorphic to `G` and has `168` elements;
* it acts freely, by homeomorphisms over the base, and transitively on every fibre, and every fibre
  of `R` has exactly `168` points (degree `168`, not `49`);
* the first-coordinate map `R → p_s⁻¹(ℂ \ {0,1})` is continuous, onto, compatible with the
  projections, and its fibres are exactly the orbits of the stabilizer of the label `0` in the
  deck group (the quotient by a point/line stabilizer recovers the degree-seven cover of `p_s`).

This is the **unbranched** part of the common regular cover over the base minus the branch
values; its completion over the branch values and the boundary as a bordered Riemann surface, and
the identification of the quotient by the other stabilizer with the cover of `p_{-s}`, are not
formalized here.
-/

@[expose] public section

open Polynomial Set Equiv PolyCover GL3F2 SteklovRegularCover

noncomputable section

namespace Degree7

variable {s : ℂ}

lemma locPathConnectedSpace_base (hs : s ^ 2 = -7) : LocPathConnectedSpace (Base (pPoly s)) :=
  (critVals_finite (pPoly_degree_pos hs)).isClosed.isOpen_compl.locPathConnectedSpace

/-- The ordered fibre tuple given by a labelling of the fibre over `A`. -/
def baseTuple {A : Base (pPoly s)} (L : proj (pPoly s) ⁻¹' {A} ≃ Fin 7) :
    OrdFib (proj (pPoly s)) 6 :=
  ⟨fun i => (L.symm i).1, fun i => (L.symm i).2.trans (L.symm 0).2.symm,
    fun _ _ h => L.symm.injective (Subtype.ext h)⟩

lemma ordProj_baseTuple {A : Base (pPoly s)} (L : proj (pPoly s) ⁻¹' {A} ≃ Fin 7) :
    ordProj _ 6 (baseTuple L) = A := (L.symm 0).2

/-- **Deck group via monodromy**: a label permutation is a deck transformation iff it is the
monodromy permutation (in the labelling `L`) of some loop at `A`. -/
theorem mem_deckGroup_iff {A : Base (pPoly s)} (L : proj (pPoly s) ⁻¹' {A} ≃ Fin 7)
    (σ : Perm (Fin 7)) :
    σ ∈ deckGroup (baseTuple L) ↔
      ∃ γ : Path.Homotopic.Quotient A A, L.permCongr (monodromyPerm (pPoly s) γ) = σ := by
  rw [mem_deckGroup, mem_regCov_iff (isCoveringMap _) (baseTuple L) (ordProj_baseTuple L)
    (permAct _ 6 σ (baseTuple L)) ((ordProj_permAct _ 6 σ _).trans (ordProj_baseTuple L))]
  refine exists_congr fun γ => ?_
  constructor
  · intro h
    ext i
    have h1 : L.symm (σ i) = monodromyPerm (pPoly s) γ (L.symm i) := Subtype.ext (h i)
    simp only [permCongr_apply]
    rw [← h1, apply_symm_apply]
  · intro h i
    subst h
    show (L.symm (L (monodromyPerm (pPoly s) γ (L.symm i)))).1 = _
    rw [symm_apply_apply]
    rfl

/-- **The unbranched regular `GL(3, 𝔽₂)` cover.** -/
theorem regular_cover (hs : s ^ 2 = -7) :
    ∃ (A : Base (pPoly s)) (f₀ : OrdFib (proj (pPoly s)) 6),
      ordProj _ 6 f₀ = A ∧
      IsCoveringMap (regProj f₀) ∧ PathConnectedSpace (RegCov f₀) ∧
      (deckGroup f₀ = rhoL.range ∨ deckGroup f₀ = rhoP.range) ∧
      Nonempty (G ≃* deckGroup f₀) ∧ Nat.card (deckGroup f₀) = 168 ∧
      (∀ (σ : deckGroup f₀) (f : RegCov f₀), regAct f₀ σ f = f → σ = 1) ∧
      (∀ f f' : RegCov f₀, regProj f₀ f = regProj f₀ f' → ∃ σ, regAct f₀ σ f = f') ∧
      Function.Surjective (regProj f₀) ∧
      (∀ x, Nat.card (regProj f₀ ⁻¹' {x}) = 168) ∧
      Continuous (evZero f₀) ∧ Function.Surjective (evZero f₀) ∧
      (∀ f, proj (pPoly s) (evZero f₀ f) = regProj f₀ f) ∧
      (∀ f f' : RegCov f₀, evZero f₀ f = evZero f₀ f' ↔
        ∃ σ : deckGroup f₀, σ.1 0 = 0 ∧ regAct f₀ σ f = f') := by
  obtain ⟨r, A, γ0, γ1, L, L', φ, -, -, -, -, -, -, -, hsurj, hmon⟩ := monodromy_full hs
  haveI := locPathConnectedSpace_base hs
  haveI := pathConnectedSpace_total (pPoly_degree_pos hs)
  have hcard : ∀ x, Nat.card (proj (pPoly s) ⁻¹' {x}) = 6 + 1 := card_fibre_pPoly hs
  set f₀ := baseTuple L
  -- the deck group is the image of the monodromy
  have hdeck : deckGroup f₀ = rhoL.range ∨ deckGroup f₀ = rhoP.range := by
    rcases hmon with h | h
    · left
      ext σ
      rw [mem_deckGroup_iff, MonoidHom.mem_range]
      constructor
      · rintro ⟨γ, rfl⟩; exact ⟨φ γ, ((h γ).1).symm⟩
      · rintro ⟨g, rfl⟩
        obtain ⟨γ, rfl⟩ := hsurj g
        exact ⟨γ, (h γ).1⟩
    · right
      ext σ
      rw [mem_deckGroup_iff, MonoidHom.mem_range]
      constructor
      · rintro ⟨γ, rfl⟩; exact ⟨φ γ, ((h γ).1).symm⟩
      · rintro ⟨g, rfl⟩
        obtain ⟨γ, rfl⟩ := hsurj g
        exact ⟨γ, (h γ).1⟩
  have hiso : Nonempty (G ≃* deckGroup f₀) := by
    rcases hdeck with h | h
    · rw [h]; exact ⟨MonoidHom.ofInjective rhoL_injective⟩
    · rw [h]; exact ⟨MonoidHom.ofInjective rhoP_injective⟩
  have hcardD : Nat.card (deckGroup f₀) = 168 := by
    obtain ⟨e⟩ := hiso
    rw [← Nat.card_congr e.toEquiv, card_G]
  have hsurjR : Function.Surjective (regProj f₀) := by
    intro x
    have hne : Nat.card (proj (pPoly s) ⁻¹' {x}) ≠ 0 := by rw [hcard]; omega
    obtain ⟨⟨e, he⟩⟩ := (Nat.card_ne_zero.1 hne).1
    obtain ⟨f, hf⟩ := evZero_surjective (isCoveringMap _) f₀ e
    exact ⟨f, by rw [← proj_evZero, hf, he]⟩
  refine ⟨A, f₀, ordProj_baseTuple L, isCoveringMap_regProj (isCoveringMap _) f₀, inferInstance,
    hdeck, hiso, hcardD, fun σ f h => regAct_eq_self h, fun f f' h => exists_regAct_eq hcard h,
    hsurjR, fun x => ?_, continuous_evZero f₀, evZero_surjective (isCoveringMap _) f₀,
    fun f => rfl, evZero_eq_iff hcard⟩
  obtain ⟨f, rfl⟩ := hsurjR x
  rw [card_regProj_fibre hcard f, hcardD]

end Degree7
