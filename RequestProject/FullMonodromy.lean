module

public import RequestProject.Pi1Generation

/-!
# The full monodromy representations of `p_s` and `p_{-s}`

For `s² = -7`, both `p_s` and `p_{-s}` are degree-seven coverings of the same base
`X = ℂ \ {0, 1}`.  We prove (`monodromy_full`) that there is a single surjective
anti-homomorphism `φ : π₁(X, -r) → G = GL(3, 𝔽₂)` (sending the standard generators to `x, y`)
such that, after labelling the fibres by `Fin 7`, the monodromy of **every** loop `γ` is
`ρ_L(φ γ)` for one of the polynomials and `ρ_P(φ γ)` for the other.  Thus the two coverings are
the quotients of one Galois covering with group `G` by a line stabilizer and by a point
stabilizer — the Gassmann-equivalent, nonconjugate pair.

Ingredients: the monodromy on the standard generators (`monodromy_rho`), the generation of
`π₁(X)` by the standard generators (`Pi1Gen.isStdLoops_generate`) and the injectivity of
`ρ_P`, `ρ_L`.
-/

@[expose] public section

open Polynomial Set Equiv PolyCover MonodromyRelation MonodromyTriple CoverIneq Pi1Gen GL3F2

noncomputable section

namespace Degree7

/-- **Abstract extension principle.**  Two anti-multiplicative maps from loop classes to
permutations which agree, on the generators, with `ρ₁ ∘ g` and `ρ₂ ∘ g` (`g` sending the
generators to `x, y`) agree with `ρ₁ ∘ φ` and `ρ₂ ∘ φ` on everything generated, for a common
surjective anti-homomorphism `φ`. -/
theorem extend_pair {P : ℂ[X]} {A : Base P}
    {γ0 γ1 : Path.Homotopic.Quotient A A} (hgen : ∀ γ, InGen γ0 γ1 γ)
    (ρ1 ρ2 : G →* Perm (Fin 7)) (hinj : Function.Injective ρ1)
    (M1 M2 : Path.Homotopic.Quotient A A → Perm (Fin 7))
    (h1refl : M1 (Path.Homotopic.Quotient.refl A) = 1)
    (h2refl : M2 (Path.Homotopic.Quotient.refl A) = 1)
    (h1trans : ∀ a b, M1 (a.trans b) = M1 b * M1 a) (h2trans : ∀ a b, M2 (a.trans b) = M2 b * M2 a)
    (h1symm : ∀ a, M1 a.symm = (M1 a)⁻¹) (h2symm : ∀ a, M2 a.symm = (M2 a)⁻¹)
    (h10 : M1 γ0 = ρ1 x) (h11 : M1 γ1 = ρ1 y) (h20 : M2 γ0 = ρ2 x) (h21 : M2 γ1 = ρ2 y) :
    ∃ φ : Path.Homotopic.Quotient A A → G, φ γ0 = x ∧ φ γ1 = y ∧
      (∀ a b, φ (a.trans b) = φ b * φ a) ∧ Function.Surjective φ ∧
      ∀ γ, M1 γ = ρ1 (φ γ) ∧ M2 γ = ρ2 (φ γ) := by
  have hex : ∀ γ, ∃ g, M1 γ = ρ1 g ∧ M2 γ = ρ2 g := by
    intro γ
    induction hgen γ with
    | refl => exact ⟨1, by rw [h1refl, map_one], by rw [h2refl, map_one]⟩
    | gen0 => exact ⟨x, h10, h20⟩
    | gen1 => exact ⟨y, h11, h21⟩
    | trans _ _ iha ihb =>
      obtain ⟨ga, ha1, ha2⟩ := iha
      obtain ⟨gb, hb1, hb2⟩ := ihb
      exact ⟨gb * ga, by rw [h1trans, ha1, hb1, map_mul], by rw [h2trans, ha2, hb2, map_mul]⟩
    | symm _ ih =>
      obtain ⟨g, h1, h2⟩ := ih
      exact ⟨g⁻¹, by rw [h1symm, h1, map_inv], by rw [h2symm, h2, map_inv]⟩
  choose φ hφ using hex
  have hφ1 : ∀ γ g, M1 γ = ρ1 g → φ γ = g := fun γ g h => hinj (by rw [← (hφ γ).1, h])
  have hmul : ∀ a b, φ (a.trans b) = φ b * φ a := fun a b =>
    hφ1 _ _ (by rw [h1trans, (hφ a).1, (hφ b).1, map_mul])
  refine ⟨φ, hφ1 _ _ h10, hφ1 _ _ h11, hmul, ?_, hφ⟩
  -- the range of `φ` is a subgroup containing `x, y`
  let S : Subgroup G :=
    { carrier := range φ
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨b.trans a, hmul b a⟩
      one_mem' := ⟨Path.Homotopic.Quotient.refl A, hφ1 _ _ (by rw [h1refl, map_one])⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨a.symm, hφ1 _ _ (by rw [h1symm, (hφ a).1, map_inv])⟩ }
  have hS : Subgroup.closure ({x, y} : Set G) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨γ0, hφ1 _ _ h10⟩
    · exact ⟨γ1, hφ1 _ _ h11⟩
  intro g
  have : g ∈ S := hS (by rw [closure_xy]; trivial)
  exact this

variable {s : ℂ}

/-- **The full monodromy representations of the two candidates.**  For `s² = -7` there are a base
point `-r` of `X = ℂ \ {0,1}`, the standard generators `γ₀, γ₁` there, labellings of the fibres of
`p_s` and `p_{-s}` over `-r` by `Fin 7`, and a surjective anti-homomorphism
`φ : π₁(X, -r) → G = GL(3, 𝔽₂)` with `φ γ₀ = x`, `φ γ₁ = y`, such that for **every** loop `γ` the
monodromy of `p_s` along `γ` is `ρ_L(φ γ)` and that of `p_{-s}` is `ρ_P(φ γ)`, or vice versa. -/
theorem monodromy_full (hs : s ^ 2 = -7) :
    ∃ (r : ℝ) (A : Base (pPoly s)) (γ0 γ1 : Path.Homotopic.Quotient A A)
      (L : proj (pPoly s) ⁻¹' {A} ≃ Fin 7)
      (L' : proj (pPoly (-s)) ⁻¹' {idBase (critVals_neg hs) A} ≃ Fin 7)
      (φ : Path.Homotopic.Quotient A A → G),
      0 < r ∧ r < 1 / 2 ∧ (A : ℂ) = -r ∧ IsStdLoops r γ0 γ1 ∧
      φ γ0 = x ∧ φ γ1 = y ∧ (∀ a b, φ (a.trans b) = φ b * φ a) ∧ Function.Surjective φ ∧
      ((∀ γ, L.permCongr (monodromyPerm (pPoly s) γ) = rhoL (φ γ) ∧
          L'.permCongr (monodromyPerm (pPoly (-s)) (γ.map (idBaseC (critVals_neg hs)))) =
            rhoP (φ γ)) ∨
        (∀ γ, L.permCongr (monodromyPerm (pPoly s) γ) = rhoP (φ γ) ∧
          L'.permCongr (monodromyPerm (pPoly (-s)) (γ.map (idBaseC (critVals_neg hs)))) =
            rhoL (φ γ))) := by
  have h := critVals_neg hs
  obtain ⟨r, A, γ0, γ1, A', γ0', γ1', L, L', hr, hr2, hA, hA', hs1, hs2, hrho⟩ :=
    monodromy_rho hs
  obtain rfl : A' = idBase h A := Subtype.ext (by rw [hA', idBase_val, hA])
  obtain ⟨rfl, rfl⟩ := isStdLoops_unique hs2 (isStdLoops_map h hs1)
  have hgen := isStdLoops_generate (critVals_pPoly hs) hr hr2 hs1
  let M1 : Path.Homotopic.Quotient A A → Perm (Fin 7) := fun γ =>
    L.permCongr (monodromyPerm (pPoly s) γ)
  let M2 : Path.Homotopic.Quotient A A → Perm (Fin 7) := fun γ =>
    L'.permCongr (monodromyPerm (pPoly (-s)) (γ.map (idBaseC h)))
  have h1refl : M1 (Path.Homotopic.Quotient.refl A) = 1 := by
    simp only [M1, ConjMonodromy.monodromyPerm_refl, permCongr_one']
  have h2refl : M2 (Path.Homotopic.Quotient.refl A) = 1 := by
    show L'.permCongr (monodromyPerm (pPoly (-s)) (Path.Homotopic.Quotient.refl (idBase h A))) = 1
    rw [ConjMonodromy.monodromyPerm_refl, permCongr_one']
  have h1trans : ∀ a b, M1 (a.trans b) = M1 b * M1 a := fun a b => by
    simp only [M1, monodromyPerm_trans, permCongr_mul]
  have h2trans : ∀ a b, M2 (a.trans b) = M2 b * M2 a := fun a b => by
    simp only [M2, quot_map_trans, monodromyPerm_trans, permCongr_mul]
  have h1symm : ∀ a, M1 a.symm = (M1 a)⁻¹ := fun a => by
    simp only [M1, ConjMonodromy.monodromyPerm_symm, permCongr_inv']
  have h2symm : ∀ a, M2 a.symm = (M2 a)⁻¹ := fun a => by
    simp only [M2, quot_map_symm, ConjMonodromy.monodromyPerm_symm, permCongr_inv']
  rcases hrho with ⟨h10, h11, h20, h21⟩ | ⟨h10, h11, h20, h21⟩
  · obtain ⟨φ, hx, hy, hmul, hsurj, hφ⟩ := extend_pair hgen rhoL rhoP rhoL_injective M1 M2
      h1refl h2refl h1trans h2trans h1symm h2symm h10 h11 h20 h21
    exact ⟨r, A, γ0, γ1, L, L', φ, hr, hr2, hA, hs1, hx, hy, hmul, hsurj, Or.inl hφ⟩
  · obtain ⟨φ, hx, hy, hmul, hsurj, hφ⟩ := extend_pair hgen rhoP rhoL rhoP_injective M1 M2
      h1refl h2refl h1trans h2trans h1symm h2symm h10 h11 h20 h21
    exact ⟨r, A, γ0, γ1, L, L', φ, hr, hr2, hA, hs1, hx, hy, hmul, hsurj, Or.inr hφ⟩

end Degree7
