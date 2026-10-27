module

public import RequestProject.Degree7QuotientSpace
public import RequestProject.Degree7CommonCover
public import RequestProject.Degree7Quotient

/-!
# The label stabilizers are the paper's `H_P`, `H_L` (up to a proved conjugacy and label swap)

For the ordered fibre `f₀` of the common regular cover, `common_regular_cover` proves that the deck
group `deckGroup f₀ ≤ Perm (Fin 14)` (label permutations of the ordered fibre) is the image of the
combined monodromy representation `combRho Φ Ψ` of `G = GL(3, 𝔽₂)`, where `(Φ, Ψ)` is
`(rhoP, rhoL)` or `(rhoL, rhoP)` (the point and line actions, coming from `monodromy_full`).

* `stab_label_iff`: for a transported coset action `ρ = conj c ∘ permCongr e ∘ (G ↷ G/H)`, the
  stabilizer of a label `i` is the conjugate `a H a⁻¹`, `a = out (e⁻¹ (c⁻¹ i))`.
* `deckIso`: the actual isomorphism `ι : G ≃* deckGroup f₀`, `ι g = combRho Φ Ψ g` (the
  ordered-fibre action).
* **`stabilizer_identification`**: under `ι`, `stabSub f₀ 0` and `stabSub f₀ 7` are explicit
  conjugates of `GL3F2.HP` and `GL3F2.HL` (in this order, or swapped).
* `actual_stabilizer_identification`: the same for the ordered fibre of
  `completed_quotient_identifications_deck`, which re-exports the completed quotient maps together
  with the deck-group description.
-/

@[expose] public section

open Polynomial Set PolyCover LocalMonodromy SteklovRegularCover SteklovPunctured SteklovFill
  SteklovRiemann Topology Manifold SteklovCritical SteklovCoalescence GL3F2 Equiv
open scoped ContDiff

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Degree7

variable {s : ℂ}

/-- **Stabilizer of a label for a transported coset action**: it is a conjugate of `H`. -/
theorem stab_label_iff {Γ L : Type*} [Group Γ] {H : Subgroup Γ} (e : Γ ⧸ H ≃ L) (c : Perm L)
    (i : L) (g : Γ) :
    ((MulAut.conj c).toMonoidHom.comp ((Equiv.permCongrHom e).toMonoidHom.comp
        (MulAction.toPermHom Γ (Γ ⧸ H)))) g i = i ↔
      g ∈ H.map (MulAut.conj (Quotient.out (e.symm (c⁻¹ i)))).toMonoidHom := by
  set q : Γ ⧸ H := e.symm (c⁻¹ i)
  set a : Γ := Quotient.out q
  have hq : (a : Γ ⧸ H) = q := Quotient.out_eq q
  have lhs : ((MulAut.conj c).toMonoidHom.comp ((Equiv.permCongrHom e).toMonoidHom.comp
      (MulAction.toPermHom Γ (Γ ⧸ H)))) g i = c (e (g • e.symm (c⁻¹ i))) := by
    simp [MulAut.conj_apply, Perm.mul_apply, Equiv.permCongr_apply]
  rw [lhs]
  have step1 : c (e (g • e.symm (c⁻¹ i))) = i ↔ g • q = q := by
    constructor
    · intro h
      have h1 : e (g • q) = c⁻¹ i := by
        rw [← h]; exact (Equiv.symm_apply_apply c _).symm
      have := congrArg e.symm h1
      simp only [Equiv.symm_apply_apply] at this
      exact this
    · intro h
      show c (e (g • q)) = i
      rw [h]; simp [q]
  rw [step1, ← hq, MulAction.Quotient.smul_mk, QuotientGroup.eq]
  constructor
  · intro h
    refine ⟨a⁻¹ * g * a, ?_, ?_⟩
    · have : (g * a)⁻¹ * a = a⁻¹ * g⁻¹ * a := by group
      have h' : (a⁻¹ * g⁻¹ * a)⁻¹ ∈ H := H.inv_mem (by rw [← this]; exact h)
      have e2 : (a⁻¹ * g⁻¹ * a)⁻¹ = a⁻¹ * g * a := by group
      rwa [e2] at h'
    · simp [MulAut.conj_apply]; group
  · rintro ⟨h, hh, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have : (a * h * a⁻¹ * a)⁻¹ * a = h⁻¹ := by group
    rw [smul_eq_mul, this]; exact H.inv_mem hh

lemma rhoP_stab_iff (i : Fin 7) (g : G) :
    rhoP g i = i ↔ g ∈ HP.map (MulAut.conj (Quotient.out (quotEquiv.symm (σP⁻¹ i)))).toMonoidHom :=
  stab_label_iff quotEquiv σP i g

lemma rhoL_stab_iff (i : Fin 7) (g : G) :
    rhoL g i = i ↔
      g ∈ HL.map (MulAut.conj (Quotient.out (quotEquivL.symm (σL⁻¹ i)))).toMonoidHom :=
  stab_label_iff quotEquivL σL i g

/-- The actual isomorphism `G ≃* deckGroup f₀` given by the ordered-fibre action `combRho Φ Ψ`. -/
def deckIso {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {Φ Ψ : G →* Perm (Fin 7)}
    (hΦ : Function.Injective Φ) (hd : deckGroup f₀ = (combRho Φ Ψ).range) : G ≃* deckGroup f₀ :=
  (MonoidHom.ofInjective (combRho_injective (Ψ := Ψ) hΦ)).trans (MulEquiv.subgroupCongr hd.symm)

lemma deckIso_apply {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {Φ Ψ : G →* Perm (Fin 7)}
    (hΦ : Function.Injective Φ) (hd : deckGroup f₀ = (combRho Φ Ψ).range) (g : G) :
    ((deckIso hΦ hd g : deckGroup f₀) : Perm (Fin 14)) = combRho Φ Ψ g := rfl

lemma label_zero : (0 : Fin 14) = Fin.castAdd 7 (0 : Fin 7) := rfl
lemma label_seven : (7 : Fin 14) = Fin.natAdd 7 (0 : Fin 7) := rfl

/-- Under `ι = deckIso`, the stabilizers of labels `0` and `7` are the `Φ`-, `Ψ`-stabilizers of
label `0`. -/
lemma stabSub_eq_map {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} {Φ Ψ : G →* Perm (Fin 7)}
    (hΦ : Function.Injective Φ) (hd : deckGroup f₀ = (combRho Φ Ψ).range)
    {K₁ K₂ : Subgroup G} (h₁ : ∀ g, Φ g 0 = 0 ↔ g ∈ K₁) (h₂ : ∀ g, Ψ g 0 = 0 ↔ g ∈ K₂) :
    stabSub f₀ 0 = K₁.map (deckIso hΦ hd).toMonoidHom ∧
      stabSub f₀ 7 = K₂.map (deckIso hΦ hd).toMonoidHom := by
  constructor
  · ext σ
    rw [Subgroup.mem_map_equiv, ← h₁]
    obtain ⟨g, rfl⟩ := (deckIso hΦ hd).surjective σ
    rw [MulEquiv.symm_apply_apply]
    show ((deckIso hΦ hd g : deckGroup f₀) : Perm (Fin 14)) 0 = 0 ↔ _
    rw [deckIso_apply, label_zero, combRho_castAdd]
    exact ⟨fun h => Fin.castAdd_injective _ _ h, fun h => by rw [h]⟩
  · ext σ
    rw [Subgroup.mem_map_equiv, ← h₂]
    obtain ⟨g, rfl⟩ := (deckIso hΦ hd).surjective σ
    rw [MulEquiv.symm_apply_apply]
    show ((deckIso hΦ hd g : deckGroup f₀) : Perm (Fin 14)) 7 = 7 ↔ _
    rw [deckIso_apply, label_seven, combRho_natAdd]
    exact ⟨fun h => Fin.natAdd_injective _ _ h, fun h => by rw [h]⟩

/-- **Identification of the label stabilizers with the paper's `H_P`, `H_L`.**  If the deck group
of `f₀` is the image of the combined point/line monodromy representation (in either order, as
proved for the actual cover in `common_regular_cover`), then there is an isomorphism
`ι : G ≃* deckGroup f₀`, acting on the `14` fibre labels by the combined representation, and
elements `a, b ∈ G` such that either `stabSub f₀ 0 = ι(a H_P a⁻¹)` and
`stabSub f₀ 7 = ι(b H_L b⁻¹)`, or (label swap) `stabSub f₀ 0 = ι(a H_L a⁻¹)` and
`stabSub f₀ 7 = ι(b H_P b⁻¹)`. -/
theorem stabilizer_identification {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13}
    (hd : deckGroup f₀ = (combRho rhoL rhoP).range ∨ deckGroup f₀ = (combRho rhoP rhoL).range) :
    ∃ ι : G ≃* deckGroup f₀, ∃ a b : G,
      ((∀ g, ((ι g : deckGroup f₀) : Perm (Fin 14)) = combRho rhoP rhoL g) ∧
        stabSub f₀ 0 = (HP.map (MulAut.conj a).toMonoidHom).map ι.toMonoidHom ∧
        stabSub f₀ 7 = (HL.map (MulAut.conj b).toMonoidHom).map ι.toMonoidHom) ∨
      ((∀ g, ((ι g : deckGroup f₀) : Perm (Fin 14)) = combRho rhoL rhoP g) ∧
        stabSub f₀ 0 = (HL.map (MulAut.conj a).toMonoidHom).map ι.toMonoidHom ∧
        stabSub f₀ 7 = (HP.map (MulAut.conj b).toMonoidHom).map ι.toMonoidHom) := by
  rcases hd with hd | hd
  · obtain ⟨h1, h2⟩ := stabSub_eq_map rhoL_injective hd (rhoL_stab_iff 0) (rhoP_stab_iff 0)
    exact ⟨deckIso rhoL_injective hd, _, _, Or.inr ⟨deckIso_apply rhoL_injective hd, h1, h2⟩⟩
  · obtain ⟨h1, h2⟩ := stabSub_eq_map rhoP_injective hd (rhoP_stab_iff 0) (rhoL_stab_iff 0)
    exact ⟨deckIso rhoP_injective hd, _, _, Or.inl ⟨deckIso_apply rhoP_injective hd, h1, h2⟩⟩

/-- `completed_quotient_identifications`, re-exported together with the description of the deck
group as the image of the combined monodromy representation (same proof). -/
theorem completed_quotient_identifications_deck (hs : s ^ 2 = -7) :
    ∃ f₀ : OrdFib (projSum hs) 13,
      (deckGroup f₀ = (combRho rhoL rhoP).range ∨ deckGroup f₀ = (combRho rhoP rhoL).range) ∧
      Nonempty (G ≃* deckGroup f₀) ∧ Nat.card (deckGroup f₀) = 168 ∧
      (∀ (σ : deckGroup f₀) (f : RegCov f₀), regAct f₀ σ f = f → σ = 1) ∧
      (∀ f f' : RegCov f₀, regProj f₀ f = regProj f₀ f' → ∃ σ, regAct f₀ σ f = f') ∧
      ∃ Ev₁ Ev₂ : RegFill hs f₀ → ℂ,
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev₁ ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev₂ ∧
        (∀ w, (pPoly s).eval (Ev₁ w) = regFillProj hs f₀ w) ∧
        (∀ w, (pPoly (-s)).eval (Ev₂ w) = regFillProj hs f₀ w) ∧
        (∀ w w', Ev₁ w = Ev₁ w' ↔ ∃ σ : deckGroup f₀, σ.1 0 = 0 ∧ regFillAct hs f₀ σ w = w') ∧
        (∀ w w', Ev₂ w = Ev₂ w' ↔ ∃ σ : deckGroup f₀, σ.1 7 = 7 ∧ regFillAct hs f₀ σ w = w') ∧
        Function.Surjective Ev₁ ∧ Function.Surjective Ev₂ ∧
        IsProperMap Ev₁ ∧ IsProperMap Ev₂ ∧
        (∀ (ε : ℝ) w, (SteklovDiskCovers.coverPoly (pPoly s) ε).eval (Ev₁ w) =
          affA ε (regFillProj hs f₀ w)) ∧
        (∀ (ε : ℝ) w, (SteklovDiskCovers.coverPoly (pPoly (-s)) ε).eval (Ev₂ w) =
          affA ε (regFillProj hs f₀ w)) := by
  obtain ⟨A, f₀, -, -, -, hdeck, hiso, hcard, hfree, htrans, -, -, ⟨ev₁, hc₁, hs₁, hp₁, hf₁⟩,
    ⟨ev₂, hc₂, hs₂, hp₂, hf₂⟩⟩ := common_regular_cover hs
  have hs' : (-s) ^ 2 = -7 := by rw [neg_sq]; exact hs
  obtain ⟨hk₁, hPk₁, hP'₁, hsu₁⟩ := coord_data (e := Homeomorph.refl _)
    (fun _ => rfl) hc₁ hs₁ hp₁ (critVals_pPoly hs)
  obtain ⟨hk₂, hPk₂, hP'₂, hsu₂⟩ := coord_data
    (e := baseHomeoG (critVals_neg hs)) (baseHomeoG_val _) hc₂ hs₂ hp₂ (critVals_pPoly hs')
  have hfib₁ : ∀ f f', (ev₁ f : ℂ) = ev₁ f' ↔ ∃ σ ∈ {σ : deckGroup f₀ | σ.1 0 = 0},
      regAct f₀ σ f = f' := fun f f' => Subtype.ext_iff.symm.trans (hf₁ f f')
  have hfib₂ : ∀ f f', (ev₂ f : ℂ) = ev₂ f' ↔ ∃ σ ∈ {σ : deckGroup f₀ | σ.1 7 = 7},
      regAct f₀ σ f = f' := fun f f' => Subtype.ext_iff.symm.trans (hf₂ f f')
  obtain ⟨m₁, -, e₁, q₁, su₁, pr₁, c₁⟩ :=
    quotient_ident hs f₀ (pPoly_degree_pos hs) hk₁ hPk₁ hP'₁ _ hfib₁ hsu₁
  obtain ⟨m₂, -, e₂, q₂, su₂, pr₂, c₂⟩ :=
    quotient_ident hs f₀ (pPoly_degree_pos hs') hk₂ hPk₂ hP'₂ _ hfib₂ hsu₂
  exact ⟨f₀, hdeck, hiso, hcard, hfree, htrans, _, _, m₁, m₂, e₁, e₂, q₁, q₂, su₁, su₂, pr₁, pr₂,
    c₁, c₂⟩

end Degree7
