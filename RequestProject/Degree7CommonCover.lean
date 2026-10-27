module

public import RequestProject.Degree7RegularCover
public import RequestProject.SumCover

/-!
# The common unbranched regular cover of the two degree-seven covers

For `s² = -7`, `p_s` and `p_{-s}` are degree-seven covers of the same base `X = ℂ \ {0, 1}`.
We apply the Galois-closure construction to their disjoint union `p_s ⊔ p_{-s}` (degree `14`):
the path component `R` of an ordering `f₀` of a complete fibre is a path-connected regular cover of
`X` whose deck group is isomorphic to `G = GL(3, 𝔽₂)` (the monodromy representations of the two
covers factor through one surjection onto `G`, `monodromy_full`), of degree `168`. The coordinate
maps `R → p_s⁻¹(X)` (label `0`) and `R → p_{-s}⁻¹(X)` (label `7`) are continuous, onto, compatible
with the projections, and their fibres are exactly the orbits of the stabilizers of these labels,
which correspond under `G ≅ deckGroup` to the stabilizers `H_L`, `H_P` (in some order) of a point
and of a line.

This is the **topological, unbranched** common regular cover with both quotient identifications;
the completion over the branch values and the boundary as a bordered Riemann surface is not
formalized.
-/

@[expose] public section

open Polynomial Set Equiv PolyCover GL3F2 SteklovRegularCover CoverIneq

noncomputable section

namespace Degree7

variable {s : ℂ}

section Generic

variable {P Q : ℂ[X]} (h : critVals P = critVals Q)

/-- The identification of the bases `ℂ \ crit(Q) ≃ₜ ℂ \ crit(P)` of two polynomial covers with
the same critical values. -/
def baseHomeoG : Base Q ≃ₜ Base P where
  toFun := idBase h.symm
  invFun := idBase h
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl
  continuous_toFun := continuous_idBase _
  continuous_invFun := continuous_idBase _

lemma baseHomeoG_val (x : Base Q) : (baseHomeoG h x : ℂ) = x := rfl

/-- The cover of `Q`, viewed over the base of `P`. -/
def projG : Total Q → Base P := baseHomeoG h ∘ proj Q

lemma isCoveringMap_projG : IsCoveringMap (projG h) :=
  (isCoveringMap Q).homeomorph_comp (baseHomeoG h)

lemma projG_preimage (x : Base P) : projG h ⁻¹' {x} = proj Q ⁻¹' {idBase h x} := by
  ext e
  simp only [projG, mem_preimage, mem_singleton_iff, Function.comp_apply]
  constructor
  · rintro rfl; exact Subtype.ext rfl
  · rintro he; rw [he]; exact Subtype.ext rfl

end Generic

section Transport

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
  {q : E → Y} (hq : IsCoveringMap q) (g : Y ≃ₜ X)

/-- The fibre of `g ∘ q` over `A` is the fibre of `q` over `g⁻¹ A`. -/
def fibreEquivH (A : X) : (g ∘ q) ⁻¹' {A} ≃ q ⁻¹' {g.symm A} where
  toFun b := ⟨b.1, by
    have hb : g (q b.1) = A := b.2
    show q b.1 = g.symm A
    exact (g.symm_apply_apply (q b.1)).symm.trans (congrArg g.symm hb)⟩
  invFun b := ⟨b.1, by
    have hb : q b.1 = g.symm A := b.2
    show g (q b.1) = A
    exact (congrArg g hb).trans (g.apply_symm_apply A)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Monodromy of `g ∘ q`** is the monodromy of `q` along the transported loop. -/
lemma monodromy_homeomorph_comp {A : X} (γ : Path.Homotopic.Quotient A A)
    (b : (g ∘ q) ⁻¹' {A}) :
    fibreEquivH g A ((hq.homeomorph_comp g).monodromy γ b) =
      hq.monodromy (γ.map ⟨g.symm, g.symm.continuous⟩) (fibreEquivH g A b) := by
  apply Subtype.ext
  induction γ using Path.Homotopic.Quotient.ind with
  | mk γ =>
    rw [← Path.Homotopic.Quotient.mk_map]
    exact (CoverTransport.monodromy_map_mk (hq.homeomorph_comp g) hq continuous_id
      g.symm.continuous (fun e => (g.symm_apply_apply (q e)).symm) γ b
      (fibreEquivH g A b) (by simp [fibreEquivH])).symm

/-- The labelling of the fibre of `g ∘ q` induced by a labelling of the fibre of `q`. -/
def labelH {A : X} {m : ℕ} (L' : q ⁻¹' {g.symm A} ≃ Fin m) : (g ∘ q) ⁻¹' {A} ≃ Fin m :=
  (fibreEquivH g A).trans L'

lemma labelH_monodromy {A : X} {m : ℕ} (L' : q ⁻¹' {g.symm A} ≃ Fin m)
    (γ : Path.Homotopic.Quotient A A) (j : Fin m) :
    labelH g L' ((hq.homeomorph_comp g).monodromy γ ((labelH g L').symm j)) =
      L' (hq.monodromy (γ.map ⟨g.symm, g.symm.continuous⟩) (L'.symm j)) := by
  show L' (fibreEquivH g A _) = _
  rw [monodromy_homeomorph_comp hq g γ]
  congr 2

end Transport

/-- The cover `p_{-s}`, viewed over the base of `p_s`. -/
abbrev proj₂ (hs : s ^ 2 = -7) : Total (pPoly (-s)) → Base (pPoly s) := projG (critVals_neg hs)

lemma isCoveringMap_proj₂ (hs : s ^ 2 = -7) : IsCoveringMap (proj₂ hs) :=
  (isCoveringMap (pPoly (-s))).homeomorph_comp (baseHomeoG (critVals_neg hs))

/-- The disjoint union `p_s ⊔ p_{-s}` over `ℂ \ {0,1}`. -/
def projSum (hs : s ^ 2 = -7) : Total (pPoly s) ⊕ Total (pPoly (-s)) → Base (pPoly s) :=
  Sum.elim (proj (pPoly s)) (proj₂ hs)

lemma isCoveringMap_projSum (hs : s ^ 2 = -7) : IsCoveringMap (projSum hs) :=
  isCoveringMap_sumElim (isCoveringMap _) (isCoveringMap_proj₂ hs)

lemma card_fibre_proj₂ (hs : s ^ 2 = -7) (x : Base (pPoly s)) :
    Nat.card (proj₂ hs ⁻¹' {x}) = 7 := by
  rw [proj₂, projG_preimage]
  exact card_fibre_pPoly (by rw [neg_sq]; exact hs) _

lemma card_fibre_projSum (hs : s ^ 2 = -7) (x : Base (pPoly s)) :
    Nat.card (projSum hs ⁻¹' {x}) = 13 + 1 := by
  have h1 := card_fibre_pPoly hs x
  have h2 := card_fibre_proj₂ hs x
  haveI : Finite (proj (pPoly s) ⁻¹' {x}) := Nat.finite_of_card_ne_zero (by rw [h1]; omega)
  haveI : Finite (proj₂ hs ⁻¹' {x}) := Nat.finite_of_card_ne_zero (by rw [h2]; omega)
  rw [projSum, card_fibre_sumElim, h1, h2]

/-! ### The combined representation and the deck group of the common cover -/

/-- The combined action of `G` on the `7 + 7` labels: `Φ` on the first block, `Ψ` on the
second. -/
def combRho (Φ Ψ : G →* Perm (Fin 7)) : G →* Perm (Fin (7 + 7)) :=
  (finSumFinEquiv.permCongrHom.toMonoidHom).comp ((Perm.sumCongrHom _ _).comp (Φ.prod Ψ))

lemma combRho_castAdd (Φ Ψ : G →* Perm (Fin 7)) (g : G) (j : Fin 7) :
    combRho Φ Ψ g (Fin.castAdd 7 j) = Fin.castAdd 7 (Φ g j) := by
  rw [show combRho Φ Ψ g = finSumFinEquiv.permCongr (Perm.sumCongr (Φ g) (Ψ g)) from rfl,
    Equiv.permCongr_apply, finSumFinEquiv_symm_apply_castAdd, Perm.sumCongr_apply, Sum.map_inl,
    finSumFinEquiv_apply_left]

lemma combRho_natAdd (Φ Ψ : G →* Perm (Fin 7)) (g : G) (j : Fin 7) :
    combRho Φ Ψ g (Fin.natAdd 7 j) = Fin.natAdd 7 (Ψ g j) := by
  rw [show combRho Φ Ψ g = finSumFinEquiv.permCongr (Perm.sumCongr (Φ g) (Ψ g)) from rfl,
    Equiv.permCongr_apply, finSumFinEquiv_symm_apply_natAdd, Perm.sumCongr_apply, Sum.map_inr,
    finSumFinEquiv_apply_right]

lemma combRho_injective {Φ Ψ : G →* Perm (Fin 7)} (hΦ : Function.Injective Φ) :
    Function.Injective (combRho Φ Ψ) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply hΦ
  rw [map_one]
  ext j
  have := congrArg (fun π : Perm (Fin (7 + 7)) => π (Fin.castAdd 7 j)) hg
  simp only [combRho_castAdd, Perm.one_apply] at this
  exact congrArg Fin.val (Fin.castAdd_injective _ _ this)

section GenericDeck

variable {X E₁ E₂ : Type*} [TopologicalSpace X] [TopologicalSpace E₁] [TopologicalSpace E₂]
  {p₁ : E₁ → X} {p₂ : E₂ → X} (h₁ : IsCoveringMap p₁) (h₂ : IsCoveringMap p₂) {A : X}
  (L₁ : p₁ ⁻¹' {A} ≃ Fin 7) (L₂ : p₂ ⁻¹' {A} ≃ Fin 7) (Φ Ψ : G →* Perm (Fin 7))
  (φ : Path.Homotopic.Quotient A A → G)

/-- Monodromy of the disjoint union in the combined labelling is the combined representation. -/
theorem sumLabel_monodromy_eq
    (h1 : ∀ γ j, L₁ (h₁.monodromy γ (L₁.symm j)) = Φ (φ γ) j)
    (h2 : ∀ γ j, L₂ (h₂.monodromy γ (L₂.symm j)) = Ψ (φ γ) j)
    (γ : Path.Homotopic.Quotient A A) (i : Fin (7 + 7)) :
    sumLabel L₁ L₂ ((isCoveringMap_sumElim h₁ h₂).monodromy γ ((sumLabel L₁ L₂).symm i)) =
      combRho Φ Ψ (φ γ) i := by
  induction i using Fin.addCases with
  | left j => rw [sumLabel_monodromy_castAdd h₁ h₂, combRho_castAdd, h1]
  | right j => rw [sumLabel_monodromy_natAdd h₁ h₂, combRho_natAdd, h2]

/-- **The deck group of the common cover is the image of the combined representation.** -/
theorem mem_deckGroup_sum_iff (hsurj : Function.Surjective φ)
    (h1 : ∀ γ j, L₁ (h₁.monodromy γ (L₁.symm j)) = Φ (φ γ) j)
    (h2 : ∀ γ j, L₂ (h₂.monodromy γ (L₂.symm j)) = Ψ (φ γ) j) (σ : Perm (Fin (13 + 1))) :
    σ ∈ deckGroup (SteklovRegularCover.baseTuple (n := 13) (sumLabel (a := 7) (b := 7) L₁ L₂)) ↔
      σ ∈ (combRho Φ Ψ).range := by
  rw [mem_deckGroup_baseTuple (isCoveringMap_sumElim h₁ h₂), MonoidHom.mem_range]
  constructor
  · rintro ⟨γ, hγ⟩
    refine ⟨φ γ, ?_⟩
    ext1 i
    rw [← sumLabel_monodromy_eq h₁ h₂ L₁ L₂ Φ Ψ φ h1 h2 γ i, ← hγ i, Equiv.apply_symm_apply]
  · rintro ⟨g, rfl⟩
    obtain ⟨γ, rfl⟩ := hsurj g
    refine ⟨γ, fun i => ?_⟩
    rw [Equiv.symm_apply_eq, sumLabel_monodromy_eq h₁ h₂ L₁ L₂ Φ Ψ φ h1 h2 γ i]

end GenericDeck

/-! ### Coordinates lying in one summand -/

lemma joined_inl {E₁ E₂ : Type*} [TopologicalSpace E₁] [TopologicalSpace E₂] {a : E₁}
    {y : E₁ ⊕ E₂} (h : Joined (Sum.inl a) y) : ∃ b, y = Sum.inl b := by
  obtain ⟨δ⟩ := h
  have hc : Continuous fun t => (δ t).isLeft :=
    ((continuous_sum_dom (f := fun z : E₁ ⊕ E₂ => z.isLeft)).2
      ⟨continuous_const, continuous_const⟩).comp δ.continuous
  have h01 := PreconnectedSpace.constant inferInstance hc (x := 0) (y := 1)
  simp only [Path.source, Path.target, Sum.isLeft_inl] at h01
  exact Sum.isLeft_iff.1 h01.symm

lemma joined_inr {E₁ E₂ : Type*} [TopologicalSpace E₁] [TopologicalSpace E₂] {a : E₂}
    {y : E₁ ⊕ E₂} (h : Joined (Sum.inr a) y) : ∃ b, y = Sum.inr b := by
  obtain ⟨δ⟩ := h
  have hc : Continuous fun t => (δ t).isRight :=
    ((continuous_sum_dom (f := fun z : E₁ ⊕ E₂ => z.isRight)).2
      ⟨continuous_const, continuous_const⟩).comp δ.continuous
  have h01 := PreconnectedSpace.constant inferInstance hc (x := 0) (y := 1)
  simp only [Path.source, Path.target, Sum.isRight_inr] at h01
  exact Sum.isRight_iff.1 h01.symm

section SummandMaps

variable {X E₁ E₂ : Type*} [TopologicalSpace X] [TopologicalSpace E₁] [TopologicalSpace E₂]
  {p₁ : E₁ → X} {p₂ : E₂ → X} {n : ℕ}

omit [TopologicalSpace X] in
lemma joined_coord {p : E₁ ⊕ E₂ → X} {f₀ : OrdFib p n} (f : RegCov f₀) (k : Fin (n + 1)) :
    Joined (f₀.1 k) (evAt f₀ k f) := by
  obtain ⟨δ⟩ := f.2
  exact ⟨δ.map ((continuous_apply k).comp continuous_subtype_val)⟩

/-- **The coordinate map to the first summand.** If the `k`-th point of `f₀` lies in `E₁`, the
`k`-th coordinate is a continuous map `RegCov f₀ → E₁` over `X`, onto when `E₁` is path
connected, whose fibres are the orbits of the stabilizer of `k` in the deck group. -/
theorem summand_map_inl (h₁ : IsCoveringMap p₁) (h₂ : IsCoveringMap p₂)
    (hcard : ∀ x, Nat.card (Sum.elim p₁ p₂ ⁻¹' {x}) = n + 1) [PathConnectedSpace E₁]
    (f₀ : OrdFib (Sum.elim p₁ p₂) n) (k : Fin (n + 1)) (a₀ : E₁) (h0 : f₀.1 k = Sum.inl a₀) :
    ∃ ev : RegCov f₀ → E₁, Continuous ev ∧ Function.Surjective ev ∧
      (∀ f, p₁ (ev f) = regProj f₀ f) ∧
      ∀ f f', ev f = ev f' ↔ ∃ σ : deckGroup f₀, σ.1 k = k ∧ regAct f₀ σ f = f' := by
  have hin : ∀ f : RegCov f₀, ∃ b, evAt f₀ k f = Sum.inl b := fun f =>
    joined_inl (E₂ := E₂) (by rw [← h0]; exact joined_coord f k)
  choose ev hev using hin
  have hcomp : Sum.inl ∘ ev = evAt f₀ k := funext fun f => (hev f).symm
  refine ⟨ev, ?_, fun e => ?_, fun f => ?_, fun f f' => ?_⟩
  · rw [(Topology.IsEmbedding.inl (Y := E₂)).continuous_iff, hcomp]
    exact continuous_evAt f₀ k
  · obtain ⟨δ⟩ := PathConnectedSpace.joined a₀ e
    have hj : Joined (f₀.1 k) (Sum.inl e) := by rw [h0]; exact ⟨δ.map continuous_inl⟩
    obtain ⟨f, hf⟩ := evAt_surjective_of_joined (isCoveringMap_sumElim h₁ h₂) f₀ k hj
    exact ⟨f, Sum.inl_injective ((hev f).symm.trans hf)⟩
  · have := proj_evAt f₀ k f
    rw [hev f] at this
    exact this
  · rw [← evAt_eq_iff hcard k f f', hev f, hev f']
    exact ⟨fun h => h ▸ rfl, fun h => Sum.inl_injective h⟩

/-- **The coordinate map to the second summand.** -/
theorem summand_map_inr (h₁ : IsCoveringMap p₁) (h₂ : IsCoveringMap p₂)
    (hcard : ∀ x, Nat.card (Sum.elim p₁ p₂ ⁻¹' {x}) = n + 1) [PathConnectedSpace E₂]
    (f₀ : OrdFib (Sum.elim p₁ p₂) n) (k : Fin (n + 1)) (a₀ : E₂) (h0 : f₀.1 k = Sum.inr a₀) :
    ∃ ev : RegCov f₀ → E₂, Continuous ev ∧ Function.Surjective ev ∧
      (∀ f, p₂ (ev f) = regProj f₀ f) ∧
      ∀ f f', ev f = ev f' ↔ ∃ σ : deckGroup f₀, σ.1 k = k ∧ regAct f₀ σ f = f' := by
  have hin : ∀ f : RegCov f₀, ∃ b, evAt f₀ k f = Sum.inr b := fun f =>
    joined_inr (E₁ := E₁) (by rw [← h0]; exact joined_coord f k)
  choose ev hev using hin
  have hcomp : Sum.inr ∘ ev = evAt f₀ k := funext fun f => (hev f).symm
  refine ⟨ev, ?_, fun e => ?_, fun f => ?_, fun f f' => ?_⟩
  · rw [(Topology.IsEmbedding.inr (X := E₁)).continuous_iff, hcomp]
    exact continuous_evAt f₀ k
  · obtain ⟨δ⟩ := PathConnectedSpace.joined a₀ e
    have hj : Joined (f₀.1 k) (Sum.inr e) := by rw [h0]; exact ⟨δ.map continuous_inr⟩
    obtain ⟨f, hf⟩ := evAt_surjective_of_joined (isCoveringMap_sumElim h₁ h₂) f₀ k hj
    exact ⟨f, Sum.inr_injective ((hev f).symm.trans hf)⟩
  · have := proj_evAt f₀ k f
    rw [hev f] at this
    exact this
  · rw [← evAt_eq_iff hcard k f f', hev f, hev f']
    exact ⟨fun h => h ▸ rfl, fun h => Sum.inr_injective h⟩

end SummandMaps

/-! ### The common regular cover: generic assembly -/

section Assembly

variable {X E₁ E₂ : Type*} [TopologicalSpace X] [TopologicalSpace E₁] [TopologicalSpace E₂]
  {p₁ : E₁ → X} {p₂ : E₂ → X}

/-- **Common regular cover of two degree-seven covers with a common monodromy group.** -/
theorem common_cover_generic [LocallyPathConnectedSpace X] [PathConnectedSpace E₁]
    [PathConnectedSpace E₂] (h₁ : IsCoveringMap p₁) (h₂ : IsCoveringMap p₂)
    (hc₁ : ∀ x, Nat.card (p₁ ⁻¹' {x}) = 7) (hc₂ : ∀ x, Nat.card (p₂ ⁻¹' {x}) = 7) {A : X}
    (L₁ : p₁ ⁻¹' {A} ≃ Fin 7) (L₂ : p₂ ⁻¹' {A} ≃ Fin 7) (Φ Ψ : G →* Perm (Fin 7))
    (hΦ : Function.Injective Φ) (φ : Path.Homotopic.Quotient A A → G)
    (hsurj : Function.Surjective φ)
    (h1 : ∀ γ j, L₁ (h₁.monodromy γ (L₁.symm j)) = Φ (φ γ) j)
    (h2 : ∀ γ j, L₂ (h₂.monodromy γ (L₂.symm j)) = Ψ (φ γ) j) :
    ∃ f₀ : OrdFib (Sum.elim p₁ p₂) 13, ordProj _ 13 f₀ = A ∧
      IsCoveringMap (regProj f₀) ∧ PathConnectedSpace (RegCov f₀) ∧
      deckGroup f₀ = (combRho Φ Ψ).range ∧
      Nonempty (G ≃* deckGroup f₀) ∧ Nat.card (deckGroup f₀) = 168 ∧
      (∀ (σ : deckGroup f₀) (f : RegCov f₀), regAct f₀ σ f = f → σ = 1) ∧
      (∀ f f' : RegCov f₀, regProj f₀ f = regProj f₀ f' → ∃ σ, regAct f₀ σ f = f') ∧
      Function.Surjective (regProj f₀) ∧
      (∀ x, Nat.card (regProj f₀ ⁻¹' {x}) = 168) ∧
      (∃ ev₁ : RegCov f₀ → E₁, Continuous ev₁ ∧ Function.Surjective ev₁ ∧
        (∀ f, p₁ (ev₁ f) = regProj f₀ f) ∧
        ∀ f f', ev₁ f = ev₁ f' ↔ ∃ σ : deckGroup f₀, σ.1 0 = 0 ∧ regAct f₀ σ f = f') ∧
      (∃ ev₂ : RegCov f₀ → E₂, Continuous ev₂ ∧ Function.Surjective ev₂ ∧
        (∀ f, p₂ (ev₂ f) = regProj f₀ f) ∧
        ∀ f f', ev₂ f = ev₂ f' ↔ ∃ σ : deckGroup f₀, σ.1 7 = 7 ∧ regAct f₀ σ f = f') := by
  have hcard : ∀ x, Nat.card (Sum.elim p₁ p₂ ⁻¹' {x}) = 13 + 1 := fun x => by
    haveI : Finite (p₁ ⁻¹' {x}) := Nat.finite_of_card_ne_zero (by rw [hc₁]; omega)
    haveI : Finite (p₂ ⁻¹' {x}) := Nat.finite_of_card_ne_zero (by rw [hc₂]; omega)
    rw [card_fibre_sumElim, hc₁, hc₂]
  have hcov := isCoveringMap_sumElim h₁ h₂
  set f₀ := SteklovRegularCover.baseTuple (n := 13) (sumLabel (a := 7) (b := 7) L₁ L₂) with hf₀
  have hdeck : deckGroup f₀ = (combRho Φ Ψ).range := by
    ext σ
    exact mem_deckGroup_sum_iff h₁ h₂ L₁ L₂ Φ Ψ φ hsurj h1 h2 σ
  have hiso : Nonempty (G ≃* deckGroup f₀) := by
    rw [hdeck]; exact ⟨MonoidHom.ofInjective (combRho_injective hΦ)⟩
  have hcardD : Nat.card (deckGroup f₀) = 168 := by
    obtain ⟨e⟩ := hiso
    rw [← Nat.card_congr e.toEquiv, card_G]
  have h00 : f₀.1 0 = Sum.inl (L₁.symm 0).1 := by
    have : (0 : Fin (13 + 1)) = Fin.castAdd 7 (0 : Fin 7) := Fin.ext rfl
    show ((sumLabel L₁ L₂).symm 0).1 = _
    rw [this, sumLabel_symm_castAdd]
  have h07 : f₀.1 7 = Sum.inr (L₂.symm 0).1 := by
    have : (7 : Fin (13 + 1)) = Fin.natAdd 7 (0 : Fin 7) := Fin.ext rfl
    show ((sumLabel L₁ L₂).symm 7).1 = _
    rw [this, sumLabel_symm_natAdd]
  obtain ⟨ev₁, hev₁⟩ := summand_map_inl h₁ h₂ hcard f₀ 0 _ h00
  obtain ⟨ev₂, hev₂⟩ := summand_map_inr h₁ h₂ hcard f₀ 7 _ h07
  have hsurjR : Function.Surjective (regProj f₀) := by
    intro x
    have hne : Nat.card (p₁ ⁻¹' {x}) ≠ 0 := by rw [hc₁]; omega
    obtain ⟨⟨e, he⟩⟩ := (Nat.card_ne_zero.1 hne).1
    obtain ⟨f, hf⟩ := hev₁.2.1 e
    exact ⟨f, by rw [← hev₁.2.2.1 f, hf]; exact he⟩
  refine ⟨f₀, SteklovRegularCover.ordProj_baseTuple _, isCoveringMap_regProj hcov f₀, inferInstance, hdeck, hiso,
    hcardD, fun σ f h => regAct_eq_self h, fun f f' h => exists_regAct_eq hcard h, hsurjR,
    fun x => ?_, ⟨ev₁, hev₁⟩, ⟨ev₂, hev₂⟩⟩
  obtain ⟨f, rfl⟩ := hsurjR x
  rw [card_regProj_fibre hcard f, hcardD]

end Assembly

/-! ### The paper's common regular cover -/

/-- **The common unbranched regular `GL(3, 𝔽₂)` cover of `p_s` and `p_{-s}`.** For `s² = -7`
there are a base point `A` of `X = ℂ \ {0,1}` and an ordering `f₀` of the fibre of `p_s ⊔ p_{-s}`
over `A` such that the path component `R = RegCov f₀` of the ordered complete fibres is a
path-connected covering space of `X` of degree `168`, with deck group the image of
`g ↦ (ρ_L(g), ρ_P(g))` or of `g ↦ (ρ_P(g), ρ_L(g))` (isomorphic to `G = GL(3,𝔽₂)`), acting freely
and transitively on the fibres; the label-`0` coordinate `R → p_s⁻¹(X)` and the label-`7`
coordinate `R → p_{-s}⁻¹(X)` are continuous, onto, compatible with the projections, and their
fibres are exactly the orbits of the stabilizers of these labels (point and line stabilizers). -/
theorem common_regular_cover (hs : s ^ 2 = -7) :
    ∃ (A : Base (pPoly s)) (f₀ : OrdFib (Sum.elim (proj (pPoly s)) (proj₂ hs)) 13),
      ordProj _ 13 f₀ = A ∧
      IsCoveringMap (regProj f₀) ∧ PathConnectedSpace (RegCov f₀) ∧
      (deckGroup f₀ = (combRho rhoL rhoP).range ∨ deckGroup f₀ = (combRho rhoP rhoL).range) ∧
      Nonempty (G ≃* deckGroup f₀) ∧ Nat.card (deckGroup f₀) = 168 ∧
      (∀ (σ : deckGroup f₀) (f : RegCov f₀), regAct f₀ σ f = f → σ = 1) ∧
      (∀ f f' : RegCov f₀, regProj f₀ f = regProj f₀ f' → ∃ σ, regAct f₀ σ f = f') ∧
      Function.Surjective (regProj f₀) ∧
      (∀ x, Nat.card (regProj f₀ ⁻¹' {x}) = 168) ∧
      (∃ ev₁ : RegCov f₀ → Total (pPoly s), Continuous ev₁ ∧ Function.Surjective ev₁ ∧
        (∀ f, proj (pPoly s) (ev₁ f) = regProj f₀ f) ∧
        ∀ f f', ev₁ f = ev₁ f' ↔ ∃ σ : deckGroup f₀, σ.1 0 = 0 ∧ regAct f₀ σ f = f') ∧
      (∃ ev₂ : RegCov f₀ → Total (pPoly (-s)), Continuous ev₂ ∧ Function.Surjective ev₂ ∧
        (∀ f, proj₂ hs (ev₂ f) = regProj f₀ f) ∧
        ∀ f f', ev₂ f = ev₂ f' ↔ ∃ σ : deckGroup f₀, σ.1 7 = 7 ∧ regAct f₀ σ f = f') := by
  obtain ⟨r, A, γ0, γ1, L, L', φ, -, -, -, -, -, -, -, hsurj, hmon⟩ := monodromy_full hs
  have hs' : (-s) ^ 2 = -7 := by rw [neg_sq]; exact hs
  haveI := locPathConnectedSpace_base hs
  haveI := pathConnectedSpace_total (pPoly_degree_pos hs)
  haveI := pathConnectedSpace_total (pPoly_degree_pos hs')
  have key1 : ∀ (ρ : G →* Perm (Fin 7)),
      (∀ γ, L.permCongr (monodromyPerm (pPoly s) γ) = ρ (φ γ)) →
      ∀ γ j, L ((isCoveringMap (pPoly s)).monodromy γ (L.symm j)) = ρ (φ γ) j := by
    intro ρ hρ γ j
    have := congrArg (fun π : Perm (Fin 7) => π j) (hρ γ)
    simpa only [Equiv.permCongr_apply, monodromyPerm_apply] using this
  let L₂ : proj₂ hs ⁻¹' {A} ≃ Fin 7 :=
    labelH (q := proj (pPoly (-s))) (baseHomeoG (critVals_neg hs)) L'
  have key2 : ∀ (ρ : G →* Perm (Fin 7)),
      (∀ γ, L'.permCongr (monodromyPerm (pPoly (-s)) (γ.map (idBaseC (critVals_neg hs)))) =
        ρ (φ γ)) →
      ∀ γ j, L₂ ((isCoveringMap_proj₂ hs).monodromy γ (L₂.symm j)) = ρ (φ γ) j := by
    intro ρ hρ γ j
    have := congrArg (fun π : Perm (Fin 7) => π j) (hρ γ)
    simp only [Equiv.permCongr_apply, monodromyPerm_apply] at this
    rw [← this]
    exact labelH_monodromy (isCoveringMap (pPoly (-s))) (baseHomeoG (critVals_neg hs)) L' γ j
  rcases hmon with hm | hm
  · obtain ⟨f₀, hA, hc, hpc, hd, rest⟩ := common_cover_generic (isCoveringMap (pPoly s))
      (isCoveringMap_proj₂ hs) (card_fibre_pPoly hs) (card_fibre_proj₂ hs) L L₂ rhoL rhoP
      rhoL_injective φ hsurj (key1 rhoL fun γ => (hm γ).1) (key2 rhoP fun γ => (hm γ).2)
    exact ⟨A, f₀, hA, hc, hpc, Or.inl hd, rest⟩
  · obtain ⟨f₀, hA, hc, hpc, hd, rest⟩ := common_cover_generic (isCoveringMap (pPoly s))
      (isCoveringMap_proj₂ hs) (card_fibre_pPoly hs) (card_fibre_proj₂ hs) L L₂ rhoP rhoL
      rhoP_injective φ hsurj (key1 rhoP fun γ => (hm γ).1) (key2 rhoL fun γ => (hm γ).2)
    exact ⟨A, f₀, hA, hc, hpc, Or.inr hd, rest⟩

end Degree7
