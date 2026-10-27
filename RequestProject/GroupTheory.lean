module

public import Mathlib

/-!
# Finite group theory used in Section 3 of the paper

* `cycleCount g S` : the number `c_S(g)` of cycles (including one-cycles) of the permutation
  induced by `g` on a finite `G`-set `S`.
* `AlmostConjugate H₁ H₂` : every conjugacy class of `G` meets `H₁` and `H₂` in the same
  number of elements.
* `AreConjugate H₁ H₂` : `H₂ = a H₁ a⁻¹` for some `a`.
* Counting lemmas: `card_conj_mem_eq` (the class equation for `#{a | a⁻¹ g a ∈ H}`),
  `card_conj_mem_stabilizer` (the same count for a stabilizer, via fixed points on an orbit),
  `card_conj_mem_map` (transport along an automorphism).
* `cycleType_eq_of_conj_equiv` : cycle types are invariant under transport of permutations
  along a bijection.
-/

@[expose] public section

noncomputable section

namespace SteklovGroup

variable {G : Type*} [Group G]

/-- `c_S(g)`: the number of cycles (one-cycles included) of the permutation of the finite set
`S` induced by `g`. -/
def cycleCount (g : G) (S : Type*) [MulAction G S] [Finite S] : ℕ :=
  letI := Fintype.ofFinite S
  letI := Classical.decEq S
  (MulAction.toPerm g : Equiv.Perm S).partition.parts.card

/-- Subgroups `H₁, H₂` are almost conjugate if every conjugacy class meets them in the same
number of elements: for every `g`, `#{h ∈ H₁ | h ~ g} = #{h ∈ H₂ | h ~ g}`. -/
def AlmostConjugate (H₁ H₂ : Subgroup G) : Prop :=
  ∀ g : G, Nat.card {h : H₁ // IsConj g h} = Nat.card {h : H₂ // IsConj g h}

/-- `H₁` and `H₂` are conjugate subgroups. -/
def AreConjugate (H₁ H₂ : Subgroup G) : Prop :=
  ∃ a : G, H₂ = H₁.map (MulAut.conj a).toMonoidHom

/-- Cycle types are invariant under transport along a bijection. -/
lemma cycleType_eq_of_conj_equiv {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [DecidableEq β]
    (f : α ≃ β) (σ : Equiv.Perm α) (τ : Equiv.Perm β) (h : ∀ b, f (σ (f.symm b)) = τ b) :
    σ.cycleType = τ.cycleType := by
  let f' : α ≃ Subtype (fun _ : β => True) := f.trans (Equiv.subtypeUnivEquiv (fun _ => trivial)).symm
  have hτ : σ.extendDomain f' = τ := by
    ext b
    rw [Equiv.Perm.extendDomain_apply_subtype _ _ (p := fun _ : β => True) trivial]
    simpa [f'] using h b
  rw [← hτ, Equiv.Perm.cycleType_extendDomain]

/-- Transport of `cycleCount` along a bijection. -/
lemma cycleCount_eq_of_conj_equiv (g : G) (S β : Type*) [MulAction G S] [Finite S]
    [Fintype β] [DecidableEq β] (f : S ≃ β) (τ : Equiv.Perm β)
    (h : ∀ b, f (g • f.symm b) = τ b) :
    cycleCount g S = τ.partition.parts.card := by
  letI := Fintype.ofFinite S
  letI := Classical.decEq S
  have hc := cycleType_eq_of_conj_equiv f (MulAction.toPerm g) τ h
  show (MulAction.toPerm g : Equiv.Perm S).partition.parts.card = _
  simp only [Equiv.Perm.partition, Multiset.card_add, Multiset.card_replicate,
    ← Equiv.Perm.sum_cycleType]
  rw [hc, Fintype.card_congr f]

section counting

open scoped Classical

variable [Fintype G]

/-- Fibre count: if `g ~ h` then `#{a | a⁻¹ g a = h} = |C_G(g)|`. -/
lemma card_conj_fiber (g h : G) (hc : IsConj g h) :
    Fintype.card {a : G // a⁻¹ * g * a = h} =
      Fintype.card (Subgroup.centralizer ({g} : Set G)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  refine Fintype.card_congr
    { toFun := fun a => ⟨a.1 * c, ?_⟩
      invFun := fun z => ⟨z.1 * c⁻¹, ?_⟩
      left_inv := fun a => by ext; simp
      right_inv := fun z => by ext; simp }
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    subst hk
    have := a.2
    calc k * (a.1 * c) = a.1 * (a.1⁻¹ * k * a.1) * c := by group
      _ = a.1 * (c * k * c⁻¹) * c := by rw [this]
      _ = a.1 * c * k := by group
  · have hz := Subgroup.mem_centralizer_iff.1 z.2 g rfl
    calc (z.1 * c⁻¹)⁻¹ * g * (z.1 * c⁻¹) = c * (z.1⁻¹ * (g * z.1)) * c⁻¹ := by group
      _ = c * (z.1⁻¹ * (z.1 * g)) * c⁻¹ := by rw [hz]
      _ = c * g * c⁻¹ := by group

lemma card_conj_fiber_of_not (g h : G) (hc : ¬ IsConj g h) :
    Fintype.card {a : G // a⁻¹ * g * a = h} = 0 := by
  rw [Fintype.card_eq_zero_iff]
  refine ⟨fun a => hc (isConj_iff.2 ⟨a.1⁻¹, ?_⟩)⟩
  simpa using a.2

/-- Class-equation count: `#{a ∈ G | a⁻¹ g a ∈ H} = |C_G(g)| · #{h ∈ H | h ~ g}`. -/
lemma card_conj_mem_eq (H : Subgroup G) (g : G) :
    Fintype.card {a : G // a⁻¹ * g * a ∈ H} =
      Fintype.card (Subgroup.centralizer ({g} : Set G)) * Fintype.card {h : H // IsConj g h} := by
  let F : {a : G // a⁻¹ * g * a ∈ H} → H := fun a => ⟨a.1⁻¹ * g * a.1, a.2⟩
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv F), Fintype.card_sigma]
  have hfib : ∀ h : H, Fintype.card {a // F a = h} =
      if IsConj g h then Fintype.card (Subgroup.centralizer ({g} : Set G)) else 0 := by
    intro h
    have e : {a // F a = h} ≃ {a : G // a⁻¹ * g * a = h} :=
      { toFun := fun a => ⟨a.1.1, by have := a.2; simp only [F, Subtype.ext_iff] at this; exact this⟩
        invFun := fun a => ⟨⟨a.1, by rw [a.2]; exact h.2⟩, by ext; exact a.2⟩
        left_inv := fun a => by rfl
        right_inv := fun a => by rfl }
    rw [Fintype.card_congr e]
    split_ifs with hc
    · exact card_conj_fiber g h hc
    · exact card_conj_fiber_of_not g h hc
  simp_rw [hfib]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, smul_eq_mul,
    mul_comm]
  congr 1
  exact (Fintype.card_subtype _).symm

/-- For a stabilizer, `#{a | a⁻¹ g a ∈ Stab(x)} = |Stab(x)| · #{y ∈ G·x | g·y = y}`. -/
lemma card_conj_mem_stabilizer {X : Type*} [MulAction G X] [Fintype X] (x : X) (g : G) :
    Fintype.card {a : G // a⁻¹ * g * a ∈ MulAction.stabilizer G x} =
      Fintype.card (MulAction.stabilizer G x) *
        Fintype.card {y : MulAction.orbit G x // g • (y : X) = y} := by
  have hmem : ∀ a : G, a⁻¹ * g * a ∈ MulAction.stabilizer G x ↔ g • a • x = a • x := by
    intro a
    rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, inv_smul_eq_iff]
  let F : {a : G // a⁻¹ * g * a ∈ MulAction.stabilizer G x} →
      {y : MulAction.orbit G x // g • (y : X) = y} :=
    fun a => ⟨⟨a.1 • x, MulAction.mem_orbit x a.1⟩, (hmem a.1).1 a.2⟩
  rw [← Fintype.card_congr (Equiv.sigmaFiberEquiv F), Fintype.card_sigma]
  have hfib : ∀ y, Fintype.card {a // F a = y} = Fintype.card (MulAction.stabilizer G x) := by
    intro y
    obtain ⟨b, hb⟩ := y.1.2
    simp only at hb
    refine Fintype.card_congr
      { toFun := fun a => ⟨b⁻¹ * a.1.1, ?_⟩
        invFun := fun s => ⟨⟨b * s.1, ?_⟩, ?_⟩
        left_inv := fun a => by ext; simp
        right_inv := fun s => by ext; simp }
    · have h1 := a.2
      simp only [F, Subtype.ext_iff] at h1
      rw [MulAction.mem_stabilizer_iff, mul_smul, h1, ← hb, inv_smul_smul]
    · rw [hmem, mul_smul, MulAction.mem_stabilizer_iff.1 s.2, hb]
      exact y.2
    · ext
      simp only [F]
      rw [mul_smul, MulAction.mem_stabilizer_iff.1 s.2, hb]
  simp_rw [hfib]
  rw [Finset.sum_const, smul_eq_mul, Finset.card_univ, mul_comm]

/-- Transport along an automorphism:
`#{a | a⁻¹ g a ∈ θ(H)} = #{b | b⁻¹ θ⁻¹(g) b ∈ H}`. -/
lemma card_conj_mem_map (θ : G ≃* G) (H : Subgroup G) (g : G) :
    Fintype.card {a : G // a⁻¹ * g * a ∈ H.map θ.toMonoidHom} =
      Fintype.card {b : G // b⁻¹ * θ.symm g * b ∈ H} := by
  refine Fintype.card_congr (Equiv.subtypeEquiv θ.symm.toEquiv ?_)
  intro a
  rw [Subgroup.mem_map_equiv]
  simp [map_mul, map_inv]

/-- `Nat.card` form of `card_conj_mem_eq`. -/
lemma natCard_conj_mem_eq (H : Subgroup G) (g : G) :
    Nat.card {a : G // a⁻¹ * g * a ∈ H} =
      Nat.card (Subgroup.centralizer ({g} : Set G)) * Nat.card {h : H // IsConj g h} := by
  simp only [Nat.card_eq_fintype_card]
  exact card_conj_mem_eq H g

/-- `Nat.card` form of `card_conj_mem_stabilizer`. -/
lemma natCard_conj_mem_stabilizer {X : Type*} [MulAction G X] [Finite X] (x : X) (g : G) :
    Nat.card {a : G // a⁻¹ * g * a ∈ MulAction.stabilizer G x} =
      Nat.card (MulAction.stabilizer G x) *
        Nat.card {y : MulAction.orbit G x // g • (y : X) = y} := by
  haveI := Fintype.ofFinite X
  simp only [Nat.card_eq_fintype_card]
  exact card_conj_mem_stabilizer x g

/-- `Nat.card` form of `card_conj_mem_map`. -/
lemma natCard_conj_mem_map (θ : G ≃* G) (H : Subgroup G) (g : G) :
    Nat.card {a : G // a⁻¹ * g * a ∈ H.map θ.toMonoidHom} =
      Nat.card {b : G // b⁻¹ * θ.symm g * b ∈ H} := by
  simp only [Nat.card_eq_fintype_card]
  exact card_conj_mem_map θ H g

end counting

end SteklovGroup

end
