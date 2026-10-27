module

public import RequestProject.GroupTheory

/-!
# The representation-theoretic core of the Sunada argument (Proposition 3.3.1)

The proof of Proposition 3.3.1 reduces, for each Steklov eigenvalue `σ`, to the following
purely algebraic statement about the finite-dimensional `G`-module `E_σ`:

> if `H₁, H₂ ≤ G` are almost conjugate then `dim E^{H₁} = dim E^{H₂}`.

This file proves that statement for every finite-dimensional representation of a finite group
over a field of characteristic zero (`sunada_finrank_invariants_eq`), following the paper's
argument: `dim E^H = tr P_H = |H|⁻¹ ∑_{h ∈ H} χ(h)` and the class-function sums over `H₁` and
`H₂` agree.  We also prove the group-theoretic step of the noncongruence argument: an
isomorphism of `G`-sets `G/H₁ ≃ G/H₂` forces `H₁` and `H₂` to be conjugate
(`areConjugate_of_equivariant`).

What is *not* formalized here is the analytic identification of `E^{H_j}` with the Steklov
eigenspaces of the quotient orbisurfaces (Dirichlet-to-Neumann operator, harmonic extension).
-/

@[expose] public section

open scoped Classical

noncomputable section

namespace SteklovGroup

variable {G : Type*} [Group G] [Fintype G]

/-- Size of the conjugacy class of `g`. -/
def conjCard (g : G) : ℕ := (Finset.univ.filter (fun g' => IsConj g g')).card

lemma conjCard_pos (g : G) : 0 < conjCard g :=
  Finset.card_pos.2 ⟨g, Finset.mem_filter.2 ⟨Finset.mem_univ _, IsConj.refl g⟩⟩

lemma conjCard_eq_of_isConj {g h : G} (hc : IsConj g h) : conjCard g = conjCard h := by
  unfold conjCard
  congr 1
  ext g'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h' => hc.symm.trans h', fun h' => hc.trans h'⟩

lemma card_isConj_left (h : G) :
    (Finset.univ.filter (fun g => IsConj g h)).card = conjCard h := by
  unfold conjCard
  congr 1
  ext g
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact isConj_comm

variable {k : Type*} [Field k] [CharZero k]

/-- A class-function sum over a subgroup only depends on the numbers `#{h ∈ H | h ~ g}`:
`∑_{h ∈ H} f(h) = ∑_{g ∈ G} f(g)/|cl(g)| · #{h ∈ H | h ~ g}`. -/
lemma sum_subgroup_classFunction (H : Subgroup G) (f : G → k)
    (hf : ∀ g h, IsConj g h → f g = f h) :
    ∑ h : H, f h = ∑ g : G, f g / conjCard g *
      ((Finset.univ.filter (fun h : H => IsConj g h)).card : k) := by
  have step1 : ∀ g : G, f g / conjCard g * ((Finset.univ.filter (fun h : H => IsConj g h)).card : k)
      = ∑ h : H, if IsConj g h then f h / conjCard (h : G) else 0 := by
    intro g
    rw [Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    split_ifs with hc
    · rw [hf g h hc, conjCard_eq_of_isConj hc]; simp
    · simp
  simp_rw [step1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, card_isConj_left, nsmul_eq_mul]
  have : (conjCard (h : G) : k) ≠ 0 := by exact_mod_cast (conjCard_pos (h : G)).ne'
  field_simp

/-- Class-function sums over almost conjugate subgroups agree. -/
theorem sum_classFunction_eq_of_almostConjugate {H₁ H₂ : Subgroup G}
    (hac : AlmostConjugate H₁ H₂) (f : G → k) (hf : ∀ g h, IsConj g h → f g = f h) :
    ∑ h : H₁, f h = ∑ h : H₂, f h := by
  rw [sum_subgroup_classFunction H₁ f hf, sum_subgroup_classFunction H₂ f hf]
  refine Finset.sum_congr rfl fun g _ => ?_
  have := hac g
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype] at this
  rw [this]

/-- Almost conjugate subgroups have the same order. -/
theorem card_eq_of_almostConjugate {H₁ H₂ : Subgroup G} (hac : AlmostConjugate H₁ H₂) :
    Fintype.card H₁ = Fintype.card H₂ := by
  have := sum_classFunction_eq_of_almostConjugate (k := ℚ) hac (fun _ => 1) (fun _ _ _ => rfl)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_inj] at this
  exact this

variable {V : Type*} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- `dim V^G = |G|⁻¹ ∑_g tr ρ(g)` (trace of the averaging projection). -/
lemma finrank_invariants_eq_average (ρ : Representation k G V) :
    (Module.finrank k ρ.invariants : k) =
      (Fintype.card G : k)⁻¹ * ∑ g : G, LinearMap.trace k V (ρ g) := by
  haveI : Invertible (Fintype.card G : k) := invertibleOfNonzero (by exact_mod_cast Fintype.card_ne_zero)
  rw [← (Representation.isProj_averageMap ρ).trace]
  simp [Representation.averageMap, GroupAlgebra.average, _root_.map_sum]

/-- **Sunada's lemma (algebraic core of Proposition 3.3.1).** For a finite-dimensional
representation `ρ` of a finite group over a field of characteristic zero and almost conjugate
subgroups `H₁, H₂`, the spaces of `H₁`- and `H₂`-invariants have the same dimension. -/
theorem sunada_finrank_invariants_eq (ρ : Representation k G V) {H₁ H₂ : Subgroup G}
    (hac : AlmostConjugate H₁ H₂) :
    Module.finrank k (Representation.invariants (ρ.comp H₁.subtype)) =
      Module.finrank k (Representation.invariants (ρ.comp H₂.subtype)) := by
  have hf : ∀ g h : G, IsConj g h →
      LinearMap.trace k V (ρ g) = LinearMap.trace k V (ρ h) := by
    intro g h hc
    obtain ⟨c, rfl⟩ := isConj_iff.1 hc
    rw [map_mul ρ (c * g) c⁻¹, LinearMap.trace_mul_comm, ← map_mul, inv_mul_cancel_left]
  have h1 := finrank_invariants_eq_average (ρ.comp H₁.subtype)
  have h2 := finrank_invariants_eq_average (ρ.comp H₂.subtype)
  have hs := sum_classFunction_eq_of_almostConjugate hac
    (fun g => LinearMap.trace k V (ρ g)) hf
  have hc := card_eq_of_almostConjugate hac
  simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at h1 h2
  rw [hs, hc, ← h2] at h1
  exact_mod_cast h1

/-- An isomorphism of `G`-sets `G/H₁ ≃ G/H₂` forces `H₁` and `H₂` to be conjugate. -/
theorem areConjugate_of_equivariant {G : Type*} [Group G] (H₁ H₂ : Subgroup G)
    (e : G ⧸ H₁ ≃ G ⧸ H₂) (he : ∀ (g : G) (q : G ⧸ H₁), e (g • q) = g • e q) :
    AreConjugate H₁ H₂ := by
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (e ((1 : G) : G ⧸ H₁))
  have hstab : H₁ = H₂.map (MulAut.conj a).toMonoidHom := by
    have h1 : MulAction.stabilizer G (e ((1 : G) : G ⧸ H₁)) = H₁ := by
      ext g
      rw [MulAction.mem_stabilizer_iff, ← he, e.apply_eq_iff_eq, ← MulAction.mem_stabilizer_iff,
        MulAction.stabilizer_quotient]
    have h2 : (a : G ⧸ H₂) = a • ((1 : G) : G ⧸ H₂) := by
      rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
    rw [← h1, ← ha, h2, MulAction.stabilizer_smul_eq_stabilizer_map_conj,
      MulAction.stabilizer_quotient]
  refine ⟨a⁻¹, ?_⟩
  rw [hstab, Subgroup.map_map]
  conv_lhs => rw [← Subgroup.map_id H₂]
  congr 1
  ext g
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulAut.conj_apply, MonoidHom.id_apply]
  group

end SteklovGroup

end
