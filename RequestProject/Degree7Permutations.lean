module

public import Mathlib
public import RequestProject.GroupInput

/-!
# The degree-seven candidate: permutation certificates

**Status: finite group-theoretic certificates only.**  Nothing here proves that the polynomials
of `Degree7Polynomial.lean` have the monodromy `(x, y₁)` or `(x, y₂)`; that link (a Riemann
existence / monodromy computation) is **not** formalized.

Zero-based permutations of `Fin 7` (Mathlib's `cycleType` omits fixed points, so `{3, 3}` is the
cycle type `(3,3,1)` and `{2, 2}` is `(2,2,1,1,1)`):
`x = (0 1)(2 3)`, `y₁ = (1 2 4)(3 5 6)`, `y₂ = (1 4 2)(3 5 6)`.

Kernel-checked counts over all of `S₇` are in `Degree7Counts.lean`:
* `card_cycleType33`: exactly `280` permutations have cycle type `(3,3,1)`;
* `card_good`: exactly `96` of them have `x y` a `7`-cycle;
* `card_centralizer`: the centralizer of `x` has `48` elements;
* `good_eq_orbits`: the `96` choices are the disjoint union of the two orbits (of size `48`) of
  `y₁`, `y₂` under conjugation by the centralizer.

Identification with the point/line Gassmann pair of `GroupInput.lean`:
* `rhoP_x`, `rhoP_y`: the action of `GL(3, 𝔽₂)` on `G/H_P` (points), transported to `Fin 7` by an
  explicit relabeling, sends the generators `x, y` to `x, y₂`; `rhoL_x`, `rhoL_y`: the action on
  `G/H_L` (lines) sends them to `x, y₁`;
* `rhoP_injective`, `rhoL_injective`: both actions are faithful;
* `card_closure_y1`, `card_closure_y2`: `⟨x, y₁⟩` and `⟨x, y₂⟩` have order `168`.
-/

@[expose] public section

open Equiv Finset Matrix

noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace Degree7

/-- `x = (0 1)(2 3)`. -/
def x7 : Perm (Fin 7) := c[0, 1] * c[2, 3]
/-- `y₁ = (1 2 4)(3 5 6)`, i.e. the tuple `(0,2,4,5,1,6,3)`. -/
def y1 : Perm (Fin 7) := c[1, 2, 4] * c[3, 5, 6]
/-- `y₂ = (1 4 2)(3 5 6)`, i.e. the tuple `(0,4,1,5,2,6,3)`. -/
def y2 : Perm (Fin 7) := c[1, 4, 2] * c[3, 5, 6]

theorem x7_tuple : (List.ofFn x7) = [1, 0, 3, 2, 4, 5, 6] := by decide
theorem y1_tuple : (List.ofFn y1) = [0, 2, 4, 5, 1, 6, 3] := by decide
theorem y2_tuple : (List.ofFn y2) = [0, 4, 1, 5, 2, 6, 3] := by decide

/-- Number of fixed points. -/
def nfix (σ : Perm (Fin 7)) : ℕ := (univ.filter fun i => σ i = i).card

lemma nfix_add_support (σ : Perm (Fin 7)) : nfix σ + σ.support.card = 7 := by
  have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin 7)))
    (p := fun i => σ i = i)
  have hs : σ.support = univ.filter (fun a => ¬ σ a = a) := by ext; simp [Perm.mem_support]
  rw [nfix, hs]
  simpa using this

lemma mem_cycleType_eq_prime {σ : Perm (Fin 7)} {p : ℕ} (hp : p.Prime) (hσ : σ ^ p = 1)
    {m : ℕ} (hm : m ∈ σ.cycleType) : m = p := by
  have h1 : m ∣ p := (Perm.dvd_of_mem_cycleType hm).trans (orderOf_dvd_of_pow_eq_one hσ)
  have h2 := Perm.two_le_of_mem_cycleType hm
  rcases (Nat.dvd_prime hp).1 h1 with h | h
  · omega
  · exact h

/-- Cycle type `(3,3,1)` ⇔ `σ³ = 1` and exactly one fixed point. -/
theorem cycleType33_iff (σ : Perm (Fin 7)) :
    σ.cycleType = {3, 3} ↔ σ ^ 3 = 1 ∧ nfix σ = 1 := by
  have hns := nfix_add_support σ
  constructor
  · intro h
    have hord : orderOf σ = 3 := by rw [← Perm.lcm_cycleType, h]; decide
    refine ⟨by rw [← hord]; exact pow_orderOf_eq_one σ, ?_⟩
    have : σ.support.card = 6 := by rw [← Perm.sum_cycleType, h]; decide
    omega
  · rintro ⟨h3, h1⟩
    have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 3 :=
      Multiset.eq_replicate.2 ⟨rfl, fun m hm => mem_cycleType_eq_prime Nat.prime_three h3 hm⟩
    have hsum : σ.cycleType.sum = 6 := by rw [Perm.sum_cycleType]; omega
    rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hk : Multiset.card σ.cycleType = 2 := by omega
    rw [hrep, hk]; decide

/-- `7`-cycle ⇔ `σ⁷ = 1`, `σ ≠ 1`. -/
theorem cycleType7_iff (σ : Perm (Fin 7)) : σ.cycleType = {7} ↔ σ ^ 7 = 1 ∧ σ ≠ 1 := by
  have hns := nfix_add_support σ
  constructor
  · intro h
    have hord : orderOf σ = 7 := by rw [← Perm.lcm_cycleType, h]; decide
    refine ⟨by have := pow_orderOf_eq_one σ; rwa [hord] at this, fun h1 => ?_⟩
    rw [h1, Perm.cycleType_one] at h
    exact absurd h (by decide)
  · rintro ⟨h7, h1⟩
    have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 7 :=
      Multiset.eq_replicate.2 ⟨rfl, fun m hm => mem_cycleType_eq_prime (by norm_num) h7 hm⟩
    have hsum : σ.cycleType.sum ≤ 7 := by rw [Perm.sum_cycleType]; omega
    rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hne : Multiset.card σ.cycleType ≠ 0 := by
      intro h0
      exact h1 (Perm.cycleType_eq_zero.1 (Multiset.card_eq_zero.1 h0))
    have hk : Multiset.card σ.cycleType = 1 := by omega
    rw [hrep, hk]; rfl

/-- Migration helper: cycle type `(2,2,1,1,1)` from `σ² = 1` and three fixed points (a symbolic
replacement for kernel evaluation of the noncomputable `cycleType`). -/
private lemma cycleType22_of_aux (σ : Perm (Fin 7)) (h2 : σ ^ 2 = 1) (h3 : nfix σ = 3) :
    σ.cycleType = {2, 2} := by
  have hns := nfix_add_support σ
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate.2 ⟨rfl, fun m hm => mem_cycleType_eq_prime Nat.prime_two h2 hm⟩
  have hsum : σ.cycleType.sum = 4 := by rw [Perm.sum_cycleType]; omega
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hk : Multiset.card σ.cycleType = 2 := by omega
  rw [hrep, hk]; decide

theorem cycleType_x7 : x7.cycleType = {2, 2} :=
  cycleType22_of_aux x7 (by first | decide | decide +kernel) (by first | decide | decide +kernel)
theorem cycleType_y1 : y1.cycleType = {3, 3} :=
  (cycleType33_iff y1).2
    ⟨by first | decide | decide +kernel, by first | decide | decide +kernel⟩
theorem cycleType_y2 : y2.cycleType = {3, 3} :=
  (cycleType33_iff y2).2
    ⟨by first | decide | decide +kernel, by first | decide | decide +kernel⟩
set_option maxRecDepth 100000 in
theorem cycleType_x7y1 : (x7 * y1).cycleType = {7} :=
  (cycleType7_iff (x7 * y1)).2 ⟨by decide +kernel, by decide +kernel⟩
set_option maxRecDepth 100000 in
theorem cycleType_x7y2 : (x7 * y2).cycleType = {7} :=
  (cycleType7_iff (x7 * y2)).2 ⟨by decide +kernel, by decide +kernel⟩

/-! ### Identification with the point/line actions of `GL(3, 𝔽₂)` -/

open GL3F2

/-- Relabeling for the point action. -/
def σP : Perm (Fin 7) := c[0, 1, 4, 6, 5, 3]
/-- Relabeling for the line action. -/
def σL : Perm (Fin 7) := c[0, 1, 4, 5, 3]

/-- The point action of `G = GL(3, 𝔽₂)` on `G/H_P`, transported to `Fin 7`. -/
def rhoP : G →* Perm (Fin 7) :=
  (MulAut.conj σP).toMonoidHom.comp
    ((Equiv.permCongrHom quotEquiv).toMonoidHom.comp (MulAction.toPermHom G (G ⧸ HP)))

/-- The line action of `G` on `G/H_L`, transported to `Fin 7`. -/
def rhoL : G →* Perm (Fin 7) :=
  (MulAut.conj σL).toMonoidHom.comp
    ((Equiv.permCongrHom quotEquivL).toMonoidHom.comp (MulAction.toPermHom G (G ⧸ HL)))

lemma rhoP_apply (g : G) (i : Fin 7) :
    rhoP g i = σP ⟨idx (g.val *ᵥ vecs (σP⁻¹ i)) - 1, idx_lt _⟩ := by
  simp only [rhoP, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Perm.mul_apply]
  rw [← quotEquiv_smul]
  rfl

lemma rhoL_apply (g : G) (i : Fin 7) :
    rhoL g i = σL ⟨idx ((θ g).val *ᵥ vecs (σL⁻¹ i)) - 1, idx_lt _⟩ := by
  simp only [rhoL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Perm.mul_apply]
  rw [← quotEquivL_smul]
  rfl

theorem rhoP_x : rhoP x = x7 := by
  ext i; rw [rhoP_apply]; revert i; decide
theorem rhoP_y : rhoP y = y2 := by
  ext i; rw [rhoP_apply]; revert i; decide
theorem rhoL_x : rhoL x = x7 := by
  ext i; rw [rhoL_apply]; revert i; decide
theorem rhoL_y : rhoL y = y1 := by
  ext i; rw [rhoL_apply]; revert i; decide

/-- A matrix over `𝔽₂` fixing all seven nonzero vectors is the identity. -/
lemma matrix_eq_one_of_fix (M : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (h : ∀ i : Fin 7, idx (M *ᵥ vecs i) - 1 = i) : M = 1 := by
  revert h
  revert M
  decide +kernel

theorem rhoP_injective : Function.Injective rhoP := by
  rw [injective_iff_map_eq_one]
  intro g hg
  apply Units.ext
  refine matrix_eq_one_of_fix g.val fun i => ?_
  have := congrArg (fun p : Perm (Fin 7) => p (σP i)) hg
  have hi : σP⁻¹ (σP i) = i := by simp
  simp only [rhoP_apply, hi, Perm.one_apply] at this
  have := congrArg Fin.val (σP.injective this)
  simpa using this

theorem rhoL_injective : Function.Injective rhoL := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hθ : θ g = 1 := by
    apply Units.ext
    refine matrix_eq_one_of_fix (θ g).val fun i => ?_
    have := congrArg (fun p : Perm (Fin 7) => p (σL i)) hg
    have hi : σL⁻¹ (σL i) = i := by simp
    simp only [rhoL_apply, hi, Perm.one_apply] at this
    have := congrArg Fin.val (σL.injective this)
    simpa using this
  exact θ.injective (hθ.trans (map_one θ).symm)

lemma card_G : Nat.card G = 168 := by
  rw [Matrix.card_GL_field, ZMod.card]; decide

theorem closure_y2_eq_range : Subgroup.closure ({x7, y2} : Set (Perm (Fin 7))) = rhoP.range := by
  rw [MonoidHom.range_eq_map, ← closure_xy, MonoidHom.map_closure, Set.image_pair, rhoP_x, rhoP_y]

theorem closure_y1_eq_range : Subgroup.closure ({x7, y1} : Set (Perm (Fin 7))) = rhoL.range := by
  rw [MonoidHom.range_eq_map, ← closure_xy, MonoidHom.map_closure, Set.image_pair, rhoL_x, rhoL_y]

/-- **`⟨x, y₂⟩` has order `168`** (it is the point action of `GL(3, 𝔽₂)`). -/
theorem card_closure_y2 : Nat.card (Subgroup.closure ({x7, y2} : Set (Perm (Fin 7)))) = 168 := by
  rw [closure_y2_eq_range, ← card_G]
  exact (Nat.card_congr (MonoidHom.ofInjective rhoP_injective).toEquiv).symm

/-- **`⟨x, y₁⟩` has order `168`** (it is the line action of `GL(3, 𝔽₂)`). -/
theorem card_closure_y1 : Nat.card (Subgroup.closure ({x7, y1} : Set (Perm (Fin 7)))) = 168 := by
  rw [closure_y1_eq_range, ← card_G]
  exact (Nat.card_congr (MonoidHom.ofInjective rhoL_injective).toEquiv).symm

end Degree7
