module

public import Mathlib

/-!
# Fixed vectors of a matrix and of its transpose

Over a finite field, a square matrix `M` and its transpose fix the same number of vectors.
This is the linear-algebra input in the proof that the point and line stabilizers in
`GL(3, 𝔽₂)` are almost conjugate (Lemma 3.1.1 of the paper): `dim ker (M - 1) = dim ker (Mᵀ - 1)`
because a matrix and its transpose have the same rank.
-/

@[expose] public section

open Matrix

open scoped Classical

noncomputable section

namespace SteklovLinear

variable {K : Type*} [Field K] [Fintype K] {n : Type*} [Fintype n] [DecidableEq n]

/-- The kernel of a square matrix has `|K|^(|n| - rank A)` elements. -/
lemma card_mulVec_eq_zero (A : Matrix n n K) :
    Fintype.card {v : n → K // A *ᵥ v = 0} = Fintype.card K ^ (Fintype.card n - A.rank) := by
  have e : {v : n → K // A *ᵥ v = 0} ≃ LinearMap.ker A.mulVecLin :=
    Equiv.subtypeEquivRight (fun v => by simp)
  rw [Fintype.card_congr e, Module.card_eq_pow_finrank (K := K)]
  congr 1
  have h := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  have hr : A.rank = Module.finrank K (LinearMap.range A.mulVecLin) := rfl
  omega

/-- A matrix and its transpose fix the same number of vectors. -/
lemma card_fixed_transpose (M : Matrix n n K) :
    Fintype.card {v : n → K // M *ᵥ v = v} = Fintype.card {v : n → K // Mᵀ *ᵥ v = v} := by
  have e1 : {v : n → K // M *ᵥ v = v} ≃ {v : n → K // (M - 1) *ᵥ v = 0} :=
    Equiv.subtypeEquivRight (fun v => by simp [sub_mulVec, sub_eq_zero])
  have e2 : {v : n → K // Mᵀ *ᵥ v = v} ≃ {v : n → K // (M - 1)ᵀ *ᵥ v = 0} :=
    Equiv.subtypeEquivRight (fun v => by simp [sub_mulVec, sub_eq_zero, transpose_sub])
  rw [Fintype.card_congr e1, Fintype.card_congr e2, card_mulVec_eq_zero, card_mulVec_eq_zero,
    rank_transpose]

/-- `Nat.card` form of `card_fixed_transpose`. -/
lemma natCard_fixed_transpose (M : Matrix n n K) :
    Nat.card {v : n → K // M *ᵥ v = v} = Nat.card {v : n → K // Mᵀ *ᵥ v = v} := by
  simp only [Nat.card_eq_fintype_card]
  exact card_fixed_transpose M

end SteklovLinear

end
