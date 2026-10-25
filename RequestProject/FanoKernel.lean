module

public import RequestProject.Degree7Permutations

/-!
# The Fano incidence intertwiner between the point and line actions

Labels: a line label `i : Fin 7` stands for the covector `vecs (σL⁻¹ i)` and a point label
`j : Fin 7` for the vector `vecs (σP⁻¹ j)` (these are the labellings used in `rhoL`, `rhoP`).
The point `j` lies on the line `i` iff the dot product vanishes (`fanoInc`).

Proved here (all finite identities are kernel-checked by `decide`; no `native_decide`):
* `fanoInc_rho`: the incidence relation is invariant: `inc (ρ_L g i) (ρ_P g j) = inc i j` for
  every `g ∈ GL(3, 𝔽₂)`;
* `fanoInc_row`, `fanoInc_col`: every line has `3` points and every point is on `3` lines;
* `fanoInc_rows`, `fanoInc_cols`: `M Mᵀ = 2 I + J` and `Mᵀ M = 2 I + J`;
* `fanoT_mul_transpose`, `fanoT_transpose_mul`: `T = (M + a J)/√2`, `a = (√2 - 3)/7`, is orthogonal;
* `fanoT_rho`: `T (ρ_L g i) (ρ_P g j) = T i j` (equivalently `P_L(g) T = T P_P(g)`).
-/

@[expose] public section

open Equiv Finset Matrix GL3F2

noncomputable section

namespace Degree7

/-- Dot product over `𝔽₂`. -/
def dot3 (u v : V) : ZMod 2 := u 0 * v 0 + u 1 * v 1 + u 2 * v 2

/-- The Fano incidence relation, line label `i`, point label `j`. -/
def fanoInc (i j : Fin 7) : Bool := decide (dot3 (vecs (σL⁻¹ i)) (vecs (σP⁻¹ j)) = 0)

/-- The incidence matrix as natural numbers. -/
def fanoN (i j : Fin 7) : ℕ := if fanoInc i j then 1 else 0

set_option maxRecDepth 100000 in
theorem fanoInc_x7 : ∀ i j : Fin 7, fanoInc (x7 i) (x7 j) = fanoInc i j := by decide +kernel

set_option maxRecDepth 100000 in
theorem fanoInc_y : ∀ i j : Fin 7, fanoInc (y1 i) (y2 j) = fanoInc i j := by decide +kernel

/-- **Invariance of incidence** under the simultaneous line/point action. -/
theorem fanoInc_rho (g : G) (i j : Fin 7) : fanoInc (rhoL g i) (rhoP g j) = fanoInc i j := by
  have hmem : g ∈ Subgroup.closure ({x, y} : Set G) := by rw [closure_xy]; trivial
  revert i j
  induction hmem using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with rfl | rfl
    · intro i j; rw [rhoL_x, rhoP_x]; exact fanoInc_x7 i j
    · intro i j; rw [rhoL_y, rhoP_y]; exact fanoInc_y i j
  | one => intro i j; simp
  | mul a b _ _ ha hb =>
    intro i j; rw [map_mul, map_mul, Perm.mul_apply, Perm.mul_apply, ha, hb]
  | inv a _ ha =>
    intro i j
    have := ha (rhoL a⁻¹ i) (rhoP a⁻¹ j)
    rw [← Perm.mul_apply, ← Perm.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one,
      map_one, Perm.one_apply, Perm.one_apply] at this
    exact this.symm

theorem fanoN_rho (g : G) (i j : Fin 7) : fanoN (rhoL g i) (rhoP g j) = fanoN i j := by
  simp only [fanoN, fanoInc_rho]

set_option maxRecDepth 100000 in
/-- Every line contains three points. -/
theorem fanoInc_row : ∀ i : Fin 7, ∑ j, fanoN i j = 3 := by
  simp only [Fin.sum_univ_seven]; decide +kernel

set_option maxRecDepth 100000 in
/-- Every point lies on three lines. -/
theorem fanoInc_col : ∀ j : Fin 7, ∑ i, fanoN i j = 3 := by
  simp only [Fin.sum_univ_seven]; decide +kernel

set_option maxRecDepth 100000 in
/-- `M Mᵀ = 2 I + J`: two distinct lines meet in exactly one point. -/
theorem fanoInc_rows : ∀ i i' : Fin 7, ∑ j, fanoN i j * fanoN i' j = if i = i' then 3 else 1 := by
  simp only [Fin.sum_univ_seven]; decide +kernel

set_option maxRecDepth 100000 in
/-- `Mᵀ M = 2 I + J`: two distinct points lie on exactly one line. -/
theorem fanoInc_cols : ∀ j j' : Fin 7, ∑ i, fanoN i j * fanoN i j' = if j = j' then 3 else 1 := by
  simp only [Fin.sum_univ_seven]; decide +kernel

/-- The constant `a = (√2 - 3)/7`, a root of `7a² + 6a + 1 = 0`. -/
def fanoA : ℝ := (Real.sqrt 2 - 3) / 7

theorem fanoA_eq : 7 * fanoA ^ 2 + 6 * fanoA + 1 = 0 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  unfold fanoA; nlinarith

/-- The real orthogonal intertwiner `T = (M + a J)/√2`. -/
def fanoT : Matrix (Fin 7) (Fin 7) ℝ := fun i j => ((fanoN i j : ℝ) + fanoA) / Real.sqrt 2

/-- **Intertwining**: `T (ρ_L g i) (ρ_P g j) = T i j` for all `g`. -/
theorem fanoT_rho (g : G) (i j : Fin 7) : fanoT (rhoL g i) (rhoP g j) = fanoT i j := by
  simp only [fanoT, fanoN_rho]

lemma fanoT_sum_aux {fanoN' fanoN'' : Fin 7 → ℕ} {c : ℕ} (hrow1 : (∑ k : Fin 7, (fanoN' k : ℝ)) = 3)
    (hrow2 : (∑ k : Fin 7, (fanoN'' k : ℝ)) = 3)
    (hprod : (∑ k : Fin 7, (fanoN' k : ℝ) * fanoN'' k) = c) :
    ∑ k : Fin 7, ((fanoN' k : ℝ) + fanoA) / Real.sqrt 2 * (((fanoN'' k : ℝ) + fanoA) /
      Real.sqrt 2) = ((c : ℝ) - 1) / 2 := by
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  have : ∀ k : Fin 7, ((fanoN' k : ℝ) + fanoA) / Real.sqrt 2 * (((fanoN'' k : ℝ) + fanoA) /
      Real.sqrt 2) = ((fanoN' k : ℝ) * fanoN'' k + fanoA * fanoN' k + fanoA * fanoN'' k +
        fanoA ^ 2) / 2 := by
    intro k; field_simp; rw [h2]; ring
  rw [Finset.sum_congr rfl fun k _ => this k, ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hprod,
    hrow1, hrow2]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have := fanoA_eq
  push_cast
  linarith

/-- **Orthogonality** `T Tᵀ = I`. -/
theorem fanoT_mul_transpose : fanoT * fanoTᵀ = 1 := by
  ext i i'
  simp only [mul_apply, transpose_apply, fanoT]
  have h := fanoT_sum_aux (fanoN' := fun k => fanoN i k) (fanoN'' := fun k => fanoN i' k)
    (c := if i = i' then 3 else 1) (by exact_mod_cast fanoInc_row i)
    (by exact_mod_cast fanoInc_row i') (by exact_mod_cast fanoInc_rows i i')
  rw [h, one_apply]
  split_ifs <;> norm_num

/-- **Orthogonality** `Tᵀ T = I`. -/
theorem fanoT_transpose_mul : fanoTᵀ * fanoT = 1 := by
  ext j j'
  simp only [mul_apply, transpose_apply, fanoT]
  have h := fanoT_sum_aux (fanoN' := fun k => fanoN k j) (fanoN'' := fun k => fanoN k j')
    (c := if j = j' then 3 else 1) (by exact_mod_cast fanoInc_col j)
    (by exact_mod_cast fanoInc_col j') (by exact_mod_cast fanoInc_cols j j')
  rw [h, one_apply]
  split_ifs <;> norm_num

end Degree7

namespace Degree7

/-- Orthonormal columns of `T`. -/
theorem fanoT_col (j j' : Fin 7) : ∑ i, fanoT i j * fanoT i j' = if j = j' then 1 else 0 := by
  have := congrFun (congrFun fanoT_transpose_mul j) j'
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

/-- Orthonormal rows of `T`. -/
theorem fanoT_row (i i' : Fin 7) : ∑ j, fanoT i j * fanoT i' j = if i = i' then 1 else 0 := by
  have := congrFun (congrFun fanoT_mul_transpose i) i'
  simpa [Matrix.mul_apply, Matrix.one_apply] using this

end Degree7
