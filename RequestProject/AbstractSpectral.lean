module

public import Mathlib
public import RequestProject.AbstractMinMax

/-!
# A spectral theorem for weak (Steklov-type) eigenproblems with a compact boundary map

Let `X` be a real Banach space and `A : X → YA`, `B : X → YB` bounded linear maps into real inner
product spaces such that

* (coercivity) `c ‖x‖² ≤ ‖A x‖² + ‖B x‖²` for some `c > 0`;
* (compactness) `B` is a compact operator;
* the range of `B` is infinite-dimensional.

The *weak eigenproblem* is: `x ≠ 0`, `σ ∈ ℝ` with `⟪A x, A y⟫ = σ ⟪B x, B y⟫` for all `y ∈ X`.
We prove (`SteklovSpectral.spectral_theorem`) that there is a sequence of eigenpairs
`(e k, σ k)` with `σ` nondecreasing, `σ k ≥ 0`, `σ k → ∞`, such that for every `τ ∈ ℝ` the
eigenspace of `τ` is spanned by `{e k | σ k = τ}`, its dimension is the number of `k` with
`σ k = τ` (so the sequence `σ` lists the eigenvalues with multiplicity), and the min–max values
of `‖A x‖² / ‖B x‖²` are exactly `σ k`.

The proof is elementary: eigenvectors are obtained as maximizers of `‖B x‖²` on
`{‖A x‖² + ‖B x‖² = 1}` in successive orthogonal complements (existence by compactness of `B`
and the parallelogram law), and the Euler–Lagrange equation gives the weak eigen-equation.
-/

@[expose] public section

open Filter Topology Set
open scoped ENNReal RealInnerProductSpace

noncomputable section

namespace SteklovSpectral

variable {X YA YB : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup YA] [InnerProductSpace ℝ YA] [NormedAddCommGroup YB] [InnerProductSpace ℝ YB]
  (A : X →L[ℝ] YA) (B : X →L[ℝ] YB)

/-- The energy-plus-boundary bilinear form `a(x, y) = ⟪A x, A y⟫ + ⟪B x, B y⟫`. -/
def aB : X →L[ℝ] X →L[ℝ] ℝ :=
  (innerSL ℝ : YA →L[ℝ] YA →L[ℝ] ℝ).bilinearComp A A +
    (innerSL ℝ : YB →L[ℝ] YB →L[ℝ] ℝ).bilinearComp B B

variable {A B}

lemma aB_apply (x y : X) : aB A B x y = ⟪A x, A y⟫ + ⟪B x, B y⟫ := by
  simp [aB]

lemma aB_comm (x y : X) : aB A B x y = aB A B y x := by
  rw [aB_apply, aB_apply, real_inner_comm (A x), real_inner_comm (B x)]

lemma aB_self (x : X) : aB A B x x = ‖A x‖ ^ 2 + ‖B x‖ ^ 2 := by
  rw [aB_apply, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

lemma aB_self_nonneg (x : X) : 0 ≤ aB A B x x := by rw [aB_self]; positivity

lemma normB_sq_le_aB (x : X) : ‖B x‖ ^ 2 ≤ aB A B x x := by
  rw [aB_self]; nlinarith [sq_nonneg ‖A x‖]

lemma aB_smul_self (t : ℝ) (x : X) : aB A B (t • x) (t • x) = t ^ 2 * aB A B x x := by
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]; ring

lemma aB_add_self (x y : X) :
    aB A B (x + y) (x + y) = aB A B x x + 2 * aB A B x y + aB A B y y := by
  simp only [map_add, ContinuousLinearMap.add_apply]
  rw [aB_comm y x]; ring

lemma aB_sub_self (x y : X) :
    aB A B (x - y) (x - y) = aB A B x x - 2 * aB A B x y + aB A B y y := by
  simp only [map_sub, ContinuousLinearMap.sub_apply]
  rw [aB_comm y x]; ring

lemma continuous_aB_self : Continuous fun x : X => aB A B x x := by
  simp_rw [aB_self]
  have := A.continuous; have := B.continuous
  fun_prop

lemma eq_zero_of_aB_self {c : ℝ} (hc : 0 < c) (hcoer : ∀ x, c * ‖x‖ ^ 2 ≤ aB A B x x) {x : X}
    (hx : aB A B x x = 0) : x = 0 := by
  have := hcoer x
  rw [hx] at this
  have : ‖x‖ ^ 2 ≤ 0 := by nlinarith
  exact norm_eq_zero.1 (by nlinarith [norm_nonneg x])

/-- A real quadratic `α t + β t²` that is `≤ 0` for all `t` has `α = 0`. -/
lemma linear_coeff_eq_zero {α β : ℝ} (h : ∀ t : ℝ, α * t + β * t ^ 2 ≤ 0) : α = 0 := by
  set M := 2 * (|β| + 1)
  have hM : 0 < M := by positivity
  have h1 := h (α / M)
  have h2 : α ^ 2 * (M + β) ≤ 0 := by
    have : α * (α / M) + β * (α / M) ^ 2 = (α ^ 2 * (M + β)) / M ^ 2 := by
      field_simp
    rw [this] at h1
    have := (div_le_iff₀ (by positivity : (0:ℝ) < M ^ 2)).1 h1
    linarith
  have hMb : 0 < M + β := by
    have := neg_abs_le β; simp only [M]; linarith
  have : α ^ 2 ≤ 0 := by
    by_contra hcon; push_neg at hcon; nlinarith
  exact pow_eq_zero_iff (n := 2) two_ne_zero |>.1 (le_antisymm this (sq_nonneg _))

/-- **Euler–Lagrange equation.** If `x ∈ W` maximizes `‖B y‖² / a(y, y)` on `W` with value `s`,
then `⟪B x, B y⟫ = s a(x, y)` for all `y ∈ W`. -/
theorem euler_lagrange {W : Submodule ℝ X} {x : X} (hx : x ∈ W) {s : ℝ}
    (hmax : ∀ y ∈ W, ‖B y‖ ^ 2 ≤ s * aB A B y y) (heq : ‖B x‖ ^ 2 = s * aB A B x x) :
    ∀ y ∈ W, ⟪B x, B y⟫ = s * aB A B x y := by
  intro y hy
  have key : ∀ t : ℝ, (2 * (⟪B x, B y⟫ - s * aB A B x y)) * t +
      (‖B y‖ ^ 2 - s * aB A B y y) * t ^ 2 ≤ 0 := by
    intro t
    have h := hmax (x + t • y) (W.add_mem hx (W.smul_mem t hy))
    rw [aB_add_self, map_add, map_smul, norm_add_sq_real, inner_smul_right, norm_smul,
      Real.norm_eq_abs, mul_pow, sq_abs] at h
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at h
    nlinarith [heq]
  have := linear_coeff_eq_zero key
  linarith

/-- **Existence of a maximizer.** On a closed subspace `W` where `B` does not vanish identically,
`‖B y‖² / a(y, y)` attains its supremum at some `x ∈ W` with `a(x, x) = 1`. -/
theorem exists_maximizer [CompleteSpace X] (hB : IsCompactOperator B) {c : ℝ} (hc : 0 < c)
    (hcoer : ∀ x, c * ‖x‖ ^ 2 ≤ aB A B x x) {W : Submodule ℝ X} (hW : IsClosed (W : Set X))
    (hne : ∃ z ∈ W, B z ≠ 0) :
    ∃ x ∈ W, aB A B x x = 1 ∧ ∀ y ∈ W, ‖B y‖ ^ 2 ≤ ‖B x‖ ^ 2 * aB A B y y := by
  set S : Set ℝ := {r | ∃ x ∈ W, aB A B x x = 1 ∧ r = ‖B x‖ ^ 2}
  have hbdd : BddAbove S := ⟨1, by
    rintro r ⟨x, -, hx1, rfl⟩; rw [← hx1]; exact normB_sq_le_aB x⟩
  have hnorm : ∀ y ∈ W, aB A B y y ≠ 0 → ‖B y‖ ^ 2 / aB A B y y ∈ S := by
    intro y hy hy0
    have hpos : 0 < aB A B y y := lt_of_le_of_ne (aB_self_nonneg y) (Ne.symm hy0)
    set t := (Real.sqrt (aB A B y y))⁻¹
    have ht2 : t ^ 2 = (aB A B y y)⁻¹ := by rw [inv_pow, Real.sq_sqrt hpos.le]
    refine ⟨t • y, W.smul_mem t hy, ?_, ?_⟩
    · rw [aB_smul_self, ht2, inv_mul_cancel₀ hy0]
    · rw [map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, ht2, div_eq_inv_mul]
  set s := sSup S
  have hle : ∀ y ∈ W, ‖B y‖ ^ 2 ≤ s * aB A B y y := by
    intro y hy
    by_cases hy0 : aB A B y y = 0
    · rw [hy0, mul_zero]; have := normB_sq_le_aB (A := A) (B := B) y; rwa [hy0] at this
    · have hpos : 0 < aB A B y y := lt_of_le_of_ne (aB_self_nonneg y) (Ne.symm hy0)
      have := le_csSup hbdd (hnorm y hy hy0)
      rwa [div_le_iff₀ hpos] at this
  obtain ⟨z, hzW, hz0⟩ := hne
  have hz : aB A B z z ≠ 0 := by
    intro h; have := normB_sq_le_aB (A := A) (B := B) z; rw [h] at this
    exact hz0 (norm_eq_zero.1 (by nlinarith [norm_nonneg (B z)]))
  have hSne : S.Nonempty := ⟨_, hnorm z hzW hz⟩
  have hs0 : 0 < s := by
    have h1 := le_csSup hbdd (hnorm z hzW hz)
    have : 0 < ‖B z‖ ^ 2 / aB A B z z :=
      div_pos (by positivity) (lt_of_le_of_ne (aB_self_nonneg z) (Ne.symm hz))
    linarith
  have hseq : ∀ n : ℕ, ∃ x ∈ W, aB A B x x = 1 ∧ s - 1 / ((n : ℝ) + 1) < ‖B x‖ ^ 2 := by
    intro n
    have hlt : s - 1 / ((n : ℝ) + 1) < s := by
      have : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    obtain ⟨r, ⟨x, hxW, hx1, rfl⟩, hr⟩ := exists_lt_of_lt_csSup hSne hlt
    exact ⟨x, hxW, hx1, hr⟩
  choose xs hxsW hxs1 hxsB using hseq
  have hxs_le : ∀ n, ‖B (xs n)‖ ^ 2 ≤ s := fun n => by
    have := hle _ (hxsW n); rwa [hxs1, mul_one] at this
  set R := Real.sqrt (1 / c)
  have hball : ∀ n, xs n ∈ Metric.closedBall (0 : X) R := by
    intro n
    rw [mem_closedBall_zero_iff]
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ hc]; have := hcoer (xs n); rw [hxs1] at this; linarith
  obtain ⟨w, -, φ, hφ, hlim⟩ :=
    ((hB : IsCompactOperator (B : X →ₗ[ℝ] YB)).isCompact_closure_image_closedBall R).tendsto_subseq
      (x := fun n => B (xs n)) (fun n => subset_closure ⟨xs n, hball n, rfl⟩)
  set y := fun n => xs (φ n) with hy
  have hlim' : Tendsto (fun n => B (y n)) atTop (𝓝 w) := hlim
  have hBs : Tendsto (fun n => ‖B (y n)‖ ^ 2) atTop (𝓝 s) := by
    have hlow : Tendsto (fun n => s - 1 / ((φ n : ℝ) + 1)) atTop (𝓝 s) := by
      have h0 : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop
      simpa using (tendsto_const_nhds (x := s)).sub h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => (hxsB (φ n)).le) (fun n => hxs_le (φ n))
  have hw : ‖w‖ ^ 2 = s :=
    tendsto_nhds_unique (((continuous_norm.pow 2).tendsto w).comp hlim') hBs
  have hcauchy : CauchySeq y := by
    rw [cauchySeq_iff_tendsto_dist_atTop_0]
    have hup : Tendsto (fun p : ℕ × ℕ => 4 - ‖B (y p.1) + B (y p.2)‖ ^ 2 / s) atTop (𝓝 0) := by
      have h1 : Tendsto (fun p : ℕ × ℕ => B (y p.1) + B (y p.2)) atTop (𝓝 (w + w)) := by
        rw [← prod_atTop_atTop_eq]
        exact (hlim'.comp tendsto_fst).add (hlim'.comp tendsto_snd)
      have h2 := ((continuous_norm.pow 2).tendsto _).comp h1
      have : (4:ℝ) - ‖w + w‖ ^ 2 / s = 0 := by
        rw [← two_smul ℝ w, norm_smul, mul_pow, hw]; field_simp; norm_num
      rw [← this]
      exact tendsto_const_nhds.sub (h2.div_const s)
    have hbound : ∀ p : ℕ × ℕ,
        dist (y p.1) (y p.2) ≤ Real.sqrt ((4 - ‖B (y p.1) + B (y p.2)‖ ^ 2 / s) / c) := by
      intro p
      apply Real.le_sqrt_of_sq_le
      rw [dist_eq_norm, le_div_iff₀ hc]
      have hpar : aB A B (y p.1 - y p.2) (y p.1 - y p.2) +
          aB A B (y p.1 + y p.2) (y p.1 + y p.2) = 4 := by
        rw [aB_sub_self, aB_add_self]; simp only [y, hxs1]; ring
      have hsum := hle _ (W.add_mem (hxsW (φ p.1)) (hxsW (φ p.2)))
      rw [map_add] at hsum
      have h3 := hcoer (y p.1 - y p.2)
      have h4 : ‖B (y p.1) + B (y p.2)‖ ^ 2 / s ≤ aB A B (y p.1 + y p.2) (y p.1 + y p.2) := by
        rw [div_le_iff₀ hs0]; linarith
      nlinarith
    have hsq : Tendsto (fun p : ℕ × ℕ => Real.sqrt ((4 - ‖B (y p.1) + B (y p.2)‖ ^ 2 / s) / c))
        atTop (𝓝 0) := by
      have h5 := hup.div_const c
      rw [zero_div] at h5
      have := (Real.continuous_sqrt.tendsto 0).comp h5
      first
        | (simp only [Real.sqrt_zero] at this; exact this)
        | simpa [Function.comp_def] using this
        | (rw [Real.sqrt_zero] at this; exact this)
    exact squeeze_zero (fun _ => dist_nonneg) hbound hsq
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hxW : x ∈ W := hW.mem_of_tendsto hx (Eventually.of_forall (fun n => hxsW _))
  have hx1 : aB A B x x = 1 := by
    refine tendsto_nhds_unique ((continuous_aB_self.tendsto x).comp hx) ?_
    simp only [Function.comp_def, y, hxs1]; exact tendsto_const_nhds
  have hBx : B x = w := tendsto_nhds_unique ((B.continuous.tendsto x).comp hx) hlim'
  refine ⟨x, hxW, hx1, ?_⟩
  rw [hBx, hw]; exact hle

/-! ### The recursive construction of eigenvectors -/

variable (A B)

/-- The `a`-orthogonal complement of a finite list of vectors. -/
def orthSub (L : List X) : Submodule ℝ X where
  carrier := {z | ∀ x ∈ L, aB A B z x = 0}
  add_mem' {a b} ha hb x hx := by
    simp only [Set.mem_setOf_eq] at ha hb
    rw [map_add, ContinuousLinearMap.add_apply, ha x hx, hb x hx, add_zero]
  zero_mem' x _ := by simp
  smul_mem' t z hz x hx := by
    simp only [Set.mem_setOf_eq] at hz
    rw [map_smul, ContinuousLinearMap.smul_apply, hz x hx, smul_zero]

/-- The hypotheses of the abstract spectral theorem. -/
structure Hyp : Prop where
  compact : IsCompactOperator B
  coercive : ∃ c > 0, ∀ x, c * ‖x‖ ^ 2 ≤ aB A B x x
  infinite : ¬ FiniteDimensional ℝ (LinearMap.range (B : X →ₗ[ℝ] YB))

/-- `x` maximizes `‖B y‖² / a(y, y)` on the `a`-orthogonal complement of `L`, normalized. -/
def IsMaxVec (L : List X) (x : X) : Prop :=
  x ∈ orthSub A B L ∧ aB A B x x = 1 ∧
    ∀ y ∈ orthSub A B L, ‖B y‖ ^ 2 ≤ ‖B x‖ ^ 2 * aB A B y y

open Classical in
/-- A chosen maximizer (or `0` if none exists). -/
def nextVec (L : List X) : X := if h : ∃ x, IsMaxVec A B L x then h.choose else 0

/-- The first `n` eigenvectors. -/
def vecs : ℕ → List X
  | 0 => []
  | n + 1 => vecs n ++ [nextVec A B (vecs n)]

/-- The `n`-th eigenvector. -/
def eig (n : ℕ) : X := nextVec A B (vecs A B n)

/-- The `n`-th orthogonal complement `{z | a(z, e_i) = 0, i < n}`. -/
def Wn (n : ℕ) : Submodule ℝ X := orthSub A B (vecs A B n)

variable {A B}

lemma isClosed_orthSub (L : List X) : IsClosed (orthSub A B L : Set X) := by
  have : (orthSub A B L : Set X) = ⋂ x ∈ L, {z | aB A B z x = 0} := by
    ext z; simp [orthSub]
  rw [this]
  exact isClosed_biInter (fun x _ =>
    isClosed_eq ((aB A B).continuous.clm_apply continuous_const) continuous_const)

lemma vecs_eq (n : ℕ) : vecs A B n = (List.range n).map (eig A B) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [vecs, List.range_succ, List.map_append, ← ih]; rfl

lemma mem_Wn {n : ℕ} {z : X} : z ∈ Wn A B n ↔ ∀ i < n, aB A B z (eig A B i) = 0 := by
  show (∀ x ∈ vecs A B n, aB A B z x = 0) ↔ _
  rw [vecs_eq]; simp

lemma Wn_mono {m n : ℕ} (h : m ≤ n) : Wn A B n ≤ Wn A B m := fun _ hz =>
  mem_Wn.2 (fun i hi => mem_Wn.1 hz i (lt_of_lt_of_le hi h))

lemma eig_spec {n : ℕ} (h : ∃ x, IsMaxVec A B (vecs A B n) x) :
    IsMaxVec A B (vecs A B n) (eig A B n) := by
  unfold eig nextVec; rw [dif_pos h]; exact h.choose_spec

/-- Orthonormality of the already constructed vectors. -/
lemma orthonormal_of {n : ℕ} (hP : ∀ i < n, IsMaxVec A B (vecs A B i) (eig A B i)) :
    ∀ i < n, ∀ j < n, aB A B (eig A B i) (eig A B j) = if i = j then 1 else 0 := by
  intro i hi j hj
  rcases lt_trichotomy i j with hij | rfl | hij
  · rw [if_neg hij.ne, aB_comm]; exact mem_Wn.1 (hP j hj).1 i hij
  · rw [if_pos rfl]; exact (hP i hi).2.1
  · rw [if_neg hij.ne']; exact mem_Wn.1 (hP i hi).1 j hij

/-- The `a`-orthogonal projection onto the first `n` eigenvectors. -/
def proj (A : X →L[ℝ] YA) (B : X →L[ℝ] YB) (n : ℕ) (z : X) : X :=
  ∑ i ∈ Finset.range n, aB A B z (eig A B i) • eig A B i

lemma aB_proj_eig {n : ℕ}
    (hON : ∀ i < n, ∀ j < n, aB A B (eig A B i) (eig A B j) = if i = j then 1 else 0)
    (z : X) {j : ℕ} (hj : j < n) : aB A B (proj A B n z) (eig A B j) = aB A B z (eig A B j) := by
  unfold proj
  rw [map_sum, ContinuousLinearMap.coe_sum', Finset.sum_apply]
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · rw [hON j hj j hj, if_pos rfl, mul_one]
  · intro i hi hij
    rw [hON i (Finset.mem_range.1 hi) j hj, if_neg hij, mul_zero]
  · intro h; exact absurd (Finset.mem_range.2 hj) h

lemma sub_proj_mem {n : ℕ}
    (hON : ∀ i < n, ∀ j < n, aB A B (eig A B i) (eig A B j) = if i = j then 1 else 0)
    (z : X) : z - proj A B n z ∈ Wn A B n := by
  refine mem_Wn.2 (fun j hj => ?_)
  rw [map_sub, ContinuousLinearMap.sub_apply, aB_proj_eig hON z hj, sub_self]

/-- If the range of `B` is infinite-dimensional, `B` does not vanish on `W_n`. -/
lemma exists_Wn_ne_zero (H : Hyp A B) {n : ℕ}
    (hON : ∀ i < n, ∀ j < n, aB A B (eig A B i) (eig A B j) = if i = j then 1 else 0) :
    ∃ z ∈ Wn A B n, B z ≠ 0 := by
  by_contra hcon
  push_neg at hcon
  apply H.infinite
  set S : Submodule ℝ YB := Submodule.span ℝ ((fun i => B (eig A B i)) '' (Finset.range n : Set ℕ))
  have hS : FiniteDimensional ℝ S :=
    FiniteDimensional.span_of_finite ℝ ((Finset.range n).finite_toSet.image _)
  suffices hle : LinearMap.range (B : X →ₗ[ℝ] YB) ≤ S from Submodule.finiteDimensional_of_le hle
  rintro _ ⟨z, rfl⟩
  have hz : B z = B (proj A B n z) := by
    have := hcon _ (sub_proj_mem hON z)
    rw [map_sub, sub_eq_zero] at this; exact this
  show B z ∈ S
  rw [hz]
  unfold proj
  rw [map_sum]
  refine Submodule.sum_mem _ (fun i hi => ?_)
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

variable [CompleteSpace X]

/-- Every `eig n` is a normalized maximizer on `W_n`. -/
theorem isMaxVec_eig (H : Hyp A B) (n : ℕ) : IsMaxVec A B (vecs A B n) (eig A B n) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨c, hc, hcoer⟩ := H.coercive
    have hON := orthonormal_of ih
    obtain ⟨x, hxW, hx1, hxmax⟩ := exists_maximizer H.compact hc hcoer
      (isClosed_orthSub (vecs A B n)) (exists_Wn_ne_zero H hON)
    exact eig_spec ⟨x, hxW, hx1, hxmax⟩

lemma orthonormal_eig (H : Hyp A B) (i j : ℕ) :
    aB A B (eig A B i) (eig A B j) = if i = j then 1 else 0 :=
  orthonormal_of (n := max i j + 1) (fun k _ => isMaxVec_eig H k) i (by omega) j (by omega)

lemma eig_mem_Wn (H : Hyp A B) (n : ℕ) : eig A B n ∈ Wn A B n := (isMaxVec_eig H n).1

lemma aB_eig_self (H : Hyp A B) (n : ℕ) : aB A B (eig A B n) (eig A B n) = 1 :=
  (isMaxVec_eig H n).2.1

lemma eig_max (H : Hyp A B) (n : ℕ) {y : X} (hy : y ∈ Wn A B n) :
    ‖B y‖ ^ 2 ≤ ‖B (eig A B n)‖ ^ 2 * aB A B y y := (isMaxVec_eig H n).2.2 y hy

lemma eig_ne_zero (H : Hyp A B) (n : ℕ) : eig A B n ≠ 0 := by
  intro h; have := aB_eig_self H n; rw [h] at this; simp at this

variable (A B) in
/-- `s_n = ‖B e_n‖²`, the maximal value of `‖B y‖² / a(y, y)` on `W_n`. -/
def sv (n : ℕ) : ℝ := ‖B (eig A B n)‖ ^ 2

variable (A B) in
/-- The `n`-th eigenvalue `σ_n = 1 / s_n - 1`. -/
def ev (n : ℕ) : ℝ := 1 / sv A B n - 1

lemma orthonormal_lt (H : Hyp A B) (n : ℕ) :
    ∀ i < n, ∀ j < n, aB A B (eig A B i) (eig A B j) = if i = j then 1 else 0 :=
  fun i _ j _ => orthonormal_eig H i j

lemma sv_pos (H : Hyp A B) (n : ℕ) : 0 < sv A B n := by
  obtain ⟨z, hzW, hz0⟩ := exists_Wn_ne_zero H (orthonormal_lt H n)
  have h1 := eig_max H n hzW
  have h2 : 0 < ‖B z‖ ^ 2 := by positivity
  have h3 := aB_self_nonneg (A := A) (B := B) z
  unfold sv
  by_contra hcon
  push_neg at hcon
  nlinarith

lemma sv_le_one (H : Hyp A B) (n : ℕ) : sv A B n ≤ 1 := by
  unfold sv; rw [← aB_eig_self H n]; exact normB_sq_le_aB _

lemma sv_antitone (H : Hyp A B) : Antitone (sv A B) := by
  refine antitone_nat_of_succ_le (fun n => ?_)
  have := eig_max H n (Wn_mono (Nat.le_succ n) (eig_mem_Wn H (n + 1)))
  rwa [aB_eig_self H, mul_one] at this

lemma ev_nonneg (H : Hyp A B) (n : ℕ) : 0 ≤ ev A B n := by
  unfold ev
  have h0 := sv_pos H n
  have : 1 ≤ 1 / sv A B n := by rw [le_div_iff₀ h0, one_mul]; exact sv_le_one H n
  linarith

lemma ev_mono (H : Hyp A B) : Monotone (ev A B) := by
  intro m n hmn
  unfold ev
  have := one_div_le_one_div_of_le (sv_pos H n) (sv_antitone H hmn)
  linarith

/-- The weak eigen-equation for `e_n` in the `a`-form: `⟪B e_n, B y⟫ = s_n a(e_n, y)`. -/
theorem eig_rel (H : Hyp A B) (n : ℕ) :
    ∀ y, ⟪B (eig A B n), B y⟫ = sv A B n * aB A B (eig A B n) y := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hEL := euler_lagrange (W := Wn A B n) (eig_mem_Wn H n) (fun y hy => eig_max H n hy)
      (by rw [aB_eig_self H, mul_one])
    intro y
    have hw := sub_proj_mem (orthonormal_lt H n) y
    have h1 := hEL _ hw
    have h2 : ⟪B (eig A B n), B (proj A B n y)⟫ = 0 := by
      unfold proj
      rw [map_sum, inner_sum]
      refine Finset.sum_eq_zero (fun i hi => ?_)
      have hi' := Finset.mem_range.1 hi
      rw [map_smul, inner_smul_right, real_inner_comm, ih i hi', orthonormal_eig H,
        if_neg hi'.ne]
      ring
    have h3 : aB A B (eig A B n) (proj A B n y) = 0 := by
      rw [aB_comm]
      have := mem_Wn.1 (eig_mem_Wn H n)
      unfold proj
      rw [map_sum, ContinuousLinearMap.coe_sum', Finset.sum_apply]
      refine Finset.sum_eq_zero (fun i hi => ?_)
      rw [map_smul, ContinuousLinearMap.smul_apply, aB_comm (eig A B i),
        this i (Finset.mem_range.1 hi), smul_zero]
    rw [map_sub, inner_sub_right, map_sub, h2, h3, sub_zero, sub_zero] at h1
    exact h1

/-- The weak eigen-equation `⟪A e_n, A y⟫ = σ_n ⟪B e_n, B y⟫`. -/
theorem eig_relA (H : Hyp A B) (n : ℕ) (y : X) :
    ⟪A (eig A B n), A y⟫ = ev A B n * ⟪B (eig A B n), B y⟫ := by
  have h := eig_rel H n y
  rw [aB_apply] at h
  have h0 := sv_pos H n
  unfold ev
  field_simp
  linarith

lemma inner_B_eig (H : Hyp A B) (i j : ℕ) :
    ⟪B (eig A B i), B (eig A B j)⟫ = if i = j then sv A B i else 0 := by
  rw [eig_rel H i, orthonormal_eig H]
  split_ifs <;> simp

/-- `s_n → 0`, by compactness of `B`. -/
theorem sv_tendsto_zero (H : Hyp A B) : Tendsto (sv A B) atTop (𝓝 0) := by
  have hbdd : BddBelow (Set.range (sv A B)) := ⟨0, by rintro _ ⟨n, rfl⟩; exact (sv_pos H n).le⟩
  have hlim := tendsto_atTop_ciInf (sv_antitone H) hbdd
  suffices h : ⨅ n, sv A B n = 0 by rwa [h] at hlim
  by_contra hne
  set L := ⨅ n, sv A B n
  have hL0 : 0 ≤ L := le_ciInf (fun n => (sv_pos H n).le)
  have hL : 0 < L := lt_of_le_of_ne hL0 (Ne.symm hne)
  have hLle : ∀ n, L ≤ sv A B n := fun n => ciInf_le hbdd n
  obtain ⟨c, hc, hcoer⟩ := H.coercive
  set R := Real.sqrt (1 / c)
  have hball : ∀ n, eig A B n ∈ Metric.closedBall (0 : X) R := by
    intro n
    rw [mem_closedBall_zero_iff]
    refine Real.le_sqrt_of_sq_le ?_
    rw [le_div_iff₀ hc]; have := hcoer (eig A B n); rw [aB_eig_self H] at this; linarith
  obtain ⟨w, -, φ, hφ, hlimw⟩ :=
    ((H.compact : IsCompactOperator (B : X →ₗ[ℝ] YB)).isCompact_closure_image_closedBall
      R).tendsto_subseq (x := fun n => B (eig A B n))
      (fun n => subset_closure ⟨eig A B n, hball n, rfl⟩)
  have hcau := hlimw.cauchySeq
  rw [Metric.cauchySeq_iff] at hcau
  obtain ⟨N, hN⟩ := hcau (Real.sqrt L) (Real.sqrt_pos.2 hL)
  have hd := hN (N + 1) (Nat.le_succ N) N le_rfl
  simp only [Function.comp_apply, dist_eq_norm] at hd
  have hne' : φ (N + 1) ≠ φ N := (hφ (Nat.lt_succ_self N)).ne'
  have hsq : ‖B (eig A B (φ (N + 1))) - B (eig A B (φ N))‖ ^ 2 =
      sv A B (φ (N + 1)) + sv A B (φ N) := by
    rw [norm_sub_sq_real, inner_B_eig H, if_neg hne']; unfold sv; ring
  have h1 : ‖B (eig A B (φ (N + 1))) - B (eig A B (φ N))‖ ^ 2 < L := by
    have := Real.sqrt_nonneg L
    calc _ < Real.sqrt L ^ 2 := by
          exact pow_lt_pow_left₀ hd (norm_nonneg _) two_ne_zero
      _ = L := Real.sq_sqrt hL0
  linarith [hLle (φ (N + 1)), hLle (φ N)]

/-- `σ_n → ∞`. -/
theorem ev_tendsto_atTop (H : Hyp A B) : Tendsto (ev A B) atTop atTop := by
  have h1 : Tendsto (sv A B) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨sv_tendsto_zero H, Eventually.of_forall (fun n => sv_pos H n)⟩
  have h2 := h1.inv_tendsto_nhdsGT_zero
  unfold ev
  simp only [one_div]
  exact tendsto_atTop_add_const_right _ (-1) h2 |>.congr (fun n => by rw [Pi.inv_apply]; ring)

/-! ### Eigenspaces and multiplicities -/

variable (A B) in
/-- The weak eigenspace `{x | ∀ y, ⟪A x, A y⟫ = τ ⟪B x, B y⟫}` of `τ ∈ ℝ`. -/
def eigenspace (τ : ℝ) : Submodule ℝ X where
  carrier := {x | ∀ y, ⟪A x, A y⟫ = τ * ⟪B x, B y⟫}
  add_mem' {a b} ha hb y := by
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_add, map_add, inner_add_left, inner_add_left, ha y, hb y]; ring
  zero_mem' y := by simp
  smul_mem' t x hx y := by
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [map_smul, map_smul, real_inner_smul_left, real_inner_smul_left, hx y]; ring

omit [CompleteSpace X] in
lemma mem_eigenspace {τ : ℝ} {x : X} :
    x ∈ eigenspace A B τ ↔ ∀ y, ⟪A x, A y⟫ = τ * ⟪B x, B y⟫ := Iff.rfl

lemma eig_mem_eigenspace (H : Hyp A B) (n : ℕ) : eig A B n ∈ eigenspace A B (ev A B n) :=
  fun y => eig_relA H n y

lemma finite_level (H : Hyp A B) (τ : ℝ) : {k | ev A B k = τ}.Finite := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((ev_tendsto_atTop H).eventually_ge_atTop (τ + 1))
  refine (Set.finite_Iio N).subset (fun k hk => ?_)
  simp only [Set.mem_setOf_eq] at hk
  by_contra hkN
  have := hN k (not_lt.1 hkN)
  linarith

lemma linearIndependent_eig (H : Hyp A B) : LinearIndependent ℝ (eig A B) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  have := congrArg (fun z => aB A B z (eig A B i)) hg
  simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul, orthonormal_eig H, map_zero,
    ContinuousLinearMap.zero_apply] at this
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg hj, mul_zero])
    (fun h => absurd hi h), if_pos rfl, mul_one] at this
  exact this

/-- **Eigenspaces are spanned by the constructed eigenvectors.** -/
theorem eigenspace_eq_span (H : Hyp A B) (τ : ℝ) :
    eigenspace A B τ = Submodule.span ℝ (eig A B '' {k | ev A B k = τ}) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨c, hc, hcoer⟩ := H.coercive
    set S := (finite_level H τ).toFinset
    set x' := x - ∑ k ∈ S, aB A B x (eig A B k) • eig A B k with hx'
    have hspan : ∑ k ∈ S, aB A B x (eig A B k) • eig A B k ∈
        Submodule.span ℝ (eig A B '' {k | ev A B k = τ}) := by
      refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ (Submodule.subset_span ?_))
      exact ⟨k, (finite_level H τ).mem_toFinset.1 hk, rfl⟩
    have hspanE : ∑ k ∈ S, aB A B x (eig A B k) • eig A B k ∈ eigenspace A B τ := by
      refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ ?_)
      have := eig_mem_eigenspace H k
      rwa [show ev A B k = τ from (finite_level H τ).mem_toFinset.1 hk] at this
    have hx'E : x' ∈ eigenspace A B τ := Submodule.sub_mem _ hx hspanE
    have horth : ∀ k, aB A B x' (eig A B k) = 0 := by
      intro k
      have hsum : aB A B (∑ j ∈ S, aB A B x (eig A B j) • eig A B j) (eig A B k) =
          if k ∈ S then aB A B x (eig A B k) else 0 := by
        simp only [map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
          ContinuousLinearMap.smul_apply, smul_eq_mul, orthonormal_eig H]
        split_ifs with hk
        · rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg hj, mul_zero])
            (fun h => absurd hk h), if_pos rfl, mul_one]
        · exact Finset.sum_eq_zero (fun j hj => by
            rw [if_neg (fun h : j = k => hk (h ▸ hj)), mul_zero])
      rw [hx', map_sub, ContinuousLinearMap.sub_apply, hsum]
      split_ifs with hk
      · ring
      · have hne : ev A B k ≠ τ := fun h => hk ((finite_level H τ).mem_toFinset.2 h)
        have h1 := hx (eig A B k)
        have h2 := eig_relA H k x
        rw [real_inner_comm (A (eig A B k)) (A x), real_inner_comm (B (eig A B k)) (B x)] at h1
        have hb : ⟪B (eig A B k), B x⟫ = 0 := by
          have : (ev A B k - τ) * ⟪B (eig A B k), B x⟫ = 0 := by linarith
          exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
        rw [sub_zero, aB_apply, real_inner_comm (A (eig A B k)) (A x),
          real_inner_comm (B (eig A B k)) (B x), h2, hb]; ring
    have hB0 : ‖B x'‖ ^ 2 = 0 := by
      have hle : ∀ n, ‖B x'‖ ^ 2 ≤ sv A B n * aB A B x' x' := fun n =>
        eig_max H n (mem_Wn.2 (fun i _ => horth i))
      have hlim : Tendsto (fun n => sv A B n * aB A B x' x') atTop (𝓝 0) := by
        simpa using (sv_tendsto_zero H).mul_const (aB A B x' x')
      exact le_antisymm (ge_of_tendsto' hlim hle) (sq_nonneg _)
    have hA0 : ‖A x'‖ ^ 2 = 0 := by
      have := hx'E x'
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hB0, mul_zero] at this
      exact this
    have hx'0 : x' = 0 := eq_zero_of_aB_self hc hcoer (by rw [aB_self, hA0, hB0, add_zero])
    have : x = ∑ k ∈ S, aB A B x (eig A B k) • eig A B k := by
      rw [← sub_eq_zero]; exact hx'0
    rw [this]; exact hspan
  · rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    have := eig_mem_eigenspace H k
    rwa [show ev A B k = τ from hk] at this

/-- **Multiplicities.** The dimension of the eigenspace of `τ` equals the number of indices `k`
with `σ_k = τ`. -/
theorem finrank_eigenspace (H : Hyp A B) (τ : ℝ) :
    Module.finrank ℝ (eigenspace A B τ) = Set.ncard {k | ev A B k = τ} := by
  have hfin := finite_level H τ
  set S := hfin.toFinset
  have himg : eig A B '' {k | ev A B k = τ} = Set.range (fun k : S => eig A B k) := by
    ext y; constructor
    · rintro ⟨k, hk, rfl⟩; exact ⟨⟨k, hfin.mem_toFinset.2 hk⟩, rfl⟩
    · rintro ⟨⟨k, hk⟩, rfl⟩; exact ⟨k, hfin.mem_toFinset.1 hk, rfl⟩
  have hli : LinearIndependent ℝ (fun k : S => eig A B k) :=
    (linearIndependent_eig H).comp (fun k : S => (k : ℕ)) Subtype.val_injective
  rw [eigenspace_eq_span H, himg, finrank_span_eq_card hli, Fintype.card_coe,
    Set.ncard_eq_toFinset_card _ hfin]

/-! ### Min–max characterization -/

omit [CompleteSpace X] in
lemma proj_add (n : ℕ) (x y : X) : proj A B n (x + y) = proj A B n x + proj A B n y := by
  unfold proj
  simp only [map_add, ContinuousLinearMap.add_apply, add_smul, Finset.sum_add_distrib]

omit [CompleteSpace X] in
lemma proj_smul (n : ℕ) (t : ℝ) (x : X) : proj A B n (t • x) = t • proj A B n x := by
  unfold proj
  simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]

lemma proj_eig (H : Hyp A B) {n i : ℕ} (hi : i < n) : proj A B n (eig A B i) = eig A B i := by
  unfold proj
  rw [Finset.sum_eq_single i]
  · rw [orthonormal_eig H, if_pos rfl, one_smul]
  · intro j _ hj; rw [orthonormal_eig H, if_neg (Ne.symm hj), zero_smul]
  · intro h; exact absurd (Finset.mem_range.2 hi) h

variable (A B) in
/-- The span of the first `k + 1` eigenvectors. -/
def spanFirst (k : ℕ) : Submodule ℝ X :=
  Submodule.span ℝ (Set.range (fun i : Fin (k + 1) => eig A B i))

lemma eq_proj_of_mem_spanFirst (H : Hyp A B) {k : ℕ} {x : X} (hx : x ∈ spanFirst A B k) :
    x = proj A B (k + 1) x := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact (proj_eig H i.2).symm
  | zero => unfold proj; simp
  | add y z _ _ hy hz => rw [proj_add, ← hy, ← hz]
  | smul t y _ hy => rw [proj_smul, ← hy]

lemma finrank_spanFirst (H : Hyp A B) (k : ℕ) :
    Module.finrank ℝ (spanFirst A B k) = k + 1 := by
  have hli : LinearIndependent ℝ (fun i : Fin (k + 1) => eig A B i) :=
    (linearIndependent_eig H).comp (fun i : Fin (k + 1) => (i : ℕ)) Fin.val_injective
  rw [spanFirst, finrank_span_eq_card hli, Fintype.card_fin]

/-- Rayleigh quotient computations on `span(e_0, …, e_k)`. -/
lemma spanFirst_formulas (H : Hyp A B) {k : ℕ} {x : X} (hx : x ∈ spanFirst A B k) :
    ‖B x‖ ^ 2 = ∑ i ∈ Finset.range (k + 1), aB A B x (eig A B i) ^ 2 * sv A B i ∧
    ‖A x‖ ^ 2 =
      ∑ i ∈ Finset.range (k + 1), aB A B x (eig A B i) ^ 2 * (ev A B i * sv A B i) := by
  have hxp := eq_proj_of_mem_spanFirst H hx
  have hBi : ∀ i, ⟪B (eig A B i), B x⟫ = sv A B i * aB A B x (eig A B i) := fun i => by
    rw [eig_rel H i, aB_comm]
  constructor
  · rw [← real_inner_self_eq_norm_sq]
    have : ⟪B x, B x⟫ = ⟪B (proj A B (k + 1) x), B x⟫ := by rw [← hxp]
    rw [this]
    unfold proj
    rw [map_sum, sum_inner]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, real_inner_smul_left, hBi]; ring
  · rw [← real_inner_self_eq_norm_sq]
    have : ⟪A x, A x⟫ = ⟪A (proj A B (k + 1) x), A x⟫ := by rw [← hxp]
    rw [this]
    unfold proj
    rw [map_sum, sum_inner]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul, real_inner_smul_left, eig_relA H, hBi]; ring

/-- **Min–max equals the constructed eigenvalues**: the `k`-th min–max value of
`‖A x‖² / ‖B x‖²` is `σ_k`. -/
theorem closureMinMax_eq_ev (H : Hyp A B) (k : ℕ) :
    SteklovH1.closureMinMax A B k = ENNReal.ofReal (ev A B k) := by
  unfold SteklovH1.closureMinMax
  apply le_antisymm
  · -- upper bound: the span of the first `k + 1` eigenvectors
    have hadm : Module.finrank ℝ (spanFirst A B k) = k + 1 ∧
        ∀ x ∈ spanFirst A B k, x ≠ 0 → ‖B x‖ₑ ^ 2 ≠ 0 := by
      refine ⟨finrank_spanFirst H k, fun x hx hx0 => ?_⟩
      rw [SteklovH1.enorm_sq_ofReal', Ne, ENNReal.ofReal_eq_zero, not_le]
      by_contra hle
      push_neg at hle
      have hB := (spanFirst_formulas H hx).1
      have hsum0 : ∑ i ∈ Finset.range (k + 1), aB A B x (eig A B i) ^ 2 * sv A B i = 0 :=
        le_antisymm (hB ▸ hle) (Finset.sum_nonneg (fun i _ =>
          mul_nonneg (sq_nonneg _) (sv_pos H i).le))
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
        mul_nonneg (sq_nonneg _) (sv_pos H i).le)] at hsum0
      apply hx0
      rw [eq_proj_of_mem_spanFirst H hx]
      unfold proj
      refine Finset.sum_eq_zero (fun i hi => ?_)
      have := hsum0 i hi
      have hc : aB A B x (eig A B i) = 0 := by
        rcases mul_eq_zero.1 this with h | h
        · exact pow_eq_zero_iff two_ne_zero |>.1 h
        · exact absurd h (sv_pos H i).ne'
      rw [hc, zero_smul]
    refine iInf₂_le_of_le (spanFirst A B k) hadm (iSup₂_le (fun x hx => iSup_le (fun hx0 => ?_)))
    rw [SteklovH1.enorm_sq_ofReal', SteklovH1.enorm_sq_ofReal']
    refine ENNReal.div_le_of_le_mul ?_
    rw [← ENNReal.ofReal_mul (ev_nonneg H k)]
    refine ENNReal.ofReal_le_ofReal ?_
    obtain ⟨hB, hA⟩ := spanFirst_formulas H hx
    rw [hA, hB, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have := ev_mono H hik
    have h0 : 0 ≤ aB A B x (eig A B i) ^ 2 * sv A B i :=
      mul_nonneg (sq_nonneg _) (sv_pos H i).le
    nlinarith
  · -- lower bound: every admissible space meets `W_k`
    refine le_iInf₂ (fun V hV => ?_)
    obtain ⟨hdim, hadm⟩ := hV
    haveI : FiniteDimensional ℝ V := Module.finite_of_finrank_eq_succ hdim
    let f : V →ₗ[ℝ] (Fin k → ℝ) :=
      LinearMap.pi (fun j : Fin k => ((aB A B).flip (eig A B j) : X →ₗ[ℝ] ℝ) ∘ₗ V.subtype)
    have hlt : Module.finrank ℝ (Fin k → ℝ) < Module.finrank ℝ V := by
      rw [Module.finrank_fin_fun, hdim]; omega
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := f) hlt)
    have hxW : (v : X) ∈ Wn A B k := by
      refine mem_Wn.2 (fun i hi => ?_)
      have h := LinearMap.mem_ker.1 hv
      exact congrFun h ⟨i, hi⟩
    have hx0 : (v : X) ≠ 0 := fun h => hv0 (Subtype.ext h)
    have hBne := hadm v v.2 hx0
    refine le_iSup₂_of_le (v : X) v.2 (le_iSup_of_le hx0 ?_)
    rw [SteklovH1.enorm_sq_ofReal'] at hBne
    rw [SteklovH1.enorm_sq_ofReal', SteklovH1.enorm_sq_ofReal',
      ENNReal.le_div_iff_mul_le (Or.inl hBne) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul (ev_nonneg H k)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hmax := eig_max H k hxW
    rw [aB_self] at hmax
    have hs := sv_pos H k
    change ‖B (v : X)‖ ^ 2 ≤ sv A B k * (‖A v‖ ^ 2 + ‖B v‖ ^ 2) at hmax
    have h1 : ‖B (v : X)‖ ^ 2 / sv A B k ≤ ‖A v‖ ^ 2 + ‖B v‖ ^ 2 := by
      rw [div_le_iff₀ hs]; linarith
    have h2 : (1 / sv A B k - 1) * ‖B (v : X)‖ ^ 2 = ‖B (v : X)‖ ^ 2 / sv A B k - ‖B v‖ ^ 2 := by
      field_simp
    unfold ev; rw [h2]; linarith

/-- The weak eigenvalues are exactly the values of `σ`. -/
theorem eigenspace_ne_bot_iff (H : Hyp A B) (τ : ℝ) :
    eigenspace A B τ ≠ ⊥ ↔ ∃ k, ev A B k = τ := by
  constructor
  · intro h
    by_contra hcon
    push_neg at hcon
    apply h
    rw [eigenspace_eq_span H]
    have : {k | ev A B k = τ} = ∅ := Set.eq_empty_iff_forall_notMem.2 (fun k hk => hcon k hk)
    rw [this, Set.image_empty, Submodule.span_empty]
  · rintro ⟨k, rfl⟩ hbot
    have := eig_mem_eigenspace H k
    rw [hbot, Submodule.mem_bot] at this
    exact eig_ne_zero H k this

/-- **Abstract spectral theorem for the weak eigenproblem** `⟪A x, A y⟫ = σ ⟪B x, B y⟫`
with a compact boundary map `B`. There are eigenvectors `e k` with eigenvalues `σ k`,
nondecreasing, nonnegative and tending to `∞`, such that every eigenspace is spanned by the `e k`
with `σ k = τ` and has dimension `#{k | σ k = τ}` (so `σ` lists all eigenvalues with
multiplicity), and `σ k` is the `k`-th min–max value of `‖A x‖² / ‖B x‖²`. -/
theorem spectral_theorem (H : Hyp A B) :
    ∃ (e : ℕ → X) (σ : ℕ → ℝ), Monotone σ ∧ (∀ k, 0 ≤ σ k) ∧ Tendsto σ atTop atTop ∧
      (∀ k, e k ≠ 0 ∧ e k ∈ eigenspace A B (σ k)) ∧
      (∀ τ, eigenspace A B τ = Submodule.span ℝ (e '' {k | σ k = τ})) ∧
      (∀ τ, Module.finrank ℝ (eigenspace A B τ) = Set.ncard {k | σ k = τ}) ∧
      (∀ τ, eigenspace A B τ ≠ ⊥ ↔ ∃ k, σ k = τ) ∧
      (∀ k, SteklovH1.closureMinMax A B k = ENNReal.ofReal (σ k)) :=
  ⟨eig A B, ev A B, ev_mono H, ev_nonneg H, ev_tendsto_atTop H,
    fun k => ⟨eig_ne_zero H k, eig_mem_eigenspace H k⟩, eigenspace_eq_span H,
    finrank_eigenspace H, eigenspace_ne_bot_iff H, closureMinMax_eq_ev H⟩

end SteklovSpectral
