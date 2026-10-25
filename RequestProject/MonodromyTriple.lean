module

public import RequestProject.MonodromyRelation
public import RequestProject.InfinityMonodromy
public import RequestProject.Degree7Counts

/-!
# The monodromy triple of a polynomial with critical values in `{0, 1}`

Combining the local monodromy theorem (around `0` and `1`), the monodromy around `∞` and the
product relation between the three loops, we obtain for every polynomial `P` with critical values
in `{0,1}` a base point `A` and two loops `γ₀, γ₁` at `A` (the small circles around `0` and `1`,
conjugated into `A`) such that

* the monodromy of `γ₀` is conjugate to the block rotation with block sizes the multiplicities of
  the roots of `P`,
* the monodromy of `γ₁` is conjugate to the block rotation with block sizes the multiplicities of
  the roots of `P - 1`,
* the monodromy of `γ₀ · γ₁` is conjugate to `finRotate (deg P)` (`monodromy_triple`).

For the degree-seven candidates `p_s` this yields permutations `x, y` of `Fin 7` (after labelling
the fibre) with cycle types `(2,2,1,1,1)`, `(3,3,1)` and with `y x` a `7`-cycle
(`Degree7.monodromy_pair`), i.e. an admissible pair in the sense of `Degree7Counts`.
-/

@[expose] public section

open Polynomial Set Filter Topology Metric Complex PolyCover LocalMonodromy MonodromyRelation
  InfinityMonodromy Equiv

noncomputable section

namespace MonodromyTriple

/-! ### Permutation facts -/

theorem permCongr_one' {α β : Type*} (e : α ≃ β) : e.permCongr (1 : Perm α) = 1 := by
  ext x; simp [permCongr_apply]

theorem permCongr_pow {α β : Type*} (e : α ≃ β) (σ : Perm α) (m : ℕ) :
    e.permCongr (σ ^ m) = (e.permCongr σ) ^ m := by
  induction m with
  | zero => simp [permCongr_one']
  | succ m ih => rw [pow_succ, permCongr_mul, ih, pow_succ]

theorem permCongr_trans' {α β γ : Type*} (e : α ≃ β) (f : β ≃ γ) (σ : Perm α) :
    f.permCongr (e.permCongr σ) = (e.trans f).permCongr σ := by
  ext x; simp [permCongr_apply]

/-- Number of fixed points. -/
def fixCard {α : Type*} [Fintype α] [DecidableEq α] (σ : Perm α) : ℕ :=
  Fintype.card {a // σ a = a}

theorem fixCard_permCongr {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (e : α ≃ β) (σ : Perm α) : fixCard (e.permCongr σ) = fixCard σ := by
  unfold fixCard
  refine (Fintype.card_congr (e.subtypeEquiv fun a => ?_)).symm
  simp [permCongr_apply]

theorem finRotate_pow_val {n : ℕ} (hn : 0 < n) (m : ℕ) (j : Fin n) :
    (((finRotate n) ^ m) j : ℕ) = (j + m) % n := by
  induction m with
  | zero => simp [Nat.mod_eq_of_lt j.2]
  | succ m ih =>
    rw [pow_succ', Perm.mul_apply, finRotate_val hn, ih, Nat.mod_add_mod]
    ring_nf

theorem blockRotation_pow_apply {ι : Type*} (k : ι → ℕ) (m : ℕ) (x : Σ i, Fin (k i)) :
    (blockRotation k ^ m) x = ⟨x.1, ((finRotate (k x.1)) ^ m) x.2⟩ := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ, Perm.mul_apply, ih, pow_succ, Perm.mul_apply]
    rfl

theorem blockRotation_pow_eq_one {ι : Type*} {k : ι → ℕ} (hk : ∀ i, 0 < k i) {m : ℕ}
    (h : ∀ i, k i ∣ m) : blockRotation k ^ m = 1 := by
  ext1 x
  rw [blockRotation_pow_apply]
  obtain ⟨i, j⟩ := x
  simp only [Perm.coe_one, id]
  congr 1
  apply Fin.ext
  obtain ⟨c, hc⟩ := h i
  rw [finRotate_pow_val (hk i), hc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt j.2]

theorem blockRotation_apply_eq_iff {ι : Type*} {k : ι → ℕ} (hk : ∀ i, 0 < k i)
    (x : Σ i, Fin (k i)) : blockRotation k x = x ↔ k x.1 = 1 := by
  obtain ⟨i, j⟩ := x
  simp only [blockRotation, sigmaCongrRight_apply, Sigma.mk.injEq, heq_eq_eq, true_and]
  rw [Fin.ext_iff, finRotate_val (hk i)]
  constructor
  · intro h
    by_contra hne
    have h2 : 2 ≤ k i := by have := hk i; omega
    rcases Nat.lt_or_ge ((j : ℕ) + 1) (k i) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h; omega
    · have hj : (j : ℕ) + 1 = k i := by have := j.2; omega
      rw [hj, Nat.mod_self] at h; omega
  · intro h1
    have := j.2
    have hj : (j : ℕ) = 0 := by omega
    rw [hj, h1]

theorem fixCard_blockRotation {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ι → ℕ}
    (hk : ∀ i, 0 < k i) : fixCard (blockRotation k) = Fintype.card {i // k i = 1} := by
  unfold fixCard
  simp_rw [blockRotation_apply_eq_iff hk]
  let e : {x : Σ i, Fin (k i) // k x.1 = 1} ≃ {i // k i = 1} :=
    { toFun := fun x => ⟨x.1.1, x.2⟩
      invFun := fun i => ⟨⟨i.1, ⟨0, by rw [i.2]; norm_num⟩⟩, i.2⟩
      left_inv := fun x => by
        obtain ⟨⟨i, j⟩, h⟩ := x
        simp only at h
        exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Fin.ext (by have := j.2; simp; omega))))
      right_inv := fun i => rfl }
  exact Fintype.card_congr e

/-! ### Transport of monodromy -/

theorem perm_eq_permCongr {α β : Type*} (f : Perm β) (E : α ≃ β) (τ : Perm α)
    (h : ∀ x, f (E x) = E (τ x)) : f = E.permCongr τ := by
  ext y
  rw [permCongr_apply, ← h, E.apply_symm_apply]

variable {P : ℂ[X]}

/-- The monodromy bijection between fibres along a path. -/
def monoEquiv (P : ℂ[X]) {x y : Base P} (w : Path x y) : proj P ⁻¹' {x} ≃ proj P ⁻¹' {y} :=
  Equiv.ofBijective _ ((isCoveringMap P).monodromy_bijective (Path.Homotopic.Quotient.mk w))

/-- Monodromy of a conjugated loop is the conjugated monodromy. -/
theorem monodromyPerm_conjLoop {x a : Base P} (w : Path x a) (γ : Path x x) :
    monodromyPerm P (conjLoop w γ) =
      (monoEquiv P w).permCongr (monodromyPerm P (Path.Homotopic.Quotient.mk γ)) := by
  ext e
  rw [permCongr_apply]
  have hinv : (isCoveringMap P).monodromy (Path.Homotopic.Quotient.mk w).symm e =
      (monoEquiv P w).symm e := by
    rw [Equiv.eq_symm_apply]
    show (isCoveringMap P).monodromy (Path.Homotopic.Quotient.mk w)
      ((isCoveringMap P).monodromy (Path.Homotopic.Quotient.mk w).symm e) = e
    rw [← (isCoveringMap P).monodromy_trans_apply, Path.Homotopic.Quotient.symm_trans,
      (isCoveringMap P).monodromy_refl, id]
  simp only [monodromyPerm_apply, conjLoop, (isCoveringMap P).monodromy_trans_apply, hinv]
  rfl

/-- **The monodromy triple** of a polynomial whose critical values lie in `{0, 1}`: there are a
base point `A` and loops `γ₀, γ₁` at `A` (the circles of a small radius `r` about `0` and `1`,
conjugated into `A` along paths `w₀`, `w₁`) such that the monodromy of `γ₀` (resp. `γ₁`) is
conjugate to the block rotation whose blocks are the root multiplicities of `P` (resp. `P - 1`),
and the monodromy of `γ₀ · γ₁` is conjugate to `finRotate (deg P)`. -/
theorem monodromy_triple (hP : 0 < P.degree) (hcrit : critVals P ⊆ {0, 1}) :
    ∃ (A : Base P) (γ0 γ1 : Path.Homotopic.Quotient A A)
      (E0 : (Σ a : (P - C 0).roots.toFinset, Fin ((P - C 0).rootMultiplicity (a : ℂ))) ≃
        proj P ⁻¹' {A})
      (E1 : (Σ a : (P - C 1).roots.toFinset, Fin ((P - C 1).rootMultiplicity (a : ℂ))) ≃
        proj P ⁻¹' {A})
      (Einf : Fin P.natDegree ≃ proj P ⁻¹' {A}),
      monodromyPerm P γ0 =
        E0.permCongr (blockRotation fun a : (P - C 0).roots.toFinset =>
          (P - C 0).rootMultiplicity (a : ℂ)) ∧
      monodromyPerm P γ1 =
        E1.permCongr (blockRotation fun a : (P - C 1).roots.toFinset =>
          (P - C 1).rootMultiplicity (a : ℂ)) ∧
      monodromyPerm P (γ0.trans γ1) = Einf.permCongr (finRotate _) ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧ IsStdLoops r γ0 γ1 ∧ ∃ (hc0 : ∀ t, circ 0 r t ∉ critVals P)
        (hc1 : ∀ t, circ 1 r t ∉ critVals P) (w0 : Path (basePt 0 r hc0) A)
        (w1 : Path (basePt 1 r hc1) A),
        γ0 = conjLoop w0 (circleLoop 0 r hc0) ∧ γ1 = conjLoop w1 (circleLoop 1 r hc1) := by
  obtain ⟨r0, hr0, H0⟩ := local_monodromy hP 0
  obtain ⟨r1, hr1, H1⟩ := local_monodromy hP 1
  obtain ⟨R0, hR0, Hinf⟩ := infinity_monodromy (natDegree_pos_iff_degree_pos.2 hP)
  set r := min (min r0 r1) (1 / 2) / 2 with hrdef
  have hm : 0 < min (min r0 r1) (1 / 2) := lt_min (lt_min hr0 hr1) (by norm_num)
  have hr : 0 < r := half_pos hm
  have hrlt : r < min (min r0 r1) (1 / 2) := half_lt_self hm
  have hr_0 : r < r0 := lt_of_lt_of_le hrlt ((min_le_left _ _).trans (min_le_left _ _))
  have hr_1 : r < r1 := lt_of_lt_of_le hrlt ((min_le_left _ _).trans (min_le_right _ _))
  have hr2 : r < 1 / 2 := lt_of_lt_of_le hrlt (min_le_right _ _)
  set R := max R0 1 + 1
  have hRR0 : R0 < R := by have := le_max_left R0 1; linarith
  have hR1 : 1 < R := by have := le_max_right R0 1; linarith
  obtain ⟨hc0, E0', hE0⟩ := H0 r hr hr_0
  obtain ⟨hc1, E1', hE1⟩ := H1 r hr hr_1
  obtain ⟨hcR, Ei', hEi⟩ := Hinf R hRR0
  obtain ⟨A, w0, w1, wR, -, hrel, hstd⟩ := loop_relation hcrit hr hr2 hR1 hc0 hc1 hcR
  refine ⟨A, conjLoop w0 (circleLoop 0 r hc0), conjLoop w1 (circleLoop 1 r hc1),
    E0'.trans (monoEquiv P w0), E1'.trans (monoEquiv P w1), Ei'.trans (monoEquiv P wR),
    ?_, ?_, ?_, r, hr, hr2, hstd, hc0, hc1, w0, w1, rfl, rfl⟩
  · rw [monodromyPerm_conjLoop, perm_eq_permCongr _ E0' _ hE0, permCongr_trans']
  · rw [monodromyPerm_conjLoop, perm_eq_permCongr _ E1' _ hE1, permCongr_trans']
  · rw [hrel, monodromyPerm_conjLoop, perm_eq_permCongr _ Ei' _ hEi, permCongr_trans']

end MonodromyTriple
