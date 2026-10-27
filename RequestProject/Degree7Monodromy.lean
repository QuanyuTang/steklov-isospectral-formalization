module

public import RequestProject.MonodromyTriple

/-!
# The actual monodromy of the degree-seven candidates

For `s² = -7` and the explicit polynomial `p_s` we prove, from the geometric monodromy of the
covering `p_s : p_s⁻¹(ℂ \ {0,1}) → ℂ \ {0,1}` (no assumption on the monodromy):

* `monodromy_pair`: there are a base point `A`, loops `γ₀, γ₁` at `A` (small circles about `0` and
  `1` conjugated into `A`) and a labelling of the fibre over `A` by `Fin 7` such that the
  monodromies `x` of `γ₀` and `y` of `γ₁` have cycle types `(2,2,1,1,1)` and `(3,3,1)`, and
  `y x` (the monodromy of `γ₀ · γ₁`) is a `7`-cycle;
* `monodromy_pair_mem_orbits`: after relabelling, `x = x₇` and `y` lies in the centralizer orbit
  of `y₁` or of `y₂` (by the kernel-checked two-orbit classification `good_eq_orbits`).
-/

@[expose] public section

open Polynomial Set Equiv PolyCover LocalMonodromy MonodromyRelation MonodromyTriple Finset

noncomputable section

namespace Degree7

/-- Cycle type `(2,2,1,1,1)` ⇔ `σ² = 1` and exactly three fixed points. -/
theorem cycleType22_iff (σ : Perm (Fin 7)) :
    σ.cycleType = {2, 2} ↔ σ ^ 2 = 1 ∧ nfix σ = 3 := by
  have hns := nfix_add_support σ
  constructor
  · intro h
    have hord : orderOf σ = 2 := by rw [← Perm.lcm_cycleType, h]; decide
    refine ⟨by rw [← hord]; exact pow_orderOf_eq_one σ, ?_⟩
    have : σ.support.card = 4 := by rw [← Perm.sum_cycleType, h]; decide
    omega
  · rintro ⟨h2, h3⟩
    have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
      Multiset.eq_replicate.2 ⟨rfl, fun m hm => mem_cycleType_eq_prime Nat.prime_two h2 hm⟩
    have hsum : σ.cycleType.sum = 4 := by rw [Perm.sum_cycleType]; omega
    rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hk : Multiset.card σ.cycleType = 2 := by omega
    rw [hrep, hk]; decide

theorem nfix_eq_fixCard (σ : Perm (Fin 7)) : nfix σ = fixCard σ := by
  unfold nfix fixCard
  rw [Fintype.card_subtype]

/-- Values of a finite family recorded by a multiset. -/
theorem card_eq_count_of_map {R : Finset ℂ} {f : ℂ → ℕ} {M : Multiset ℕ}
    (h : R.val.map f = M) : Fintype.card {i : R // f i = 1} = M.count 1 := by
  classical
  rw [← h, Multiset.count_map]
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter fun i : R => f i = 1).card = (R.filter fun a => f a = 1).card := by
    rw [← Finset.card_map ⟨Subtype.val, Subtype.val_injective⟩]
    congr 1
    ext a
    simp [and_comm]
  rw [this, Finset.card_def, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun a _ => eq_comm

theorem mem_of_map {R : Finset ℂ} {f : ℂ → ℕ} {M : Multiset ℕ} (h : R.val.map f = M)
    (i : R) : f i ∈ M := by
  rw [← h]; exact Multiset.mem_map_of_mem f i.2

theorem finRotate_pow_self {n : ℕ} (hn : 0 < n) : finRotate n ^ n = 1 := by
  ext j
  rw [finRotate_pow_val hn, Nat.add_mod_right, Nat.mod_eq_of_lt j.2]
  rfl

theorem finRotate_ne_one {n : ℕ} (hn : 2 ≤ n) : finRotate n ≠ 1 := by
  intro h
  have := congrArg (fun σ : Perm (Fin n) => ((σ ⟨0, by omega⟩ : Fin n) : ℕ)) h
  simp only [Perm.coe_one, id] at this
  rw [finRotate_val (by omega)] at this
  dsimp only at this
  rw [Nat.mod_eq_of_lt (by omega)] at this
  omega

variable {s : ℂ}

theorem critVals_pPoly_subset (hs : s ^ 2 = -7) : critVals (pPoly s) ⊆ {0, 1} :=
  (critVals_pPoly hs).le

/-- **The actual monodromy pair of `p_s`.**  There are a base point `A`, loops `γ₀, γ₁` at `A`
(the circles of some radius `r` about `0` and `1`, conjugated into `A`) and a labelling `L` of the
fibre of `p_s` over `A` by `Fin 7` such that `x = L∘mon(γ₀)∘L⁻¹` has cycle type `(2,2,1,1,1)`,
`y = L∘mon(γ₁)∘L⁻¹` has cycle type `(3,3,1)`, and `y x = L∘mon(γ₀·γ₁)∘L⁻¹` is a `7`-cycle. -/
theorem monodromy_pair (hs : s ^ 2 = -7) :
    ∃ (A : Base (pPoly s)) (γ0 γ1 : Path.Homotopic.Quotient A A)
      (L : proj (pPoly s) ⁻¹' {A} ≃ Fin 7),
      (L.permCongr (monodromyPerm (pPoly s) γ0)).cycleType = {2, 2} ∧
      (L.permCongr (monodromyPerm (pPoly s) γ1)).cycleType = {3, 3} ∧
      L.permCongr (monodromyPerm (pPoly s) (γ0.trans γ1)) =
        L.permCongr (monodromyPerm (pPoly s) γ1) * L.permCongr (monodromyPerm (pPoly s) γ0) ∧
      (L.permCongr (monodromyPerm (pPoly s) γ1) *
        L.permCongr (monodromyPerm (pPoly s) γ0)).cycleType = {7} ∧
      ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧ IsStdLoops r γ0 γ1 ∧
        ∃ (hc0 : ∀ t, circ 0 r t ∉ critVals (pPoly s))
        (hc1 : ∀ t, circ 1 r t ∉ critVals (pPoly s)) (w0 : Path (basePt 0 r hc0) A)
        (w1 : Path (basePt 1 r hc1) A),
        γ0 = conjLoop w0 (circleLoop 0 r hc0) ∧ γ1 = conjLoop w1 (circleLoop 1 r hc1) := by
  classical
  obtain ⟨A, γ0, γ1, E0, E1, Ei, h0, h1, hi, hloops⟩ :=
    monodromy_triple (pPoly_degree_pos hs) (critVals_pPoly_subset hs)
  have hN : (pPoly s).natDegree = 7 := pPoly_natDegree hs
  let L : proj (pPoly s) ⁻¹' {A} ≃ Fin 7 := Ei.symm.trans (finCongr hN)
  have hmul : L.permCongr (monodromyPerm (pPoly s) (γ0.trans γ1)) =
      L.permCongr (monodromyPerm (pPoly s) γ1) * L.permCongr (monodromyPerm (pPoly s) γ0) := by
    rw [monodromyPerm_trans, permCongr_mul]
  refine ⟨A, γ0, γ1, L, ?_, ?_, hmul, ?_, hloops⟩
  · -- the passport over `0`
    have hpass : (pPoly s - C 0).roots.toFinset.val.map
        (fun z => (pPoly s - C 0).rootMultiplicity z) = {2, 2, 1, 1, 1} := by
      rw [show pPoly s - C 0 = pPoly s by simp]; exact passport_zero hs
    have hk : ∀ i : (pPoly s - C 0).roots.toFinset, 0 < (pPoly s - C 0).rootMultiplicity (i : ℂ) :=
      fun i => (by decide : ∀ m ∈ ({2, 2, 1, 1, 1} : Multiset ℕ), 0 < m) _ (mem_of_map hpass i)
    rw [cycleType22_iff, h0, permCongr_trans', ← permCongr_pow, nfix_eq_fixCard,
      fixCard_permCongr, fixCard_blockRotation hk, card_eq_count_of_map hpass,
      blockRotation_pow_eq_one hk (fun i =>
        (by decide : ∀ m ∈ ({2, 2, 1, 1, 1} : Multiset ℕ), m ∣ 2) _ (mem_of_map hpass i)),
      permCongr_one']
    exact ⟨rfl, by decide⟩
  · -- the passport over `1`
    have hpass := passport_one hs
    have hk : ∀ i : (pPoly s - C 1).roots.toFinset, 0 < (pPoly s - C 1).rootMultiplicity (i : ℂ) :=
      fun i => (by decide : ∀ m ∈ ({3, 3, 1} : Multiset ℕ), 0 < m) _ (mem_of_map hpass i)
    rw [cycleType33_iff, h1, permCongr_trans', ← permCongr_pow, nfix_eq_fixCard,
      fixCard_permCongr, fixCard_blockRotation hk, card_eq_count_of_map hpass,
      blockRotation_pow_eq_one hk (fun i =>
        (by decide : ∀ m ∈ ({3, 3, 1} : Multiset ℕ), m ∣ 3) _ (mem_of_map hpass i)),
      permCongr_one']
    exact ⟨rfl, by decide⟩
  · -- the loop around infinity
    rw [← hmul, cycleType7_iff, hi, permCongr_trans', ← permCongr_pow]
    have h7 : finRotate (pPoly s).natDegree ^ 7 = 1 := by
      rw [show (7 : ℕ) = (pPoly s).natDegree from hN.symm]
      exact finRotate_pow_self (by rw [hN]; norm_num)
    refine ⟨by rw [h7, permCongr_one'], fun h => ?_⟩
    apply finRotate_ne_one (n := (pPoly s).natDegree) (by rw [hN]; norm_num)
    have := congrArg (fun σ => (Ei.trans L).symm.permCongr σ) h
    simpa [permCongr_trans', permCongr_one'] using this

end Degree7

namespace Degree7

/-- **Normal form of an admissible triple (pure permutation algebra).**  If `x` has cycle type
`(2,2,1,1,1)`, `y` has cycle type `(3,3,1)` and `y x` is a `7`-cycle, then after relabelling `x = x₇`
and `y ∈ {y₁, y₂}`.  Uses the kernel-checked classification `good_eq_orbits`. -/
theorem admissible_normal_form (x y : Perm (Fin 7)) (hx : x.cycleType = {2, 2})
    (hy : y.cycleType = {3, 3}) (hyx : (y * x).cycleType = {7}) :
    ∃ τ : Perm (Fin 7), τ * x * τ⁻¹ = x7 ∧ (τ * y * τ⁻¹ = y1 ∨ τ * y * τ⁻¹ = y2) := by
  classical
  obtain ⟨τ, hτ⟩ : ∃ τ : Perm (Fin 7), τ * x * τ⁻¹ = x7 :=
    isConj_iff.1 (Perm.isConj_iff_cycleType_eq.2 (by rw [hx, cycleType_x7]))
  have hxy : (x * y).cycleType = {7} := by
    rw [← hyx, show x * y = x * (y * x) * x⁻¹ by group, Perm.cycleType_conj]
  have hmem : τ * y * τ⁻¹ ∈ univ.filter fun y : Perm (Fin 7) =>
      y.cycleType = {3, 3} ∧ (x7 * y).cycleType = {7} := by
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [Perm.cycleType_conj, hy], ?_⟩
    rw [← hτ, show τ * x * τ⁻¹ * (τ * y * τ⁻¹) = τ * (x * y) * τ⁻¹ by group,
      Perm.cycleType_conj, hxy]
  obtain ⟨hU, -⟩ := good_eq_orbits
  rw [hU, Finset.mem_union, Finset.mem_image, Finset.mem_image] at hmem
  have key : ∀ σ : Perm (Fin 7), σ * x7 = x7 * σ → ∀ z, σ * z * σ⁻¹ = τ * y * τ⁻¹ →
      (σ⁻¹ * τ) * x * (σ⁻¹ * τ)⁻¹ = x7 ∧ (σ⁻¹ * τ) * y * (σ⁻¹ * τ)⁻¹ = z := by
    intro σ hσ z hz
    constructor
    · rw [show σ⁻¹ * τ * x * (σ⁻¹ * τ)⁻¹ = σ⁻¹ * (τ * x * τ⁻¹) * σ by group, hτ]
      rw [show σ⁻¹ * x7 * σ = σ⁻¹ * (x7 * σ) by group, ← hσ]; group
    · rw [show σ⁻¹ * τ * y * (σ⁻¹ * τ)⁻¹ = σ⁻¹ * (τ * y * τ⁻¹) * σ by group, ← hz]; group
  rcases hmem with ⟨σ, hσ, hz⟩ | ⟨σ, hσ, hz⟩
  · obtain ⟨h1, h2⟩ := key σ (Finset.mem_filter.1 hσ).2 _ hz
    exact ⟨_, h1, Or.inl h2⟩
  · obtain ⟨h1, h2⟩ := key σ (Finset.mem_filter.1 hσ).2 _ hz
    exact ⟨_, h1, Or.inr h2⟩

end Degree7
