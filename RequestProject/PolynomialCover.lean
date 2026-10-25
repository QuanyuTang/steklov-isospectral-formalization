module

public import RequestProject.Degree7Passport

/-!
# Polynomial maps are covering maps off their critical values; monodromy

For a complex polynomial `P` of positive degree we prove, with no extra hypotheses:

* `Polynomial.isClosedMap_eval`: `z ↦ P(z)` is a closed (indeed proper) map `ℂ → ℂ`;
* `Polynomial.critVals_finite`: the set of critical values is finite;
* `Polynomial.isCoveringMapOn_eval`: `z ↦ P(z)` is a covering map over the complement of the
  critical values (inverse function theorem + properness);
* `PolyCover.isCoveringMap`: the restriction `P⁻¹(Sᶜ) → Sᶜ`, `S` = critical values, is a genuine
  `IsCoveringMap`; its monodromy (Mathlib's path-lifting monodromy) gives a permutation
  `PolyCover.monodromyPerm` of every fibre for every homotopy class of loops, and this is
  multiplicative (`monodromyPerm_trans`);
* `PolyCover.monodromy_transitive`: the total space `P⁻¹(Sᶜ)` is path connected, so the
  monodromy action on each fibre is transitive.

For the degree-seven candidates `p_s` (`s² = -7`) the critical values are exactly `0` and `1`
(`Degree7.critVals_pPoly`), every fibre over `ℂ \ {0,1}` has exactly `7` points, and the
monodromy action on it is transitive (`Degree7.monodromy_transitive`).
-/

@[expose] public section

open Polynomial Set Filter Topology

noncomputable section

namespace Polynomial

variable (P : ℂ[X])

/-- The critical values of a polynomial. -/
def critVals : Set ℂ := P.eval '' {z | P.derivative.eval z = 0}

variable {P}

theorem derivative_ne_zero_of_degree_pos (hP : 0 < P.degree) : derivative P ≠ 0 := by
  intro h
  have h0 := natDegree_eq_zero_of_derivative_eq_zero h
  rw [eq_C_of_natDegree_eq_zero h0] at hP
  exact absurd hP (not_lt.2 degree_C_le)

theorem fibre_finite (hP : 0 < P.degree) (w : ℂ) : (P.eval ⁻¹' {w}).Finite := by
  have hne : P - C w ≠ 0 := by
    intro h
    have : P = C w := sub_eq_zero.1 h
    rw [this] at hP; exact absurd hP (not_lt.2 degree_C_le)
  refine (P - C w).roots.toFinset.finite_toSet.subset fun z hz => ?_
  simp only [mem_preimage, mem_singleton_iff] at hz
  simp [mem_roots hne, hz]

theorem critVals_finite (hP : 0 < P.degree) : (critVals P).Finite := by
  have hd := derivative_ne_zero_of_degree_pos hP
  refine Finite.image _ ((derivative P).roots.toFinset.finite_toSet.subset fun z hz => ?_)
  simp only [mem_setOf_eq] at hz
  simp [mem_roots hd, hz]

end Polynomial

namespace PolyCover

variable {P : ℂ[X]}

/-- The base `ℂ \ critVals P`. -/
abbrev Base (P : ℂ[X]) := ↥(critVals P)ᶜ

/-- The total space `P⁻¹(ℂ \ critVals P)`. -/
abbrev Total (P : ℂ[X]) := ↥(P.eval ⁻¹' (critVals P)ᶜ)

/-- The covering projection `P⁻¹(ℂ \ S) → ℂ \ S`. -/
abbrev proj (P : ℂ[X]) : Total P → Base P := (critVals P)ᶜ.restrictPreimage P.eval

theorem isCoveringMap (P : ℂ[X]) : IsCoveringMap (proj P) :=
  P.isCoveringMapOn_eval.isCoveringMap_restrictPreimage

/-- The monodromy permutation of the fibre over `x` along a homotopy class of loops at `x`. -/
def monodromyPerm (P : ℂ[X]) {x : Base P} (γ : Path.Homotopic.Quotient x x) :
    Equiv.Perm (proj P ⁻¹' {x}) :=
  Equiv.ofBijective _ ((isCoveringMap P).monodromy_bijective γ)

theorem monodromyPerm_apply (P : ℂ[X]) {x : Base P} (γ : Path.Homotopic.Quotient x x)
    (e : proj P ⁻¹' {x}) : monodromyPerm P γ e = (isCoveringMap P).monodromy γ e := rfl

theorem monodromyPerm_trans (P : ℂ[X]) {x : Base P}
    (γ γ' : Path.Homotopic.Quotient x x) :
    monodromyPerm P (γ.trans γ') = monodromyPerm P γ' * monodromyPerm P γ := by
  ext e
  simp [monodromyPerm_apply, (isCoveringMap P).monodromy_trans_apply]

theorem finite_exceptional (hP : 0 < P.degree) :
    (P.eval ⁻¹' critVals P).Finite := by
  have := critVals_finite hP
  refine Set.Finite.subset (this.biUnion fun w _ => fibre_finite hP w) fun z hz => ?_
  simp only [mem_iUnion, mem_preimage, mem_singleton_iff]
  exact ⟨_, hz, rfl⟩

instance pathConnectedSpace_total (hP : 0 < P.degree) : PathConnectedSpace (Total P) := by
  rw [← isPathConnected_iff_pathConnectedSpace, preimage_compl]
  refine (finite_exceptional hP).countable.isPathConnected_compl_of_one_lt_rank ?_
  rw [Complex.rank_real_complex]; norm_num

/-- **Transitivity of the monodromy action**: for any two points of a fibre there is a loop whose
monodromy sends the first to the second. -/
theorem monodromy_transitive (hP : 0 < P.degree) {x : Base P} (e e' : proj P ⁻¹' {x}) :
    ∃ γ : Path.Homotopic.Quotient x x, monodromyPerm P γ e = e' := by
  haveI := pathConnectedSpace_total hP
  have h1 : x = proj P e.1 := e.2.symm
  have h2 : x = proj P e'.1 := e'.2.symm
  let δ : Path e.1 e'.1 := PathConnectedSpace.somePath e.1 e'.1
  let γ : Path x x := (δ.map (isCoveringMap P).continuous).cast h1 h2
  refine ⟨Path.Homotopic.Quotient.mk γ, Subtype.ext ?_⟩
  have hl : (isCoveringMap P).liftPath (γ : C(unitInterval, Base P)) e.1
      (γ.source.trans h1) = (δ : C(unitInterval, Total P)) :=
    (((isCoveringMap P).eq_liftPath_iff' _).2 ⟨rfl, δ.source⟩).symm
  show (isCoveringMap P).liftPath (γ : C(unitInterval, Base P)) e.1 _ 1 = e'.1
  rw [hl]
  exact δ.target

/-- The fibre of the covering over `x` is the set of all solutions of `P(z) = x`. -/
def fibreEquiv (x : Base P) : proj P ⁻¹' {x} ≃ {z : ℂ // P.eval z = x.1} where
  toFun e := ⟨e.1.1, by have := congrArg Subtype.val e.2; simpa using this⟩
  invFun z := ⟨⟨z.1, by simp only [mem_preimage, z.2]; exact x.2⟩, Subtype.ext (by simp [z.2])⟩
  left_inv e := rfl
  right_inv z := rfl

/-- **Fibre cardinality**: over every regular value the fibre has exactly `deg P` points. -/
theorem card_fibre (hP : 0 < P.degree) (x : Base P) :
    Nat.card (proj P ⁻¹' {x}) = P.natDegree := by
  classical
  have hne : P - C x.1 ≠ 0 := by
    intro h
    have : P = C x.1 := sub_eq_zero.1 h
    rw [this] at hP; exact absurd hP (not_lt.2 degree_C_le)
  have hnd : (P - C x.1).roots.Nodup := by
    rw [Multiset.nodup_iff_count_le_one]
    intro z
    rw [count_roots]
    by_contra hlt
    push_neg at hlt
    have := (one_lt_rootMultiplicity_iff_isRoot hne).1 hlt
    simp only [IsRoot, eval_sub, eval_C, derivative_sub, derivative_C, sub_zero,
      sub_eq_zero] at this
    exact x.2 ⟨z, this.2, this.1⟩
  rw [Nat.card_congr (fibreEquiv x)]
  have : {z : ℂ // P.eval z = x.1} ≃ (P - C x.1).roots.toFinset :=
    Equiv.subtypeEquivRight fun z => by simp [mem_roots hne, sub_eq_zero]
  rw [Nat.card_congr this, Nat.card_eq_fintype_card, Fintype.card_coe,
    Multiset.toFinset_card_of_nodup hnd, IsAlgClosed.card_roots_eq_natDegree, natDegree_sub_C]

end PolyCover

namespace Degree7

variable {s : ℂ}

theorem pPoly_degree_pos (hs : s ^ 2 = -7) : 0 < (pPoly s).degree := by
  rw [degree_eq_natDegree (pPoly_ne_zero hs), pPoly_natDegree hs]; norm_num

/-- The critical values of `p_s` are exactly `0` and `1`. -/
theorem critVals_pPoly (hs : s ^ 2 = -7) : critVals (pPoly s) = {0, 1} := by
  have hf : (fun z => (pPoly s).eval z) = pfun s := funext (pPoly_eval s)
  have hd : ∀ z, (derivative (pPoly s)).eval z = deriv (pfun s) z := fun z => by
    rw [derivative_pPoly_eval, (hasDerivAt_pfun s z).deriv]
  ext w
  simp only [critVals, hf, mem_image, mem_setOf_eq, hd, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩; exact pfun_critical_value_mem hs hz
  · rintro (rfl | rfl)
    · -- a root of `q_c` exists (the quadratic `q_c` has degree 2)
      obtain ⟨z, hz⟩ := Complex.exists_root (f := qPoly (cc s))
        (by rw [degree_eq_natDegree (qPoly_ne_zero _), qPoly_natDegree]; norm_num)
      have hz' : qpoly (cc s) z = 0 := by rw [← qPoly_eval]; exact hz
      exact ⟨z, (deriv_pfun_eq_zero_iff hs z).2 (Or.inr (Or.inr hz')),
        (pfun_critical_values hs).2.2 z hz'⟩
    · exact ⟨1, by rw [(deriv_pfun_eq_zero_iff hs 1)]; left; rfl, (pfun_critical_values hs).1⟩

end Degree7

namespace Degree7

variable {s : ℂ}

/-- The covering `p_s : p_s⁻¹(ℂ \ {0,1}) → ℂ \ {0,1}` has fibres of exactly `7` points. -/
theorem card_fibre_pPoly (hs : s ^ 2 = -7) (x : PolyCover.Base (pPoly s)) :
    Nat.card (PolyCover.proj (pPoly s) ⁻¹' {x}) = 7 := by
  rw [PolyCover.card_fibre (pPoly_degree_pos hs), pPoly_natDegree hs]

/-- The monodromy action of `p_s` on every fibre over `ℂ \ {0,1}` is transitive. -/
theorem monodromy_transitive (hs : s ^ 2 = -7) {x : PolyCover.Base (pPoly s)}
    (e e' : PolyCover.proj (pPoly s) ⁻¹' {x}) :
    ∃ γ : Path.Homotopic.Quotient x x, PolyCover.monodromyPerm (pPoly s) γ e = e' :=
  PolyCover.monodromy_transitive (pPoly_degree_pos hs) e e'

end Degree7
