module

public import RequestProject.Degree7PointLine

/-!
# The two degree-seven polynomial coverings are not isomorphic

For `s² = -7` both `p_s` and `p_{-s}` are coverings of `ℂ \ {0,1}` of degree `7`.  We prove that
there is **no homeomorphism** `Ψ : p_s⁻¹(ℂ \ {0,1}) → p_{-s}⁻¹(ℂ \ {0,1})` with `p_{-s} ∘ Ψ = p_s`
(`covers_not_isomorphic`).  The proof: such a `Ψ` intertwines the monodromy actions along every loop
(`CoverTransport.monodromy_map_mk`); on the standard generators these are, after labelling,
`(x₇, y₁)` for one polynomial and `(x₇, y₂)` for the other (`monodromy_point_line`), and the two
pairs lie in different centralizer orbits (`good_eq_orbits`), so no relabelling intertwines them.
-/

@[expose] public section

open Polynomial Set Equiv PolyCover LocalMonodromy MonodromyRelation MonodromyTriple

noncomputable section

namespace CoverIneq

variable {P Q : ℂ[X]}

theorem quot_map_trans {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {a b c : X}
    (γ : Path.Homotopic.Quotient a b) (δ : Path.Homotopic.Quotient b c) (f : C(X, Y)) :
    (γ.trans δ).map f = (γ.map f).trans (δ.map f) := by
  induction γ using Path.Homotopic.Quotient.ind with | mk γ =>
  induction δ using Path.Homotopic.Quotient.ind with | mk δ =>
  rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_map, Path.map_trans,
    Path.Homotopic.Quotient.mk_trans]

theorem quot_map_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {a b : X}
    (γ : Path.Homotopic.Quotient a b) (f : C(X, Y)) : γ.symm.map f = (γ.map f).symm := by
  induction γ using Path.Homotopic.Quotient.ind with | mk γ =>
  rw [← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_map, ← Path.Homotopic.Quotient.mk_symm, Path.map_symm]

/-- The identity of `ℂ`, viewed as a map between the bases of two coverings with the same
critical values. -/
def idBase (h : critVals P = critVals Q) (x : Base P) : Base Q := ⟨x.1, h ▸ x.2⟩

@[simp] theorem idBase_val (h : critVals P = critVals Q) (x : Base P) :
    (idBase h x : ℂ) = x := Subtype.coe_mk _ _

theorem continuous_idBase (h : critVals P = critVals Q) : Continuous (idBase h) :=
  continuous_subtype_val.subtype_mk _

/-- The identity as a continuous map. -/
def idBaseC (h : critVals P = critVals Q) : C(Base P, Base Q) := ⟨idBase h, continuous_idBase h⟩

/-- The standard generators are mapped to the standard generators. -/
theorem isStdLoops_map (h : critVals P = critVals Q) {r : ℝ} {A : Base P}
    {γ0 γ1 : Path.Homotopic.Quotient A A} (hs : IsStdLoops r γ0 γ1) :
    IsStdLoops r (γ0.map (idBaseC h)) (γ1.map (idBaseC h)) := by
  obtain ⟨B, C, D, U0, L0, U1, L1, sBC, hU0, hL0, hU1, hL1, hs, rfl, rfl⟩ := hs
  refine ⟨_, _, _, U0.map (continuous_idBase h), L0.map (continuous_idBase h),
    U1.map (continuous_idBase h), L1.map (continuous_idBase h), sBC.map (continuous_idBase h),
    fun t => (idBase_val h _).trans (hU0 t), fun t => (idBase_val h _).trans (hL0 t),
    fun t => (idBase_val h _).trans (hU1 t), fun t => (idBase_val h _).trans (hL1 t),
    fun t => (idBase_val h _).trans (hs t), ?_, ?_⟩
  · rw [quot_map_trans]; rfl
  · simp only [quot_map_trans, quot_map_symm]; rfl

/-- **Uniqueness of the standard generators**: the explicit parametrizations determine them. -/
theorem isStdLoops_unique {r : ℝ} {A : Base P} {γ0 γ1 γ0' γ1' : Path.Homotopic.Quotient A A}
    (hs : IsStdLoops r γ0 γ1) (hs' : IsStdLoops r γ0' γ1') : γ0 = γ0' ∧ γ1 = γ1' := by
  obtain ⟨B, C, D, U0, L0, U1, L1, sBC, hU0, hL0, hU1, hL1, hsBC, rfl, rfl⟩ := hs
  obtain ⟨B', C', D', U0', L0', U1', L1', sBC', hU0', hL0', hU1', hL1', hsBC', rfl, rfl⟩ := hs'
  obtain rfl : B' = B := Subtype.ext (by
    rw [← congrArg Subtype.val U0.source, ← congrArg Subtype.val U0'.source, hU0, hU0'])
  obtain rfl : C' = C := Subtype.ext (by
    rw [← congrArg Subtype.val U1.target, ← congrArg Subtype.val U1'.target, hU1, hU1'])
  obtain rfl : D' = D := Subtype.ext (by
    rw [← congrArg Subtype.val U1.source, ← congrArg Subtype.val U1'.source, hU1, hU1'])
  obtain rfl : U0' = U0 := by ext t; rw [hU0, hU0']
  obtain rfl : L0' = L0 := by ext t; rw [hL0, hL0']
  obtain rfl : U1' = U1 := by ext t; rw [hU1, hU1']
  obtain rfl : L1' = L1 := by ext t; rw [hL1, hL1']
  obtain rfl : sBC' = sBC := by ext t; rw [hsBC, hsBC']
  exact ⟨rfl, rfl⟩

/-- A homeomorphism of total spaces over the identity of the base restricts to bijections of
fibres. -/
def fibreHomeo (h : critVals P = critVals Q) (Ψ : Total P ≃ₜ Total Q)
    (hΨ : ∀ e, proj Q (Ψ e) = idBase h (proj P e)) (x : Base P) :
    proj P ⁻¹' {x} ≃ proj Q ⁻¹' {idBase h x} where
  toFun e := ⟨Ψ e.1, by rw [mem_preimage, hΨ, show proj P e.1 = x from e.2]; rfl⟩
  invFun f := ⟨Ψ.symm f.1, by
    apply Subtype.ext
    have h1 := congrArg Subtype.val (hΨ (Ψ.symm f.1))
    rw [Homeomorph.apply_symm_apply] at h1
    have h2 : (proj Q f.1 : ℂ) = x.1 := (congrArg Subtype.val f.2).trans (idBase_val h x)
    exact (idBase_val h _).symm.trans (h1.symm.trans h2)⟩
  left_inv e := Subtype.ext (Ψ.symm_apply_apply e.1)
  right_inv f := Subtype.ext (Ψ.apply_symm_apply f.1)

/-- A homeomorphism over the identity intertwines the monodromies. -/
theorem monodromy_homeo (h : critVals P = critVals Q) (Ψ : Total P ≃ₜ Total Q)
    (hΨ : ∀ e, proj Q (Ψ e) = idBase h (proj P e)) {x : Base P}
    (γ : Path.Homotopic.Quotient x x) :
    monodromyPerm Q (γ.map (idBaseC h)) = (fibreHomeo h Ψ hΨ x).permCongr (monodromyPerm P γ) := by
  induction γ using Path.Homotopic.Quotient.ind with | mk γ =>
  refine Equiv.ext fun f => ?_
  erw [Equiv.permCongr_apply]
  apply Subtype.ext
  rw [← Path.Homotopic.Quotient.mk_map, monodromyPerm_apply, monodromyPerm_apply]
  have hf : f = fibreHomeo h Ψ hΨ x ((fibreHomeo h Ψ hΨ x).symm f) := by simp
  conv_lhs => rw [hf]
  exact CoverTransport.monodromy_map_mk (isCoveringMap P) (isCoveringMap Q) Ψ.continuous
    (continuous_idBase h) hΨ γ _ _ rfl

end CoverIneq

namespace Degree7

open CoverIneq

variable {s : ℂ}

theorem critVals_neg (hs : s ^ 2 = -7) : critVals (pPoly s) = critVals (pPoly (-s)) := by
  rw [critVals_pPoly hs, critVals_pPoly (neg_sq_seven hs)]

/-- No relabelling commuting with `x₇` carries `y₁` to `y₂`. -/
theorem no_intertwiner (σ : Perm (Fin 7)) (hx : σ * x7 * σ⁻¹ = x7) : σ * y1 * σ⁻¹ ≠ y2 := by
  classical
  intro hy
  obtain ⟨-, -, -, hdisj⟩ := good_eq_orbits
  have hσ : σ * x7 = x7 * σ := by
    calc σ * x7 = σ * x7 * σ⁻¹ * σ := by group
      _ = x7 * σ := by rw [hx]
  exact Finset.disjoint_left.1 hdisj
    (Finset.mem_image.2 ⟨σ, Finset.mem_filter.2 ⟨Finset.mem_univ _, hσ⟩, hy⟩)
    (Finset.mem_image.2 ⟨1, Finset.mem_filter.2 ⟨Finset.mem_univ _, by rw [one_mul, mul_one]⟩,
      by rw [one_mul, inv_one, mul_one]⟩)

/-- Neither of the two pairs can be carried to the other by a relabelling. -/
theorem no_intertwiner_pair (σ : Perm (Fin 7)) (hx : σ * x7 * σ⁻¹ = x7)
    (hy : σ * y1 * σ⁻¹ = y2 ∨ σ * y2 * σ⁻¹ = y1) : False := by
  rcases hy with hy | hy
  · exact no_intertwiner σ hx hy
  · have e1 : σ⁻¹ * (σ * x7 * σ⁻¹) * σ = x7 := by group
    rw [hx] at e1
    have e2 : σ⁻¹ * (σ * y2 * σ⁻¹) * σ = y2 := by group
    rw [hy] at e2
    exact no_intertwiner σ⁻¹ (by rwa [inv_inv]) (by rwa [inv_inv])

theorem permCongr_relabel {α β : Type*} (L : α ≃ Fin 7) (L' : β ≃ Fin 7) (F : α ≃ β)
    (τ : Perm α) : L'.permCongr (F.permCongr τ) =
      (L.symm.trans (F.trans L')) * L.permCongr τ * (L.symm.trans (F.trans L'))⁻¹ := by
  ext i; simp [permCongr_apply, Perm.mul_apply]

/-- **The coverings `p_s` and `p_{-s}` of `ℂ \ {0,1}` are not isomorphic**: there is no
homeomorphism `Ψ` between their total spaces `p_{±s}⁻¹(ℂ \ {0,1})` with `p_{-s} ∘ Ψ = p_s`. -/
theorem covers_not_isomorphic (hs : s ^ 2 = -7) :
    ¬ ∃ Ψ : Total (pPoly s) ≃ₜ Total (pPoly (-s)),
      ∀ e, ((proj (pPoly (-s)) (Ψ e)) : ℂ) = proj (pPoly s) e := by
  rintro ⟨Ψ, hΨ⟩
  have h := critVals_neg hs
  have hΨ' : ∀ e, proj (pPoly (-s)) (Ψ e) = idBase h (proj (pPoly s) e) :=
    fun e => Subtype.ext (hΨ e)
  obtain ⟨r, A, γ0, γ1, A', γ0', γ1', L, L', -, -, hA, hA', hs1, hs2, h0, h0', hy⟩ :=
    monodromy_point_line hs
  obtain rfl : A' = idBase h A := Subtype.ext (by rw [hA', idBase_val, hA])
  obtain ⟨rfl, rfl⟩ := isStdLoops_unique hs2 (isStdLoops_map h hs1)
  rw [monodromy_homeo h Ψ hΨ'] at h0' hy
  rw [permCongr_relabel L L', h0] at h0'
  refine no_intertwiner_pair _ h0' ?_
  rcases hy with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
  · rw [permCongr_relabel L L', h1] at h1'
    exact Or.inl h1'
  · rw [permCongr_relabel L L', h1] at h1'
    exact Or.inr h1'

end Degree7
