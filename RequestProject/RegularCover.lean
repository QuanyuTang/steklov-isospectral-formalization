module

public import RequestProject.OrderedFibre

/-!
# The regular (Galois) cover as a path component of the ordered fibre cover

For a covering map `p : E → X` and a base ordered fibre tuple `f₀ ∈ OrdFib p n`:

* `isCoveringMap_restrict_pathComponent`: the restriction of a covering map to a path component of
  its total space is a covering map (base locally path connected);
* `RegCov f₀`: the path component of `f₀` in the ordered fibre cover, `regProj` its projection
  to `X`, a covering map (`isCoveringMap_regProj`);
* `deckGroup f₀`: the subgroup of label permutations `σ` with `f₀ ∘ σ ∈ RegCov f₀`; it acts on
  `RegCov f₀` by homeomorphisms over `X` (`regAct`, `regProj_regAct`), **freely**
  (`regAct_eq_self`) and, when the fibres of `p` have exactly `n + 1` points, **transitively on
  every fibre** (`exists_regAct_eq`);
* `mem_regCov_iff`: a tuple over the base point lies in `RegCov f₀` iff it is the coordinatewise
  monodromy image of `f₀` along some loop.
-/

@[expose] public section

open Topology Set

noncomputable section

namespace SteklovRegularCover

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]

/-- Points of one sheet of an even covering over a path-connected set are joined. -/
lemma joined_sheet {U : Set X} {I : Type*} [TopologicalSpace I] {p : E → X}
    (H : p ⁻¹' U ≃ₜ U × I) {V : Set X} (hV : IsPathConnected V) (hVU : V ⊆ U)
    {u u' : X} (hu : u ∈ V) (hu' : u' ∈ V) (i : I) :
    Joined (H.symm (⟨u, hVU hu⟩, i)).1 (H.symm (⟨u', hVU hu'⟩, i)).1 := by
  obtain ⟨γ⟩ := (hV.joinedIn u hu u' hu').joined_subtype
  let g : V → E := fun v => (H.symm (Set.inclusion hVU v, i)).1
  have hg : Continuous g := continuous_subtype_val.comp (H.symm.continuous.comp
    ((continuous_inclusion hVU).prodMk continuous_const))
  exact ⟨γ.map hg⟩

/-- **Restriction of a covering map to a path component is a covering map.** -/
theorem isCoveringMap_restrict_pathComponent [LocPathConnectedSpace X] {p : E → X}
    (hp : IsCoveringMap p) (e₀ : E) :
    IsCoveringMap (fun c : pathComponent e₀ => p c) := by
  intro x
  obtain ⟨hI, U, hxU, hU, hpU, H, hH⟩ := hp x
  have hxV : x ∈ pathComponentIn U x := mem_pathComponentIn_self hxU
  have hVo : IsOpen (pathComponentIn U x) := hU.pathComponentIn x
  have hVc : IsPathConnected (pathComponentIn U x) := isPathConnected_pathComponentIn hxU
  have hVU : pathComponentIn U x ⊆ U := pathComponentIn_subset
  set V := pathComponentIn U x
  let J := {i : p ⁻¹' {x} // (H.symm (⟨x, hxU⟩, i)).1 ∈ pathComponent e₀}
  have hmemS : ∀ (u : U) (i : p ⁻¹' {x}), p (H.symm (u, i)).1 = u := fun u i => by
    rw [← hH, H.apply_symm_apply]
  have hcU : ∀ c : (fun c : pathComponent e₀ => p c) ⁻¹' V, c.1.1 ∈ p ⁻¹' U :=
    fun c => hVU c.2
  have hJ : ∀ c : (fun c : pathComponent e₀ => p c) ⁻¹' V,
      (H.symm (⟨x, hxU⟩, (H ⟨c.1.1, hcU c⟩).2)).1 ∈ pathComponent e₀ := by
    intro c
    have h1 : (H ⟨c.1.1, hcU c⟩).1 = ⟨p c.1.1, hVU c.2⟩ := Subtype.ext (hH _)
    have h2 : (H.symm (⟨p c.1.1, hVU c.2⟩, (H ⟨c.1.1, hcU c⟩).2)).1 = c.1.1 := by
      rw [← h1, Prod.mk.eta, H.symm_apply_apply]
    have hj := joined_sheet H hVc hVU c.2 hxV (H ⟨c.1.1, hcU c⟩).2
    rw [h2] at hj
    exact hj.mem_pathComponent c.1.2
  haveI := hI
  refine IsEvenlyCovered.to_isEvenlyCovered_preimage (I := J) ⟨inferInstance, V, hxV, hVo, ?_, ?_⟩
  · exact hVo.preimage (hp.continuous.comp continuous_subtype_val)
  refine ⟨{
    toFun := fun c => (⟨p c.1.1, c.2⟩, ⟨(H ⟨c.1.1, hcU c⟩).2, hJ c⟩)
    invFun := fun vj => ⟨⟨(H.symm (Set.inclusion hVU vj.1, vj.2.1)).1, ?_⟩, ?_⟩
    left_inv := fun c => ?_
    right_inv := fun vj => ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }, fun c => rfl⟩
  · have hj := joined_sheet H hVc hVU hxV vj.1.2 vj.2.1
    exact hj.mem_pathComponent vj.2.2
  · show p (H.symm (Set.inclusion hVU vj.1, vj.2.1)).1 ∈ V
    rw [hmemS]; exact vj.1.2
  · apply Subtype.ext; apply Subtype.ext
    show (H.symm (Set.inclusion hVU ⟨p c.1.1, c.2⟩, (H ⟨c.1.1, hcU c⟩).2)).1 = c.1.1
    have h1 : Set.inclusion hVU ⟨p c.1.1, c.2⟩ = (H ⟨c.1.1, hcU c⟩).1 :=
      Subtype.ext (hH ⟨c.1.1, hcU c⟩).symm
    rw [h1, Prod.mk.eta, H.symm_apply_apply]
  · obtain ⟨v, j, hj⟩ := vj
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · show p (H.symm (Set.inclusion hVU v, j)).1 = v
      rw [hmemS]
    · show (H ⟨(H.symm (Set.inclusion hVU v, j)).1, _⟩).2 = j
      rw [Subtype.coe_eta, H.apply_symm_apply]
  · refine Continuous.prodMk (Continuous.subtype_mk (hp.continuous.comp
      (continuous_subtype_val.comp continuous_subtype_val)) _) (Continuous.subtype_mk
      (continuous_snd.comp (H.continuous.comp (Continuous.subtype_mk
        (continuous_subtype_val.comp continuous_subtype_val) _))) _)
  · exact Continuous.subtype_mk (Continuous.subtype_mk (continuous_subtype_val.comp
      (H.symm.continuous.comp (((continuous_inclusion hVU).comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)))) _) _

/-! ### The regular cover inside the ordered fibre cover -/

variable {p : E → X} {n : ℕ}

/-- The regular cover: the path component of `f₀` in the ordered fibre cover. -/
def RegCov (f₀ : OrdFib p n) : Set (OrdFib p n) := pathComponent f₀

/-- Its projection to the base. -/
def regProj (f₀ : OrdFib p n) : RegCov f₀ → X := fun f => ordProj p n f.1

/-- **The regular cover is a covering space.** -/
theorem isCoveringMap_regProj [LocPathConnectedSpace X] (hp : IsCoveringMap p)
    (f₀ : OrdFib p n) : IsCoveringMap (regProj f₀) :=
  isCoveringMap_restrict_pathComponent (isCoveringMap_ordProj hp n) f₀

instance (f₀ : OrdFib p n) : PathConnectedSpace (RegCov f₀) :=
  isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_pathComponent (x := f₀))

omit [TopologicalSpace X] in
lemma permAct_mem_pathComponent {f₀ f : OrdFib p n} (σ : Equiv.Perm (Fin (n + 1)))
    (h : f ∈ pathComponent f₀) : permAct p n σ f ∈ pathComponent (permAct p n σ f₀) := by
  obtain ⟨γ⟩ := h
  exact ⟨γ.map (continuous_permAct p n σ)⟩

/-- **The deck group**: label permutations moving `f₀` inside its own path component. -/
def deckGroup (f₀ : OrdFib p n) : Subgroup (Equiv.Perm (Fin (n + 1))) where
  carrier := {σ | permAct p n σ f₀ ∈ pathComponent f₀}
  one_mem' := mem_pathComponent_self f₀
  mul_mem' := by
    intro σ τ hσ hτ
    show permAct p n τ (permAct p n σ f₀) ∈ pathComponent f₀
    have := permAct_mem_pathComponent τ hσ
    rwa [pathComponent_congr hτ] at this
  inv_mem' := by
    intro σ hσ
    have h1 := permAct_mem_pathComponent σ⁻¹ hσ
    rw [← permAct_mul, mul_inv_cancel, permAct_one] at h1
    exact mem_pathComponent_of_mem h1

omit [TopologicalSpace X] in
lemma mem_deckGroup {f₀ : OrdFib p n} {σ : Equiv.Perm (Fin (n + 1))} :
    σ ∈ deckGroup f₀ ↔ permAct p n σ f₀ ∈ RegCov f₀ := Iff.rfl

omit [TopologicalSpace X] in
lemma permAct_mem_regCov {f₀ f : OrdFib p n} {σ : Equiv.Perm (Fin (n + 1))}
    (hσ : σ ∈ deckGroup f₀) (hf : f ∈ RegCov f₀) : permAct p n σ f ∈ RegCov f₀ := by
  have h2 := permAct_mem_pathComponent σ hf
  rwa [pathComponent_congr hσ] at h2

/-- The deck action on the regular cover. -/
def regAct (f₀ : OrdFib p n) (σ : deckGroup f₀) (f : RegCov f₀) : RegCov f₀ :=
  ⟨permAct p n σ f.1, permAct_mem_regCov σ.2 f.2⟩

omit [TopologicalSpace X] in
lemma regProj_regAct (f₀ : OrdFib p n) (σ : deckGroup f₀) (f : RegCov f₀) :
    regProj f₀ (regAct f₀ σ f) = regProj f₀ f := ordProj_permAct p n σ f.1

omit [TopologicalSpace X] in
lemma continuous_regAct (f₀ : OrdFib p n) (σ : deckGroup f₀) : Continuous (regAct f₀ σ) :=
  Continuous.subtype_mk ((continuous_permAct p n σ).comp continuous_subtype_val) _

omit [TopologicalSpace X] in
lemma regAct_one (f₀ : OrdFib p n) (f : RegCov f₀) : regAct f₀ 1 f = f := rfl

omit [TopologicalSpace X] in
lemma regAct_mul (f₀ : OrdFib p n) (σ τ : deckGroup f₀) (f : RegCov f₀) :
    regAct f₀ (σ * τ) f = regAct f₀ τ (regAct f₀ σ f) := rfl

omit [TopologicalSpace X] in
/-- **The deck action is free.** -/
lemma regAct_eq_self {f₀ : OrdFib p n} {σ : deckGroup f₀} {f : RegCov f₀}
    (h : regAct f₀ σ f = f) : σ = 1 :=
  Subtype.ext (permAct_eq_self (congrArg Subtype.val h))

omit [TopologicalSpace X] in
/-- **The deck action is transitive on the fibres** when every fibre of `p` has exactly `n + 1`
points (the ordered fibre tuples are then complete labellings of the fibre). -/
theorem exists_regAct_eq (hcard : ∀ x : X, Nat.card (p ⁻¹' {x}) = n + 1) {f₀ : OrdFib p n}
    {f f' : RegCov f₀} (h : regProj f₀ f = regProj f₀ f') :
    ∃ σ : deckGroup f₀, regAct f₀ σ f = f' := by
  set x := regProj f₀ f
  have hfin : Finite (p ⁻¹' {x}) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  let a : Fin (n + 1) → p ⁻¹' {x} := fun i => ⟨f.1.1 i, (ordProj_apply p n f.1 i)⟩
  let b : Fin (n + 1) → p ⁻¹' {x} := fun i => ⟨f'.1.1 i, (ordProj_apply p n f'.1 i).trans h.symm⟩
  have ha : Function.Injective a := fun i j hij => f.1.2.2 (congrArg Subtype.val hij)
  have hb : Function.Injective b := fun i j hij => f'.1.2.2 (congrArg Subtype.val hij)
  have hc : Nat.card (p ⁻¹' {x}) ≤ Nat.card (Fin (n + 1)) := by rw [hcard, Nat.card_fin]
  have hab := ha.bijective_of_nat_card_le hc
  have hbb := hb.bijective_of_nat_card_le hc
  let A := Equiv.ofBijective a hab
  let B := Equiv.ofBijective b hbb
  let σ : Equiv.Perm (Fin (n + 1)) := B.trans A.symm
  have hσf : permAct p n σ f.1 = f'.1 := by
    apply Subtype.ext; funext i
    show f.1.1 (A.symm (B i)) = f'.1.1 i
    have := congrArg Subtype.val (A.apply_symm_apply (B i))
    exact this
  have hσ : σ ∈ deckGroup f₀ := by
    have h1 := permAct_mem_pathComponent σ (mem_pathComponent_of_mem f.2)
    rw [hσf, pathComponent_congr f'.2] at h1
    exact h1
  exact ⟨⟨σ, hσ⟩, Subtype.ext hσf⟩

/-! ### The fibre over the base point and the monodromy -/

lemma joined_monodromy {E' : Type*} [TopologicalSpace E'] {q : E' → X} (hq : IsCoveringMap q)
    {x y : X} (γ : Path.Homotopic.Quotient x y) (e : q ⁻¹' {x}) :
    Joined e.1 (hq.monodromy γ e).1 := by
  induction γ using Quotient.inductionOn with
  | h γ =>
    let L := hq.liftPath (γ : C(unitInterval, X)) e.1 (γ.source.trans e.2.symm)
    exact ⟨⟨L, hq.liftPath_zero _ _ _, rfl⟩⟩

/-- **Fibres of the regular cover via monodromy**: a tuple `f` over `y` lies in `RegCov f₀` iff it
is the coordinatewise monodromy image of `f₀` along some path class from `ordProj f₀` to `y`. -/
theorem mem_regCov_iff (hp : IsCoveringMap p) (f₀ : OrdFib p n) {x y : X}
    (hx : ordProj p n f₀ = x) (f : OrdFib p n) (hy : ordProj p n f = y) :
    f ∈ RegCov f₀ ↔ ∃ γ : Path.Homotopic.Quotient x y, ∀ i,
      f.1 i = (hp.monodromy γ ⟨f₀.1 i, (ordProj_apply p n f₀ i).trans hx⟩).1 := by
  subst hx hy
  have hcov := isCoveringMap_ordProj hp n
  constructor
  · rintro ⟨δ⟩
    refine ⟨(Path.Homotopic.Quotient.mk δ).map ⟨ordProj p n, hcov.continuous⟩, fun i => ?_⟩
    rw [← monodromy_ordProj hp n _ ⟨f₀, rfl⟩ i, hcov.monodromy_map]
  · rintro ⟨γ, hγ⟩
    have hj := joined_monodromy hcov γ ⟨f₀, rfl⟩
    have heq : (hcov.monodromy γ ⟨f₀, rfl⟩).1 = f := by
      apply Subtype.ext; funext i
      rw [monodromy_ordProj hp n γ ⟨f₀, rfl⟩ i, hγ i]
    rw [heq] at hj
    exact hj

/-! ### Quotient by the stabilizer of a label: the original cover -/

/-- The first coordinate `RegCov f₀ → E`. -/
def evZero (f₀ : OrdFib p n) (f : RegCov f₀) : E := f.1.1 0

omit [TopologicalSpace X] in
lemma proj_evZero (f₀ : OrdFib p n) (f : RegCov f₀) : p (evZero f₀ f) = regProj f₀ f := rfl

omit [TopologicalSpace X] in
lemma continuous_evZero (f₀ : OrdFib p n) : Continuous (evZero f₀) :=
  (continuous_apply 0).comp (continuous_subtype_val.comp continuous_subtype_val)

omit [TopologicalSpace X] in
/-- **The fibres of the first-coordinate map are exactly the orbits of the label stabilizer**
`{σ ∈ deckGroup f₀ | σ 0 = 0}` (complete fibres of `p` of size `n + 1`). -/
theorem evZero_eq_iff (hcard : ∀ x : X, Nat.card (p ⁻¹' {x}) = n + 1) {f₀ : OrdFib p n}
    (f f' : RegCov f₀) :
    evZero f₀ f = evZero f₀ f' ↔ ∃ σ : deckGroup f₀, σ.1 0 = 0 ∧ regAct f₀ σ f = f' := by
  constructor
  · intro h
    have hb : regProj f₀ f = regProj f₀ f' := by
      rw [← proj_evZero, ← proj_evZero, h]
    obtain ⟨σ, hσ⟩ := exists_regAct_eq hcard hb
    refine ⟨σ, f.1.2.2 ?_, hσ⟩
    have := congrFun (congrArg (fun g : RegCov f₀ => g.1.1) hσ) 0
    exact this.trans h.symm
  · rintro ⟨σ, hσ0, rfl⟩
    show f.1.1 0 = f.1.1 (σ.1 0)
    rw [hσ0]

/-- **The first-coordinate map is onto** when `E` is path connected. -/
theorem evZero_surjective [PathConnectedSpace E] (hp : IsCoveringMap p) (f₀ : OrdFib p n) :
    Function.Surjective (evZero f₀) := by
  intro e
  let δ : Path (f₀.1 0) e := PathConnectedSpace.somePath _ _
  let γ : C(unitInterval, X) := ⟨fun t => p (δ t), hp.continuous.comp δ.continuous⟩
  have h0 : γ 0 = ordProj p n f₀ := by show p (δ 0) = p (f₀.1 0); rw [δ.source]
  have hcov := isCoveringMap_ordProj hp n
  set Λ := hcov.liftPath γ f₀ h0
  have hΛ0 : Λ 0 = f₀ := hcov.liftPath_zero _ _ _
  have hcoord : hp.liftPath γ (f₀.1 0) (h0.trans (ordProj_apply p n f₀ 0).symm) =
      (δ : C(unitInterval, E)) :=
    ((hp.eq_liftPath_iff' _).2 ⟨rfl, δ.source⟩).symm
  have hmem : Λ 1 ∈ RegCov f₀ := by
    rw [← hΛ0]
    exact ⟨⟨Λ, rfl, rfl⟩⟩
  refine ⟨⟨Λ 1, hmem⟩, ?_⟩
  show (Λ 1).1 0 = e
  rw [liftPath_ordProj hp n γ f₀ h0 1 0, hcoord]
  exact δ.target

omit [TopologicalSpace X] in
/-- **Every fibre of the regular cover is a torsor of the deck group**: it has as many points as
the deck group (complete fibres of `p` of size `n + 1`). -/
theorem card_regProj_fibre (hcard : ∀ x : X, Nat.card (p ⁻¹' {x}) = n + 1) {f₀ : OrdFib p n}
    (f : RegCov f₀) :
    Nat.card (regProj f₀ ⁻¹' {regProj f₀ f}) = Nat.card (deckGroup f₀) := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun σ : deckGroup f₀ => (⟨regAct f₀ σ f, regProj_regAct f₀ σ f⟩ :
      regProj f₀ ⁻¹' {regProj f₀ f})) ⟨fun σ τ h => ?_, fun g => ?_⟩)).symm
  · have h1 := congrArg (fun g : regProj f₀ ⁻¹' {regProj f₀ f} => regAct f₀ τ⁻¹ g.1) h
    simp only [← regAct_mul, mul_inv_cancel, regAct_one] at h1
    have := regAct_eq_self h1
    rw [mul_inv_eq_one] at this
    exact this
  · obtain ⟨σ, hσ⟩ := exists_regAct_eq hcard (f := f) (f' := g.1) g.2.symm
    exact ⟨σ, Subtype.ext hσ⟩

/-! ### Evaluation at an arbitrary label, and base tuples from labellings -/

/-- The `k`-th coordinate `RegCov f₀ → E`. -/
def evAt (f₀ : OrdFib p n) (k : Fin (n + 1)) (f : RegCov f₀) : E := f.1.1 k

omit [TopologicalSpace X] in
lemma proj_evAt (f₀ : OrdFib p n) (k : Fin (n + 1)) (f : RegCov f₀) :
    p (evAt f₀ k f) = regProj f₀ f := ordProj_apply p n f.1 k

omit [TopologicalSpace X] in
lemma continuous_evAt (f₀ : OrdFib p n) (k : Fin (n + 1)) : Continuous (evAt f₀ k) :=
  (continuous_apply k).comp (continuous_subtype_val.comp continuous_subtype_val)

omit [TopologicalSpace X] in
/-- **The fibres of the `k`-th coordinate map are the orbits of the stabilizer of the label `k`**
in the deck group. -/
theorem evAt_eq_iff (hcard : ∀ x : X, Nat.card (p ⁻¹' {x}) = n + 1) {f₀ : OrdFib p n}
    (k : Fin (n + 1)) (f f' : RegCov f₀) :
    evAt f₀ k f = evAt f₀ k f' ↔ ∃ σ : deckGroup f₀, σ.1 k = k ∧ regAct f₀ σ f = f' := by
  constructor
  · intro h
    have hb : regProj f₀ f = regProj f₀ f' := by
      rw [← proj_evAt f₀ k, ← proj_evAt f₀ k, h]
    obtain ⟨σ, hσ⟩ := exists_regAct_eq hcard hb
    refine ⟨σ, f.1.2.2 ?_, hσ⟩
    have := congrFun (congrArg (fun g : RegCov f₀ => g.1.1) hσ) k
    exact this.trans h.symm
  · rintro ⟨σ, hσk, rfl⟩
    show f.1.1 k = f.1.1 (σ.1 k)
    rw [hσk]

/-- **Every point joined to the `k`-th point of `f₀` is the `k`-th point of some tuple in the
regular cover.** -/
theorem evAt_surjective_of_joined (hp : IsCoveringMap p) (f₀ : OrdFib p n) (k : Fin (n + 1))
    {e : E} (hj : Joined (f₀.1 k) e) : ∃ f : RegCov f₀, evAt f₀ k f = e := by
  obtain ⟨δ⟩ := hj
  let γ : C(unitInterval, X) := ⟨fun t => p (δ t), hp.continuous.comp δ.continuous⟩
  have h0 : γ 0 = ordProj p n f₀ := by
    show p (δ 0) = ordProj p n f₀; rw [δ.source]; exact ordProj_apply p n f₀ k
  have hcov := isCoveringMap_ordProj hp n
  set Λ := hcov.liftPath γ f₀ h0
  have hΛ0 : Λ 0 = f₀ := hcov.liftPath_zero _ _ _
  have hcoord : hp.liftPath γ (f₀.1 k) (h0.trans (ordProj_apply p n f₀ k).symm) =
      (δ : C(unitInterval, E)) :=
    ((hp.eq_liftPath_iff' _).2 ⟨rfl, δ.source⟩).symm
  have hmem : Λ 1 ∈ RegCov f₀ := by
    rw [← hΛ0]
    exact ⟨⟨Λ, rfl, rfl⟩⟩
  refine ⟨⟨Λ 1, hmem⟩, ?_⟩
  show (Λ 1).1 k = e
  rw [liftPath_ordProj hp n γ f₀ h0 1 k, hcoord]
  exact δ.target

/-- The ordered fibre tuple given by a labelling `L` of the fibre over `A`. -/
def baseTuple {A : X} (L : p ⁻¹' {A} ≃ Fin (n + 1)) : OrdFib p n :=
  ⟨fun i => (L.symm i).1, fun i => (L.symm i).2.trans (L.symm 0).2.symm,
    fun _ _ h => L.symm.injective (Subtype.ext h)⟩

omit [TopologicalSpace E] [TopologicalSpace X] in
lemma ordProj_baseTuple {A : X} (L : p ⁻¹' {A} ≃ Fin (n + 1)) :
    ordProj p n (baseTuple L) = A := (L.symm 0).2

/-- **Deck transformations are monodromy permutations**: in the labelling `L`, a permutation is a
deck transformation of `RegCov (baseTuple L)` iff it is the monodromy of some loop at `A`. -/
theorem mem_deckGroup_baseTuple (hp : IsCoveringMap p) {A : X} (L : p ⁻¹' {A} ≃ Fin (n + 1))
    (σ : Equiv.Perm (Fin (n + 1))) :
    σ ∈ deckGroup (baseTuple L) ↔
      ∃ γ : Path.Homotopic.Quotient A A, ∀ i, L.symm (σ i) = hp.monodromy γ (L.symm i) := by
  rw [mem_deckGroup, mem_regCov_iff hp (baseTuple L) (ordProj_baseTuple L)
    (permAct p n σ (baseTuple L)) ((ordProj_permAct p n σ _).trans (ordProj_baseTuple L))]
  refine exists_congr fun γ => forall_congr' fun i => ?_
  rw [Subtype.ext_iff]
  rfl

end SteklovRegularCover
