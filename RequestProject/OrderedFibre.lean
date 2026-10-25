module

public import Mathlib

/-!
# The cover of ordered complete fibres

For a covering map `p : E → X` and `n : ℕ`, `OrdFib p n` is the space of injective
`(n+1)`-tuples of points of `E` lying in one fibre of `p`, with projection `ordProj` (the common
image point).  We prove:

* `isCoveringMap_ordProj`: `ordProj` is a covering map (fibre over `x`: injective tuples in the
  fibre of `p` over `x`);
* `permAct`: the right action of `Equiv.Perm (Fin (n+1))` by permuting the coordinates; it covers
  the identity of `X` (`ordProj_permAct`), is continuous, and is free (`permAct_eq_self`);
* `liftPath_ordProj`, `monodromy_ordProj`: path lifting and monodromy of `ordProj` are computed
  coordinatewise from those of `p`.

This is the first step of the Galois-closure construction of the common regular cover: for a
degree-`(n+1)` cover, the ordered complete fibres over `x` are the bijective labellings of the
fibre of `p`.
-/

@[expose] public section

open Topology

noncomputable section

namespace SteklovRegularCover

variable {E X : Type*}

/-- Injective `(n+1)`-tuples of points of `E` lying in one fibre of `p`. -/
def OrdFib (p : E → X) (n : ℕ) : Set (Fin (n + 1) → E) :=
  {f | (∀ i, p (f i) = p (f 0)) ∧ Function.Injective f}

/-- The projection of an ordered fibre tuple to its base point. -/
def ordProj (p : E → X) (n : ℕ) : OrdFib p n → X := fun f => p (f.1 0)

lemma ordProj_apply (p : E → X) (n : ℕ) (f : OrdFib p n) (i : Fin (n + 1)) :
    p (f.1 i) = ordProj p n f := f.2.1 i

/-- The right action of permutations of the labels on ordered fibre tuples. -/
def permAct (p : E → X) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) (f : OrdFib p n) : OrdFib p n :=
  ⟨f.1 ∘ σ, fun i => by
    show p (f.1 (σ i)) = p (f.1 (σ 0))
    rw [f.2.1 (σ i), f.2.1 (σ 0)], f.2.2.comp σ.injective⟩

@[simp] lemma permAct_val (p : E → X) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) (f : OrdFib p n) :
    (permAct p n σ f).1 = f.1 ∘ σ := rfl

lemma ordProj_permAct (p : E → X) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) (f : OrdFib p n) :
    ordProj p n (permAct p n σ f) = ordProj p n f := f.2.1 (σ 0)

lemma permAct_one (p : E → X) (n : ℕ) (f : OrdFib p n) : permAct p n 1 f = f := rfl

lemma permAct_mul (p : E → X) (n : ℕ) (σ τ : Equiv.Perm (Fin (n + 1))) (f : OrdFib p n) :
    permAct p n (σ * τ) f = permAct p n τ (permAct p n σ f) := rfl

/-- **The permutation action is free.** -/
lemma permAct_eq_self {p : E → X} {n : ℕ} {σ : Equiv.Perm (Fin (n + 1))} {f : OrdFib p n}
    (h : permAct p n σ f = f) : σ = 1 := by
  ext i
  have := congrFun (congrArg Subtype.val h) i
  exact congrArg Fin.val (f.2.2 this)

variable [TopologicalSpace E] [TopologicalSpace X]

/-- Even covering of `ordProj` from an even covering of `p`, with fibre the injective tuples of
the fibre model. -/
theorem isEvenlyCovered_ordProj {p : E → X} {n : ℕ} {x : X} {I : Type*} [TopologicalSpace I]
    (h : IsEvenlyCovered p x I) :
    IsEvenlyCovered (ordProj p n) x {g : Fin (n + 1) → I // Function.Injective g} := by
  obtain ⟨hI, U, hxU, hU, hpU, H, hH⟩ := h
  have hmem : ∀ (f : ordProj p n ⁻¹' U) (i : Fin (n + 1)), f.1.1 i ∈ p ⁻¹' U := fun f i => by
    show p (f.1.1 i) ∈ U
    rw [ordProj_apply p n f.1 i]; exact f.2
  have hmemS : ∀ (u : U) (i : I), p (H.symm (u, i)).1 = u := fun u i => by
    rw [← hH, H.apply_symm_apply]
  refine ⟨inferInstance, U, hxU, hU, ?_, ?_⟩
  · show IsOpen ((fun f : OrdFib p n => f.1 0) ⁻¹' (p ⁻¹' U))
    exact hpU.preimage ((continuous_apply 0).comp continuous_subtype_val)
  refine ⟨{
    toFun := fun f => ((H ⟨f.1.1 0, hmem f 0⟩).1,
      ⟨fun i => (H ⟨f.1.1 i, hmem f i⟩).2, fun i j hij => ?_⟩)
    invFun := fun ug => ⟨⟨fun i => (H.symm (ug.1, ug.2.1 i)).1, fun i => by
        rw [hmemS, hmemS], fun i j hij => ug.2.2 ?_⟩, by
        show p (H.symm (ug.1, ug.2.1 0)).1 ∈ U
        rw [hmemS]; exact ug.1.2⟩
    left_inv := fun f => ?_
    right_inv := fun ug => ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }, fun f => ?_⟩
  · -- injectivity of the fibre coordinates
    apply f.1.2.2
    have h1 : (H ⟨f.1.1 i, hmem f i⟩).1 = (H ⟨f.1.1 j, hmem f j⟩).1 := Subtype.ext (by
      rw [hH, hH, ordProj_apply p n f.1 i, ordProj_apply p n f.1 j])
    have := congrArg Subtype.val (H.injective (Prod.ext h1 hij))
    exact this
  · have := H.symm.injective (Subtype.ext hij)
    exact congrArg Prod.snd this
  · apply Subtype.ext; apply Subtype.ext; funext i
    show (H.symm ((H ⟨f.1.1 0, hmem f 0⟩).1, (H ⟨f.1.1 i, hmem f i⟩).2)).1 = f.1.1 i
    have h1 : (H ⟨f.1.1 0, hmem f 0⟩).1 = (H ⟨f.1.1 i, hmem f i⟩).1 := Subtype.ext (by
      rw [hH, hH, ordProj_apply p n f.1 0, ordProj_apply p n f.1 i])
    rw [h1, Prod.mk.eta, H.symm_apply_apply]
  · obtain ⟨u, g, hg⟩ := ug
    refine Prod.ext ?_ (Subtype.ext (funext fun i => ?_))
    · show (H ⟨(H.symm (u, g 0)).1, _⟩).1 = u
      rw [Subtype.coe_eta, H.apply_symm_apply]
    · show (H ⟨(H.symm (u, g i)).1, _⟩).2 = g i
      rw [Subtype.coe_eta, H.apply_symm_apply]
  · refine Continuous.prodMk ?_ (Continuous.subtype_mk (continuous_pi fun i => ?_) _)
    · exact continuous_fst.comp (H.continuous.comp (Continuous.subtype_mk
        ((continuous_apply 0).comp (continuous_subtype_val.comp continuous_subtype_val)) _))
    · exact continuous_snd.comp (H.continuous.comp (Continuous.subtype_mk
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_subtype_val)) _))
  · refine Continuous.subtype_mk (Continuous.subtype_mk (continuous_pi fun i => ?_) _) _
    exact continuous_subtype_val.comp (H.symm.continuous.comp (continuous_fst.prodMk
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))))
  · show (H ⟨f.1.1 0, hmem f 0⟩).1.1 = p (f.1.1 0)
    rw [hH]

/-- **The ordered complete fibres form a covering space.** -/
theorem isCoveringMap_ordProj {p : E → X} (hp : IsCoveringMap p) (n : ℕ) :
    IsCoveringMap (ordProj p n) :=
  fun x => (isEvenlyCovered_ordProj (n := n) (hp x)).to_isEvenlyCovered_preimage

omit [TopologicalSpace X] in
lemma continuous_permAct (p : E → X) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) :
    Continuous (permAct p n σ) :=
  continuous_induced_rng.2 (continuous_pi fun i =>
    (continuous_apply (σ i)).comp continuous_subtype_val)

/-- The permutation action as a homeomorphism. -/
def permHomeo (p : E → X) (n : ℕ) (σ : Equiv.Perm (Fin (n + 1))) : OrdFib p n ≃ₜ OrdFib p n where
  toFun := permAct p n σ
  invFun := permAct p n σ⁻¹
  left_inv f := by rw [← permAct_mul, mul_inv_cancel, permAct_one]
  right_inv f := by rw [← permAct_mul, inv_mul_cancel, permAct_one]
  continuous_toFun := continuous_permAct p n σ
  continuous_invFun := continuous_permAct p n σ⁻¹

/-! ### Coordinatewise path lifting and monodromy -/

section lifting

variable {p : E → X} (hp : IsCoveringMap p) (n : ℕ)

/-- **Path lifting in the ordered fibre cover is coordinatewise.** -/
theorem liftPath_ordProj (γ : C(unitInterval, X)) (f : OrdFib p n) (h0 : γ 0 = ordProj p n f) (t)
    (i : Fin (n + 1)) :
    ((isCoveringMap_ordProj hp n).liftPath γ f h0 t).1 i =
      hp.liftPath γ (f.1 i) (h0.trans (ordProj_apply p n f i).symm) t := by
  set L : Fin (n + 1) → C(unitInterval, E) := fun i =>
    hp.liftPath γ (f.1 i) (h0.trans (ordProj_apply p n f i).symm)
  have hL : ∀ i s, p (L i s) = γ s := fun i s => congrFun (hp.liftPath_lifts _ _ _) s
  have hinj : ∀ s, Function.Injective fun i => L i s := by
    intro s i j hij
    have heq : L i = L j := by
      have := hp.eq_of_comp_eq (L i).continuous (L j).continuous
        (by funext s; simp only [Function.comp_apply, hL]) s hij
      exact ContinuousMap.ext (congrFun this)
    apply f.2.2
    rw [← hp.liftPath_zero γ (f.1 i) (h0.trans (ordProj_apply p n f i).symm),
      ← hp.liftPath_zero γ (f.1 j) (h0.trans (ordProj_apply p n f j).symm)]
    exact congrArg (fun c : C(unitInterval, E) => c 0) heq
  let Γ : C(unitInterval, OrdFib p n) :=
    ⟨fun s => ⟨fun i => L i s, fun i => (hL i s).trans (hL 0 s).symm, hinj s⟩,
      Continuous.subtype_mk (continuous_pi fun i => (L i).continuous) _⟩
  have hΓ : Γ = (isCoveringMap_ordProj hp n).liftPath γ f h0 := by
    rw [IsCoveringMap.eq_liftPath_iff']
    refine ⟨funext fun s => ?_, Subtype.ext (funext fun i => ?_)⟩
    · exact hL 0 s
    · exact hp.liftPath_zero _ _ _
  rw [← hΓ]
  rfl

/-- **Monodromy of the ordered fibre cover is coordinatewise.** -/
theorem monodromy_ordProj {x y : X} (γ : Path.Homotopic.Quotient x y)
    (f : ordProj p n ⁻¹' {x}) (i : Fin (n + 1)) :
    ((isCoveringMap_ordProj hp n).monodromy γ f).1.1 i =
      (hp.monodromy γ ⟨f.1.1 i, (ordProj_apply p n f.1 i).trans f.2⟩).1 := by
  induction γ using Quotient.inductionOn with
  | h γ =>
    exact liftPath_ordProj hp n (γ : C(unitInterval, X)) f.1 _ 1 i

end lifting

end SteklovRegularCover
