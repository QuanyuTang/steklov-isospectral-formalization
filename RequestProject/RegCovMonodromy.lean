module

public import RequestProject.RegularCover

/-!
# Monodromy of the regular (Galois-closure) cover

For a covering `p : E → X` with fibres of size `n + 1` and the regular cover `RegCov f₀` (path
component of ordered complete fibres), the monodromy of a loop `γ` on `RegCov f₀` is computed
coordinatewise from the monodromy of `p` (`regMonodromy_val`).  Consequently a point of the regular
cover returns to itself after `k` turns around `γ` iff the `k`-th power of the monodromy of `p`
along `γ` is the identity on the whole fibre (`regMonodromy_iterate_eq_self_iff`).
-/

@[expose] public section

open Topology

noncomputable section

namespace SteklovRegularCover

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] [LocallyPathConnectedSpace X]
  {p : E → X} {n : ℕ} (hp : IsCoveringMap p) (f₀ : OrdFib p n)

/-- The monodromy of the regular cover is the monodromy of the ordered fibre cover. -/
theorem regMonodromy_val {x y : X} (γ : Path.Homotopic.Quotient x y) (f : regProj f₀ ⁻¹' {x}) :
    ((isCoveringMap_regProj hp f₀).monodromy γ f).1.1 =
      ((isCoveringMap_ordProj hp n).monodromy γ ⟨f.1.1, f.2⟩).1 := by
  induction γ using Quotient.inductionOn with
  | h γ =>
    show ((isCoveringMap_regProj hp f₀).liftPath (γ : C(unitInterval, X)) f.1 _ 1).1 =
      (isCoveringMap_ordProj hp n).liftPath (γ : C(unitInterval, X)) f.1.1 _ 1
    set Γ := (isCoveringMap_regProj hp f₀).liftPath (γ : C(unitInterval, X)) f.1
      (γ.source.trans f.2.symm)
    have hΓ : (⟨fun t => (Γ t).1, continuous_subtype_val.comp Γ.continuous⟩ :
        C(unitInterval, OrdFib p n)) = (isCoveringMap_ordProj hp n).liftPath
          (γ : C(unitInterval, X)) f.1.1 (γ.source.trans f.2.symm) := by
      rw [IsCoveringMap.eq_liftPath_iff']
      refine ⟨funext fun t => ?_, ?_⟩
      · exact congrFun ((isCoveringMap_regProj hp f₀).liftPath_lifts _ _ _) t
      · simp only [ContinuousMap.coe_mk]
        rw [(isCoveringMap_regProj hp f₀).liftPath_zero]
    exact congrFun (congrArg DFunLike.coe hΓ) 1

/-- Coordinates of the monodromy of the regular cover. -/
theorem regMonodromy_coord {x y : X} (γ : Path.Homotopic.Quotient x y) (f : regProj f₀ ⁻¹' {x})
    (i : Fin (n + 1)) :
    ((isCoveringMap_regProj hp f₀).monodromy γ f).1.1.1 i =
      (hp.monodromy γ ⟨f.1.1.1 i, (ordProj_apply p n f.1.1 i).trans f.2⟩).1 := by
  rw [regMonodromy_val hp f₀]
  exact monodromy_ordProj hp n γ ⟨f.1.1, f.2⟩ i

/-- Coordinates of iterated monodromy of the regular cover. -/
theorem regMonodromy_iterate_coord {x : X} (γ : Path.Homotopic.Quotient x x)
    (f : regProj f₀ ⁻¹' {x}) (k : ℕ) (i : Fin (n + 1)) :
    (((isCoveringMap_regProj hp f₀).monodromy γ)^[k] f).1.1.1 i =
      ((hp.monodromy γ)^[k] ⟨f.1.1.1 i, (ordProj_apply p n f.1.1 i).trans f.2⟩).1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', regMonodromy_coord hp f₀]
    congr 2
    exact Subtype.ext ih

/-- **Return criterion.**  If all fibres of `p` have `n + 1` points, a point of the regular cover
returns to itself after `k` turns around the loop `γ` iff the `k`-th iterate of the monodromy of
`p` along `γ` fixes the whole fibre. -/
theorem regMonodromy_iterate_eq_self_iff (hcard : ∀ x : X, Nat.card (p ⁻¹' {x}) = n + 1)
    {x : X} (γ : Path.Homotopic.Quotient x x) (f : regProj f₀ ⁻¹' {x}) (k : ℕ) :
    ((isCoveringMap_regProj hp f₀).monodromy γ)^[k] f = f ↔
      ∀ e : p ⁻¹' {x}, (hp.monodromy γ)^[k] e = e := by
  -- the coordinates of `f` enumerate the fibre
  let F : Fin (n + 1) → p ⁻¹' {x} := fun i => ⟨f.1.1.1 i, (ordProj_apply p n f.1.1 i).trans f.2⟩
  have hFinj : Function.Injective F := fun i j h => f.1.1.2.2 (congrArg Subtype.val h)
  have hfin : Finite (p ⁻¹' {x}) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
  have hFsurj : Function.Surjective F := by
    have := Fintype.ofFinite (p ⁻¹' {x})
    refine (Fintype.bijective_iff_injective_and_card F).2 ⟨hFinj, ?_⟩ |>.2
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card, hcard]
  constructor
  · intro h e
    obtain ⟨i, rfl⟩ := hFsurj e
    apply Subtype.ext
    rw [← regMonodromy_iterate_coord hp f₀ γ f k i, h]
  · intro h
    apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; funext i
    rw [regMonodromy_iterate_coord hp f₀ γ f k i]
    exact congrArg Subtype.val (h (F i))

end SteklovRegularCover
