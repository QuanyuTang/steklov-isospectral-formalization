module

public import Mathlib
public import RequestProject.Degree7Permutations

/-!
# The degree-seven candidate: kernel-checked counts in `S₇`

All statements are decided by the Lean kernel (`decide +kernel`) over the `5040` elements of
`S₇`, after rewriting the cycle-type conditions into the equivalent elementary conditions of
`cycleType33_iff` (`σ³ = 1` with one fixed point) and `cycleType7_iff` (`σ⁷ = 1`, `σ ≠ 1`).
-/

@[expose] public section

open Equiv Finset

noncomputable section

namespace Degree7

set_option maxHeartbeats 0 in
/-- **Exactly `280` permutations of `Fin 7` have cycle type `(3,3,1)`.** -/
theorem card_cycleType33 :
    (univ.filter fun y : Perm (Fin 7) => y.cycleType = {3, 3}).card = 280 := by
  rw [Finset.filter_congr fun y _ => cycleType33_iff y]
  decide +kernel

set_option maxHeartbeats 0 in
/-- **Exactly `96` of them make `x y` a `7`-cycle.** -/
theorem card_good :
    (univ.filter fun y : Perm (Fin 7) =>
      y.cycleType = {3, 3} ∧ (x7 * y).cycleType = {7}).card = 96 := by
  rw [Finset.filter_congr fun y _ => and_congr (cycleType33_iff y) (cycleType7_iff (x7 * y))]
  decide +kernel

set_option maxHeartbeats 0 in
/-- **The centralizer of `x` has `48` elements.** -/
theorem card_centralizer :
    (univ.filter fun σ : Perm (Fin 7) => σ * x7 = x7 * σ).card = 48 := by
  decide +kernel

set_option maxHeartbeats 0 in
/-- **The `96` choices form two centralizer orbits of size `48`, represented by `y₁` and `y₂`.** -/
theorem good_eq_orbits :
    let C := univ.filter fun σ : Perm (Fin 7) => σ * x7 = x7 * σ
    (univ.filter fun y : Perm (Fin 7) => y.cycleType = {3, 3} ∧ (x7 * y).cycleType = {7}) =
      C.image (fun σ => σ * y1 * σ⁻¹) ∪ C.image (fun σ => σ * y2 * σ⁻¹) ∧
    (C.image (fun σ => σ * y1 * σ⁻¹)).card = 48 ∧ (C.image (fun σ => σ * y2 * σ⁻¹)).card = 48 ∧
    Disjoint (C.image (fun σ => σ * y1 * σ⁻¹)) (C.image (fun σ => σ * y2 * σ⁻¹)) := by
  intro C
  rw [Finset.filter_congr fun y _ => and_congr (cycleType33_iff y) (cycleType7_iff (x7 * y))]
  decide +kernel

end Degree7
