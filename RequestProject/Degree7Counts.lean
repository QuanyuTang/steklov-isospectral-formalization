module

public import Mathlib
public import RequestProject.Degree7Permutations

/-!
# The degree-seven candidate: kernel-checked counts in `S₇`

`card_cycleType33`, `card_good` and `card_centralizer` are decided by the Lean kernel
(`decide +kernel`) over the `5040` elements of `S₇`, after rewriting the cycle-type conditions into
the equivalent elementary conditions of `cycleType33_iff` (`σ³ = 1` with one fixed point) and
`cycleType7_iff` (`σ⁷ = 1`, `σ ≠ 1`).

`good_eq_orbits` is proved structurally (it does not enumerate `S₇`): the two orbits lie in the
set of good `y` by conjugation invariance of `cycleType`; each has `48` elements because the
centralizer of `x` has order `48` (Mathlib's centralizer-order formula) and acts freely on `y₁`,
`y₂`; they are disjoint because no centralizer element conjugates `y₁` to `y₂`; and the set of good
`y` has at most `96` elements by a small kernel-checked search over partial assignments
(`GoodOrbits.search_ok`), pruned by `y³ = 1`, the fixed-point freeness of `x y` and injectivity.
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

/-! ### Structural proof of `good_eq_orbits` (private helpers) -/

namespace GoodOrbits

private def xf : Fin 7 → Fin 7 := ![1, 0, 3, 2, 4, 5, 6]
private def y1f : Fin 7 → Fin 7 := ![0, 2, 4, 5, 1, 6, 3]
private def y2f : Fin 7 → Fin 7 := ![0, 4, 1, 5, 2, 6, 3]

private theorem coe_x7 : ⇑x7 = xf := funext <| by decide
private theorem coe_y1 : ⇑y1 = y1f := funext <| by decide
private theorem coe_y2 : ⇑y2 = y2f := funext <| by decide

/-- A permutation commuting with `x` and conjugating `y₁` to `f` is determined by its value `b`
at `0`: it is `wA f b` (follow the words `0 ↦ 1 = x 0 ↦ 2 = y₁ 1 ↦ …`). -/
private def wA (f : Fin 7 → Fin 7) (b : Fin 7) : Fin 7 → Fin 7 :=
  ![b, xf b, f (xf b), xf (f (xf b)), f (f (xf b)), f (xf (f (xf b))), f (f (xf (f (xf b))))]
/-- The analogue of `wA` for `y₂`. -/
private def wB (f : Fin 7 → Fin 7) (b : Fin 7) : Fin 7 → Fin 7 :=
  ![b, xf b, f (f (xf b)), xf (f (f (xf b))), f (xf b), f (xf (f (f (xf b)))),
    f (f (xf (f (f (xf b)))))]

private abbrev Conj (y f s : Fin 7 → Fin 7) : Prop :=
  (∀ i, s (xf i) = xf (s i)) ∧ ∀ i, s (y i) = f (s i)

private theorem conj_of_perm {ρ f y : Perm (Fin 7)} (hx : ρ * x7 = x7 * ρ) (hy : ρ * y = f * ρ) :
    Conj ⇑y ⇑f ⇑ρ := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · have := congrArg (fun p : Perm (Fin 7) => p i) hx
    simpa [Perm.mul_apply, coe_x7] using this
  · have := congrArg (fun p : Perm (Fin 7) => p i) hy
    simpa [Perm.mul_apply] using this

private theorem eq_wA {f s : Fin 7 → Fin 7} (h : Conj y1f f s) : s = wA f (s 0) := by
  obtain ⟨hx, hy⟩ := h
  have h1 : s 1 = xf (s 0) := hx 0
  have h2 : s 2 = f (s 1) := hy 1
  have h3 : s 3 = xf (s 2) := hx 2
  have h4 : s 4 = f (s 2) := hy 2
  have h5 : s 5 = f (s 3) := hy 3
  have h6 : s 6 = f (s 5) := hy 5
  funext i; fin_cases i
  · rfl
  · exact h1
  · exact h2.trans (by rw [h1]; rfl)
  · exact h3.trans (by rw [h2, h1]; rfl)
  · exact h4.trans (by rw [h2, h1]; rfl)
  · exact h5.trans (by rw [h3, h2, h1]; rfl)
  · exact h6.trans (by rw [h5, h3, h2, h1]; rfl)

private theorem eq_wB {f s : Fin 7 → Fin 7} (h : Conj y2f f s) : s = wB f (s 0) := by
  obtain ⟨hx, hy⟩ := h
  have h1 : s 1 = xf (s 0) := hx 0
  have h4 : s 4 = f (s 1) := hy 1
  have h2 : s 2 = f (s 4) := hy 4
  have h3 : s 3 = xf (s 2) := hx 2
  have h5 : s 5 = f (s 3) := hy 3
  have h6 : s 6 = f (s 5) := hy 5
  funext i; fin_cases i
  · rfl
  · exact h1
  · exact h2.trans (by rw [h4, h1]; rfl)
  · exact h3.trans (by rw [h2, h4, h1]; rfl)
  · exact h4.trans (by rw [h1]; rfl)
  · exact h5.trans (by rw [h3, h2, h4, h1]; rfl)
  · exact h6.trans (by rw [h5, h3, h2, h4, h1]; rfl)

/-- The only centralizer candidate fixing `y₁` is the identity (`7` cases). -/
private theorem stab_y1 : ∀ b : Fin 7, Conj y1f y1f (wA y1f b) → ∀ i, wA y1f b i = i := by
  decide +kernel
/-- The only centralizer candidate fixing `y₂` is the identity (`7` cases). -/
private theorem stab_y2 : ∀ b : Fin 7, Conj y2f y2f (wB y2f b) → ∀ i, wB y2f b i = i := by
  decide +kernel
/-- No centralizer candidate conjugates `y₁` to `y₂` (`7` cases). -/
private theorem not_conj_y1_y2 : ∀ b : Fin 7, ¬ Conj y1f y2f (wA y2f b) := by decide +kernel

private theorem conj_tail {σ τ y y' : Perm (Fin 7)} (h : σ * y * σ⁻¹ = τ * y' * τ⁻¹) :
    τ⁻¹ * σ * y = y' * (τ⁻¹ * σ) := by
  calc τ⁻¹ * σ * y = τ⁻¹ * (σ * y * σ⁻¹) * σ := by group
    _ = τ⁻¹ * (τ * y' * τ⁻¹) * σ := by rw [h]
    _ = y' * (τ⁻¹ * σ) := by group

private theorem comm_tail {σ τ : Perm (Fin 7)} (hσ : σ * x7 = x7 * σ) (hτ : τ * x7 = x7 * τ) :
    τ⁻¹ * σ * x7 = x7 * (τ⁻¹ * σ) :=
  ((Commute.inv_left hτ).mul_left hσ : Commute (τ⁻¹ * σ) x7)

private theorem fixFree_of_seven {g : Perm (Fin 7)} (h : g.cycleType = {7}) (i : Fin 7) :
    g i ≠ i := by
  have hs : g.support = univ :=
    Finset.eq_univ_of_card _ (by rw [← Perm.sum_cycleType, h]; rfl)
  exact Perm.mem_support.1 (hs ▸ Finset.mem_univ i)

private theorem card_C : (univ.filter fun σ : Perm (Fin 7) => σ * x7 = x7 * σ).card = 48 := by
  classical
  have : (univ.filter fun σ : Perm (Fin 7) => σ * x7 = x7 * σ) =
      univ.filter fun σ => σ ∈ Subgroup.centralizer {x7} := by
    ext σ; simp [Subgroup.mem_centralizer_singleton_iff]
  rw [this, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Perm.nat_card_centralizer,
    cycleType_x7]
  simp; decide

/-! ### A recursor-level search over partial assignments -/

private def memB (a : ℕ) (l : List ℕ) : Bool :=
  List.rec false (fun b _ ih => Nat.beq a b || ih) l

private def nthB (l : List ℕ) : ℕ → ℕ :=
  List.rec (fun _ => 0) (fun b _ ih n => Nat.rec b (fun m _ => ih m) n) l

private def lenB (l : List ℕ) : ℕ := List.rec 0 (fun _ _ ih => Nat.succ ih) l

private def xs : List ℕ := [1, 0, 3, 2, 4, 5, 6]

/-- May the reversed partial assignment `r = [y (k-1), …, y 0]` be extended by `y k = a`?
Requires `a ≠ x k` (no fixed point of `x y`), `a ∉ r` (injectivity), the `3`-cycle condition
`y³ = 1` on the newly closed chain `k ↦ a ↦ y a ↦ k`, and not both `y 0 = 0` and `y 1 = 1`
(at most one fixed point).  Written with recursors and `Nat.beq`/`Nat.blt` only, so that the
kernel evaluates it with few reduction steps. -/
private def okR (r : List ℕ) (a : ℕ) : Bool :=
  !(Nat.beq a (nthB xs (lenB r))) && !(memB a r) &&
    (match Nat.blt a (lenB r) with
     | false => !(Nat.beq (lenB r) 1 && Nat.beq (nthB r 0) 0 && Nat.beq a 1)
     | true => !(Nat.beq (nthB r (lenB r - 1 - a)) (lenB r)) &&
        (!(Nat.blt (nthB r (lenB r - 1 - a)) (lenB r)) ||
          Nat.beq (nthB r (lenB r - 1 - nthB r (lenB r - 1 - a))) (lenB r)))

private def listEqB (l : List ℕ) : List ℕ → Bool :=
  List.rec (fun m => List.rec true (fun _ _ _ => false) m)
    (fun b _ ih m => List.rec false (fun c m' _ => Nat.beq b c && ih m') m) l

private def anyEq (r : List ℕ) (E : List (List ℕ)) : Bool :=
  List.rec false (fun e _ ih => listEqB e r || ih) E

/-- An explicit list of `96` reversed tuples; it is only used as an upper bound (`ER_length`). -/
private def ER : List (List ℕ) :=
  [[3, 6, 1, 5, 4, 2, 0], [5, 3, 1, 6, 4, 2, 0], [3, 1, 6, 4, 5, 2, 0], [4, 1, 3, 6, 5, 2, 0],
   [1, 3, 5, 4, 6, 2, 0], [1, 4, 3, 5, 6, 2, 0], [2, 1, 6, 5, 4, 3, 0], [1, 2, 5, 6, 4, 3, 0],
   [2, 6, 1, 4, 5, 3, 0], [1, 4, 2, 6, 5, 3, 0], [5, 2, 1, 4, 6, 3, 0], [4, 1, 2, 5, 6, 3, 0],
   [3, 6, 2, 5, 1, 4, 0], [5, 3, 2, 6, 1, 4, 0], [2, 6, 3, 1, 5, 4, 0], [5, 2, 3, 1, 6, 4, 0],
   [3, 2, 6, 4, 1, 5, 0], [4, 2, 3, 6, 1, 5, 0], [2, 3, 6, 1, 4, 5, 0], [4, 3, 2, 1, 6, 5, 0],
   [2, 3, 5, 4, 1, 6, 0], [2, 4, 3, 5, 1, 6, 0], [3, 2, 5, 1, 4, 6, 0], [3, 4, 2, 1, 5, 6, 0],
   [3, 6, 0, 5, 4, 1, 2], [5, 3, 0, 6, 4, 1, 2], [3, 0, 6, 4, 5, 1, 2], [4, 0, 3, 6, 5, 1, 2],
   [0, 3, 5, 4, 6, 1, 2], [0, 4, 3, 5, 6, 1, 2], [1, 0, 6, 3, 5, 4, 2], [0, 1, 5, 3, 6, 4, 2],
   [1, 6, 0, 3, 4, 5, 2], [0, 4, 1, 3, 6, 5, 2], [5, 1, 0, 3, 4, 6, 2], [4, 0, 1, 3, 5, 6, 2],
   [2, 0, 6, 5, 4, 1, 3], [0, 2, 5, 6, 4, 1, 3], [2, 6, 0, 4, 5, 1, 3], [0, 4, 2, 6, 5, 1, 3],
   [5, 2, 0, 4, 6, 1, 3], [4, 0, 2, 5, 6, 1, 3], [1, 0, 6, 5, 2, 4, 3], [0, 1, 5, 6, 2, 4, 3],
   [1, 6, 0, 4, 2, 5, 3], [0, 4, 1, 6, 2, 5, 3], [5, 1, 0, 4, 2, 6, 3], [4, 0, 1, 5, 2, 6, 3],
   [3, 6, 2, 5, 0, 1, 4], [5, 3, 2, 6, 0, 1, 4], [2, 6, 3, 0, 5, 1, 4], [5, 2, 3, 0, 6, 1, 4],
   [0, 1, 6, 3, 5, 2, 4], [1, 0, 5, 3, 6, 2, 4], [0, 1, 6, 5, 2, 3, 4], [1, 0, 5, 6, 2, 3, 4],
   [1, 6, 2, 3, 0, 5, 4], [0, 2, 6, 3, 1, 5, 4], [1, 6, 3, 0, 2, 5, 4], [0, 3, 6, 1, 2, 5, 4],
   [5, 1, 2, 3, 0, 6, 4], [2, 0, 5, 3, 1, 6, 4], [5, 1, 3, 0, 2, 6, 4], [3, 0, 5, 1, 2, 6, 4],
   [3, 2, 6, 4, 0, 1, 5], [4, 2, 3, 6, 0, 1, 5], [2, 3, 6, 0, 4, 1, 5], [4, 3, 2, 0, 6, 1, 5],
   [0, 6, 1, 3, 4, 2, 5], [1, 4, 0, 3, 6, 2, 5], [0, 6, 1, 4, 2, 3, 5], [1, 4, 0, 6, 2, 3, 5],
   [1, 2, 6, 3, 0, 4, 5], [0, 6, 2, 3, 1, 4, 5], [1, 3, 6, 0, 2, 4, 5], [0, 6, 3, 1, 2, 4, 5],
   [4, 2, 1, 3, 0, 6, 5], [2, 4, 0, 3, 1, 6, 5], [4, 3, 1, 0, 2, 6, 5], [3, 4, 0, 1, 2, 6, 5],
   [2, 3, 5, 4, 0, 1, 6], [2, 4, 3, 5, 0, 1, 6], [3, 2, 5, 0, 4, 1, 6], [3, 4, 2, 0, 5, 1, 6],
   [5, 0, 1, 3, 4, 2, 6], [4, 1, 0, 3, 5, 2, 6], [5, 0, 1, 4, 2, 3, 6], [4, 1, 0, 5, 2, 3, 6],
   [2, 1, 5, 3, 0, 4, 6], [5, 0, 2, 3, 1, 4, 6], [3, 1, 5, 0, 2, 4, 6], [5, 0, 3, 1, 2, 4, 6],
   [2, 4, 1, 3, 0, 5, 6], [4, 2, 0, 3, 1, 5, 6], [3, 4, 1, 0, 2, 5, 6], [4, 3, 0, 1, 2, 5, 6]]

private def allCand (f : ℕ → Bool) : Bool :=
  f 0 && f 1 && f 2 && f 3 && f 4 && f 5 && f 6

/-- Depth-`n` search below the partial assignment `r`: every admissible completion lies in `ER`. -/
private def searchR (n : ℕ) : List ℕ → Bool :=
  Nat.rec (fun r => anyEq r ER) (fun _ ih r => allCand fun a => !(okR r a) || ih (a :: r)) n

/-- The only large kernel computation: about `1500` search nodes. -/
private theorem search_ok : searchR 7 [] = true := by decide +kernel

private theorem ER_length : ER.length = 96 := rfl

/-! ### Semantics of the search -/

private theorem beqF {n m : ℕ} (h : n ≠ m) : Nat.beq n m = false :=
  Bool.eq_false_iff.2 fun e => h (Nat.eq_of_beq_eq_true e)

private theorem bltF {n m : ℕ} (h : ¬ n < m) : Nat.blt n m = false :=
  Bool.eq_false_iff.2 fun e => h (by rw [Nat.blt_eq] at e; exact e)

private theorem bltT {n m : ℕ} (h : n < m) : Nat.blt n m = true := by rw [Nat.blt_eq]; exact h

private theorem lenB_eq (l : List ℕ) : lenB l = l.length := by
  induction l with
  | nil => rfl
  | cons b l ih => exact congrArg Nat.succ ih

private theorem memB_false {a : ℕ} {l : List ℕ} (h : a ∉ l) : memB a l = false := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hab : a ≠ b := fun e => h (e ▸ List.mem_cons_self)
    have hl : a ∉ l := fun e => h (List.mem_cons_of_mem _ e)
    change (Nat.beq a b || memB a l) = false
    rw [beqF hab, ih hl]; rfl

private theorem listEqB_eq {l m : List ℕ} (h : listEqB l m = true) : l = m := by
  induction l generalizing m with
  | nil => cases m with
    | nil => rfl
    | cons c m => exact absurd h (by simp [listEqB])
  | cons b l ih => cases m with
    | nil => exact absurd h (by simp [listEqB])
    | cons c m =>
      change (Nat.beq b c && listEqB l m) = true at h
      rw [Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1, ih h.2]

private theorem mem_of_anyEq {r : List ℕ} {E : List (List ℕ)} (h : anyEq r E = true) : r ∈ E := by
  induction E with
  | nil => exact absurd h (by simp [anyEq])
  | cons e E ih =>
    change (listEqB e r || anyEq r E) = true at h
    rw [Bool.or_eq_true] at h
    rcases h with h | h
    · exact listEqB_eq h ▸ List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

private theorem allCand_spec {f : ℕ → Bool} (h : allCand f = true) {a : ℕ} (ha : a < 7) :
    f a = true := by
  simp only [allCand, Bool.and_eq_true] at h
  interval_cases a <;> simp_all

/-- `y` as a function on `ℕ`. -/
private def yN (y : Perm (Fin 7)) (i : ℕ) : ℕ := if h : i < 7 then (y ⟨i, h⟩).val else 0

private theorem yN_fin (y : Perm (Fin 7)) (i : Fin 7) : yN y i.val = (y i).val := by
  simp [yN, i.isLt]

private theorem yN_lt (y : Perm (Fin 7)) (i : ℕ) : yN y i < 7 := by
  unfold yN; split
  · exact (y _).isLt
  · omega

/-- The reversed list `[y (k-1), …, y 0]`. -/
private def rev (y : Perm (Fin 7)) : ℕ → List ℕ
  | 0 => []
  | k + 1 => yN y k :: rev y k

private theorem rev_length (y : Perm (Fin 7)) (k : ℕ) : (rev y k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rev, ih]

private theorem nthB_rev (y : Perm (Fin 7)) {k i : ℕ} (h : i < k) :
    nthB (rev y k) (k - 1 - i) = yN y i := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [show k + 1 - 1 - i = (k - 1 - i) + 1 by omega]
      exact ih h
    · rw [show i + 1 - 1 - i = 0 by omega]; rfl

private theorem mem_rev {y : Perm (Fin 7)} {k a : ℕ} (h : a ∈ rev y k) : ∃ i < k, yN y i = a := by
  induction k with
  | zero => simp [rev] at h
  | succ k ih =>
    rcases List.mem_cons.1 h with h | h
    · exact ⟨k, by omega, h.symm⟩
    · obtain ⟨i, hi, e⟩ := ih h
      exact ⟨i, by omega, e⟩

private theorem xs_spec : ∀ i : Fin 7, nthB xs i.val = (x7 i).val := by decide

private theorem okR_rev {y : Perm (Fin 7)} (h3 : ∀ i, y (y (y i)) = i) (hx : ∀ i, y i ≠ x7 i)
    (h01 : ¬ (y 0 = 0 ∧ y 1 = 1)) {k : ℕ} (hk : k < 7) : okR (rev y k) (yN y k) = true := by
  set i : Fin 7 := ⟨k, hk⟩
  have hyk : yN y k = (y i).val := yN_fin y i
  have hlen : lenB (rev y k) = k := by rw [lenB_eq, rev_length]
  have h1 : Nat.beq (yN y k) (nthB xs k) = false := by
    refine beqF fun e => hx i (Fin.ext ?_)
    rw [← hyk, e]; exact xs_spec i
  have h2 : memB (yN y k) (rev y k) = false := by
    refine memB_false fun hm => ?_
    obtain ⟨j, hj, e⟩ := mem_rev hm
    have : (⟨j, by omega⟩ : Fin 7) = i := y.injective (Fin.ext (by
      rw [← yN_fin, ← yN_fin]; exact e))
    exact absurd (congrArg Fin.val this) (by simp [i]; omega)
  unfold okR
  rw [hlen, h1, h2]
  by_cases hak : yN y k < k
  · rw [bltT hak]
    have hc : nthB (rev y k) (k - 1 - yN y k) = (y (y i)).val := by
      rw [nthB_rev y hak, hyk, yN_fin]
    rw [hc]
    have hne : (y (y i)).val ≠ k := by
      intro e
      have e' : y (y i) = i := Fin.ext e
      have : y i = i := by
        have := congrArg y e'
        rw [h3] at this
        exact this.symm
      rw [hyk, this] at hak
      exact absurd hak (lt_irrefl _)
    rw [beqF hne]
    by_cases hck : (y (y i)).val < k
    · rw [bltT hck, nthB_rev y hck, yN_fin, h3]
      simp [i, Nat.beq_refl]
    · rw [bltF hck]; rfl
  · rw [bltF hak]
    by_cases hk1 : k = 1
    · subst hk1
      have hn : nthB (rev y 1) 0 = (y 0).val := rfl
      rw [hn]
      have : ¬ ((y 0).val = 0 ∧ (y 1).val = 1) := fun ⟨a, b⟩ => h01 ⟨Fin.ext a, Fin.ext b⟩
      have hy1 : yN y 1 = (y 1).val := yN_fin y 1
      rw [hy1]
      by_cases h0 : (y 0).val = 0
      · rw [h0, beqF (fun e => this ⟨h0, e⟩)]; rfl
      · rw [beqF h0]; rfl
    · rw [beqF hk1]; rfl

private theorem search_sound {y : Perm (Fin 7)} (h3 : ∀ i, y (y (y i)) = i) (hx : ∀ i, y i ≠ x7 i)
    (h01 : ¬ (y 0 = 0 ∧ y 1 = 1)) :
    ∀ n k, n + k = 7 → searchR n (rev y k) = true → rev y 7 ∈ ER := by
  intro n
  induction n with
  | zero => intro k hk h; rw [show k = 7 by omega] at h; exact mem_of_anyEq h
  | succ n ih =>
    intro k hk h
    have hk7 : k < 7 := by omega
    change allCand (fun a => !(okR (rev y k) a) || searchR n (a :: rev y k)) = true at h
    have := allCand_spec h (yN_lt y k)
    rw [okR_rev h3 hx h01 hk7, Bool.not_true, Bool.false_or] at this
    exact ih (k + 1) (by omega) this

private theorem rev_injective {y y' : Perm (Fin 7)} (h : rev y 7 = rev y' 7) : y = y' := by
  ext i
  have := nthB_rev y i.isLt
  rw [h, nthB_rev y' i.isLt, yN_fin, yN_fin] at this
  exact this.symm

private theorem good_rev_mem {y : Perm (Fin 7)} (hy : y.cycleType = {3, 3})
    (hxy : (x7 * y).cycleType = {7}) : rev y 7 ∈ ER := by
  obtain ⟨h3, h1⟩ := (cycleType33_iff y).1 hy
  have h3' : ∀ i, y (y (y i)) = i := fun i => by
    have := congrArg (fun p : Perm (Fin 7) => p i) h3
    simpa [pow_succ, Perm.mul_apply] using this
  have hxx : ∀ i, x7 (x7 i) = i := by decide
  have hx : ∀ i, y i ≠ x7 i := fun i hi => fixFree_of_seven hxy i (by
    rw [Perm.mul_apply, hi, hxx])
  have h01 : ¬ (y 0 = 0 ∧ y 1 = 1) := by
    rintro ⟨a, b⟩
    have hsub : ({0, 1} : Finset (Fin 7)) ⊆ univ.filter fun i => y i = i := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl <;> simp [a, b]
    have := Finset.card_le_card hsub
    rw [show ({0, 1} : Finset (Fin 7)).card = 2 by decide] at this
    unfold nfix at h1
    omega
  exact search_sound h3' hx h01 7 0 rfl search_ok

private theorem card_good_le :
    (univ.filter fun y : Perm (Fin 7) => y.cycleType = {3, 3} ∧ (x7 * y).cycleType = {7}).card
      ≤ 96 := by
  calc _ ≤ ER.toFinset.card := by
        refine Finset.card_le_card_of_injOn (fun y => rev y 7) ?_ ?_
        · intro y hy
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hy
          exact List.mem_toFinset.2 (good_rev_mem hy.1 hy.2)
        · intro y _ y' _ h; exact rev_injective h
    _ ≤ ER.length := List.toFinset_card_le _
    _ = 96 := ER_length

end GoodOrbits

open GoodOrbits in
/-- **The `96` choices form two centralizer orbits of size `48`, represented by `y₁` and `y₂`.** -/
theorem good_eq_orbits :
    let C := univ.filter fun σ : Perm (Fin 7) => σ * x7 = x7 * σ
    (univ.filter fun y : Perm (Fin 7) => y.cycleType = {3, 3} ∧ (x7 * y).cycleType = {7}) =
      C.image (fun σ => σ * y1 * σ⁻¹) ∪ C.image (fun σ => σ * y2 * σ⁻¹) ∧
    (C.image (fun σ => σ * y1 * σ⁻¹)).card = 48 ∧ (C.image (fun σ => σ * y2 * σ⁻¹)).card = 48 ∧
    Disjoint (C.image (fun σ => σ * y1 * σ⁻¹)) (C.image (fun σ => σ * y2 * σ⁻¹)) := by
  intro C
  have hC : ∀ σ, σ ∈ C ↔ σ * x7 = x7 * σ := fun σ => by simp [C]
  have conj_x7 : ∀ σ y : Perm (Fin 7), σ * x7 = x7 * σ →
      x7 * (σ * y * σ⁻¹) = σ * (x7 * y) * σ⁻¹ := fun σ y h => by
    rw [show x7 * (σ * y * σ⁻¹) = x7 * σ * y * σ⁻¹ by group, ← h]; group
  have hcard1 : (C.image (fun σ => σ * y1 * σ⁻¹)).card = 48 := by
    rw [Finset.card_image_of_injOn, card_C]
    intro σ hσ τ hτ h
    have hc := conj_of_perm (comm_tail ((hC σ).1 hσ) ((hC τ).1 hτ)) (conj_tail h)
    rw [coe_y1] at hc
    have hρ := stab_y1 _ (eq_wA hc ▸ hc)
    have : τ⁻¹ * σ = 1 := by
      ext i; rw [eq_wA hc]; exact congrArg Fin.val (hρ i)
    exact (inv_mul_eq_one.1 this).symm
  have hcard2 : (C.image (fun σ => σ * y2 * σ⁻¹)).card = 48 := by
    rw [Finset.card_image_of_injOn, card_C]
    intro σ hσ τ hτ h
    have hc := conj_of_perm (comm_tail ((hC σ).1 hσ) ((hC τ).1 hτ)) (conj_tail h)
    rw [coe_y2] at hc
    have hρ := stab_y2 _ (eq_wB hc ▸ hc)
    have : τ⁻¹ * σ = 1 := by
      ext i; rw [eq_wB hc]; exact congrArg Fin.val (hρ i)
    exact (inv_mul_eq_one.1 this).symm
  have hdisj : Disjoint (C.image (fun σ => σ * y1 * σ⁻¹)) (C.image (fun σ => σ * y2 * σ⁻¹)) := by
    rw [Finset.disjoint_left]
    rintro y hy1 hy2
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hy1
    obtain ⟨τ, hτ, h⟩ := Finset.mem_image.1 hy2
    have hc := conj_of_perm (comm_tail ((hC σ).1 hσ) ((hC τ).1 hτ)) (conj_tail h.symm)
    rw [coe_y1, coe_y2] at hc
    exact not_conj_y1_y2 _ (eq_wA hc ▸ hc)
  have hsub : C.image (fun σ => σ * y1 * σ⁻¹) ∪ C.image (fun σ => σ * y2 * σ⁻¹) ⊆
      univ.filter fun y : Perm (Fin 7) => y.cycleType = {3, 3} ∧ (x7 * y).cycleType = {7} := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_union.1 hy with hy | hy <;> obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.1 hy
    · exact ⟨by rw [Perm.cycleType_conj, cycleType_y1],
        by rw [conj_x7 σ y1 ((hC σ).1 hσ), Perm.cycleType_conj, cycleType_x7y1]⟩
    · exact ⟨by rw [Perm.cycleType_conj, cycleType_y2],
        by rw [conj_x7 σ y2 ((hC σ).1 hσ), Perm.cycleType_conj, cycleType_x7y2]⟩
  refine ⟨(Finset.eq_of_subset_of_card_le hsub ?_).symm, hcard1, hcard2, hdisj⟩
  rw [Finset.card_union_of_disjoint hdisj, hcard1, hcard2]
  exact card_good_le

end Degree7
