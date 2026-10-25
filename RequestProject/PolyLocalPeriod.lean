module

public import RequestProject.LocalMonodromy

/-!
# Iterated local monodromy of a polynomial cover

For a nonconstant polynomial `P` and `w₀ ∈ ℂ`, for every sufficiently small circle about `w₀` the
`k`-th iterate of the monodromy of the circle fixes the whole fibre iff `k` is divisible by the
multiplicity of every root of `P - w₀` (`local_monodromy_iterate`).  This is derived from the
block-rotation normal form `local_monodromy`.
-/

@[expose] public section

open Polynomial Set PolyCover

noncomputable section

namespace LocalMonodromy

lemma finRotate_iterate_val {m : ℕ} (hm : 0 < m) (j : Fin m) (k : ℕ) :
    (((finRotate m)^[k] j : Fin m) : ℕ) = (j + k) % m := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt j.2]
  | succ k ih =>
    rw [Function.iterate_succ_apply', finRotate_val hm, ih, Nat.mod_add_mod, add_assoc]

lemma finRotate_iterate_eq_iff {m : ℕ} (hm : 0 < m) (j : Fin m) (k : ℕ) :
    (finRotate m)^[k] j = j ↔ m ∣ k := by
  rw [Fin.ext_iff, finRotate_iterate_val hm]
  have h1 : ((j : ℕ) + k) % m = j ↔ Nat.ModEq m (j + k) (j + 0) := by
    rw [Nat.ModEq, add_zero, Nat.mod_eq_of_lt j.2]
  rw [h1, ← Nat.modEq_zero_iff_dvd]
  exact ⟨Nat.ModEq.add_left_cancel' _, Nat.ModEq.add_left _⟩

lemma blockRotation_iterate {ι : Type*} (k : ι → ℕ) (n : ℕ) (a : ι) (j : Fin (k a)) :
    (blockRotation k)^[n] ⟨a, j⟩ = ⟨a, (finRotate (k a))^[n] j⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    rfl

/-- **Iterated local monodromy.**  For all sufficiently small circles about `w₀`, the `k`-th
iterate of the monodromy fixes every point of the fibre iff every root multiplicity of `P - w₀`
divides `k`. -/
theorem local_monodromy_iterate {P : ℂ[X]} (hP : 0 < P.degree) (w0 : ℂ) :
    ∃ r0 > 0, ∀ r : ℝ, 0 < r → r < r0 → ∃ hcirc : ∀ t, circ w0 r t ∉ critVals P,
      ∀ k : ℕ, (∀ e, ((isCoveringMap P).monodromy
          (Path.Homotopic.Quotient.mk (circleLoop w0 r hcirc)))^[k] e = e) ↔
        ∀ a ∈ (P - C w0).roots.toFinset, (P - C w0).rootMultiplicity a ∣ k := by
  obtain ⟨r0, hr0, H⟩ := local_monodromy hP w0
  refine ⟨r0, hr0, fun r hr hrr => ?_⟩
  obtain ⟨hcirc, E, hE⟩ := H r hr hrr
  refine ⟨hcirc, fun k => ?_⟩
  set M := (isCoveringMap P).monodromy (Path.Homotopic.Quotient.mk (circleLoop w0 r hcirc))
  have hM : ∀ x, M (E x) = E (blockRotation _ x) := hE
  have hMk : ∀ x, M^[k] (E x) = E ((blockRotation _)^[k] x) := by
    intro x
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply', ih, hM, Function.iterate_succ_apply']
  have hQ : P - C w0 ≠ 0 := by
    intro h
    have : P = C w0 := sub_eq_zero.1 h
    rw [this] at hP; exact absurd hP (not_lt.2 degree_C_le)
  have hpos : ∀ a ∈ (P - C w0).roots.toFinset, 0 < (P - C w0).rootMultiplicity a := by
    intro a ha
    rw [Multiset.mem_toFinset, mem_roots hQ] at ha
    exact (rootMultiplicity_pos hQ).2 ha
  constructor
  · intro h a ha
    have h1 := h (E ⟨⟨a, ha⟩, ⟨0, hpos a ha⟩⟩)
    rw [hMk, E.apply_eq_iff_eq, blockRotation_iterate] at h1
    have h2 : (finRotate _)^[k] (⟨0, hpos a ha⟩ : Fin ((P - C w0).rootMultiplicity a)) =
        ⟨0, hpos a ha⟩ := by
      exact eq_of_heq (Sigma.mk.inj_iff.1 h1).2
    exact (finRotate_iterate_eq_iff (hpos a ha) _ k).1 h2
  · intro h e
    obtain ⟨⟨a, j⟩, rfl⟩ := E.surjective e
    rw [hMk, blockRotation_iterate, (finRotate_iterate_eq_iff (hpos a a.2) j k).2 (h a a.2)]

end LocalMonodromy
