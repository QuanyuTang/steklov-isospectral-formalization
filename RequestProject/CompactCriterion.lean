module

public import Mathlib

/-!
# A compactness criterion for operators

If for every `ε > 0` there is a finite-dimensional subspace `F` such that `T x` lies within `ε`
of `F` for every `x` in the closed unit ball, then `T` is a compact operator.
-/

@[expose] public section

open Filter Topology Set Metric

noncomputable section

namespace SteklovH1

theorem isCompactOperator_of_approx {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] (T : X →L[ℝ] Y)
    (h : ∀ ε > 0, ∃ F : Submodule ℝ Y, FiniteDimensional ℝ F ∧
      ∀ x : X, ‖x‖ ≤ 1 → ∃ y ∈ F, ‖T x - y‖ ≤ ε) :
    IsCompactOperator T := by
  have key := (isCompactOperator_iff_isCompact_closure_image_closedBall
    (T : X →ₗ[ℝ] Y) zero_lt_one).2
  refine key ?_
  refine TotallyBounded.isCompact_of_isClosed ?_ isClosed_closure
  refine TotallyBounded.closure ?_
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨F, hFd, hF⟩ := h (ε / 3) (by positivity)
  set R := ‖T‖ + ε / 3
  let K : Set Y := ((↑) : F → Y) '' closedBall (0 : F) R
  have hK : IsCompact K := (isCompact_closedBall (0 : F) R).image continuous_subtype_val
  obtain ⟨t, htK, htf, hcov⟩ := hK.finite_cover_balls (e := ε / 3) (by positivity)
  refine ⟨t, htf, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hx1 : ‖x‖ ≤ 1 := by simpa using hx
  obtain ⟨y, hyF, hy⟩ := hF x hx1
  have hyK : y ∈ K := by
    refine ⟨⟨y, hyF⟩, ?_, rfl⟩
    rw [mem_closedBall_zero_iff, Submodule.coe_norm]
    calc ‖y‖ = ‖T x - (T x - y)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖T x‖ + ‖T x - y‖ := norm_sub_le _ _
      _ ≤ ‖T‖ * ‖x‖ + ε / 3 := add_le_add (T.le_opNorm x) hy
      _ ≤ ‖T‖ + ε / 3 := by
        gcongr
        exact mul_le_of_le_one_right (norm_nonneg _) hx1
  obtain ⟨z, hzt, hz⟩ := mem_iUnion₂.1 (hcov hyK)
  refine mem_iUnion₂.2 ⟨z, hzt, ?_⟩
  rw [mem_ball] at hz ⊢
  have : dist ((T : X →ₗ[ℝ] Y) x) y ≤ ε / 3 := by
    rw [dist_eq_norm]; exact hy
  calc dist ((T : X →ₗ[ℝ] Y) x) z ≤ dist ((T : X →ₗ[ℝ] Y) x) y + dist y z := dist_triangle _ _ _
    _ < ε := by linarith

end SteklovH1
