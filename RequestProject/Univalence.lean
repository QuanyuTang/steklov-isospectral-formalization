module

public import Mathlib

/-!
# Univalence criterion (the injectivity step of Proposition 2.3.1)

If `F` is complex differentiable at every point of a convex set `S ⊆ ℂ` and
`Re F' > 0` on `S`, then `F` is injective on `S`.  This is the argument of the paper:
`(F(z₂) - F(z₁))/(z₂ - z₁) = ∫₀¹ F'(z₁ + s(z₂ - z₁)) ds` has positive real part.
We prove it by showing that `s ↦ Re (F(z₁ + s(z₂ - z₁))/(z₂ - z₁))` is strictly increasing
on `[0, 1]`.

In the paper this is applied with `S = 𝔻̄` and `F = F_ρ = ∫₀^z O_ρ`, where `Re O_ρ > 0` on `𝔻̄`.
-/

@[expose] public section

open Set

namespace SteklovAnalytic

/-- **Univalence criterion.** A function holomorphic at each point of a convex set `S ⊆ ℂ`
whose derivative has positive real part on `S` is injective on `S`. -/
theorem injOn_of_re_deriv_pos {F : ℂ → ℂ} {S : Set ℂ} (hS : Convex ℝ S)
    (hF : ∀ z ∈ S, DifferentiableAt ℂ F z) (hre : ∀ z ∈ S, 0 < (deriv F z).re) :
    InjOn F S := by
  intro z₁ h₁ z₂ h₂ heq
  by_contra hne
  have hw : z₂ - z₁ ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
  set w := z₂ - z₁ with hw_def
  -- points of the segment
  have hseg : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → z₁ + (t : ℂ) * w ∈ S := by
    intro t ht
    have := hS.add_smul_sub_mem h₁ h₂ ht
    simpa [hw_def, Complex.real_smul] using this
  let e : ℂ → ℂ := fun u => F (z₁ + u * w) / w
  let g : ℝ → ℝ := fun t => (e t).re
  have hderiv : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 →
      HasDerivAt g (deriv F (z₁ + (t : ℂ) * w)).re t := by
    intro t ht
    have hF' := (hF _ (hseg t ht)).hasDerivAt
    have hlin : HasDerivAt (fun u : ℂ => z₁ + u * w) w (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).mul_const w).const_add z₁
    have hcomp : HasDerivAt (fun u : ℂ => F (z₁ + u * w))
        (deriv F (z₁ + (t : ℂ) * w) * w) (t : ℂ) := hF'.comp (t : ℂ) hlin
    have he : HasDerivAt e (deriv F (z₁ + (t : ℂ) * w)) (t : ℂ) := by
      have := hcomp.div_const w
      simpa [e, mul_div_assoc, div_self hw] using this
    exact he.real_of_complex
  have hmono : StrictMonoOn g (Icc 0 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc 0 1) ?_ ?_
    · intro t ht
      exact (hderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hderiv t (Ioo_subset_Icc_self ht)).deriv]
      exact hre _ (hseg t (Ioo_subset_Icc_self ht))
  have hlt := hmono (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_lt_one
  have h0 : g 0 = (F z₁ / w).re := by simp [g, e]
  have h1 : g 1 = (F z₂ / w).re := by simp [g, e, hw_def]
  rw [h0, h1, heq] at hlt
  exact lt_irrefl _ hlt

end SteklovAnalytic
