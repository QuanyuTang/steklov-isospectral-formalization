module

public import RequestProject.TransplantTransfer
public import RequestProject.LocalBranches

/-!
# Spectral comparison from intrinsic kernel data

A version of `weightedSteklovEigenvalue_le_of_transplant` whose local-branch hypothesis is
replaced by intrinsic data: `B₁` holomorphic on an open `W₁ ⊇ 𝔻̄` and proper over a
neighbourhood of `B₂(U)`, the fibres over `B₂(U \ S)` regular, and the kernel `K` locally
constant on the fibre product `{(z', p) | B₂ z' = B₁ p}` near points over `U \ S`.  The local
holomorphic branches are constructed (`HolInv.exists_local_branches_comp`).
-/

@[expose] public section

open Complex Metric Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace SteklovTransplant

open SteklovBlaschke Steklov

/-- **Spectral comparison by transplantation, intrinsic form.** -/
theorem weightedSteklovEigenvalue_le_of_kernel {B₁ B₂ : ℂ → ℂ} {n₁ n₂ : ℕ}
    (hB₁ : IsFiniteBlaschke B₁ n₁) (hn₁ : 0 < n₁) (hB₂ : IsFiniteBlaschke B₂ n₂) (hn₂ : 0 < n₂)
    {U : Set ℂ} (hU : IsOpen U) (hcbU : closedBall (0:ℂ) 1 ⊆ U)
    (hB₂U : DifferentiableOn ℂ B₂ U)
    {W₁ : Set ℂ} (hW₁o : IsOpen W₁) (hW₁ : closedBall (0:ℂ) 1 ⊆ W₁)
    (hB₁W : DifferentiableOn ℂ B₁ W₁)
    (hin₁ : ∀ p ∈ W₁, ‖B₁ p‖ = 1 → ‖p‖ = 1) (hin₁' : ∀ p ∈ W₁, ‖B₁ p‖ < 1 → ‖p‖ < 1)
    (hfinW : ∀ w, {p | p ∈ W₁ ∧ B₁ p = w}.Finite)
    (hcard : ∃ N : ℕ, ∀ w, (hfinW w).toFinset.card ≤ N)
    {L V : Set ℂ} (hL : IsCompact L) (hLW : L ⊆ W₁) (hVo : IsOpen V) (hUV : B₂ '' U ⊆ V)
    (hprop : ∀ p ∈ W₁, B₁ p ∈ V → p ∈ L)
    (hfin₂ : ∀ w, {z : ℂ | ‖z‖ < 1 ∧ B₂ z = w}.Finite)
    (K : ℂ → ℂ → ℝ) (hKb : ∃ M, ∀ z' p, |K z' p| ≤ M)
    (S : Finset ℂ) (hS : ∀ s ∈ S, ‖s‖ < 1)
    (hcrit₁ : ∀ p, ‖p‖ < 1 → B₁ p ∉ B₂ '' ↑S → deriv B₁ p ≠ 0)
    (hreg₁ : ∀ z' ∈ U, z' ∉ S → ∀ p ∈ W₁, B₁ p = B₂ z' → deriv B₁ p ≠ 0)
    (hcrit₂ : ∀ z, ‖z‖ < 1 → B₂ z ∉ B₂ '' ↑S → deriv B₂ z ≠ 0)
    (hKloc : ∀ z' ∈ U, z' ∉ S → ∀ p ∈ W₁, B₁ p = B₂ z' →
      ∀ᶠ q in 𝓝 (z', p), B₂ q.1 = B₁ q.2 → K q.1 q.2 = K z' p)
    (horth : ∀ w, ‖w‖ < 1 → w ∉ B₂ '' ↑S → ∀ p p', ‖p‖ < 1 → B₁ p = w → ‖p'‖ < 1 →
      B₁ p' = w →
      ∑ᶠ z' ∈ {z' : ℂ | ‖z'‖ < 1 ∧ B₂ z' = w}, K z' p * K z' p' = if p = p' then 1 else 0)
    (horthT : ∀ w, ‖w‖ = 1 → ∀ p p', ‖p‖ = 1 → B₁ p = w → ‖p'‖ = 1 → B₁ p' = w →
      ∑ᶠ z' ∈ {z' : ℂ | ‖z'‖ = 1 ∧ B₂ z' = w}, K z' p * K z' p' = if p = p' then 1 else 0)
    (k : ℕ) :
    weightedSteklovEigenvalue (fun z => ‖deriv B₂ z‖) k ≤
      weightedSteklovEigenvalue (fun z => ‖deriv B₁ z‖) k := by
  refine weightedSteklovEigenvalue_le_of_transplant hB₁ hn₁ hB₂ hn₂ hU hcbU hB₂U hW₁ hin₁ hin₁'
    hfinW hfin₂ K hKb hcard S hS hcrit₁ hcrit₂ horth horthT ?_ k
  intro z' hz'U hz'S
  refine HolInv.exists_local_branches_comp hW₁o hB₁W
    (hB₂U.continuousOn.continuousAt (hU.mem_nhds hz'U)) (hfinW _)
    (fun p hp => hreg₁ z' hz'U hz'S p hp.1 hp.2) hL hLW ?_ K
    (fun p hp => hKloc z' hz'U hz'S p hp.1 hp.2)
  filter_upwards [hVo.mem_nhds (hUV ⟨z', hz'U, rfl⟩)] with w hw p hp hpw
  exact hprop p hp (hpw ▸ hw)

end SteklovTransplant

end
