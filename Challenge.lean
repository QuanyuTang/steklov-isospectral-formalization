module

public import Mathlib

/-!
# Strictly convex Steklov-isospectral plane domains

Statement surface for Theorem 1.1.2 of Hu--Shi--Tang, arXiv:2608.10557v2.
All five conclusions are stated below with the original simultaneous quantifiers.
The spectrum is the full variational Steklov sequence, with multiplicities;
the proof development additionally identifies it with the weak and classical PDE spectra.

This file imports only Mathlib. The definitions are copied verbatim from the
verified development so the statement can be read independently of its proof.
The single deliberate `sorry` at the end belongs to this statement surface only.
Solution.lean supplies the actual proof without importing this module.

Proof scope: explicit degree-seven polynomial realization and verified monodromy.
The general Riemann existence theorem for arbitrary permutation data is not claimed.
The internal orbifold development uses proved concrete disk-coordinate models.
Exact verification evidence and any remaining checks are recorded in PALOMAR_STATUS.md
and docs/PALOMAR.md; this statement file does not assert registry acceptance.
-/

@[expose] public section


open MeasureTheory Set Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Steklov

/-- The Dirichlet energy `∫_Ω |∇u|²` of a real function on the plane, over `Ω ⊆ ℂ ≅ ℝ²`. -/
def dirichletEnergy (Ω : Set ℂ) (u : ℂ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in Ω, ‖fderiv ℝ u z‖ₑ ^ 2

/-- The boundary `L²` mass `∫_{∂Ω} |u|² ds`, where `ds` is arc length, i.e. one-dimensional
Hausdorff measure restricted to the topological boundary `frontier Ω`. -/
def boundaryMass (Ω : Set ℂ) (u : ℂ → ℝ) : ℝ≥0∞ :=
  ∫⁻ z in frontier Ω, ‖u z‖ₑ ^ 2 ∂(Measure.hausdorffMeasure 1)

/-- Admissible test spaces for `σ_k`: `(k+1)`-dimensional spaces of smooth (`C^∞`) functions on
the plane on which the boundary mass is positive definite.

(Correction made in the second run: the smoothness order is `∞ = ((⊤ : ℕ∞) : WithTop ℕ∞)`, i.e.
`C^∞`.  The first version wrote `ContDiff ℝ ⊤ u`, which in current Mathlib means `ContDiff ℝ ω u`,
real-analyticity on the whole plane — not the intended class of smooth test functions.) -/
def AdmissibleSpace (B : (ℂ → ℝ) → ℝ≥0∞) (k : ℕ) (V : Submodule ℝ (ℂ → ℝ)) : Prop :=
  (∀ u ∈ V, ContDiff ℝ ∞ u) ∧ Module.finrank ℝ V = k + 1 ∧ ∀ u ∈ V, u ≠ 0 → B u ≠ 0

/-- Generic min–max value `inf_{V} sup_{u ∈ V \ 0} E(u)/B(u)` over admissible `(k+1)`-spaces. -/
def minMax (E B : (ℂ → ℝ) → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule ℝ (ℂ → ℝ)) (_ : AdmissibleSpace B k V),
    ⨆ (u : ℂ → ℝ) (_ : u ∈ V) (_ : u ≠ 0), E u / B u

/-- The `k`-th Steklov eigenvalue `σ_k(Ω)` (counted with multiplicity, `σ_0 = 0`), defined by
the Courant–Fischer min–max principle for the Rayleigh quotient
`∫_Ω |∇u|² / ∫_{∂Ω} u² ds`. -/
def steklovEigenvalue (Ω : Set ℂ) (k : ℕ) : ℝ≥0∞ :=
  minMax (dirichletEnergy Ω) (boundaryMass Ω) k

/-- The Steklov spectrum `Spec_St(Ω)` as the nondecreasing sequence of eigenvalues repeated
according to multiplicity.  Two domains have identical Steklov spectra including multiplicities
iff these sequences are equal. -/
def steklovSpectrum (Ω : Set ℂ) : ℕ → ℝ≥0∞ := steklovEigenvalue Ω

/-- Boundary mass for the weighted Steklov problem on the unit disk:
`∫_0^{2π} |u(e^{it})|² ρ(e^{it}) dt`. -/
def weightedBoundaryMass (ρ : ℂ → ℝ) (u : ℂ → ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 (2 * Real.pi),
    ‖u (Complex.exp (t * Complex.I))‖ₑ ^ 2 * ENNReal.ofReal (ρ (Complex.exp (t * Complex.I)))

/-- The `k`-th eigenvalue of the weighted Steklov problem `Spec_St(𝔻, ρ)`
(`Δu = 0` in `𝔻`, `∂_ν u = σ ρ u` on `𝕋`), defined variationally. -/
def weightedSteklovEigenvalue (ρ : ℂ → ℝ) (k : ℕ) : ℝ≥0∞ :=
  minMax (dirichletEnergy (Metric.ball 0 1)) (weightedBoundaryMass ρ) k

/-- The weighted Steklov spectrum `Spec_St(𝔻, ρ)` (with multiplicities). -/
def weightedSteklovSpectrum (ρ : ℂ → ℝ) : ℕ → ℝ≥0∞ := weightedSteklovEigenvalue ρ

end Steklov

namespace PlaneDomain

/-- A (plane) domain: a nonempty connected open subset of `ℂ ≅ ℝ²`. -/
def IsDomain (Ω : Set ℂ) : Prop := IsOpen Ω ∧ IsConnected Ω

/-- The boundary of `Ω` is a real-analytic Jordan curve: it is the image of a `2π`-periodic,
real-analytic, regular (nonvanishing derivative) curve that is injective on one period. -/
def IsRealAnalyticJordanBoundary (Ω : Set ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, AnalyticOnNhd ℝ γ univ ∧ Function.Periodic γ (2 * Real.pi) ∧
    InjOn γ (Ico 0 (2 * Real.pi)) ∧ (∀ t, deriv γ t ≠ 0) ∧ range γ = frontier Ω

/-- Strict convexity of a domain: its closure is strictly convex (any open chord of the closure
lies in the interior).  Note: for an *open* set, `StrictConvex ℝ Ω` would merely be convexity, so
the closure is used. -/
def IsStrictlyConvexDomain (Ω : Set ℂ) : Prop := StrictConvex ℝ (closure Ω)

/-- Congruence: equivalence under a Euclidean rigid motion (any isometry of the plane;
orientation-reversing ones included, which makes noncongruence the *stronger* statement). -/
def Congruent (Ω₁ Ω₂ : Set ℂ) : Prop := ∃ J : ℂ ≃ᵢ ℂ, J '' Ω₁ = Ω₂

/-- `Ω` admits an orientation-reversing Euclidean symmetry `z ↦ a z̄ + b`, `|a| = 1`. -/
def HasOrientationReversingSymmetry (Ω : Set ℂ) : Prop :=
  ∃ a b : ℂ, ‖a‖ = 1 ∧ (fun z => a * (starRingEnd ℂ) z + b) '' Ω = Ω

/-- Length of the boundary: one-dimensional Hausdorff measure of `∂Ω`. -/
def boundaryLength (Ω : Set ℂ) : ℝ≥0∞ := Measure.hausdorffMeasure 1 (frontier Ω)

/-- `F` is a conformal map `𝔻 → Ω` with `F(0) = 0`, `F'(0) > 0`, extending holomorphically to
a neighbourhood of the closed unit disk. -/
def IsNormalizedConformalMap (F : ℂ → ℂ) (Ω : Set ℂ) : Prop :=
  (∃ U : Set ℂ, IsOpen U ∧ Metric.closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ F U) ∧
  InjOn F (Metric.ball 0 1) ∧ F '' Metric.ball 0 1 = Ω ∧
  F 0 = 0 ∧ 0 < (deriv F 0).re ∧ (deriv F 0).im = 0

/-- `F ε → id` in `C^∞(𝔻̄)` as `ε → 0⁺`: for every order `k`, the `k`-th (real) derivative of
`F ε - id` tends to zero uniformly on the closed unit disk.  (The operator norm of the `k`-th
derivative is equivalent to the max of the partial derivatives of order `k` used in the paper, so
this is the same notion of convergence.) -/
def TendstoIdInCInfty (F : ℝ → ℂ → ℂ) : Prop :=
  ∀ k : ℕ, ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
    ‖iteratedFDeriv ℝ k (fun w => F ε w - w) z‖ < η

end PlaneDomain

set_option backward.isDefEq.respectTransparency false in
/-- The two labels `P` (points) and `L` (lines) of the family in Theorem 1.1.2. -/
inductive Label | P | L
  deriving DecidableEq, Fintype, Repr




open Set PlaneDomain Steklov

/-- **Theorem 1.1.2.** There exist `ε₀ > 0` and a family `Ω i ε` (`i ∈ {P, L}`, `0 < ε < ε₀`)
of plane domains such that
(i) each is bounded, simply connected, strictly convex, with real-analytic Jordan boundary;
(ii) `Spec_St(Ω P ε) = Spec_St(Ω L ε)` including multiplicities;
(iii) distinct labels/parameters give noncongruent domains, and no domain has an
     orientation-reversing Euclidean symmetry;
(iv) each boundary has length `2π`;
(v) there are normalized conformal maps `F i ε : 𝔻 → Ω i ε`, holomorphic near `𝔻̄`, with
    `F i ε → id` in `C^∞(𝔻̄)` as `ε → 0`. -/
def MainTheorem : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Ω : Label → ℝ → Set ℂ,
    -- (i)
    (∀ i ε, 0 < ε → ε < ε₀ →
      IsDomain (Ω i ε) ∧ Bornology.IsBounded (Ω i ε) ∧ SimplyConnectedSpace (Ω i ε) ∧
      IsStrictlyConvexDomain (Ω i ε) ∧ IsRealAnalyticJordanBoundary (Ω i ε)) ∧
    -- (ii)
    (∀ ε, 0 < ε → ε < ε₀ → steklovSpectrum (Ω Label.P ε) = steklovSpectrum (Ω Label.L ε)) ∧
    -- (iii)
    (∀ i j ε ε', 0 < ε → ε < ε₀ → 0 < ε' → ε' < ε₀ → (i, ε) ≠ (j, ε') →
      ¬ Congruent (Ω i ε) (Ω j ε')) ∧
    (∀ i ε, 0 < ε → ε < ε₀ → ¬ HasOrientationReversingSymmetry (Ω i ε)) ∧
    -- (iv)
    (∀ i ε, 0 < ε → ε < ε₀ → boundaryLength (Ω i ε) = ENNReal.ofReal (2 * Real.pi)) ∧
    -- (v)
    (∃ F : Label → ℝ → ℂ → ℂ,
      (∀ i ε, 0 < ε → ε < ε₀ → IsNormalizedConformalMap (F i ε) (Ω i ε)) ∧
      ∀ i, TendstoIdInCInfty (F i))


/-- All five conclusions of the paper's main theorem, with no extra hypotheses. -/
theorem SteklovSubmission.main_result : MainTheorem := by
  sorry

end
