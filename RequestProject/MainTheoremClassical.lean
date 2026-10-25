module

public import RequestProject.MainTheoremDom
public import RequestProject.ClassicalSteklovDom

/-!
# Theorem 1.1.2 with the classical Steklov problem on each domain

`SteklovH1.HasClassicalSteklovSpectrum Ω`: `Ω = G(𝔻)` for conformal data `c` (`G` holomorphic
and injective on an open `U ⊇ 𝔻̄`, `G' ≠ 0` on `U`) and the **classical** Steklov eigenproblem

  `Δv = 0` in `Ω`,  `∂_ν v = σ v` at every boundary point `G(e^{iθ})` (outward unit normal `ν`),

for smooth `v`, with eigenfunctions identified with their restrictions to `Ω` (equivalently with
their `H¹(Ω)` classes, `SteklovH1.BddDomain.embedH_eq_iff`), has a nondecreasing eigenvalue
sequence `σ_k → ∞`, `σ_0 = 0`, containing every classical eigenvalue, with eigenspace dimensions
equal to the multiplicities, and `σ_k = Steklov.steklovSpectrum Ω k`.

`MainTheoremClassical` is `MainTheoremDom` plus this property for every domain of the family.
-/

@[expose] public section

open Complex Metric Set Filter Topology Steklov PlaneDomain

noncomputable section

namespace SteklovH1

/-- The classical Steklov spectrum of `Ω = G(𝔻)`, with multiplicities, equals its Steklov
spectrum. -/
def HasClassicalSteklovSpectrum (Ω : Set ℂ) : Prop :=
  ∃ c : ConfMap, c.Ω = Ω ∧
    ∃ (e : ℕ → c.dom.H1) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = 0 ∧ Tendsto σ atTop atTop ∧
      (∀ k, e k ≠ 0 ∧ c.IsClassicalEigenClass (σ k) (e k)) ∧
      (∀ τ, (∃ x : c.dom.H1, x ≠ 0 ∧ c.IsClassicalEigenClass τ x) ↔ ∃ k, σ k = τ) ∧
      (∀ τ, ∃ S : Submodule ℝ c.dom.H1, (∀ x, x ∈ S ↔ c.IsClassicalEigenClass τ x) ∧
        Module.finrank ℝ S = Set.ncard {k | σ k = τ}) ∧
      (∀ k, Steklov.steklovSpectrum Ω k = ENNReal.ofReal (σ k))

theorem hasClassicalSteklovSpectrum_image {G : ℂ → ℂ}
    (hG : ∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ G U)
    (hinj : InjOn G (closedBall 0 1)) (hder : ∀ z ∈ sphere (0 : ℂ) 1, deriv G z ≠ 0) :
    HasClassicalSteklovSpectrum (G '' ball 0 1) := by
  obtain ⟨c, rfl⟩ := ConfMap.ofHyp hG hinj hder
  exact ⟨c, rfl, c.classical_spectral_theorem_dom⟩

theorem hasClassicalSteklovSpectrum_of {Ω : Set ℂ} (h : HasWeakSteklovSpectrum Ω) :
    HasClassicalSteklovSpectrum Ω := by
  obtain ⟨G, hG, hinj, hder, rfl, -⟩ := h
  exact hasClassicalSteklovSpectrum_image hG hinj hder

end SteklovH1

/-- **Theorem 1.1.2, with the weak problem on `H¹(Ω) = W^{1,2}(Ω)` and the classical Steklov
problem on each domain.** -/
def MainTheoremClassical : Prop :=
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
    -- (ii-H¹)
    (∀ ε, 0 < ε → ε < ε₀ →
      SteklovH1.h1SteklovSpectrum (Ω Label.P ε) = SteklovH1.h1SteklovSpectrum (Ω Label.L ε)) ∧
    (∀ i ε, 0 < ε → ε < ε₀ → steklovSpectrum (Ω i ε) = SteklovH1.h1SteklovSpectrum (Ω i ε)) ∧
    -- weak spectrum of the pulled-back problem on `H¹(𝔻)`
    (∀ i ε, 0 < ε → ε < ε₀ → SteklovH1.HasWeakSteklovSpectrum (Ω i ε)) ∧
    -- weak spectrum posed on `H¹(Ω) = W^{1,2}(Ω)` of the domain itself
    (∀ i ε, 0 < ε → ε < ε₀ → SteklovH1.HasSobolevWeakSteklovSpectrum (Ω i ε)) ∧
    -- classical spectrum (harmonic, `∂_ν v = σ v` pointwise on the boundary)
    (∀ i ε, 0 < ε → ε < ε₀ → SteklovH1.HasClassicalSteklovSpectrum (Ω i ε)) ∧
    -- (v)
    (∃ F : Label → ℝ → ℂ → ℂ,
      (∀ i ε, 0 < ε → ε < ε₀ → IsNormalizedConformalMap (F i ε) (Ω i ε)) ∧
      ∀ i, TendstoIdInCInfty (F i))

theorem SteklovCoalescence.mainTheoremClassical_proved : MainTheoremClassical := by
  obtain ⟨ε₀, hε₀, Ω, h1, h2, h3, h3', h4, h5, h6, h7, h8⟩ :=
    SteklovCoalescence.mainTheoremWeak_proved
  exact ⟨ε₀, hε₀, Ω, h1, h2, h3, h3', h4, h5, h6, h7,
    fun i ε h0 h1 => SteklovH1.hasSobolevWeakSteklovSpectrum_of (h7 i ε h0 h1),
    fun i ε h0 h1 => SteklovH1.hasClassicalSteklovSpectrum_of (h7 i ε h0 h1), h8⟩

theorem mainTheoremDom_of_mainTheoremClassical (h : MainTheoremClassical) : MainTheoremDom := by
  obtain ⟨ε₀, hε₀, Ω, h1, h2, h3, h3', h4, h5, h6, h7, h7', -, h8⟩ := h
  exact ⟨ε₀, hε₀, Ω, h1, h2, h3, h3', h4, h5, h6, h7, h7', h8⟩
