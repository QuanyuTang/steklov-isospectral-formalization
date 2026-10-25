module

public import RequestProject.MainTheoremWeak
public import RequestProject.ConformalSpectrum
public import RequestProject.DomainDensity

/-!
# Theorem 1.1.2 with the weak Steklov problem posed on `H¹(Ω) = W^{1,2}(Ω)` of each domain

`SteklovH1.HasSobolevWeakSteklovSpectrum Ω`: `Ω` is a bounded domain with finite boundary length
such that

* `H¹(Ω)` (closure of smooth graphs) equals the weak-gradient space `W^{1,2}(Ω)`;
* the trace `H¹(Ω) → L²(∂Ω, H¹)` is compact;
* the weak Steklov eigenproblem `∫_Ω ⟨∇u, ∇v⟩ = σ ∫_{∂Ω} Tu Tv dH¹` (all `v ∈ H¹(Ω)`) has a
  nondecreasing eigenvalue sequence `σ_k → ∞`, `σ_0 = 0`, containing every weak eigenvalue, with
  the dimension of each eigenspace equal to the number of repetitions, and `σ_k` equals the `k`-th
  Steklov eigenvalue of `Ω` (`Steklov.steklovSpectrum Ω k`).

`MainTheoremDom` is `MainTheoremWeak` plus this property for every domain of the family.
-/

@[expose] public section

open Complex Metric Set Filter Topology Steklov PlaneDomain

noncomputable section

namespace SteklovH1

/-- The weak Steklov spectrum of `Ω`, posed on `H¹(Ω) = W^{1,2}(Ω)`, with multiplicities. -/
def HasSobolevWeakSteklovSpectrum (Ω : Set ℂ) : Prop :=
  ∃ D : BddDomain, D.carrier = Ω ∧ (∀ x : D.Amb, x ∈ D.H1 ↔ D.IsWeakGradientPair x) ∧
    IsCompactOperator D.trace ∧
    ∃ (e : ℕ → D.H1) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = 0 ∧ Tendsto σ atTop atTop ∧
      (∀ k, e k ≠ 0 ∧ IsWeakSteklovEigenDom D (σ k) (e k)) ∧
      (∀ τ, (∃ x : D.H1, x ≠ 0 ∧ IsWeakSteklovEigenDom D τ x) ↔ ∃ k, σ k = τ) ∧
      (∀ τ, ∃ S : Submodule ℝ D.H1, (∀ x, x ∈ S ↔ IsWeakSteklovEigenDom D τ x) ∧
        Module.finrank ℝ S = Set.ncard {k | σ k = τ}) ∧
      (∀ k, Steklov.steklovSpectrum Ω k = ENNReal.ofReal (σ k))

/-- `G(𝔻)` (with `G` holomorphic near `𝔻̄`, injective on `𝔻̄`, `G' ≠ 0` on `𝕋`) has the weak
Steklov spectrum posed on `H¹(G(𝔻)) = W^{1,2}(G(𝔻))`. -/
theorem hasSobolevWeakSteklovSpectrum_image {G : ℂ → ℂ}
    (hG : ∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ G U)
    (hinj : InjOn G (closedBall 0 1)) (hder : ∀ z ∈ sphere (0 : ℂ) 1, deriv G z ≠ 0) :
    HasSobolevWeakSteklovSpectrum (G '' ball 0 1) := by
  obtain ⟨c, rfl⟩ := ConfMap.ofHyp hG hinj hder
  exact ⟨c.dom, rfl, c.mem_H1_iff_isWeakGradientPair, c.isCompactOperator_trace,
    c.weak_spectral_theorem_dom⟩

theorem hasSobolevWeakSteklovSpectrum_of {Ω : Set ℂ} (h : HasWeakSteklovSpectrum Ω) :
    HasSobolevWeakSteklovSpectrum Ω := by
  obtain ⟨G, hG, hinj, hder, rfl, -⟩ := h
  exact hasSobolevWeakSteklovSpectrum_image hG hinj hder

end SteklovH1

/-- **Theorem 1.1.2, with the weak Steklov problem on `H¹(Ω) = W^{1,2}(Ω)` of each domain.** -/
def MainTheoremDom : Prop :=
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
    -- (v)
    (∃ F : Label → ℝ → ℂ → ℂ,
      (∀ i ε, 0 < ε → ε < ε₀ → IsNormalizedConformalMap (F i ε) (Ω i ε)) ∧
      ∀ i, TendstoIdInCInfty (F i))

theorem SteklovCoalescence.mainTheoremDom_proved : MainTheoremDom := by
  obtain ⟨ε₀, hε₀, Ω, h1, h2, h3, h3', h4, h5, h6, h7, h8⟩ := SteklovCoalescence.mainTheoremWeak_proved
  exact ⟨ε₀, hε₀, Ω, h1, h2, h3, h3', h4, h5, h6, h7,
    fun i ε h0 h1 => SteklovH1.hasSobolevWeakSteklovSpectrum_of (h7 i ε h0 h1), h8⟩

theorem mainTheoremWeak_of_mainTheoremDom (h : MainTheoremDom) : MainTheoremWeak := by
  obtain ⟨ε₀, hε₀, Ω, h1, h2, h3, h3', h4, h5, h6, h7, -, h8⟩ := h
  exact ⟨ε₀, hε₀, Ω, h1, h2, h3, h3', h4, h5, h6, h7, h8⟩
