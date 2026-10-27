module

public import RequestProject.Defs

/-!
# Precise statements of the analytic results of Section 2

These are recorded as `Prop`-valued definitions (no `sorry`, no axioms).

* `Prop_2_1_1` — conformal pullback (Proposition 2.1.1) for maps **holomorphic on a neighbourhood
  of `𝔻̄`**, injective on `𝔻̄`, with `F' ≠ 0` on `𝕋`: **proved** (`ConformalPullback.prop_2_1_1`).
  The paper states Proposition 2.1.1 more generally, for conformal maps with a `C¹`-diffeomorphic
  boundary extension; its weak C¹ version is proved separately as
  `SteklovC1.prop_2_1_1_C1_weak`. This definition retains the holomorphic version
  used for the construction (Proposition 2.3.1 produces such maps).
* `Prop_2_3_1`, `Prop_2_3_1_realization` — Proposition 2.3.1, first part: **proved**
  (`OuterRealization.prop_2_3_1`, `OuterRealization.prop_2_3_1_realization`).
* `Prop_2_3_1_convergence` (parameter formulation, for *every* normalized realizing map) and
  `Prop_2_3_1_convergence_seq` (the paper's sequence formulation): **proved**
  (`OuterConvergence.prop_2_3_1_convergence`, `OuterConvergence.prop_2_3_1_convergence_seq`).
* `Prop_2_3_1_complete` — all assertions of Proposition 2.3.1: **proved**
  (`OuterConvergence.prop_2_3_1_complete`).
* `SteklovDilation` — the scaling law `σ_k(cΩ) = σ_k(Ω)/c` used in §3.5: **proved**
  (`SteklovDilationProof.steklovDilation`).

Propositions 2.2.1 and 3.3.1 and Lemma 3.2.1 are supplied elsewhere in the completed
development using concrete disk-coordinate orbifold models and the explicit
degree-seven construction. This is not a general Riemann existence theorem or
general orbifold library; see `docs/RESULTS.md`. Proposition 3.4.1 (coalescence) is proved
(`SteklovCoalescence.prop_3_4_1`, `RequestProject.Coalescence`) conditional on an explicit cover
input (`SteklovCoalescence.IsNormalizedDiskCover`: normalized conformal maps onto the cover
components and the Blaschke property of `Q_ε ∘ ψ_ε`); no Carathéodory kernel theorem is used.
The existence of this cover input is proved (`SteklovCoalescence.exists_paper_diskCover`,
`RequestProject.DiskCoverExistence`), so Proposition 3.4.1 holds without it
(`SteklovCoalescence.prop_3_4_1_unconditional`).
-/

@[expose] public section

open Set Metric Filter Topology PlaneDomain Steklov

/-- **Proposition 2.1.1 (conformal pullback), holomorphic-neighbourhood version.**  If `F` is
holomorphic on a neighbourhood of `𝔻̄`, injective on `𝔻̄`, with `F' ≠ 0` on `𝕋`, and `Ω = F(𝔻)`,
then `Spec_St(Ω) = Spec_St(𝔻, |F'|_𝕋)`.  (The paper's statement allows conformal maps with a
`C¹`-diffeomorphic boundary extension; this definition covers only the holomorphic case.) -/
def Prop_2_1_1 : Prop :=
  ∀ F : ℂ → ℂ,
    (∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ F U) →
    InjOn F (closedBall 0 1) → (∀ z ∈ sphere (0 : ℂ) 1, deriv F z ≠ 0) →
    steklovSpectrum (F '' ball 0 1) = weightedSteklovSpectrum (fun z => ‖deriv F z‖)

/-- The weight `ρ` (viewed as `t ↦ ρ(e^{it})`) is positive and real-analytic on the circle. -/
def IsPosRealAnalyticWeight (ρ : ℂ → ℝ) : Prop :=
  AnalyticOnNhd ℝ (fun t : ℝ => ρ (Complex.exp (t * Complex.I))) univ ∧
    ∀ t : ℝ, 0 < ρ (Complex.exp (t * Complex.I))

/-- `ρ` is within `δ` of the constant `c` in the `C^k(𝕋)` norm. -/
def CkClose (k : ℕ) (δ : ℝ) (ρ : ℂ → ℝ) (c : ℝ) : Prop :=
  ∀ j ≤ k, ∀ t : ℝ,
    |iteratedDeriv j (fun s : ℝ => ρ (Complex.exp (s * Complex.I)) - c) t| < δ

/-- **Proposition 2.3.1 (realization of weights near a constant), first part.**  For every
`c > 0` there is a `C^∞`-neighbourhood (here: a `C^k` ball of radius `δ`) of the constant `c`
such that every positive real-analytic weight `ρ` in it is `|F'|` on `𝕋` for a map `F`
holomorphic near `𝔻̄`, injective on `𝔻̄`, with `F(0) = 0` and `F'(0) > 0`; consequently
`Spec_St(F(𝔻)) = Spec_St(𝔻, ρ)` (via `Prop_2_1_1`). -/
def Prop_2_3_1 : Prop :=
  ∀ c : ℝ, 0 < c → ∃ k : ℕ, ∃ δ > (0 : ℝ), ∀ ρ : ℂ → ℝ,
    IsPosRealAnalyticWeight ρ → CkClose k δ ρ c →
    ∃ F : ℂ → ℂ,
      (∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ F U) ∧
      InjOn F (closedBall 0 1) ∧ F 0 = 0 ∧ 0 < (deriv F 0).re ∧ (deriv F 0).im = 0 ∧
      (∀ z ∈ sphere (0 : ℂ) 1, ‖deriv F z‖ = ρ z) ∧
      steklovSpectrum (F '' ball 0 1) = weightedSteklovSpectrum ρ

/-- The realization part of Proposition 2.3.1 alone (without the spectral conclusion, which
follows from Proposition 2.1.1: see `prop_2_3_1_of_realization` in
`RequestProject.Prop231Reduction`). -/
def Prop_2_3_1_realization : Prop :=
  ∀ c : ℝ, 0 < c → ∃ k : ℕ, ∃ δ > (0 : ℝ), ∀ ρ : ℂ → ℝ,
    IsPosRealAnalyticWeight ρ → CkClose k δ ρ c →
    ∃ F : ℂ → ℂ,
      (∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ F U) ∧
      InjOn F (closedBall 0 1) ∧ F 0 = 0 ∧ 0 < (deriv F 0).re ∧ (deriv F 0).im = 0 ∧
      (∀ z ∈ sphere (0 : ℂ) 1, ‖deriv F z‖ = ρ z)

/-- **Proposition 2.3.1, convergence part, parameter formulation** (not covered by
`Prop_2_3_1`; proved as `OuterConvergence.prop_2_3_1_convergence`): if positive real-analytic weights `ρ ε` tend to the constant `c > 0` in every
`C^k(𝕋)` norm as `ε → 0⁺`, then normalized realizing maps `F ε` (holomorphic near `𝔻̄`,
injective on `𝔻̄`, `F ε 0 = 0`, `F ε'(0) > 0`, `|F ε'| = ρ ε` on `𝕋`) tend to `z ↦ c z` in
`C^∞(𝔻̄)`.  (Normalized realizing maps are unique, so this is the convergence of *the*
maps produced by the first part.) -/
def Prop_2_3_1_convergence : Prop :=
  ∀ c : ℝ, 0 < c → ∀ (ρ : ℝ → ℂ → ℝ) (F : ℝ → ℂ → ℂ),
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsPosRealAnalyticWeight (ρ ε)) →
    (∀ k : ℕ, ∀ δ > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), CkClose k δ (ρ ε) c) →
    (∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ (F ε) U) ∧
      InjOn (F ε) (closedBall 0 1) ∧ F ε 0 = 0 ∧ 0 < (deriv (F ε) 0).re ∧
      (deriv (F ε) 0).im = 0 ∧ ∀ z ∈ sphere (0 : ℂ) 1, ‖deriv (F ε) z‖ = ρ ε z) →
    ∀ k : ℕ, ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ k (fun w => F ε w - (c : ℂ) * w) z‖ < η

/-- `F` is a *normalized realizing map* for the weight `ρ`: holomorphic on a neighbourhood of
`𝔻̄`, injective on `𝔻̄`, `F(0) = 0`, `F'(0) > 0` and `|F'| = ρ` on `𝕋`. -/
def IsNormalizedRealizing (F : ℂ → ℂ) (ρ : ℂ → ℝ) : Prop :=
  (∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ F U) ∧
    InjOn F (closedBall 0 1) ∧ F 0 = 0 ∧ 0 < (deriv F 0).re ∧ (deriv F 0).im = 0 ∧
    ∀ z ∈ sphere (0 : ℂ) 1, ‖deriv F z‖ = ρ z

/-- **Proposition 2.3.1, convergence part, in the paper's sequence formulation**: if positive
real-analytic weights `ρ n` tend to the constant `c > 0` in `C^∞(𝕋)` (every `C^k` norm), then the
corresponding normalized realizing maps may be chosen (for all large `n`) so that
`F n → c · id` in `C^∞(𝔻̄)`. -/
def Prop_2_3_1_convergence_seq : Prop :=
  ∀ c : ℝ, 0 < c → ∀ ρ : ℕ → ℂ → ℝ,
    (∀ n, IsPosRealAnalyticWeight (ρ n)) →
    (∀ k : ℕ, ∀ δ > (0 : ℝ), ∀ᶠ n in atTop, CkClose k δ (ρ n) c) →
    ∃ F : ℕ → ℂ → ℂ, (∀ᶠ n in atTop, IsNormalizedRealizing (F n) (ρ n)) ∧
      ∀ k : ℕ, ∀ η > (0 : ℝ), ∀ᶠ n in atTop, ∀ z ∈ closedBall (0 : ℂ) 1,
        ‖iteratedFDeriv ℝ k (fun w => F n w - (c : ℂ) * w) z‖ < η

/-- **Proposition 2.3.1, complete statement**: (first part) for every `c > 0`, every positive
real-analytic weight in a `C^k`-ball (hence `C^∞`-neighbourhood) around `c` is realized by a
normalized map `F` (holomorphic near `𝔻̄`, injective on `𝔻̄`, `F(0)=0`, `F'(0)>0`, `|F'|=ρ` on
`𝕋`), and `F(𝔻)` is a bounded simply connected domain with real-analytic Jordan boundary and
`Spec_St(F(𝔻)) = Spec_St(𝔻, ρ)`; (second part) the convergence statement in the sequence
formulation. -/
def Prop_2_3_1_complete : Prop :=
  (∀ c : ℝ, 0 < c → ∃ k : ℕ, ∃ δ > (0 : ℝ), ∀ ρ : ℂ → ℝ,
    IsPosRealAnalyticWeight ρ → CkClose k δ ρ c →
    ∃ F : ℂ → ℂ, IsNormalizedRealizing F ρ ∧ IsDomain (F '' ball 0 1) ∧
      Bornology.IsBounded (F '' ball 0 1) ∧ SimplyConnectedSpace (F '' ball 0 1) ∧
      IsRealAnalyticJordanBoundary (F '' ball 0 1) ∧
      steklovSpectrum (F '' ball 0 1) = weightedSteklovSpectrum ρ) ∧
  Prop_2_3_1_convergence_seq

/-- **Dilation law** used in §3.5: `σ_k(cΩ) = σ_k(Ω)/c` for `c > 0`. -/
def SteklovDilation : Prop :=
  ∀ (Ω : Set ℂ) (c : ℝ), 0 < c → ∀ k : ℕ,
    steklovEigenvalue ((fun z => (c : ℂ) * z) '' Ω) k = steklovEigenvalue Ω k / ENNReal.ofReal c

end
