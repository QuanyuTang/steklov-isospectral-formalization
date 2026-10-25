module

public import RequestProject.ConditionalFamily

/-!
# Conditional assembly of the full Theorem 1.1.2

`mainTheorem_of_cover_data` is `mainTheorem_except_iii_of_cover_data` with conclusion (iii) added:
given the polynomial data, the cover input, the spectral equality **and** a noncongruence input
`hiii` stated for the realizing maps of the weights `|B_{i,ε}'|`, it yields `MainTheorem`.  The
input `hiii` is discharged for the actual degree-seven families in `MainTheoremProof.lean`.
-/

@[expose] public section

open Complex Metric Set Filter Topology SteklovBlaschke PlaneDomain Steklov

noncomputable section

namespace SteklovCoalescence

open SteklovCritical in
/-- **Conditional assembly of Theorem 1.1.2 (i), (ii), (iv), (v)** from explicit inputs: the
polynomial data, the cover input for both labels, and equality of the weighted disk spectra
`Spec_St(𝔻, |B_{P,ε}'|) = Spec_St(𝔻, |B_{L,ε}'|)`.  The domains are
`Ω_i^ε = (1/n) F_{i,ε}(𝔻)` with `F_{i,ε}` the normalized realizing maps of the weights
`|B_{i,ε}'|`. -/
theorem mainTheorem_of_cover_data {n : ℕ} (hn : 1 ≤ n) (P : Label → Polynomial ℂ)
    (hP : ∀ i, (P i).Monic) (hdeg : ∀ i, (P i).natDegree = n) (τ : Label → ℝ → ℂ)
    (hτ : ∀ i ε, τ i ε ^ n = (lamStar - 1) * ε) (ψ B : Label → ℝ → ℂ → ℂ)
    (hcov : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IsNormalizedDiskCover (paperQ (P i) (τ i) ε) n (ψ i ε) (B i ε))
    (hspec : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      weightedSteklovSpectrum (fun z => ‖deriv (B Label.P ε) z‖) =
        weightedSteklovSpectrum (fun z => ‖deriv (B Label.L ε) z‖))
    (hiii : ∀ F : Label → ℝ → ℂ → ℂ, (∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        IsNormalizedRealizing (F i ε) (fun z => ‖deriv (B i ε) z‖)) →
      ∃ ε₁ > (0 : ℝ), ∀ i j ε ε', 0 < ε → ε < ε₁ → 0 < ε' → ε' < ε₁ →
        ((i, ε) ≠ (j, ε') → ¬ Congruent ((fun w => (((n : ℝ)⁻¹ : ℝ) : ℂ) * F i ε w) '' ball 0 1)
          ((fun w => (((n : ℝ)⁻¹ : ℝ) : ℂ) * F j ε' w) '' ball 0 1)) ∧
        ¬ HasOrientationReversingSymmetry
          ((fun w => (((n : ℝ)⁻¹ : ℝ) : ℂ) * F i ε w) '' ball 0 1)) :
    MainTheorem := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.2 hn0
  choose F hFgood hFconv using fun i => coalescence_realization (hP i) hn (hdeg i) (hτ i) (hcov i)
  set c : ℂ := (((n : ℝ)⁻¹ : ℝ) : ℂ) with hc_def
  set G : Label → ℝ → ℂ → ℂ := fun i ε w => c * F i ε w with hG
  set Ω : Label → ℝ → Set ℂ := fun i ε => G i ε '' ball 0 1 with hΩ
  -- positivity of the weights on the circle
  have hpos : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ sphere (0 : ℂ) 1, 0 < ‖deriv (B i ε) z‖ := by
    intro i
    filter_upwards [hcov i] with ε h z hz
    obtain ⟨t, rfl⟩ := circle_surj (by simpa using hz)
    exact (blaschke_weight_posAnalytic hn h.2.2.2.2.2.2.1).2 t
  -- convergence of the rescaled maps
  have hGconv : ∀ i, TendstoIdInCInfty (G i) := by
    intro i
    refine rescale_tendsto hc ((hFgood i).mono fun ε h => h.1.1) ?_
    intro k η hη
    have := hFconv i k η hη
    simpa [inv_inv] using this
  -- strict convexity
  have hconvex : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsStrictlyConvexDomain (Ω i ε) := by
    intro i
    refine SteklovConvexity.eventually_strictConvex_of_C2 (c := 1) one_pos ?_ ?_
    · filter_upwards [hFgood i] with ε h
      obtain ⟨U, hU, hcb, hd⟩ := h.1.1
      exact ⟨U, hU, hcb, hd.const_mul _⟩
    · intro k η hη
      simpa using hGconv i k η hη
  -- everything holds eventually
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i : Label,
      IsNormalizedConformalMap (G i ε) (Ω i ε) ∧ IsDomain (Ω i ε) ∧
      Bornology.IsBounded (Ω i ε) ∧ SimplyConnectedSpace (Ω i ε) ∧
      IsStrictlyConvexDomain (Ω i ε) ∧ IsRealAnalyticJordanBoundary (Ω i ε) ∧
      boundaryLength (Ω i ε) = ENNReal.ofReal (2 * Real.pi) := by
    have hlab : ∀ i : Label, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        IsNormalizedConformalMap (G i ε) (Ω i ε) ∧ IsDomain (Ω i ε) ∧
        Bornology.IsBounded (Ω i ε) ∧ SimplyConnectedSpace (Ω i ε) ∧
        IsStrictlyConvexDomain (Ω i ε) ∧ IsRealAnalyticJordanBoundary (Ω i ε) ∧
        boundaryLength (Ω i ε) = ENNReal.ofReal (2 * Real.pi) := by
      intro i
      filter_upwards [hFgood i, hpos i, hconvex i] with ε h hp hcv
      obtain ⟨r1, r2, r3, r4, r5⟩ := rescale_props hc h.1 hp
      refine ⟨r1, r2, r3, r4, hcv, r5, ?_⟩
      have hlen := h.2.2.2.2.2.2
      simp only [hΩ, hG, rescale_image]
      convert hlen using 3
    filter_upwards [hlab Label.P, hlab Label.L] with ε hP' hL' i
    cases i
    · exact hP'
    · exact hL'
  have hiso : ∀ᶠ ε in 𝓝[>] (0 : ℝ), steklovSpectrum (Ω Label.P ε) = steklovSpectrum (Ω Label.L ε) := by
    filter_upwards [hFgood Label.P, hFgood Label.L, hpos Label.P, hpos Label.L, hspec]
      with ε hP' hL' hpP hpL hs
    simp only [hΩ, hG, rescale_image]
    exact Prop231Reduction.isospectral_of_weighted hP'.1.1 hL'.1.1 hP'.1.2.1 hL'.1.2.1
      (fun z hz => ⟨hP'.1.2.2.2.2.2 z hz, hpP z hz⟩) (fun z hz => ⟨hL'.1.2.2.2.2.2 z hz, hpL z hz⟩)
      hs hc
  obtain ⟨ε₀, hε₀, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 (hall.and hiso)
  obtain ⟨ε₁, hε₁, h3⟩ := hiii F (fun i => (hFgood i).mono fun ε h => h.1)
  have hsub' : ∀ ε, 0 < ε → ε < min ε₀ ε₁ → _ := fun ε h0 h1 =>
    hsub ⟨h0, lt_of_lt_of_le h1 (min_le_left _ _)⟩
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, Ω, fun i ε h0 h1 => ?_, fun ε h0 h1 => (hsub' ε h0 h1).2,
    fun i j ε ε' h0 h1 h0' h1' hne => (h3 i j ε ε' h0 (lt_of_lt_of_le h1 (min_le_right _ _)) h0'
      (lt_of_lt_of_le h1' (min_le_right _ _))).1 hne,
    fun i ε h0 h1 => (h3 i i ε ε h0 (lt_of_lt_of_le h1 (min_le_right _ _)) h0
      (lt_of_lt_of_le h1 (min_le_right _ _))).2,
    fun i ε h0 h1 => ((hsub' ε h0 h1).1 i).2.2.2.2.2.2, G,
    fun i ε h0 h1 => ((hsub' ε h0 h1).1 i).1, hGconv⟩
  obtain ⟨-, a1, a2, a3, a4, a5, -⟩ := (hsub' ε h0 h1).1 i
  exact ⟨a1, a2, a3, a4, a5⟩

end SteklovCoalescence
