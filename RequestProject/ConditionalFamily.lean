module

public import Mathlib
public import RequestProject.CoalescenceRealization
public import RequestProject.StrictConvexity
public import RequestProject.ConformalImage
public import RequestProject.MainStatement

/-!
# Conditional assembly of Theorem 1.1.2, conclusions (i), (ii), (iv), (v)

**This is conditional scaffolding, not a proof of Theorem 1.1.2.**  The theorem
`mainTheorem_except_iii_of_cover_data` derives conclusions (i) (including strict convexity), (ii),
(iv) and (v) of Theorem 1.1.2 — with the paper's quantifier structure — from the following
**explicit input parameters to this assembly lemma**:

* polynomial data for both labels (monic `P_i` of a common degree `n ≥ 1`;
  their permutation/monodromy properties are not used by this conditional lemma);
* the cover input `IsNormalizedDiskCover` for both labels and all small `ε` (uniformization of the
  cover domains and the Blaschke property of `B_{i,ε} = Q_{i,ε} ∘ ψ_{i,ε}`);
* the spectral transfer `Spec_St(𝔻, |B_{P,ε}'|) = Spec_St(𝔻, |B_{L,ε}'|)`.

The completed development supplies the explicit polynomial/cover data and spectral
transfer separately. The unconditional five-conclusion theorem and its PDE/Sobolev
interpretation are in `RequestProject.MainTheoremClassical`; current scope and the
weighted-disk proof route are recorded in `docs/RESULTS.md`.

Conclusion (iii) (noncongruence) is not addressed here.  Everything else in the chain —
coalescence (Proposition 3.4.1), realization and convergence (Proposition 2.3.1), conformal
pullback (Proposition 2.1.1), the dilation law, the length computation and strict convexity —
is proved.
-/

@[expose] public section

open Complex Metric Set Filter Topology SteklovBlaschke PlaneDomain Steklov

noncomputable section

namespace SteklovCoalescence

/-- Conclusions (i), (ii), (iv), (v) of Theorem 1.1.2 (i.e. `MainTheorem` without (iii)), with the
same quantifier structure. -/
def MainTheoremExceptNoncongruence : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Ω : Label → ℝ → Set ℂ,
    (∀ i ε, 0 < ε → ε < ε₀ →
      IsDomain (Ω i ε) ∧ Bornology.IsBounded (Ω i ε) ∧ SimplyConnectedSpace (Ω i ε) ∧
      IsStrictlyConvexDomain (Ω i ε) ∧ IsRealAnalyticJordanBoundary (Ω i ε)) ∧
    (∀ ε, 0 < ε → ε < ε₀ → steklovSpectrum (Ω Label.P ε) = steklovSpectrum (Ω Label.L ε)) ∧
    (∀ i ε, 0 < ε → ε < ε₀ → boundaryLength (Ω i ε) = ENNReal.ofReal (2 * Real.pi)) ∧
    (∃ F : Label → ℝ → ℂ → ℂ,
      (∀ i ε, 0 < ε → ε < ε₀ → IsNormalizedConformalMap (F i ε) (Ω i ε)) ∧
      ∀ i, TendstoIdInCInfty (F i))

/-- `MainTheorem` implies its conclusions other than (iii). -/
theorem mainTheoremExceptNoncongruence_of_mainTheorem (h : MainTheorem) :
    MainTheoremExceptNoncongruence := by
  obtain ⟨ε₀, hε₀, Ω, h1, h2, -, -, h4, h5⟩ := h
  exact ⟨ε₀, hε₀, Ω, h1, h2, h4, h5⟩

/-! ### The rescaled maps `G = F / n` -/

lemma rescale_image (c : ℂ) (F : ℂ → ℂ) :
    (fun w => c * F w) '' ball 0 1 = (fun z => c * z) '' (F '' ball 0 1) := by
  rw [image_image]

lemma rescale_props {F : ℂ → ℂ} {ρ : ℂ → ℝ} {c : ℝ} (hc : 0 < c)
    (hF : IsNormalizedRealizing F ρ) (hpos : ∀ z ∈ sphere (0 : ℂ) 1, 0 < ρ z) :
    IsNormalizedConformalMap (fun w => (c : ℂ) * F w) ((fun w => (c : ℂ) * F w) '' ball 0 1) ∧
      IsDomain ((fun w => (c : ℂ) * F w) '' ball 0 1) ∧
      Bornology.IsBounded ((fun w => (c : ℂ) * F w) '' ball 0 1) ∧
      SimplyConnectedSpace ((fun w => (c : ℂ) * F w) '' ball 0 1) ∧
      IsRealAnalyticJordanBoundary ((fun w => (c : ℂ) * F w) '' ball 0 1) := by
  obtain ⟨⟨U, hU, hcb, hd⟩, hinj, h0, hre, him, hnorm⟩ := hF
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  set G : ℂ → ℂ := fun w => (c : ℂ) * F w with hG
  have hGd : DifferentiableOn ℂ G U := hd.const_mul _
  have hGinj : InjOn G (closedBall 0 1) := fun x hx y hy hxy =>
    hinj hx hy (mul_left_cancel₀ hc0 hxy)
  have hderiv : ∀ z ∈ U, deriv G z = c * deriv F z := fun z hz =>
    ((hd.differentiableAt (hU.mem_nhds hz)).hasDerivAt.const_mul (c : ℂ)).deriv
  have hG' : ∀ z ∈ sphere (0 : ℂ) 1, deriv G z ≠ 0 := by
    intro z hz
    rw [hderiv z (hcb (sphere_subset_closedBall hz))]
    refine mul_ne_zero hc0 fun h => ?_
    have := hnorm z hz
    rw [h, norm_zero] at this
    exact (hpos z hz).ne this
  have h0U : (0 : ℂ) ∈ U := hcb (mem_closedBall_self zero_le_one)
  refine ⟨⟨⟨U, hU, hcb, hGd⟩, hGinj.mono ball_subset_closedBall, rfl, ?_, ?_, ?_⟩,
    ConformalImage.isDomain_image_ball hcb hGd hGinj,
    ConformalImage.isBounded_image_ball hcb hGd,
    ConformalImage.simplyConnected_image_ball hcb hGd hGinj,
    ConformalImage.realAnalyticJordan_image_ball hU hcb hGd hGinj hG'⟩
  · simp [hG, h0]
  · rw [hderiv 0 h0U]; simp [him]; exact mul_pos hc hre
  · rw [hderiv 0 h0U]; simp [him]

/-- Rescaling preserves `C^∞` convergence: if `F ε → n·id` then `F ε / n → id`. -/
lemma rescale_tendsto {F : ℝ → ℂ → ℂ} {c : ℝ} (hc : 0 < c)
    (hF : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      ∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ (F ε) U)
    (hconv : ∀ k : ℕ, ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ closedBall (0 : ℂ) 1,
      ‖iteratedFDeriv ℝ k (fun w => F ε w - ((c⁻¹ : ℝ) : ℂ) * w) z‖ < η) :
    TendstoIdInCInfty (fun ε w => (c : ℂ) * F ε w) := by
  intro k η hη
  filter_upwards [hF, hconv k (η / c) (by positivity)] with ε hε h
  obtain ⟨U, hU, hcb, hd⟩ := hε
  intro z hz
  have hfun : (fun w => (c : ℂ) * F ε w - w) =
      fun w => c • (F ε w - ((c⁻¹ : ℝ) : ℂ) * w) := by
    ext w
    rw [Complex.real_smul]
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
    push_cast
    field_simp
  have hcd : ContDiffAt ℝ k (fun w => F ε w - ((c⁻¹ : ℝ) : ℂ) * w) z := by
    have : ContDiffOn ℂ k (fun w => F ε w - ((c⁻¹ : ℝ) : ℂ) * w) U :=
      ((hd.sub (by fun_prop)).contDiffOn hU)
    exact (this.contDiffAt (hU.mem_nhds (hcb hz))).restrict_scalars ℝ
  rw [hfun, iteratedFDeriv_const_smul_apply' hcd, norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have := h z hz
  calc c * _ < c * (η / c) := by gcongr
    _ = η := by field_simp

/-! ### The conditional assembly -/

open SteklovCritical in
/-- **Conditional assembly of Theorem 1.1.2 (i), (ii), (iv), (v)** from explicit inputs: the
polynomial data, the cover input for both labels, and equality of the weighted disk spectra
`Spec_St(𝔻, |B_{P,ε}'|) = Spec_St(𝔻, |B_{L,ε}'|)`.  The domains are
`Ω_i^ε = (1/n) F_{i,ε}(𝔻)` with `F_{i,ε}` the normalized realizing maps of the weights
`|B_{i,ε}'|`. -/
theorem mainTheorem_except_iii_of_cover_data {n : ℕ} (hn : 1 ≤ n) (P : Label → Polynomial ℂ)
    (hP : ∀ i, (P i).Monic) (hdeg : ∀ i, (P i).natDegree = n) (τ : Label → ℝ → ℂ)
    (hτ : ∀ i ε, τ i ε ^ n = (lamStar - 1) * ε) (ψ B : Label → ℝ → ℂ → ℂ)
    (hcov : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IsNormalizedDiskCover (paperQ (P i) (τ i) ε) n (ψ i ε) (B i ε))
    (hspec : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      weightedSteklovSpectrum (fun z => ‖deriv (B Label.P ε) z‖) =
        weightedSteklovSpectrum (fun z => ‖deriv (B Label.L ε) z‖)) :
    MainTheoremExceptNoncongruence := by
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
    first
      | simpa [inv_inv] using this
      | simpa [inv_inv, Function.comp_def] using this
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
  refine ⟨ε₀, hε₀, Ω, fun i ε h0 h1 => ?_, fun ε h0 h1 => (hsub ⟨h0, h1⟩).2,
    fun i ε h0 h1 => ((hsub ⟨h0, h1⟩).1 i).2.2.2.2.2.2, G, fun i ε h0 h1 => ((hsub ⟨h0, h1⟩).1 i).1,
    hGconv⟩
  obtain ⟨-, a1, a2, a3, a4, a5, -⟩ := (hsub ⟨h0, h1⟩).1 i
  exact ⟨a1, a2, a3, a4, a5⟩

end SteklovCoalescence
