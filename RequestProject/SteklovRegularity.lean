module

public import Mathlib
public import RequestProject.WeylLemma
public import RequestProject.ConformalSpectrum

/-!
# Interior regularity of weak Steklov eigenfunctions

Every weak Steklov eigenfunction `x ∈ H¹(Ω)` (`∫_Ω ⟨∇x, ∇y⟩ = τ ∫_{∂Ω} Tx Ty dH¹` for all
`y ∈ H¹(Ω)`) is, after modification on a null set, a classical harmonic function in `Ω`:
its `L²` class has a representative `h` with `h ∈ C²` near every point of `Ω` and `Δ h = 0`.
This is the interior part of matching the weak problem with the classical problem
`Δu = 0` in `Ω`, `∂_ν u = τ u` on `∂Ω`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric InnerProductSpace
open scoped ENNReal ContDiff RealInnerProductSpace Manifold

noncomputable section

namespace SteklovWeyl

lemma exists_cutoff {K V : Set ℂ} (hK : IsClosed K) (hd : K ⊆ interior V) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧ (∀ᶠ x in 𝓝ˢ K, χ x = 1) ∧ (∀ x ∉ V, χ x = 0) := by
  obtain ⟨f, h1, h2, -⟩ := exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, ℂ) (n := ⊤) hK hd
  exact ⟨f, contMDiff_iff_contDiff.1 f.contMDiff, h1, h2⟩

/-- **Integration by parts for functions that are only `C¹` on an open set**, against test
functions supported in that set. -/
lemma ibp_local {U : Set ℂ} (hU : IsOpen U) {h : ℂ → ℝ} (hh : ∀ x ∈ U, ContDiffAt ℝ 1 h x)
    {φ : ℂ → ℝ} (h1 : ContDiff ℝ ∞ φ) (h2 : HasCompactSupport φ) (h3 : tsupport φ ⊆ U)
    (v : ℂ) :
    ∫ t, h t * fderiv ℝ φ t v = - ∫ t, fderiv ℝ h t v * φ t := by
  set K := tsupport φ
  obtain ⟨δ, hδ, hδU⟩ := h2.isCompact.exists_cthickening_subset_open hU h3
  have hKV : K ⊆ interior (thickening δ K) := by
    rw [isOpen_thickening.interior_eq]; exact self_subset_thickening hδ K
  obtain ⟨χ, hχ, hχ1, hχ0⟩ := exists_cutoff (isClosed_tsupport φ) hKV
  set g : ℂ → ℝ := fun t => χ t * h t with hg
  have hgc : ContDiff ℝ 1 g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ U
    · exact (hχ.of_le (by simp)).contDiffAt.mul (hh x hx)
    · have hxc : x ∉ cthickening δ K := fun h => hx (hδU h)
      have hev : g =ᶠ[𝓝 x] fun _ => 0 := by
        have hop : IsOpen (closure (thickening δ K))ᶜ := isClosed_closure.isOpen_compl
        have hmem : x ∈ (closure (thickening δ K))ᶜ := fun h' =>
          hxc ((closure_thickening_subset_cthickening δ K) h')
        filter_upwards [hop.mem_nhds hmem] with y hy
        have : y ∉ thickening δ K := fun h' => hy (subset_closure h')
        simp [hg, hχ0 y this]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hφ1 : ContDiff ℝ 1 φ := h1.of_le (by simp)
  have hcg : Continuous g := hgc.continuous
  have hcφ : Continuous φ := hφ1.continuous
  have hcg' : Continuous (fderiv ℝ g) := hgc.continuous_fderiv one_ne_zero
  have hcφ' : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv one_ne_zero
  have hfφ0 : ∀ t, t ∉ K → fderiv ℝ φ t = 0 := fun t ht =>
    image_eq_zero_of_notMem_tsupport (fun h => ht (tsupport_fderiv_subset ℝ h))
  have hφ0 : ∀ t, t ∉ K → φ t = 0 := fun t ht => image_eq_zero_of_notMem_tsupport ht
  have hloc : ∀ t ∈ K, g =ᶠ[𝓝 t] h := by
    intro t ht
    have := hχ1.filter_mono (nhds_le_nhdsSet ht)
    filter_upwards [this] with y hy
    simp [hg, hy]
  have e1 : ∫ t, h t * fderiv ℝ φ t v = ∫ t, g t * fderiv ℝ φ t v := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ K
    · show h t * fderiv ℝ φ t v = g t * fderiv ℝ φ t v
      rw [(hloc t ht).self_of_nhds]
    · simp [hfφ0 t ht]
  have e2 : ∫ t, fderiv ℝ h t v * φ t = ∫ t, fderiv ℝ g t v * φ t := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : t ∈ K
    · simp only [(hloc t ht).fderiv_eq]
    · simp [hφ0 t ht]
  rw [e1, e2]
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ => (hgc.differentiable one_ne_zero) x) (fun x _ => (hφ1.differentiable one_ne_zero) x)
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop) h2.mul_left
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (h2.fderiv_apply (𝕜 := ℝ) v).mul_left
  · exact Continuous.integrable_of_hasCompactSupport (by fun_prop) h2.mul_left

/-- **Weak gradients of locally `C¹` functions are classical gradients.** If `G` is a locally
integrable weak gradient of `F` on the open set `U` and `F` agrees a.e. on `U` with a function
`h` that is `C¹` near every point of `U`, then `G = ∇h` a.e. on `U`. -/
theorem weak_gradient_ae_eq_grad {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℝ} {G : ℂ → ℂ}
    (hG : LocallyIntegrable G volume)
    (hw : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v : ℂ,
      ∫ t, F t * fderiv ℝ φ t v = - ∫ t, inner ℝ (G t) v * φ t)
    {h : ℂ → ℝ} (hh : ∀ x ∈ U, ContDiffAt ℝ 1 h x) (hFh : F =ᵐ[volume.restrict U] h) :
    G =ᵐ[volume.restrict U] SteklovH1.grad h := by
  have hFh' : ∀ᵐ t ∂volume, t ∈ U → F t = h t := (ae_restrict_iff' hU.measurableSet).1 hFh
  have hcont : ∀ v : ℂ, ContinuousOn (fun t => fderiv ℝ h t v) U := by
    intro v x hx
    have h1 := (hh x hx).fderiv_right (m := 0) (by norm_num)
    exact ((h1.continuousAt).clm_apply continuousAt_const).continuousWithinAt
  have hcomp : ∀ v : ℂ, ∀ᵐ t ∂volume, t ∈ U → ⟪G t, v⟫ - fderiv ℝ h t v = 0 := by
    intro v
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
    · exact ((SteklovWeyl.locallyIntegrable_inner hG v).locallyIntegrableOn U).sub
        ((hcont v).locallyIntegrableOn hU.measurableSet)
    · intro φ h1 h2 h3
      have hiG : Integrable (fun t => φ t * ⟪G t, v⟫) volume := by
        have := (SteklovWeyl.locallyIntegrable_inner hG v).integrable_smul_left_of_hasCompactSupport
          h1.continuous h2
        simpa [smul_eq_mul] using this
      have hih : Integrable (fun t => φ t * fderiv ℝ h t v) volume := by
        have hK : IntegrableOn (fun t => φ t * fderiv ℝ h t v) (tsupport φ) volume :=
          (h1.continuous.continuousOn.mul ((hcont v).mono h3)).integrableOn_compact h2.isCompact
        refine (integrableOn_iff_integrable_of_support_subset ?_).1 hK
        intro t ht
        by_contra hts
        exact ht (by simp [image_eq_zero_of_notMem_tsupport hts])
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub hiG hih]
      have eG : ∫ t, φ t * ⟪G t, v⟫ = - ∫ t, h t * fderiv ℝ φ t v := by
        have hwv := hw φ h1 h2 h3 v
        have eF : ∫ t, F t * fderiv ℝ φ t v = ∫ t, h t * fderiv ℝ φ t v := by
          refine integral_congr_ae ?_
          filter_upwards [hFh'] with t ht
          by_cases htU : t ∈ U
          · rw [ht htU]
          · have : fderiv ℝ φ t = 0 := image_eq_zero_of_notMem_tsupport
              (fun h' => htU (h3 (tsupport_fderiv_subset ℝ h')))
            simp [this]
        have ec : ∫ t, φ t * ⟪G t, v⟫ = ∫ t, ⟪G t, v⟫ * φ t := by
          refine integral_congr_ae (Eventually.of_forall fun t => ?_)
          simp only; ring
        rw [ec, ← eF]
        linarith
      rw [eG, ibp_local hU hh h1 h2 h3 v, neg_neg, sub_eq_zero]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only; ring
  rw [EventuallyEq, ae_restrict_iff' hU.measurableSet]
  filter_upwards [hcomp 1, hcomp Complex.I] with t h1 h2 htU
  have e1 := sub_eq_zero.1 (h1 htU)
  have e2 := sub_eq_zero.1 (h2 htU)
  rw [← SteklovH1.inner_grad] at e1 e2
  apply Complex.ext
  · simpa [Complex.inner] using e1
  · simpa [Complex.inner] using e2

end SteklovWeyl

namespace SteklovH1

namespace BddDomain

variable (D : BddDomain)

/-- For an `H¹(Ω)` element, the zero extensions of `(f, g)` form a weak gradient pair on `Ω`
in the whole-plane sense used by Weyl's lemma. -/
lemma weak_gradient_indicator (x : D.H1) (φ : ℂ → ℝ) (h1 : ContDiff ℝ ∞ φ)
    (h2 : HasCompactSupport φ) (h3 : tsupport φ ⊆ D.carrier) (v : ℂ) :
    ∫ t, D.carrier.indicator ((x : D.Amb).fst : ℂ → ℝ) t * fderiv ℝ φ t v =
      - ∫ t, inner ℝ (D.carrier.indicator ((x : D.Amb).snd : ℂ → ℂ) t) v * φ t := by
  have hBm : MeasurableSet D.carrier := D.isOpen.measurableSet
  have e1 : (fun t => D.carrier.indicator ((x : D.Amb).fst : ℂ → ℝ) t * fderiv ℝ φ t v) =
      D.carrier.indicator (fun t => (x : D.Amb).fst t * fderiv ℝ φ t v) := by
    funext t; by_cases ht : t ∈ D.carrier <;> simp [ht]
  have e2 : (fun t => inner ℝ (D.carrier.indicator ((x : D.Amb).snd : ℂ → ℂ) t) v * φ t) =
      D.carrier.indicator (fun t => inner ℝ ((x : D.Amb).snd t) v * φ t) := by
    funext t; by_cases ht : t ∈ D.carrier <;> simp [ht]
  rw [e1, e2, integral_indicator hBm, integral_indicator hBm]
  exact D.weak_gradient x ⟨h1, h2, h3⟩ v

/-- **Weak Steklov eigenfunctions are weakly harmonic in `Ω`**: testing the eigenvalue equation
against a compactly supported smooth `φ` in `Ω` (which has zero trace) gives
`∫_Ω ⟨∇x, ∇φ⟩ = 0`. -/
lemma weakly_harmonic_of_eigen {C : ℝ} (hC : D.HasTraceIneq C) {τ : ℝ} {x : D.H1}
    (hx : IsWeakSteklovEigenDom D τ x) (φ : ℂ → ℝ) (h1 : ContDiff ℝ ∞ φ)
    (h3 : tsupport φ ⊆ D.carrier) :
    ∫ t, ⟪D.carrier.indicator ((x : D.Amb).snd : ℂ → ℂ) t, grad φ t⟫ = 0 := by
  have hBm : MeasurableSet D.carrier := D.isOpen.measurableSet
  set u : smoothFns := ⟨φ, h1⟩
  have e1 : (fun t => ⟪D.carrier.indicator ((x : D.Amb).snd : ℂ → ℂ) t, grad φ t⟫) =
      D.carrier.indicator (fun t => ⟪((x : D.Amb).snd : ℂ → ℂ) t, grad φ t⟫) := by
    funext t; by_cases ht : t ∈ D.carrier <;> simp [ht]
  rw [e1, integral_indicator hBm]
  have e2 : ∫ t in D.carrier, ⟪((x : D.Amb).snd : ℂ → ℂ) t, grad φ t⟫ =
      ∫ t in D.carrier, ⟪((x : D.Amb).snd : ℂ → ℂ) t,
        (((D.embedH u : D.H1) : D.Amb).snd : ℂ → ℂ) t⟫ := by
    refine integral_congr_ae ?_
    filter_upwards [D.gradL2_ae u] with t ht
    simp only [coe_embedH, embed_snd]
    rw [ht]
  rw [e2, hx (D.embedH u)]
  have e3 : ∫ w, (D.trace x : ℂ → ℝ) w * (D.trace (D.embedH u) : ℂ → ℝ) w ∂D.ν = 0 := by
    refine integral_eq_zero_of_ae ?_
    have hfr : ∀ᵐ w ∂D.ν, w ∈ frontier D.carrier :=
      ae_restrict_mem (isClosed_frontier.measurableSet)
    filter_upwards [D.trace_embed_ae hC u, hfr] with w hw hwf
    rw [hw]
    have : φ w = 0 := by
      refine image_eq_zero_of_notMem_tsupport fun hw' => ?_
      have hwc := h3 hw'
      rw [D.isOpen.frontier_eq] at hwf
      exact hwf.2 hwc
    simp [u, this]
  rw [e3, mul_zero]

/-- **Interior regularity of weak Steklov eigenfunctions.** If `Ω` carries a trace inequality and
`x ∈ H¹(Ω)` is a weak Steklov eigenfunction with eigenvalue `τ`, then the `L²(Ω)` class of `x`
has a representative `h : ℂ → ℝ` which is harmonic at every point of `Ω`
(`C²` near the point with `Δ h = 0`). -/
theorem exists_harmonic_of_eigen {C : ℝ} (hC : D.HasTraceIneq C) {τ : ℝ} {x : D.H1}
    (hx : IsWeakSteklovEigenDom D τ x) :
    ∃ h : ℂ → ℝ, HarmonicOnNhd h D.carrier ∧ ((x : D.Amb).fst : ℂ → ℝ) =ᵐ[D.μ] h := by
  have hBm : MeasurableSet D.carrier := D.isOpen.measurableSet
  set F := D.carrier.indicator ((x : D.Amb).fst : ℂ → ℝ) with hF
  set G := D.carrier.indicator ((x : D.Amb).snd : ℂ → ℂ) with hG
  have hFL : MemLp F 2 volume := (memLp_indicator_iff_restrict hBm).2 (Lp.memLp _)
  have hFm : StronglyMeasurable F := (Lp.stronglyMeasurable _).indicator hBm
  have hGL : MemLp G 2 volume := (memLp_indicator_iff_restrict hBm).2 (Lp.memLp _)
  obtain ⟨h, hharm, hae⟩ := SteklovWeyl.weyl_lemma D.isOpen hFL hFm
    (hGL.locallyIntegrable one_le_two) (D.weak_gradient_indicator x)
    (fun φ h1 _ h3 => D.weakly_harmonic_of_eigen hC hx φ h1 h3)
  refine ⟨h, hharm, ?_⟩
  have hmem : ∀ᵐ t ∂D.μ, t ∈ D.carrier := ae_restrict_mem hBm
  filter_upwards [hae, hmem] with t ht htm
  rw [← ht, hF, indicator_of_mem htm]

/-- **Interior regularity, with gradients.** A weak Steklov eigenfunction `x = (f, g) ∈ H¹(Ω)`
has a representative `h` harmonic on `Ω` with `f = h` and `g = ∇h` almost everywhere on `Ω`. -/
theorem exists_harmonic_grad_of_eigen {C : ℝ} (hC : D.HasTraceIneq C) {τ : ℝ} {x : D.H1}
    (hx : IsWeakSteklovEigenDom D τ x) :
    ∃ h : ℂ → ℝ, HarmonicOnNhd h D.carrier ∧ ((x : D.Amb).fst : ℂ → ℝ) =ᵐ[D.μ] h ∧
      ((x : D.Amb).snd : ℂ → ℂ) =ᵐ[D.μ] grad h := by
  obtain ⟨h, hharm, hae⟩ := D.exists_harmonic_of_eigen hC hx
  refine ⟨h, hharm, hae, ?_⟩
  have hBm : MeasurableSet D.carrier := D.isOpen.measurableSet
  have hGL : MemLp (D.carrier.indicator ((x : D.Amb).snd : ℂ → ℂ)) 2 volume :=
    (memLp_indicator_iff_restrict hBm).2 (Lp.memLp _)
  have hmem : ∀ᵐ t ∂D.μ, t ∈ D.carrier := ae_restrict_mem hBm
  have hFh : D.carrier.indicator ((x : D.Amb).fst : ℂ → ℝ) =ᵐ[volume.restrict D.carrier] h := by
    filter_upwards [hae, hmem] with t ht htm
    rw [indicator_of_mem htm, ht]
  have hgr := SteklovWeyl.weak_gradient_ae_eq_grad D.isOpen (hGL.locallyIntegrable one_le_two)
    (D.weak_gradient_indicator x) (fun z hz => (hharm z hz).1.of_le (by norm_num)) hFh
  filter_upwards [hgr, hmem] with t ht htm
  rw [← ht, indicator_of_mem htm]

end BddDomain

/-- **Interior regularity on the constructed domains `Ω = G(𝔻)`.** For a conformal map `c`
(holomorphic and injective on a neighbourhood of the closed disk, `G' ≠ 0` there), every weak
Steklov eigenfunction on `Ω = G(𝔻)` is a.e. equal on `Ω` to a classical harmonic function on `Ω`. -/
theorem ConfMap.exists_harmonic_of_eigen (c : ConfMap) {τ : ℝ} {x : c.dom.H1}
    (hx : IsWeakSteklovEigenDom c.dom τ x) :
    ∃ h : ℂ → ℝ, HarmonicOnNhd h c.dom.carrier ∧ ((x : c.dom.Amb).fst : ℂ → ℝ) =ᵐ[c.dom.μ] h := by
  obtain ⟨C, hC⟩ := c.exists_hasTraceIneq
  exact c.dom.exists_harmonic_of_eigen hC hx

/-- **Interior regularity with gradients on `Ω = G(𝔻)`.** -/
theorem ConfMap.exists_harmonic_grad_of_eigen (c : ConfMap) {τ : ℝ} {x : c.dom.H1}
    (hx : IsWeakSteklovEigenDom c.dom τ x) :
    ∃ h : ℂ → ℝ, HarmonicOnNhd h c.dom.carrier ∧
      ((x : c.dom.Amb).fst : ℂ → ℝ) =ᵐ[c.dom.μ] h ∧
      ((x : c.dom.Amb).snd : ℂ → ℂ) =ᵐ[c.dom.μ] grad h := by
  obtain ⟨C, hC⟩ := c.exists_hasTraceIneq
  exact c.dom.exists_harmonic_grad_of_eigen hC hx

end SteklovH1
