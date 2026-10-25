module

public import Mathlib
public import RequestProject.ConformalSobolev

/-!
# `H¹(Ω) = W^{1,2}(Ω)` for `Ω = G(𝔻)`

`SteklovH1.BddDomain.IsWeakGradientPair D x`: `x = (f, g) ∈ L²(Ω) × L²(Ω; ℝ²)` and `g` is the weak
gradient of `f` on `Ω` (tested with compactly supported smooth `φ`, `tsupport φ ⊆ Ω`).

* `ConfMap.pullAmb_isWeakGradientPair` (**weak chain rule**): if `(f, g)` is a weak-gradient pair
  on `Ω = G(𝔻)`, then `(f ∘ G, conj(G') · g ∘ G)` is a weak-gradient pair on `𝔻`. The proof
  mollifies `f` (the gradient of the mollification is the mollified weak gradient on compact
  subsets of `Ω`), applies the smooth chain rule and passes to the limit using the `L²` bounds of
  the pullback.
* `ConfMap.mem_H1_iff_isWeakGradientPair`: for `Ω = G(𝔻)`, the closure-of-smooth-graphs space
  `H¹(Ω)` coincides with the weak-gradient space `W^{1,2}(Ω)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Real ComplexConjugate

noncomputable section

namespace SteklovH1

/-- `(f, g)` is a **weak-gradient pair** on the domain `D`: `∫_Ω f ∂_v φ = -∫_Ω ⟨g, v⟩ φ` for all
compactly supported smooth `φ` with `tsupport φ ⊆ Ω` and all `v`. -/
def BddDomain.IsWeakGradientPair (D : BddDomain) (x : D.Amb) : Prop :=
  ∀ φ : ℂ → ℝ, D.IsTest φ → ∀ v : ℂ,
    ∫ z in D.carrier, x.fst z * fderiv ℝ φ z v = - ∫ z in D.carrier, inner ℝ (x.snd z) v * φ z

namespace ConfMap

open SteklovDensity

variable (c : ConfMap)

lemma memLp_testfun {w : ℂ → ℝ} (hw : Continuous w) : MemLp w 2 μD := memLp_disk hw

/-- **Weak chain rule** for the conformal map `G`. -/
theorem pullAmb_isWeakGradientPair (x : c.dom.Amb) (hx : c.dom.IsWeakGradientPair x) :
    IsWeakGradientPair (c.pullAmb x) := by
  intro φ hφ v
  set f := x.fst
  set g := x.snd
  set Ω := c.Ω
  have hΩm : MeasurableSet Ω := c.measurableSet_Ω
  set F : ℂ → ℝ := Ω.indicator (f : ℂ → ℝ) with hFdef
  set Gg : ℂ → ℂ := Ω.indicator (g : ℂ → ℂ) with hGdef
  have hFm : StronglyMeasurable F := (Lp.stronglyMeasurable f).indicator hΩm
  have hGm : StronglyMeasurable Gg := (Lp.stronglyMeasurable g).indicator hΩm
  have hFL : MemLp F 2 volume := (memLp_indicator_iff_restrict hΩm).2 (Lp.memLp f)
  have hGL : MemLp Gg 2 volume := (memLp_indicator_iff_restrict hΩm).2 (Lp.memLp g)
  have hFl := hFL.locallyIntegrable one_le_two
  have hGl := hGL.locallyIntegrable one_le_two
  -- the weak identity on the whole plane
  have hwF : ∀ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ Ω →
      ∀ v : ℂ, ∫ t, F t * fderiv ℝ ψ t v = - ∫ t, inner ℝ (Gg t) v * ψ t := by
    intro ψ h1 h2 h3 v
    have e1 : (fun t => F t * fderiv ℝ ψ t v) = Ω.indicator (fun t => f t * fderiv ℝ ψ t v) := by
      funext t; by_cases ht : t ∈ Ω <;> simp [hFdef, ht]
    have e2 : (fun t => inner ℝ (Gg t) v * ψ t) = Ω.indicator (fun t => inner ℝ (g t) v * ψ t) := by
      funext t; by_cases ht : t ∈ Ω <;> simp [hGdef, ht]
    rw [e1, e2, integral_indicator hΩm, integral_indicator hΩm]
    exact hx ψ ⟨h1, h2, h3⟩ v
  -- the compact set `K = G(tsupport φ)` and a margin `δ`
  have hK : IsCompact (c.G '' tsupport φ) :=
    hφ.2.1.isCompact.image_of_continuousOn (c.diff.continuousOn.mono (hφ.2.2.trans c.ball_sub))
  have hKΩ : c.G '' tsupport φ ⊆ Ω := image_mono hφ.2.2
  obtain ⟨δ, hδ, hδK⟩ := hK.exists_cthickening_subset_open c.isOpen_Ω hKΩ
  -- test vectors in `L²(𝔻)`
  have hφ1 := hφ.contDiff_one
  have hcφ : Continuous φ := hφ1.continuous
  have hcφ' : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv one_ne_zero
  have hψ₁ : MemLp (fun z => fderiv ℝ φ z v) 2 μD := memLp_disk (by fun_prop)
  have hψ₂ : MemLp (fun z => φ z • v) 2 μD := memLp_disk (by fun_prop)
  set ψ₁ := hψ₁.toLp _
  set ψ₂ := hψ₂.toLp _
  -- the functionals
  set A : Lp ℝ 2 c.dom.μ → ℝ := fun h => inner ℝ (c.pullF h) ψ₁ with hA
  set B : Lp ℂ 2 c.dom.μ → ℝ := fun k => inner ℝ (c.pullG k) ψ₂ with hB
  have hAf : A f = ∫ z in ball (0:ℂ) 1, (c.pullAmb x).fst z * fderiv ℝ φ z v := by
    rw [hA]; simp only; rw [inner_toLp_real]; rfl
  have hBg : B g = ∫ z in ball (0:ℂ) 1, inner ℝ ((c.pullAmb x).snd z) v * φ z := by
    rw [hB]; simp only; rw [inner_toLp_smul]; rfl
  rw [← hAf, ← hBg]
  -- bounds
  obtain ⟨C, hC0, hCF, hCG, -, -⟩ := c.exists_C
  have hAb : ∀ h, |A h| ≤ C * ‖ψ₁‖ * ‖h‖ := fun h => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖c.pullF h‖ * ‖ψ₁‖ ≤ C * ‖h‖ * ‖ψ₁‖ := mul_le_mul_of_nonneg_right (hCF h) (norm_nonneg _)
      _ = _ := by ring
  have hBb : ∀ k, |B k| ≤ C * ‖ψ₂‖ * ‖k‖ := fun k => by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖c.pullG k‖ * ‖ψ₂‖ ≤ C * ‖k‖ * ‖ψ₂‖ := mul_le_mul_of_nonneg_right (hCG k) (norm_nonneg _)
      _ = _ := by ring
  have hAlin : ∀ h h', A (h - h') = A h - A h' := fun h h' => by
    simp only [hA, map_sub, inner_sub_left]
  have hBlin : ∀ k k', B (k - k') = B k - B k' := fun k k' => by
    simp only [hB, map_sub, inner_sub_left]
  -- the identity for mollified functions
  have hmoll : ∀ b : ContDiffBump (0 : ℂ), b.rOut ≤ δ →
      ∃ fb : Lp ℝ 2 c.dom.μ, ∃ gb : Lp ℂ 2 c.dom.μ, A fb = - B gb ∧
        (fb : ℂ → ℝ) =ᵐ[c.dom.μ] moll b F ∧ (gb : ℂ → ℂ) =ᵐ[c.dom.μ] moll b Gg := by
    intro b hb
    have hsm : moll b F ∈ smoothFns := contDiff_moll b hFl
    set u : smoothFns := ⟨moll b F, hsm⟩
    have hgc : Continuous (moll b Gg) := continuous_moll b hGl
    refine ⟨c.dom.toL2 u, (c.dom.memLp_dom hgc).toLp _, ?_, c.dom.toL2_ae u,
      (c.dom.memLp_dom hgc).coeFn_toLp⟩
    set w := c.pullSmooth u
    have hibp := ibp_disk (contDiff_one_of_mem w.2) hφ v
    have e1 : A (c.dom.toL2 u) = ∫ z in ball (0:ℂ) 1, (w : ℂ → ℝ) z * fderiv ℝ φ z v := by
      rw [hA]; simp only; rw [inner_toLp_real]
      refine integral_congr_ae ?_
      filter_upwards [c.pullF_ae (c.dom.toL2 u), c.ae_comp (c.dom.toL2_ae u),
        ae_restrict_mem measurableSet_ball] with z h1 h2 hz
      rw [h1, h2, ((c.pullSmooth_eventually u (ball_subset_closedBall hz)).eq_of_nhds)]
    have e2 : B ((c.dom.memLp_dom hgc).toLp _) =
        ∫ z in ball (0:ℂ) 1, fderiv ℝ (w : ℂ → ℝ) z v * φ z := by
      rw [hB]; simp only; rw [inner_toLp_smul]
      refine integral_congr_ae ?_
      filter_upwards [c.pullG_ae ((c.dom.memLp_dom hgc).toLp _),
        c.ae_comp (c.dom.memLp_dom hgc).coeFn_toLp, ae_restrict_mem measurableSet_ball]
        with z h1 h2 hz
      rw [h1, h2, ← inner_grad, c.grad_pullSmooth u (ball_subset_closedBall hz)]
      by_cases hφz : φ z = 0
      · simp [hφz]
      · have hzK : c.G z ∈ c.G '' tsupport φ := ⟨z, subset_tsupport _ hφz, rfl⟩
        have hball : closedBall (c.G z) b.rOut ⊆ Ω :=
          ((closedBall_subset_closedBall hb).trans (closedBall_subset_cthickening hzK δ)).trans hδK
        rw [show grad (u : ℂ → ℝ) (c.G z) = moll b Gg (c.G z) from
          grad_moll Ω hFl hGl hwF b (c.G z) hball, mul_comm ((starRingEnd ℂ) _) (moll b Gg _)]
    rw [e1, e2, hibp]
  -- conclude by an `ε`-argument
  set K₁ := C * ‖ψ₁‖
  set K₂ := C * ‖ψ₂‖
  have hK₁ : 0 ≤ K₁ := by positivity
  have hK₂ : 0 ≤ K₂ := by positivity
  have key : ∀ ε > 0, |A f + B g| ≤ ε := by
    intro ε hε
    set ε' := ε / (K₁ + K₂ + 1) with hε'
    have hε'0 : 0 < ε' := by positivity
    obtain ⟨δ₁, hδ₁, hmF⟩ := moll_tendsto hFL hFm hε'0
    obtain ⟨δ₂, hδ₂, hmG⟩ := moll_tendsto hGL hGm hε'0
    set r := min (min δ₁ δ₂) δ / 2 with hr
    have hr0 : 0 < r := by positivity
    have hrm : r < min (min δ₁ δ₂) δ := by rw [hr]; linarith [lt_min (lt_min hδ₁ hδ₂) hδ]
    let b : ContDiffBump (0 : ℂ) := ⟨r / 2, r, by positivity, by linarith⟩
    have hb1 : b.rOut < δ₁ := hrm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
    have hb2 : b.rOut < δ₂ := hrm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
    have hb3 : b.rOut ≤ δ := (hrm.trans_le (min_le_right _ _)).le
    obtain ⟨fb, gb, hid, hfb, hgb⟩ := hmoll b hb3
    have hnf : ‖f - fb‖ ≤ ε' := by
      rw [Lp.norm_def]
      refine ENNReal.toReal_le_of_le_ofReal hε'0.le ?_
      have hae : ((f - fb : Lp ℝ 2 c.dom.μ) : ℂ → ℝ) =ᵐ[c.dom.μ] F - moll b F := by
        filter_upwards [Lp.coeFn_sub f fb, hfb, ae_restrict_mem hΩm] with z h1 h2 h3
        rw [h1, Pi.sub_apply, h2, Pi.sub_apply, hFdef, Set.indicator_of_mem (show z ∈ Ω from h3)]
      rw [eLpNorm_congr_ae hae]
      exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hmF b hb1)
    have hng : ‖g - gb‖ ≤ ε' := by
      rw [Lp.norm_def]
      refine ENNReal.toReal_le_of_le_ofReal hε'0.le ?_
      have hae : ((g - gb : Lp ℂ 2 c.dom.μ) : ℂ → ℂ) =ᵐ[c.dom.μ] Gg - moll b Gg := by
        filter_upwards [Lp.coeFn_sub g gb, hgb, ae_restrict_mem hΩm] with z h1 h2 h3
        rw [h1, Pi.sub_apply, h2, Pi.sub_apply, hGdef, Set.indicator_of_mem (show z ∈ Ω from h3)]
      rw [eLpNorm_congr_ae hae]
      exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans (hmG b hb2)
    have hsplit : A f + B g = A (f - fb) + B (g - gb) := by
      rw [hAlin, hBlin, hid]; ring
    rw [hsplit]
    calc |A (f - fb) + B (g - gb)| ≤ |A (f - fb)| + |B (g - gb)| := abs_add_le _ _
      _ ≤ K₁ * ‖f - fb‖ + K₂ * ‖g - gb‖ := add_le_add (hAb _) (hBb _)
      _ ≤ K₁ * ε' + K₂ * ε' := add_le_add (mul_le_mul_of_nonneg_left hnf hK₁)
          (mul_le_mul_of_nonneg_left hng hK₂)
      _ ≤ ε := by
          rw [← add_mul, hε', mul_div_assoc']
          rw [div_le_iff₀ (by positivity)]
          nlinarith
  have h0 : A f + B g = 0 := by
    by_contra hne
    have := key (|A f + B g| / 2) (by positivity)
    linarith [abs_pos.2 hne]
  linarith

/-- **`H¹(Ω) = W^{1,2}(Ω)` for `Ω = G(𝔻)`**: an element of `L²(Ω) ⊕ L²(Ω; ℝ²)` lies in the closure
of the smooth graphs iff its second component is the weak gradient of the first. -/
theorem mem_H1_iff_isWeakGradientPair (x : c.dom.Amb) :
    x ∈ c.dom.H1 ↔ c.dom.IsWeakGradientPair x := by
  constructor
  · intro hx φ hφ v
    exact c.dom.weak_gradient ⟨x, hx⟩ hφ v
  · intro hx
    have h1 : c.pullAmb x ∈ H1 :=
      (SteklovH1.mem_H1_iff_isWeakGradientPair _).2 (c.pullAmb_isWeakGradientPair x hx)
    have h2 := c.pushAmb_mem ⟨_, h1⟩
    simpa [c.pushAmb_pullAmb] using h2

end ConfMap

end SteklovH1
