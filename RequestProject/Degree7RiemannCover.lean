module

public import RequestProject.Degree7CommonCover
public import RequestProject.LocalHomeoRiemann

/-!
# The common regular cover is a Riemann surface; analytic deck group and quotient maps

For `s² = -7` and any ordering `f₀` of a fibre of `p_s ⊔ p_{-s}` over `ℂ \ {0,1}`, the regular
cover `R = RegCov f₀` (the Galois closure built in `Degree7CommonCover.lean`) carries the complex
structure pulled back from `ℂ` by its projection (`regCov_riemannSurface`):

* `R` is a complex-analytic one-dimensional manifold whose charts are restrictions of the
  projection `R → ℂ \ {0,1} ⊆ ℂ`;
* the projection is analytic, every deck transformation `regAct f₀ σ` is analytic (hence
  biholomorphic, with analytic inverse `regAct f₀ σ⁻¹`);
* every continuous map `ev₁ : R → p_s⁻¹(ℂ \ {0,1})` over the base, in particular the quotient
  coordinate maps of `Degree7.common_regular_cover`, is holomorphic as a map to `ℂ`; likewise for
  `p_{-s}`.  (Their fibres are the orbits of the point/line stabilizers, by
  `Degree7.common_regular_cover`.)

This is the analytic structure on the **unbranched** part only; the completion over the branch
values and over the boundary is not constructed here.
-/

@[expose] public section

open Polynomial Set PolyCover SteklovRegularCover SteklovRiemann Topology Manifold
open scoped ContDiff

noncomputable section

namespace Degree7

variable {s : ℂ}

/-- The projection of the regular cover to `ℂ`. -/
def coverProjC (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) : RegCov f₀ → ℂ :=
  fun f => ((regProj (p := projSum hs) f₀ f : Base (pPoly s)) : ℂ)

lemma isOpen_base (hs : s ^ 2 = -7) : IsOpen ((critVals (pPoly s))ᶜ : Set ℂ) :=
  (critVals_finite (pPoly_degree_pos hs)).isClosed.isOpen_compl

lemma isLocalHomeomorph_coverProjC (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    IsLocalHomeomorph (coverProjC hs f₀) := by
  haveI := locPathConnectedSpace_base hs
  show IsLocalHomeomorph (Subtype.val ∘ regProj f₀)
  exact (isOpen_base hs).isOpenEmbedding_subtypeVal.isLocalHomeomorph.comp
    (isCoveringMap_regProj (isCoveringMap_projSum hs) f₀).isLocalHomeomorph

lemma derivative_ne_zero_of_total {P : ℂ[X]} (z : Total P) :
    deriv (fun w => P.eval w) (z : ℂ) ≠ 0 := by
  rw [Polynomial.deriv]
  intro h
  exact z.2 ⟨z, h, rfl⟩

/-- **The common regular cover is a Riemann surface**, with analytic projection, analytic deck
transformations and holomorphic quotient coordinate maps to both degree-`7` covers. -/
theorem regCov_riemannSurface (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    ∃ _ : ChartedSpace ℂ (RegCov f₀), IsManifold 𝓘(ℂ) ω (RegCov f₀) ∧
      ChartsAre (RegCov f₀) (coverProjC hs f₀) ∧
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (coverProjC hs f₀) ∧
      (∀ σ : deckGroup f₀, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (regAct f₀ σ)) ∧
      (∀ ev₁ : RegCov f₀ → Total (pPoly s), Continuous ev₁ →
        (∀ f, proj (pPoly s) (ev₁ f) = regProj f₀ f) →
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun f => (ev₁ f : ℂ))) ∧
      (∀ ev₂ : RegCov f₀ → Total (pPoly (-s)), Continuous ev₂ →
        (∀ f, proj₂ hs (ev₂ f) = regProj f₀ f) →
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (fun f => (ev₂ f : ℂ))) := by
  have hπ := isLocalHomeomorph_coverProjC hs f₀
  letI := lhChartedSpace hπ
  have hc : ChartsAre (RegCov f₀) (coverProjC hs f₀) := chartsAre_lhChartedSpace hπ
  have hπc : Continuous (coverProjC hs f₀) := hπ.continuous
  refine ⟨lhChartedSpace hπ, isManifold_of_chartsAre hc, hc, contMDiff_proj hc hπc,
    fun σ => ?_, fun ev₁ hev hcomp => ?_, fun ev₂ hev hcomp => ?_⟩
  · refine contMDiff_of_comp_eq hc hc (continuous_regAct f₀ σ) fun f => ?_
    simp only [coverProjC, regProj_regAct]
  · refine contMDiff_of_comp_eq_holo hc (continuous_subtype_val.comp hev)
      (F := fun w => (pPoly s).eval w) (fun f => (pPoly s).differentiableAt)
      (fun f => derivative_ne_zero_of_total (ev₁ f)) fun f => ?_
    have := congrArg Subtype.val (hcomp f)
    first
      | simpa [coverProjC] using this
      | simpa [coverProjC, Function.comp_def] using this
  · refine contMDiff_of_comp_eq_holo hc (continuous_subtype_val.comp hev)
      (F := fun w => (pPoly (-s)).eval w) (fun f => (pPoly (-s)).differentiableAt)
      (fun f => derivative_ne_zero_of_total (ev₂ f)) fun f => ?_
    have := congrArg Subtype.val (hcomp f)
    first
      | simpa [coverProjC] using this
      | simpa [coverProjC, Function.comp_def] using this

end Degree7
