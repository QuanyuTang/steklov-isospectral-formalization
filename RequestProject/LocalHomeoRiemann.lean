module

public import Mathlib

/-!
# Riemann surface structure pulled back by a local homeomorphism to `ℂ`

If `π : E → ℂ` is a local homeomorphism, the restrictions of `π` to open sets on which it is a
homeomorphism onto an open set form an atlas (`lhChartedSpace`); all transition maps are
restrictions of the identity, so `E` is a complex-analytic (`C^ω` over `ℂ`) one-dimensional
manifold, i.e. a Riemann surface (`isManifold_of_chartsAre`).  Moreover (`ChartsAre π`):

* `contMDiff_of_comp_eq`: a continuous map `f : E → E'` between two such surfaces with
  `π' ∘ f = π` is complex-analytic (in charts it is the identity); in particular deck
  transformations of a cover are analytic;
* `contMDiff_proj`: `π` itself is analytic;
* `mdifferentiable_of_comp_eq_poly`: a continuous `g : E → ℂ` with `F ∘ g = π` for a holomorphic
  `F` with `F' ≠ 0` along `g` is holomorphic (inverse function theorem in charts).
-/

@[expose] public section

open Set Topology Manifold Filter
open scoped ContDiff

noncomputable section

namespace SteklovRiemann

variable {E : Type*} [TopologicalSpace E] {π : E → ℂ}

/-- The atlas of a local homeomorphism `π : E → ℂ`: all open partial homeomorphisms that are
restrictions of `π`. -/
def lhChartedSpace (hπ : IsLocalHomeomorph π) : ChartedSpace ℂ E where
  atlas := {e | ⇑e = π}
  chartAt x := Classical.choose (hπ x)
  mem_chart_source x := (Classical.choose_spec (hπ x)).1
  chart_mem_atlas x := (Classical.choose_spec (hπ x)).2.symm

/-- All charts of the charted space are restrictions of `π`. -/
def ChartsAre (E : Type*) [TopologicalSpace E] [ChartedSpace ℂ E] (π : E → ℂ) : Prop :=
  ∀ e ∈ atlas ℂ E, ⇑e = π

lemma chartsAre_lhChartedSpace (hπ : IsLocalHomeomorph π) :
    @ChartsAre E _ (lhChartedSpace hπ) π := fun _ he => he

section Charts

variable [ChartedSpace ℂ E]

lemma ChartsAre.chartAt (h : ChartsAre E π) (x : E) : ⇑(chartAt ℂ x) = π :=
  h _ (chart_mem_atlas ℂ x)

lemma ChartsAre.apply_symm (h : ChartsAre E π) {e : OpenPartialHomeomorph E ℂ}
    (he : e ∈ atlas ℂ E) {z : ℂ} (hz : z ∈ e.target) : π (e.symm z) = z := by
  rw [← h e he]; exact e.right_inv hz

/-- **The pulled-back atlas is complex-analytic**: `E` is a Riemann surface. -/
theorem isManifold_of_chartsAre (h : ChartsAre E π) : IsManifold 𝓘(ℂ) ω E := by
  refine isManifold_of_contDiffOn _ _ _ fun e e' he he' => ?_
  refine contDiff_id.contDiffOn.congr fun z hz => ?_
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply,
    preimage_id_eq, id_eq] at hz ⊢
  rw [OpenPartialHomeomorph.trans_source] at hz
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, h e' he', h.apply_symm he hz.1.1]

end Charts

section Maps

variable [ChartedSpace ℂ E] {E' : Type*} [TopologicalSpace E'] [ChartedSpace ℂ E'] {π' : E' → ℂ}

/-- **Maps over the base are analytic**: if `π' ∘ f = π`, then `f` is `C^ω` (in charts it is the
identity). -/
theorem contMDiff_of_comp_eq (h : ChartsAre E π) (h' : ChartsAre E' π') {f : E → E'}
    (hf : Continuous f) (hcomp : ∀ x, π' (f x) = π x) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f := by
  haveI := isManifold_of_chartsAre h
  haveI := isManifold_of_chartsAre h'
  intro x
  rw [contMDiffAt_iff]
  refine ⟨hf.continuousAt, ?_⟩
  have hev : ∀ᶠ z in 𝓝[range 𝓘(ℂ)] (extChartAt 𝓘(ℂ) x x),
      (extChartAt 𝓘(ℂ) (f x) ∘ f ∘ (extChartAt 𝓘(ℂ) x).symm) z = z := by
    rw [modelWithCornersSelf_coe, range_id, nhdsWithin_univ]
    filter_upwards [(extChartAt_target_mem_nhds (I := 𝓘(ℂ)) x)] with z hz
    simp only [extChartAt, OpenPartialHomeomorph.extend, Function.comp_apply,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, PartialEquiv.coe_trans,
      PartialEquiv.coe_trans_symm, OpenPartialHomeomorph.toFun_eq_coe, id_eq,
      ModelWithCorners.toPartialEquiv_coe, ModelWithCorners.toPartialEquiv_coe_symm,
      OpenPartialHomeomorph.coe_coe_symm, OpenPartialHomeomorph.coe_coe] at hz ⊢
    rw [h'.chartAt, hcomp]
    have hz' : z ∈ (chartAt ℂ x).target := by
      simpa [extChartAt, OpenPartialHomeomorph.extend] using hz
    exact h.apply_symm (chart_mem_atlas ℂ x) hz'
  refine (contDiffWithinAt_id.congr_of_eventuallyEq hev ?_)
  simp only [extChartAt, OpenPartialHomeomorph.extend, Function.comp_apply,
    modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, PartialEquiv.coe_trans,
    PartialEquiv.coe_trans_symm, OpenPartialHomeomorph.toFun_eq_coe, id_eq,
    ModelWithCorners.toPartialEquiv_coe, ModelWithCorners.toPartialEquiv_coe_symm,
    OpenPartialHomeomorph.coe_coe_symm, OpenPartialHomeomorph.coe_coe]
  rw [h'.chartAt, hcomp, (chartAt ℂ x).left_inv (mem_chart_source ℂ x), h.chartAt]

/-- The projection `π : E → ℂ` is analytic. -/
theorem contMDiff_proj (h : ChartsAre E π) (hπ : Continuous π) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω π :=
  contMDiff_of_comp_eq h (π' := id) (fun e he => by
    rw [chartedSpaceSelf_atlas] at he; rw [he]; rfl) hπ fun _ => rfl

/-- **Coordinate maps solving `F ∘ g = π` are holomorphic** (complex-analytic), provided `F` is
holomorphic with nonvanishing derivative along `g`: in a chart, `g ∘ e⁻¹` is a continuous local
inverse of `F`, hence holomorphic by the inverse function theorem. -/
theorem contMDiff_of_comp_eq_holo (h : ChartsAre E π) {g : E → ℂ} (hg : Continuous g)
    {F : ℂ → ℂ} (hF : ∀ x, DifferentiableAt ℂ F (g x)) (hF' : ∀ x, deriv F (g x) ≠ 0)
    (hcomp : ∀ x, F (g x) = π x) : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g := by
  haveI := isManifold_of_chartsAre h
  intro x
  rw [contMDiffAt_iff]
  refine ⟨hg.continuousAt, ?_⟩
  set e := chartAt ℂ x
  have hdiff : DifferentiableOn ℂ (g ∘ e.symm) e.target := by
    intro z hz
    have hcont : ContinuousAt (g ∘ e.symm) z :=
      hg.continuousAt.comp (e.continuousAt_symm hz)
    have hloc : ∀ᶠ y in 𝓝 z, F ((g ∘ e.symm) y) = y := by
      filter_upwards [e.open_target.mem_nhds hz] with y hy
      simp only [Function.comp_apply]
      rw [hcomp, h.apply_symm (chart_mem_atlas ℂ x) hy]
    exact (HasDerivAt.of_local_left_inverse hcont (hF _).hasDerivAt (hF' _) hloc
      ).differentiableAt.differentiableWithinAt
  have hcd : ContDiffOn ℂ ω (g ∘ e.symm) e.target := hdiff.contDiffOn e.open_target
  have hx : e x ∈ e.target := e.map_source (mem_chart_source ℂ x)
  have := (hcd.contDiffAt (e.open_target.mem_nhds hx)).contDiffWithinAt (s := range 𝓘(ℂ))
  simpa [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def] using this

end Maps

end SteklovRiemann
