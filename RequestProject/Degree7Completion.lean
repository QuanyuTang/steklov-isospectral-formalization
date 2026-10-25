module

public import RequestProject.Degree7Inertia
public import RequestProject.Degree7RiemannCover
public import RequestProject.BranchedCompletion

/-!
# The branched completion of the actual common regular cover over `ℂ`

For `s² = -7` and an ordered complete fibre `f₀` of `p_s ⊔ p_{-s}`, the regular cover
`R = RegCov f₀ → ℂ \ {0,1}` has, over the punctured disks of radius `1/2` about `0` and `1`, the
local power models `z = Φ²` and `z = 1 + Φ³` (`Degree7.regCov_local_model_zero/one`).  Filling in
the corresponding punctures (`SteklovFill`) yields the **branched completion**
`RegFill hs f₀ = Fill (regEnds hs f₀)` of `R`, an open Riemann surface with a holomorphic branched
projection `regFillProj : RegFill hs f₀ → ℂ` extending the projection of `R` and sending the added
points to the branch values `0` (local model `t ↦ t²`) and `1` (local model `t ↦ 1 + t³`)
(`regFill_riemannSurface`).
-/

@[expose] public section

open Polynomial Set PolyCover LocalMonodromy SteklovRegularCover SteklovPunctured SteklovFill
  SteklovRiemann Topology Manifold
open scoped ContDiff

noncomputable section

namespace Degree7

variable {s : ℂ}

/-- The Riemann surface structure of the unbranched regular cover (charts = its projection). -/
instance regCovCharted {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} :
    ChartedSpace ℂ (RegCov f₀) :=
  lhChartedSpace (isLocalHomeomorph_coverProjC hs f₀)

lemma chartsAre_regCov (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    ChartsAre (RegCov f₀) (coverProjC hs f₀) :=
  chartsAre_lhChartedSpace (isLocalHomeomorph_coverProjC hs f₀)

instance regCovLocPath {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13} :
    LocPathConnectedSpace (RegCov f₀) :=
  ChartedSpace.locPathConnectedSpace ℂ (RegCov f₀)

/-- The two finite branch values. -/
def cB : Bool → ℂ
  | false => 0
  | true => 1

/-- The local inertia orders over them. -/
def dB : Bool → ℕ
  | false => 2
  | true => 3

lemma dB_pos (b : Bool) : 0 < dB b := by cases b <;> decide

lemma cB_not_mem (hs : s ^ 2 = -7) (b : Bool) : cB b ∉ (critVals (pPoly s))ᶜ := by
  rw [critVals_pPoly hs]; cases b <;> simp [cB]

lemma cB_disj (b b' : Bool) (h : b ≠ b') (z : ℂ) (hz : z - cB b ∈ pdisk (1 / 2)) :
    z - cB b' ∉ pdisk (1 / 2) := by
  rintro hz'
  have h1 := hz.2
  have h2 := hz'.2
  have key : ‖cB b' - cB b‖ < 1 := by
    calc ‖cB b' - cB b‖ = ‖(z - cB b) - (z - cB b')‖ := by ring_nf
      _ ≤ ‖z - cB b‖ + ‖z - cB b'‖ := norm_sub_le _ _
      _ < 1 / 2 + 1 / 2 := add_lt_add h1 h2
      _ = 1 := by norm_num
  cases b <;> cases b' <;> simp_all [cB]

/-- The local power models over both branch values. -/
lemma regModel (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (b : Bool)
    (y : regProj f₀ ⁻¹' nbhdSet (critVals (pPoly s))ᶜ (cB b) (1 / 2)) :
    ∃ Φ : LocComp (regProj f₀) y ≃ₜ pdisk (rootRad (1 / 2) (dB b)),
      ∀ x, ((Φ x : ℂ)) ^ (dB b) = ((regProj f₀ (incl y x) : Base (pPoly s)) : ℂ) - cB b := by
  cases b
  · obtain ⟨hS, H⟩ := regCov_local_model_zero hs f₀
    obtain ⟨Φ, hΦ, -⟩ := H y
    exact ⟨Φ, hΦ⟩
  · obtain ⟨hS, H⟩ := regCov_local_model_one hs f₀
    obtain ⟨Φ, hΦ, -⟩ := H y
    exact ⟨Φ, hΦ⟩

/-- The punctured-disk ends of the actual regular cover over `0` and `1`. -/
def regEnds (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    Ends (RegCov f₀) (BIdx (regProj f₀) cB (1 / 2)) :=
  haveI := locPathConnectedSpace_base hs
  branchEnds (isCoveringMap_regProj (isCoveringMap_projSum hs) f₀) dB (regModel hs f₀) (by norm_num) (cB_not_mem hs) dB_pos
    cB_disj


/-- **The branched completion of the actual regular cover** over `ℂ`. -/
abbrev RegFill (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) : Type _ := Fill (regEnds hs f₀)

/-- Its branched projection to `ℂ`. -/
def regFillProj (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) : RegFill hs f₀ → ℂ :=
  Fill.πFill (coverProjC hs f₀) (fun j => cB j.1)

lemma regEnds_pow (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13)
    (j : BIdx (regProj f₀) cB (1 / 2)) (x : (regEnds hs f₀).U j) :
    (((regEnds hs f₀).Φ j x : pdisk _) : ℂ) ^ (dB j.1) = coverProjC hs f₀ x - cB j.1 := by
  haveI := locPathConnectedSpace_base hs
  exact branchEnds_pow (isCoveringMap_regProj (isCoveringMap_projSum hs) f₀) dB (regModel hs f₀)
    (by norm_num) (cB_not_mem hs) dB_pos cB_disj j x

/-- **The branched completion is a Riemann surface with holomorphic branched projection.**
`RegFill hs f₀` is Hausdorff and a complex-analytic one-dimensional manifold; the unbranched cover
`R` is an open subspace; the projection is holomorphic and extends that of `R`; every added point
is a cusp `j` lying over `cB j.1 ∈ {0, 1}`, with an atlas chart centred at it in which the
projection is `t ↦ cB j.1 + t^(dB j.1)` (`dB = 2` over `0`, `dB = 3` over `1`). -/
theorem regFill_riemannSurface (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    T2Space (RegFill hs f₀) ∧ IsManifold 𝓘(ℂ) ω (RegFill hs f₀) ∧
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (regFillProj hs f₀) ∧
      IsOpenEmbedding (Fill.inl : RegCov f₀ → RegFill hs f₀) ∧
      (∀ f, regFillProj hs f₀ (Fill.inl f) = coverProjC hs f₀ f) ∧
      (∀ w : RegFill hs f₀, (∃ f, w = Fill.inl f) ∨ ∃ j, w = Fill.cusp j) ∧
      ∀ j, ∃ e : OpenPartialHomeomorph (RegFill hs f₀) ℂ, e ∈ atlas ℂ (RegFill hs f₀) ∧
        Fill.cusp j ∈ e.source ∧ e (Fill.cusp j) = 0 ∧
        ∀ t ∈ e.target, regFillProj hs f₀ (e.symm t) = cB j.1 + t ^ (dB j.1) := by
  have hπ := chartsAre_regCov hs f₀
  have hpow := regEnds_pow hs f₀
  refine ⟨inferInstance, Fill.isManifold_fill hπ _ _ (fun j => dB_pos j.1) hpow,
    Fill.contMDiff_πFill hπ _ _ (fun j => dB_pos j.1) hpow, Fill.isOpenEmbedding_inl,
    fun f => rfl, fun w => ?_, fun j => ⟨Fill.cuspChart j, Or.inr ⟨j, rfl⟩, Or.inr rfl, rfl,
      fun t ht => Fill.πFill_cuspChart_symm _ _ hpow j ht (dB_pos j.1)⟩⟩
  rcases w with f | j
  · exact Or.inl ⟨f, rfl⟩
  · exact Or.inr ⟨j, rfl⟩

end Degree7
