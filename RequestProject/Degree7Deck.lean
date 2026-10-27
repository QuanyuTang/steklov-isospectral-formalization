module

public import RequestProject.Degree7Proper
public import RequestProject.FillMap

/-!
# The deck action on the branched completion of the actual regular cover

Every deck transformation `regAct f₀ σ` (`σ ∈ deckGroup f₀ ≅ GL(3, 𝔽₂)`) of the unbranched regular
cover `R = RegCov f₀` extends to the branched completion `RegFill hs f₀`, permuting the added points
over `0` and over `1` (`regFillAct`).  We prove (`regFill_deckAction`):

* the extension is holomorphic and a homeomorphism (`regFillHomeo`), it extends `regAct f₀ σ`,
  commutes with the branched projection `regFillProj`, and preserves the branch value of every
  added point;
* it is a right action: `regFillAct 1 = id`, `regFillAct (σ * τ) = regFillAct τ ∘ regFillAct σ`;
* in the cusp chart at an added point over `cB i` it is the rotation `t ↦ ζ t` with
  `ζ^(dB i) = 1`;
* it is free at every point not lying over a branch value `0`, `1` (in particular on the preimage
  of any circle avoiding `0` and `1`).
-/

@[expose] public section

open Polynomial Set PolyCover LocalMonodromy SteklovRegularCover SteklovPunctured SteklovFill
  SteklovRiemann Topology Manifold
open scoped ContDiff

noncomputable section

namespace Degree7

variable {s : ℂ}

/-- The induced permutation of the added points. -/
def cuspAct (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (σ : deckGroup f₀) :
    BIdx (regProj f₀) cB (1 / 2) → BIdx (regProj f₀) cB (1 / 2) :=
  bMap (regAct f₀ σ) (regProj_regAct f₀ σ)

/-- **The extended deck transformation** of the branched completion. -/
def regFillAct (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (σ : deckGroup f₀) :
    RegFill hs f₀ → RegFill hs f₀ :=
  Fill.map (regAct f₀ σ) (cuspAct hs f₀ σ)

lemma endCompat_regAct (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (σ : deckGroup f₀) :
    Fill.EndCompat (regEnds hs f₀) (regAct f₀ σ) (cuspAct hs f₀ σ) := by
  haveI := locPathConnectedSpace_base hs
  exact endCompat_bMap (isCoveringMap_regProj (isCoveringMap_projSum hs) f₀) dB (regModel hs f₀)
    (by norm_num) (cB_not_mem hs) dB_pos cB_disj (continuous_regAct f₀ σ) (regProj_regAct f₀ σ)

lemma coverProjC_regAct (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (σ : deckGroup f₀)
    (f : RegCov f₀) : coverProjC hs f₀ (regAct f₀ σ f) = coverProjC hs f₀ f := by
  simp only [coverProjC, regProj_regAct]

lemma continuous_regFillAct (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13)
    (σ : deckGroup f₀) : Continuous (regFillAct hs f₀ σ) :=
  Fill.continuous_map (continuous_regAct f₀ σ) (endCompat_regAct hs f₀ σ)

lemma regFillAct_one (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    regFillAct hs f₀ 1 = id := by
  funext w
  rcases w with f | j
  · rfl
  · show Fill.cusp (cuspAct hs f₀ 1 j) = Fill.cusp j
    congr 1
    exact bMap_id j

lemma regFillAct_mul (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (σ τ : deckGroup f₀) :
    regFillAct hs f₀ (σ * τ) = regFillAct hs f₀ τ ∘ regFillAct hs f₀ σ := by
  funext w
  rcases w with f | j
  · rfl
  · show Fill.cusp (cuspAct hs f₀ (σ * τ) j) = Fill.cusp (cuspAct hs f₀ τ (cuspAct hs f₀ σ j))
    congr 1
    exact bMap_comp (continuous_regAct f₀ τ) (regProj_regAct f₀ τ) (regProj_regAct f₀ σ) j

/-- The extended deck transformation as a homeomorphism. -/
def regFillHomeo (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (σ : deckGroup f₀) :
    RegFill hs f₀ ≃ₜ RegFill hs f₀ where
  toFun := regFillAct hs f₀ σ
  invFun := regFillAct hs f₀ σ⁻¹
  left_inv w := by
    show (regFillAct hs f₀ σ⁻¹ ∘ regFillAct hs f₀ σ) w = w
    rw [← regFillAct_mul, mul_inv_cancel, regFillAct_one]; rfl
  right_inv w := by
    show (regFillAct hs f₀ σ ∘ regFillAct hs f₀ σ⁻¹) w = w
    rw [← regFillAct_mul, inv_mul_cancel, regFillAct_one]; rfl
  continuous_toFun := continuous_regFillAct hs f₀ σ
  continuous_invFun := continuous_regFillAct hs f₀ σ⁻¹

/-- **The deck action on the branched completion.** -/
theorem regFill_deckAction (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    (∀ σ, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (regFillAct hs f₀ σ)) ∧
    (∀ σ, Continuous (regFillAct hs f₀ σ) ∧ Function.Bijective (regFillAct hs f₀ σ)) ∧
    (∀ σ f, regFillAct hs f₀ σ (Fill.inl f) = Fill.inl (regAct f₀ σ f)) ∧
    (∀ σ w, regFillProj hs f₀ (regFillAct hs f₀ σ w) = regFillProj hs f₀ w) ∧
    (∀ σ j, regFillAct hs f₀ σ (Fill.cusp j) = Fill.cusp (cuspAct hs f₀ σ j) ∧
      (cuspAct hs f₀ σ j).1 = j.1) ∧
    regFillAct hs f₀ 1 = id ∧
    (∀ σ τ, regFillAct hs f₀ (σ * τ) = regFillAct hs f₀ τ ∘ regFillAct hs f₀ σ) ∧
    (∀ σ j, ∃ ζ : ℂ, ζ ^ (dB j.1) = 1 ∧ ∀ t ∈ Metric.ball (0 : ℂ) ((regEnds hs f₀).r j),
      Fill.cuspChart (cuspAct hs f₀ σ j) (regFillAct hs f₀ σ ((Fill.cuspChart j).symm t)) =
        ζ * t) ∧
    (∀ σ w, regFillProj hs f₀ w ≠ 0 → regFillProj hs f₀ w ≠ 1 →
      regFillAct hs f₀ σ w = w → σ = 1) := by
  have hπ := chartsAre_regCov hs f₀
  have hpow := regEnds_pow hs f₀
  have hcb : ∀ σ (j : BIdx (regProj f₀) cB (1 / 2)), cB (cuspAct hs f₀ σ j).1 = cB j.1 :=
    fun _ _ => rfl
  have hdb : ∀ σ (j : BIdx (regProj f₀) cB (1 / 2)), dB (cuspAct hs f₀ σ j).1 = dB j.1 :=
    fun _ _ => rfl
  refine ⟨fun σ => ?_, fun σ => ⟨continuous_regFillAct hs f₀ σ,
      (regFillHomeo hs f₀ σ).bijective⟩, fun σ f => rfl,
    fun σ w => Fill.πFill_map _ _ (coverProjC_regAct hs f₀ σ) (hcb σ) w,
    fun σ j => ⟨rfl, rfl⟩, regFillAct_one hs f₀, regFillAct_mul hs f₀, fun σ j => ?_,
    fun σ w h0 h1 hw => ?_⟩
  · haveI := Fill.isManifold_fill hπ _ _ (fun (j : BIdx (regProj f₀) cB (1 / 2)) => dB_pos j.1) hpow
    exact Fill.contMDiff_map (E := regEnds hs f₀) (fun j => cB j.1) (fun j => dB j.1) (fun j => dB_pos j.1) hpow
      (continuous_regAct f₀ σ) (endCompat_regAct hs f₀ σ) (coverProjC_regAct hs f₀ σ) (hcb σ)
      (hdb σ) hπ
  · exact Fill.exists_rotation (E := regEnds hs f₀) (fun j => cB j.1) (fun j => dB j.1)
      (fun j => dB_pos j.1) hpow
      (continuous_regAct f₀ σ) (endCompat_regAct hs f₀ σ) (coverProjC_regAct hs f₀ σ) (hcb σ)
      (hdb σ) j
  · rcases w with f | j
    · exact regAct_eq_self (Fill.inl_injective hw)
    · exfalso
      rcases j with ⟨i, P⟩
      cases i
      · exact h0 rfl
      · exact h1 rfl

end Degree7
