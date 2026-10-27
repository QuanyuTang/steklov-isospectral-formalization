module

public import Mathlib
public import RequestProject.AnalyticWeight

/-!
# Weak = classical Steklov eigenfunctions on the constructed domains `Ω = G(𝔻)`

For conformal data `c : SteklovH1.ConfMap` (`G` holomorphic and injective on an open `U ⊇ 𝔻̄`,
`G' ≠ 0` on `U`) and `Ω = G(𝔻)`:

* `ConfMap.weak_eigen_classical_dom`: every weak Steklov eigenfunction `x ∈ H¹(Ω)`
  (`∫_Ω ⟨∇x, ∇y⟩ = τ ∫_{∂Ω} Tx Ty dH¹` for all `y ∈ H¹(Ω)`) is the class of a globally smooth
  function `v` which is **harmonic on an open neighbourhood of `Ω̄ = G(𝔻̄)`** and satisfies the
  **classical Steklov condition** `∂_ν v = τ v` at every boundary point `G(e^{iθ})`, `ν` the
  outward unit normal;
* `ConfMap.isWeakSteklovEigenDom_iff_classical`: conversely such classical eigenfunctions are weak
  eigenfunctions, so the weak and the classical eigenproblems coincide;
* `ConfMap.classical_spectral_theorem_dom`: the classical Steklov spectrum of `Ω`, with
  multiplicities, is the Steklov spectrum `Steklov.steklovSpectrum Ω`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Real InnerProductSpace
open scoped ContDiff ComplexConjugate

noncomputable section

namespace SteklovH1

/-- Two smooth functions have the same `H¹(Ω)` class iff they agree on `Ω`; so an `H¹(Ω)` class
of a smooth function is the same thing as its restriction to `Ω`. -/
theorem BddDomain.embedH_eq_iff (D : BddDomain) (u w : smoothFns) :
    D.embedH u = D.embedH w ↔ ∀ z ∈ D.carrier, (u : ℂ → ℝ) z = (w : ℂ → ℝ) z := by
  have hBm : MeasurableSet D.carrier := D.isOpen.measurableSet
  constructor
  · intro h
    have h1 : D.toL2 u = D.toL2 w := by
      have := congrArg (fun x : D.H1 => (x : D.Amb).fst) h
      simpa using this
    have hae : (u : ℂ → ℝ) =ᵐ[D.μ] (w : ℂ → ℝ) := by
      filter_upwards [D.toL2_ae u, D.toL2_ae w] with z hu hw
      rw [← hu, ← hw, h1]
    intro z hz
    by_contra hne
    set O := D.carrier ∩ {y | (u : ℂ → ℝ) y ≠ (w : ℂ → ℝ) y}
    have hO : IsOpen O := D.isOpen.inter (isOpen_ne_fun (continuous_of_mem u.2)
      (continuous_of_mem w.2))
    have hpos : 0 < volume O := hO.measure_pos volume ⟨z, hz, hne⟩
    have hnull : D.μ {y | (u : ℂ → ℝ) y ≠ (w : ℂ → ℝ) y} = 0 := by
      rw [← ae_iff]; exact hae
    rw [Measure.restrict_apply' hBm, inter_comm] at hnull
    exact hpos.ne' hnull
  · intro h
    apply Subtype.ext
    refine ConfMap.dom_amb_ext ?_ ?_
    · simp only [coe_embedH, BddDomain.embed_fst]
      ext1
      filter_upwards [D.toL2_ae u, D.toL2_ae w, ae_restrict_mem hBm] with z hu hw hz
      rw [hu, hw, h z hz]
    · simp only [coe_embedH, BddDomain.embed_snd]
      ext1
      filter_upwards [D.gradL2_ae u, D.gradL2_ae w, ae_restrict_mem hBm] with z hu hw hz
      rw [hu, hw]
      have hev : (u : ℂ → ℝ) =ᶠ[𝓝 z] (w : ℂ → ℝ) := by
        filter_upwards [D.isOpen.mem_nhds hz] with y hy using h y hy
      simp only [grad, hev.fderiv_eq]

namespace ConfMap

variable (c : ConfMap)

open SteklovBoundary

/-- The boundary weight `|G'|` of conformal data is a real-analytic weight. -/
theorem isAnalyticWeight_ρ : IsAnalyticWeight c.ρ :=
  isAnalyticWeight_norm (g := deriv c.G) c.isOpen (sphere_subset_closedBall.trans c.cb)
    (c.diff.deriv c.isOpen) (fun z hz => c.deriv_ne z (c.cb (sphere_subset_closedBall hz)))

lemma sobolevPullback_symm_embedH (u : smoothFns) :
    c.sobolevPullback.symm (embedH u) = c.dom.embedH (c.pushSmooth u) :=
  Subtype.ext (c.pushAmb_embed u)

/-- `x ∈ H¹(Ω)` is the class of a **classical Steklov eigenfunction** with eigenvalue `τ`: a
globally smooth `v` harmonic in `Ω` with `∂_ν v = τ v` at every boundary point `G(e^{iθ})`. -/
def IsClassicalEigenClass (τ : ℝ) (x : c.dom.H1) : Prop :=
  ∃ v : smoothFns, x = c.dom.embedH v ∧ HarmonicOnNhd (v : ℂ → ℝ) c.Ω ∧
    ∀ θ : ℝ, fderiv ℝ (v : ℂ → ℝ) (c.G (ee θ)) (c.nrm θ) = τ * (v : ℂ → ℝ) (c.G (ee θ))

/-- **Regularity of weak Steklov eigenfunctions on `Ω = G(𝔻)`.** Every weak Steklov
eigenfunction `x ∈ H¹(Ω)` with eigenvalue `τ` is the `H¹(Ω)` class of a globally smooth `v`
that is harmonic on an open set `W ⊇ Ω̄ = G(𝔻̄)` and satisfies the classical Steklov boundary
condition `∂_ν v(G(e^{iθ})) = τ v(G(e^{iθ}))` for every `θ`, `ν = c.nrm θ` the outward unit
normal. -/
theorem weak_eigen_classical_dom {τ : ℝ} {x : c.dom.H1}
    (hx : IsWeakSteklovEigenDom c.dom τ x) :
    ∃ v : smoothFns, x = c.dom.embedH v ∧
      (∃ W : Set ℂ, IsOpen W ∧ c.G '' closedBall 0 1 ⊆ W ∧ HarmonicOnNhd (v : ℂ → ℝ) W) ∧
      ∀ θ : ℝ, fderiv ℝ (v : ℂ → ℝ) (c.G (ee θ)) (c.nrm θ) = τ * (v : ℂ → ℝ) (c.G (ee θ)) := by
  have hy := (c.isWeakSteklovEigenDom_iff τ x).1 hx
  obtain ⟨r, hr, u, hyu, hu, hbc⟩ := weak_eigen_classical c.isAnalyticWeight_ρ hy
  set v := c.pushSmooth u with hv
  have hxv : x = c.dom.embedH v := by
    rw [hv, ← c.sobolevPullback_symm_embedH, ← hyu, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨v, hxv, ?_, ?_⟩
  · -- harmonicity on a neighbourhood of `G(𝔻̄)`
    set W := {w : ℂ | ∀ᶠ y in 𝓝 w, (v : ℂ → ℝ) y = (u : ℂ → ℝ) (c.H y)} ∩
      c.G '' (c.U ∩ ball 0 r) with hW
    have hWo : IsOpen W := isOpen_setOf_eventually_nhds.inter
      (HolInv.isOpen_image c.diff c.inj inter_subset_left (c.isOpen.inter isOpen_ball))
    refine ⟨W, hWo, fun w hw => ⟨c.pushSmooth_eventually u hw, ?_⟩, ?_⟩
    · obtain ⟨z, hz, rfl⟩ := hw
      exact ⟨z, ⟨c.cb hz, closedBall_subset_ball hr hz⟩, rfl⟩
    · intro w hw
      obtain ⟨hev, z, ⟨hzU, hzr⟩, rfl⟩ := hw
      have hH : AnalyticAt ℂ c.H (c.G z) :=
        c.differentiableOn_H.analyticAt (c.isOpen_V.mem_nhds ⟨z, hzU, rfl⟩)
      have hu' : HarmonicAt (u : ℂ → ℝ) (c.H (c.G z)) := by
        rw [c.H_G hzU]; exact hu z hzr
      exact (harmonicAt_congr_nhds hev).2 (harmonicAt_comp_analyticAt hu' hH)
  · intro θ
    set e := ee θ with he
    have hes : e ∈ closedBall (0:ℂ) 1 := by simp [he, Complex.norm_exp_ofReal_mul_I]
    have hsph : e ∈ sphere (0:ℂ) 1 := by simp [he, Complex.norm_exp_ofReal_mul_I]
    have heU : e ∈ c.U := c.cb hes
    have hev := c.pushSmooth_eventually u ⟨e, hes, rfl⟩
    have hud : DifferentiableAt ℝ (u : ℂ → ℝ) (c.H (c.G e)) :=
      ((contDiff_one_of_mem u.2).differentiable one_ne_zero) _
    have hHd := c.hasDerivAt_H heU
    have hcomp : HasFDerivAt (fun w => (u : ℂ → ℝ) (c.H w))
        ((fderiv ℝ (u : ℂ → ℝ) (c.H (c.G e))).comp
          ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (deriv c.G e)⁻¹).restrictScalars ℝ))
        (c.G e) :=
      hud.hasFDerivAt.comp (c.G e) (hHd.hasFDerivAt.restrictScalars ℝ)
    rw [hev.fderiv_eq, hcomp.fderiv, hev.self_of_nhds, c.H_G heU]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul]
    have hρ0 := c.ρ_pos e hsph
    have hG0 : deriv c.G e ≠ 0 := c.deriv_ne e heU
    have hkey : c.nrm θ * (deriv c.G e)⁻¹ = (c.ρ e)⁻¹ • e := by
      simp only [nrm, ← he, ρ]
      rw [Complex.real_smul]
      push_cast
      field_simp
    rw [hkey, map_smul, hbc θ, smul_eq_mul, c.H_G heU, ← he]
    field_simp

/-- **Weak = classical** on `Ω = G(𝔻)`. -/
theorem isWeakSteklovEigenDom_iff_classical (τ : ℝ) (x : c.dom.H1) :
    IsWeakSteklovEigenDom c.dom τ x ↔ c.IsClassicalEigenClass τ x := by
  constructor
  · intro hx
    obtain ⟨v, hxv, ⟨W, -, hW, hvW⟩, hbc⟩ := c.weak_eigen_classical_dom hx
    exact ⟨v, hxv, fun w hw => hvW w (hW (image_mono ball_subset_closedBall hw)), hbc⟩
  · rintro ⟨v, rfl, hharm, hbc⟩
    exact c.isWeakSteklovEigenDom_of_classical v hharm hbc

/-- **Classical Steklov spectral theorem on `Ω = G(𝔻)`**, with multiplicities. -/
theorem classical_spectral_theorem_dom :
    ∃ (e : ℕ → c.dom.H1) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = 0 ∧ Tendsto σ atTop atTop ∧
      (∀ k, e k ≠ 0 ∧ c.IsClassicalEigenClass (σ k) (e k)) ∧
      (∀ τ, (∃ x : c.dom.H1, x ≠ 0 ∧ c.IsClassicalEigenClass τ x) ↔ ∃ k, σ k = τ) ∧
      (∀ τ, ∃ S : Submodule ℝ c.dom.H1, (∀ x, x ∈ S ↔ c.IsClassicalEigenClass τ x) ∧
        Module.finrank ℝ S = Set.ncard {k | σ k = τ}) ∧
      (∀ k, Steklov.steklovSpectrum c.Ω k = ENNReal.ofReal (σ k)) := by
  have h := c.weak_spectral_theorem_dom
  simp only [c.isWeakSteklovEigenDom_iff_classical] at h
  exact h

end ConfMap

end SteklovH1
