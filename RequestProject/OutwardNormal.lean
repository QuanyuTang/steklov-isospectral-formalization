module

public import RequestProject.ClassicalSteklov

/-!
# `ConfMap.nrm` is the outward normal

For `Ω = G(𝔻)` (`G` holomorphic and injective on a neighbourhood of `𝔻̄`, `G' ≠ 0`) the unit
vector `ν = c.nrm θ = e^{iθ}G'(e^{iθ})/|G'(e^{iθ})|` at the boundary point `p = G(e^{iθ})` points
out of `Ω` in the geometric sense: for all sufficiently small `t > 0`,
`p + tν ∉ Ω̄` and `p − tν ∈ Ω`.
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace SteklovH1.ConfMap

variable (c : ConfMap)

lemma closure_Ω : closure c.Ω = c.G '' closedBall 0 1 := by
  have hcont : ContinuousOn c.G (closedBall 0 1) := c.diff.continuousOn.mono c.cb
  apply le_antisymm
  · exact closure_minimal (image_mono ball_subset_closedBall)
      ((isCompact_closedBall 0 1).image_of_continuousOn hcont).isClosed
  · have := ContinuousOn.image_closure (s := ball (0 : ℂ) 1)
      (by rwa [closure_ball (0 : ℂ) one_ne_zero])
    rwa [closure_ball (0 : ℂ) one_ne_zero] at this

/-- **`nrm` is the outward normal.**  At the boundary point `p = G(e^{iθ})`, moving a small
positive distance along `ν = c.nrm θ` leaves the closed domain, and moving along `-ν` enters the
open domain. -/
theorem nrm_outward (θ : ℝ) :
    ∀ᶠ t : ℝ in 𝓝[>] 0,
      c.G (Complex.exp (θ * Complex.I)) + (t : ℂ) * c.nrm θ ∉ closure c.Ω ∧
      c.G (Complex.exp (θ * Complex.I)) - (t : ℂ) * c.nrm θ ∈ c.Ω := by
  set z₀ := Complex.exp (θ * Complex.I)
  have hz₀ : ‖z₀‖ = 1 := by simp [z₀, Complex.norm_exp_ofReal_mul_I]
  have hz₀U : z₀ ∈ c.U := c.cb (by simp [hz₀])
  set H := Function.invFunOn c.G c.U
  set d := deriv c.G z₀
  have hd : d ≠ 0 := c.deriv_ne z₀ hz₀U
  have hdn : 0 < ‖d‖ := norm_pos_iff.2 hd
  have hH : HasDerivAt H d⁻¹ (c.G z₀) :=
    HolInv.hasDerivAt_invFunOn c.isOpen c.diff c.inj hz₀U hd
  set γ : ℝ → ℂ := fun t => c.G z₀ + (t : ℂ) * c.nrm θ
  have hγ : HasDerivAt γ (c.nrm θ) 0 := by
    have := ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (c.nrm θ)).const_add
      (c.G z₀)
    first
      | simpa [γ] using this
      | simpa [γ, Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.neg_def, Function.comp_def] using this
      | exact (this.congr_deriv (by first | rfl | simp | (simp; ring))).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => by first | rfl | simp | (simp; ring))
  have hγ0 : γ 0 = c.G z₀ := by simp [γ]
  have hHγ : HasDerivAt (H ∘ γ) (d⁻¹ * c.nrm θ) 0 := by
    have hH' : HasDerivAt H d⁻¹ (γ 0) := by rwa [hγ0]
    exact hH'.comp (0 : ℝ) hγ
  have hH0 : (H ∘ γ) 0 = z₀ := by
    simp only [Function.comp, hγ0, H]; exact HolInv.invFunOn_apply_self c.inj hz₀U
  have hval : d⁻¹ * c.nrm θ = z₀ * ((‖d‖⁻¹ : ℝ) : ℂ) := by
    have hn : ((‖d‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hdn.ne'
    show d⁻¹ * (z₀ * d / ((‖d‖ : ℝ) : ℂ)) = z₀ * ((‖d‖⁻¹ : ℝ) : ℂ)
    rw [Complex.ofReal_inv]
    field_simp
  -- `f t = ‖H(γ t)‖²` has positive derivative at `0`
  set f : ℝ → ℝ := fun t => ‖(H ∘ γ) t‖ ^ 2
  have hf : HasDerivAt f (2 * ‖d‖⁻¹) 0 := by
    have := hHγ.norm_sq
    rw [hH0, hval] at this
    convert this using 1
    rw [real_inner_eq_re_inner ℂ]
    simp only [inner]
    -- Lean 4.35 / current Mathlib: the inner product unfolds to `z₀ * star z₀ * _`, written with
    -- `Star.star` rather than `starRingEnd ℂ`; normalise it before using `Complex.mul_conj`.
    have hzz : z₀ * star z₀ = 1 := by
      have hconj : z₀ * (starRingEnd ℂ) z₀ = 1 := by
        first
          | (rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz₀]; norm_num)
          | (rw [Complex.mul_conj', hz₀]; norm_num)
          | (apply Complex.ext <;>
              simp [Complex.mul_re, Complex.mul_im, ← Complex.normSq_apply,
                Complex.normSq_eq_norm_sq, hz₀] <;> ring)
      simpa only [starRingEnd_apply] using hconj
    first
      | (rw [hzz, one_mul]; simp)
      | (rw [hzz, one_mul]; simp [RCLike.re_to_complex])
      | (simp only [hzz, one_mul, RCLike.re_to_complex, Complex.ofReal_re])
      | (simp [hzz])
      | (simp [← starRingEnd_apply, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz₀])
  have hf0 : f 0 = 1 := by
    show ‖(H ∘ γ) 0‖ ^ 2 = 1
    rw [hH0, hz₀]; norm_num
  have hpos : (0 : ℝ) < 2 * ‖d‖⁻¹ := by positivity
  have hright : ∀ᶠ t in 𝓝[>] (0 : ℝ), 1 < f t := by
    have := hf.tendsto_slope_zero_right
    filter_upwards [this.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with t ht ht0
    simp only [zero_add, smul_eq_mul, hf0] at ht
    have ht0' : (0 : ℝ) < t := ht0
    have := (mul_pos_iff_of_pos_left (inv_pos.2 ht0')).1 ht
    linarith
  have hleft : ∀ᶠ t in 𝓝[<] (0 : ℝ), f t < 1 := by
    have := hf.tendsto_slope_zero_left
    filter_upwards [this.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with t ht ht0
    simp only [zero_add, smul_eq_mul, hf0] at ht
    have ht0' : t < 0 := ht0
    by_contra hc
    push_neg at hc
    have : t⁻¹ * (f t - 1) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.2 ht0'.le) (by linarith)
    linarith
  -- near `0`, `γ t` lies in the open set `G(U)`, so `G (H (γ t)) = γ t` with `H (γ t) ∈ U`
  have hVo : IsOpen (c.G '' c.U) := HolInv.isOpen_image c.diff c.inj subset_rfl c.isOpen
  have hγc : ContinuousAt γ 0 := hγ.continuousAt
  have hnear : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ c.G '' c.U :=
    hγc.preimage_mem_nhds (by rw [hγ0]; exact hVo.mem_nhds ⟨z₀, hz₀U, rfl⟩)
  have hgood : ∀ t, γ t ∈ c.G '' c.U → H (γ t) ∈ c.U ∧ c.G (H (γ t)) = γ t := fun t ht =>
    ⟨Function.invFunOn_mem ht, Function.invFunOn_eq ht⟩
  have hneg : Tendsto (fun t : ℝ => -t) (𝓝[>] 0) (𝓝[<] 0) := by
    simpa using tendsto_neg_nhdsGT (a := (0 : ℝ))
  filter_upwards [hright, hneg.eventually hleft, nhdsWithin_le_nhds hnear,
    hneg.eventually (nhdsWithin_le_nhds hnear)] with t h1 h2 h3 h4
  obtain ⟨hU3, hG3⟩ := hgood t h3
  obtain ⟨hU4, hG4⟩ := hgood (-t) h4
  constructor
  · rw [closure_Ω]
    rintro ⟨w, hw, hGw⟩
    have : H (γ t) = w := c.inj hU3 (c.cb hw) (by rw [hG3]; exact hGw.symm)
    have h1' : 1 < ‖H (γ t)‖ ^ 2 := h1
    rw [this] at h1'
    have : ‖w‖ ≤ 1 := by simpa using hw
    nlinarith [norm_nonneg w]
  · refine ⟨H (γ (-t)), ?_, ?_⟩
    · have h2' : ‖H (γ (-t))‖ ^ 2 < 1 := h2
      rw [mem_ball_zero_iff]
      nlinarith [norm_nonneg (H (γ (-t)))]
    · rw [hG4]; simp [γ, sub_eq_add_neg]

end SteklovH1.ConfMap
