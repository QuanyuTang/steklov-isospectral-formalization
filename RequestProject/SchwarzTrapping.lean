module

public import Mathlib
public import RequestProject.HolomorphicInverse

/-!
# Quantitative Schwarz–Pick estimates and disk trapping (for Proposition 3.4.1)

* `schwarz_near_id`: if `f : 𝔻 → 𝔻̄` is holomorphic, `f 0 = 0` and `f'(0) = a ∈ [0,1)`, then
  `|f(z) - z| ≤ |z| (1-a)(1+|z|)/(1-|z|)`.  (Schwarz–Pick applied to `f(z)/z`.)
* `inverse_schwarz`: if `ψ` is holomorphic and injective on `𝔻` with `ψ 0 = 0` and
  `B(0,r) ⊆ ψ(𝔻)`, then `|z| ≤ |ψ z| / r` whenever `|ψ z| < r`.
* `norm_deriv_ge_of_ball_subset`, `norm_deriv_le_of_image_subset`: `r ≤ |ψ'(0)| ≤ R` if
  `B(0,r) ⊆ ψ(𝔻) ⊆ B(0,R)`.
* `trapped_map_close_to_id`: a normalized map `ψ` (`ψ 0 = 0`, `ψ'(0) > 0`) with
  `B(0,r) ⊆ ψ(𝔻) ⊆ B(0,R)` satisfies an explicit bound for `|ψ z - z|`, tending to `0` as
  `r, R → 1`.
-/

@[expose] public section

open Complex Metric Set Filter Topology

noncomputable section

namespace SteklovCoalescence

lemma mobius_den_ne_zero {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    (1 - (a : ℂ) * w) ≠ 0 := by
  intro h
  have h1 : (a : ℂ) * w = 1 := (sub_eq_zero.1 h).symm
  have h2 := congrArg norm h1
  rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg ha0, norm_one] at h2
  nlinarith [norm_nonneg w]

/-- The real Möbius map `w ↦ (w - a)/(1 - a w)` maps the closed unit disk into itself. -/
lemma mobius_norm_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    ‖(w - a) / (1 - a * w)‖ ≤ 1 := by
  have hden := mobius_den_ne_zero ha0 ha1 hw
  rw [norm_div, div_le_one (norm_pos_iff.2 hden)]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← normSq_eq_norm_sq, ← normSq_eq_norm_sq]
  have hw2 : normSq w ≤ 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg w]
  simp only [normSq_apply, sub_re, sub_im, ofReal_re, ofReal_im, mul_re, mul_im, one_re, one_im]
  rw [normSq_apply] at hw2
  nlinarith [mul_nonneg (by nlinarith : 0 ≤ 1 - a ^ 2) (by linarith : 0 ≤ 1 - (w.re * w.re + w.im * w.im))]

/-- **Quantitative Schwarz–Pick estimate near the identity.** -/
theorem schwarz_near_id {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hmap : MapsTo f (ball 0 1) (closedBall 0 1)) (h0 : f 0 = 0) {a : ℝ}
    (ha : deriv f 0 = a) (ha0 : 0 ≤ a) (ha1 : a < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖f z - z‖ ≤ ‖z‖ * ((1 - a) * (1 + ‖z‖) / (1 - ‖z‖)) := by
  set g := dslope f 0 with hg_def
  have hgd : DifferentiableOn ℂ g (ball 0 1) :=
    (differentiableOn_dslope (ball_mem_nhds 0 one_pos)).2 hd
  have hmap' : MapsTo f (ball 0 1) (closedBall (f 0) 1) := by rwa [h0]
  have hgle : ∀ w ∈ ball (0 : ℂ) 1, ‖g w‖ ≤ 1 := fun w hw => by
    simpa using Complex.norm_dslope_le_div_of_mapsTo_ball hd hmap' hw
  have hg0 : g 0 = a := by rw [hg_def, dslope_same, ha]
  set h : ℂ → ℂ := fun w => (g w - a) / (1 - a * g w) with hh
  have hhd : DifferentiableOn ℂ h (ball 0 1) := by
    intro w hw
    refine ((hgd w hw).sub_const _).div ((differentiableWithinAt_const _).sub
      ((differentiableWithinAt_const _).mul (hgd w hw))) ?_
    exact mobius_den_ne_zero ha0 ha1 (hgle w hw)
  have hhmap : MapsTo h (ball 0 1) (closedBall 0 1) := fun w hw => by
    rw [mem_closedBall_zero_iff]; exact mobius_norm_le ha0 ha1 (hgle w hw)
  have hh0 : h 0 = 0 := by simp [hh, hg0]
  have hsch : ‖h z‖ ≤ ‖z‖ :=
    Complex.norm_le_norm_of_mapsTo_ball hhd hhmap hh0 hz
  have hzb : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.2 hz
  have hden := mobius_den_ne_zero ha0 ha1 (hgle z hzb)
  have key : ‖g z - a‖ ≤ ‖z‖ * ‖1 - a * g z‖ := by
    have : ‖h z‖ = ‖g z - a‖ / ‖1 - a * g z‖ := by rw [hh]; simp only [norm_div]
    rw [this, div_le_iff₀ (norm_pos_iff.2 hden)] at hsch
    linarith
  -- real inequality
  set x := ‖1 - g z‖
  have hx1 : x - (1 - a) ≤ ‖g z - a‖ := by
    have : (1 : ℂ) - g z = ((1 - a : ℝ) : ℂ) - (g z - a) := by push_cast; ring
    have h2 : x ≤ (1 - a) + ‖g z - a‖ := by
      calc x = ‖((1 - a : ℝ) : ℂ) - (g z - a)‖ := by rw [← this]
        _ ≤ ‖((1 - a : ℝ) : ℂ)‖ + ‖g z - a‖ := norm_sub_le _ _
        _ = (1 - a) + ‖g z - a‖ := by
          rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hx2 : ‖1 - a * g z‖ ≤ (1 - a) + x := by
    have : (1 : ℂ) - a * g z = ((1 - a : ℝ) : ℂ) + (a : ℂ) * (1 - g z) := by push_cast; ring
    calc ‖1 - a * g z‖ = ‖((1 - a : ℝ) : ℂ) + (a : ℂ) * (1 - g z)‖ := by rw [this]
      _ ≤ ‖((1 - a : ℝ) : ℂ)‖ + ‖(a : ℂ) * (1 - g z)‖ := norm_add_le _ _
      _ = (1 - a) + a * x := by
          rw [norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_mul, norm_real,
            Real.norm_eq_abs, abs_of_nonneg ha0]
      _ ≤ (1 - a) + x := by nlinarith [norm_nonneg (1 - g z)]
  have hzn := norm_nonneg z
  have hxbound : x ≤ (1 - a) * (1 + ‖z‖) / (1 - ‖z‖) := by
    rw [le_div_iff₀ (by linarith)]
    nlinarith
  have hfz : f z - z = z * (g z - 1) := by
    have := sub_smul_dslope f 0 z
    simp only [sub_zero, h0, smul_eq_mul] at this
    rw [← this]; ring
  rw [hfz, norm_mul, norm_sub_rev]
  exact mul_le_mul_of_nonneg_left hxbound hzn

section trapping

variable {ψ : ℂ → ℂ}

/-- The inverse of an injective holomorphic map of `𝔻` is holomorphic on the image. -/
lemma differentiableAt_invFunOn (hd : DifferentiableOn ℂ ψ (ball 0 1))
    (hinj : InjOn ψ (ball 0 1)) {y : ℂ} (hy : y ∈ ψ '' ball 0 1) :
    DifferentiableAt ℂ (Function.invFunOn ψ (ball 0 1)) y := by
  obtain ⟨x, hx, rfl⟩ := hy
  exact (HolInv.hasDerivAt_invFunOn isOpen_ball hd hinj hx
    (HolInv.deriv_ne_zero_of_injOn isOpen_ball hd hinj hx)).differentiableAt

/-- **Inverse Schwarz estimate.** If `ψ` is holomorphic and injective on `𝔻`, `ψ 0 = 0` and
`B(0,r) ⊆ ψ(𝔻)`, then `|z| ≤ |ψ z|/r` whenever `|ψ z| < r`. -/
theorem inverse_schwarz (hd : DifferentiableOn ℂ ψ (ball 0 1)) (hinj : InjOn ψ (ball 0 1))
    (h0 : ψ 0 = 0) {r : ℝ} (hr : 0 < r) (hball : ball 0 r ⊆ ψ '' ball 0 1) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) 1) (hψz : ‖ψ z‖ < r) : ‖z‖ ≤ ‖ψ z‖ / r := by
  set G := Function.invFunOn ψ (ball 0 1)
  set h : ℂ → ℂ := fun w => G (r * w) with hh
  have hmem : ∀ w ∈ ball (0 : ℂ) 1, (r : ℂ) * w ∈ ψ '' ball 0 1 := fun w hw => by
    apply hball
    rw [mem_ball_zero_iff, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have := mem_ball_zero_iff.1 hw
    nlinarith [norm_nonneg w]
  have hhd : DifferentiableOn ℂ h (ball 0 1) := fun w hw =>
    ((differentiableAt_invFunOn hd hinj (hmem w hw)).comp w
      ((differentiableAt_const _).mul differentiableAt_id)).differentiableWithinAt
  have hhmap : MapsTo h (ball 0 1) (closedBall 0 1) := fun w hw => by
    obtain ⟨x, hx, hxw⟩ := hmem w hw
    exact ball_subset_closedBall (Function.invFunOn_mem ⟨x, hx, hxw⟩)
  have hh0 : h 0 = 0 := by
    simp only [hh, mul_zero]
    have := HolInv.invFunOn_apply_self hinj (mem_ball_self one_pos : (0 : ℂ) ∈ ball 0 1)
    rwa [h0] at this
  have hw : ‖ψ z / r‖ < 1 := by
    rw [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr, div_lt_one hr]; exact hψz
  have := Complex.norm_le_norm_of_mapsTo_ball hhd hhmap hh0 hw
  have hcalc : h (ψ z / r) = z := by
    simp only [hh]
    rw [mul_div_cancel₀ _ (by exact_mod_cast hr.ne')]
    exact HolInv.invFunOn_apply_self hinj hz
  rwa [hcalc, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr] at this

/-- Schwarz: `|ψ'(0)| ≤ R` if `ψ(𝔻) ⊆ B(0,R)`. -/
theorem norm_deriv_le_of_image_subset (hd : DifferentiableOn ℂ ψ (ball 0 1)) (h0 : ψ 0 = 0)
    {R : ℝ} (himg : ψ '' ball 0 1 ⊆ ball 0 R) : ‖deriv ψ 0‖ ≤ R := by
  have hmap : MapsTo ψ (ball 0 1) (closedBall (ψ 0) R) := fun w hw => by
    rw [h0]; exact ball_subset_closedBall (himg ⟨w, hw, rfl⟩)
  simpa using Complex.norm_deriv_le_div_of_mapsTo_ball hd hmap one_pos

/-- Inverse Schwarz: `r ≤ |ψ'(0)|` if `B(0,r) ⊆ ψ(𝔻)`. -/
theorem norm_deriv_ge_of_ball_subset (hd : DifferentiableOn ℂ ψ (ball 0 1))
    (hinj : InjOn ψ (ball 0 1)) (h0 : ψ 0 = 0) {r : ℝ} (hr : 0 < r)
    (hball : ball 0 r ⊆ ψ '' ball 0 1) : r ≤ ‖deriv ψ 0‖ := by
  have hdiff : DifferentiableAt ℂ ψ 0 := hd.differentiableAt (ball_mem_nhds 0 one_pos)
  have hcont : ContinuousAt (dslope ψ 0) 0 := continuousAt_dslope_same.2 hdiff
  have ht : Tendsto (fun z => ‖dslope ψ 0 z‖) (𝓝[≠] 0) (𝓝 ‖deriv ψ 0‖) := by
    have := (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := {0}ᶜ))).norm
    rwa [dslope_same] at this
  have hψc : ContinuousAt ψ 0 := hdiff.continuousAt
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), r ≤ ‖dslope ψ 0 z‖ := by
    have h1 : ∀ᶠ z in 𝓝 (0 : ℂ), z ∈ ball (0 : ℂ) 1 ∧ ‖ψ z‖ < r := by
      have h2 : ∀ᶠ z in 𝓝 (0 : ℂ), ψ z ∈ ball (0 : ℂ) r :=
        hψc.preimage_mem_nhds (by rw [h0]; exact ball_mem_nhds 0 hr)
      filter_upwards [ball_mem_nhds (0 : ℂ) one_pos, h2] with z hz1 hz2
      exact ⟨hz1, mem_ball_zero_iff.1 hz2⟩
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    have hle := inverse_schwarz hd hinj h0 hr hball hz.1 hz.2
    rw [dslope_of_ne _ hz0', slope_def_module, h0, sub_zero, sub_zero, norm_smul, norm_inv,
      ← div_eq_inv_mul, le_div_iff₀ (norm_pos_iff.2 hz0')]
    rw [le_div_iff₀ hr] at hle
    linarith
  exact ge_of_tendsto ht hev

/-- **A trapped normalized map is close to the identity.**  If `ψ` is holomorphic and injective
on `𝔻`, `ψ 0 = 0`, `ψ'(0) = a > 0` and `B(0,r) ⊆ ψ(𝔻) ⊆ B(0,R)`, then for every `R' > R` and
`|z| < 1`:
`|ψ z - z| ≤ R' |z| (1 - r/R')(1+|z|)/(1-|z|) + |R' - 1| |z|`. -/
theorem trapped_map_close_to_id (hd : DifferentiableOn ℂ ψ (ball 0 1))
    (hinj : InjOn ψ (ball 0 1)) (h0 : ψ 0 = 0) {a : ℝ} (ha : deriv ψ 0 = a) (ha0 : 0 < a)
    {r R R' : ℝ} (hr : 0 < r) (hball : ball 0 r ⊆ ψ '' ball 0 1)
    (himg : ψ '' ball 0 1 ⊆ ball 0 R) (hRR' : R < R') {z : ℂ} (hz : ‖z‖ < 1) :
    ‖ψ z - z‖ ≤ R' * (‖z‖ * ((1 - r / R') * (1 + ‖z‖) / (1 - ‖z‖))) + |R' - 1| * ‖z‖ := by
  have haR : a ≤ R := by
    have := norm_deriv_le_of_image_subset hd h0 himg
    rwa [ha, norm_real, Real.norm_eq_abs, abs_of_pos ha0] at this
  have har : r ≤ a := by
    have := norm_deriv_ge_of_ball_subset hd hinj h0 hr hball
    rwa [ha, norm_real, Real.norm_eq_abs, abs_of_pos ha0] at this
  have hR'0 : 0 < R' := by linarith
  set f : ℂ → ℂ := fun w => ψ w / R' with hf
  have hfd : DifferentiableOn ℂ f (ball 0 1) := hd.div_const _
  have hfmap : MapsTo f (ball 0 1) (closedBall 0 1) := fun w hw => by
    have h1 := mem_ball_zero_iff.1 (himg ⟨w, hw, rfl⟩)
    rw [mem_closedBall_zero_iff, hf]
    simp only [norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hR'0]
    rw [div_le_one hR'0]; linarith
  have hf0 : f 0 = 0 := by simp [hf, h0]
  have hfa : deriv f 0 = ((a / R' : ℝ) : ℂ) := by
    rw [hf, deriv_div_const, ha]; push_cast; ring
  have hsch := schwarz_near_id hfd hfmap hf0 hfa (by positivity)
    (by rw [div_lt_one hR'0]; linarith) hz
  have hdecomp : ψ z - z = (R' : ℂ) * (f z - z) + ((R' - 1 : ℝ) : ℂ) * z := by
    have : (R' : ℂ) ≠ 0 := by exact_mod_cast hR'0.ne'
    simp only [hf]; push_cast; field_simp; ring
  have hzn := norm_nonneg z
  have h1z : 0 < 1 - ‖z‖ := by linarith
  have hmono : (1 - a / R') * (1 + ‖z‖) / (1 - ‖z‖) ≤ (1 - r / R') * (1 + ‖z‖) / (1 - ‖z‖) := by
    apply div_le_div_of_nonneg_right _ h1z.le
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    have : r / R' ≤ a / R' := div_le_div_of_nonneg_right har hR'0.le
    linarith
  calc ‖ψ z - z‖ ≤ ‖(R' : ℂ) * (f z - z)‖ + ‖((R' - 1 : ℝ) : ℂ) * z‖ := by
        rw [hdecomp]; exact norm_add_le _ _
    _ = R' * ‖f z - z‖ + |R' - 1| * ‖z‖ := by
        rw [norm_mul, norm_mul, norm_real, norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_pos hR'0]
    _ ≤ R' * (‖z‖ * ((1 - r / R') * (1 + ‖z‖) / (1 - ‖z‖))) + |R' - 1| * ‖z‖ := by
        gcongr
        exact hsch.trans (mul_le_mul_of_nonneg_left hmono hzn)

end trapping

end SteklovCoalescence
