module

public import Mathlib
public import RequestProject.DiskTrace
public import RequestProject.WeylLemma

/-!
# Divergence theorem and Green's identity on the unit disk

For `C¹` functions `P, Q : ℂ → ℝ`,
`∫_𝔻 (∂ₓP + ∂_yQ) = ∫_0^{2π} (P(e^{iθ}) cos θ + Q(e^{iθ}) sin θ) dθ`,
proved in polar coordinates (fundamental theorem of calculus along rays, periodicity in the
angle). As a consequence, Green's first identity
`∫_𝔻 ⟨∇u, ∇v⟩ + ∫_𝔻 v Δu = ∫_0^{2π} v(e^{iθ}) ∂_r u(e^{iθ}) dθ` for `u ∈ C²`, `v ∈ C¹`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real Laplacian
open scoped ENNReal ContDiff RealInnerProductSpace

noncomputable section

namespace SteklovGreen

/-- Swapping two interval integrals of a jointly continuous function. -/
lemma swap_rect {f : ℝ → ℝ → ℝ} (hf : Continuous (Function.uncurry f)) {a b c d : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) :
    ∫ x in a..b, ∫ y in c..d, f x y = ∫ y in c..d, ∫ x in a..b, f x y := by
  simp only [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
  refine integral_integral_swap ?_
  rw [Measure.prod_restrict]
  have : IntegrableOn (Function.uncurry f) (Icc a b ×ˢ Icc c d) (volume.prod volume) :=
    hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  exact this.mono_set (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)

/-- `fderiv P z e^{iθ} = cos θ ∂ₓP + sin θ ∂_yP`. -/
lemma fderiv_exp (P : ℂ → ℝ) (z : ℂ) (θ : ℝ) :
    fderiv ℝ P z (Complex.exp (θ * Complex.I)) =
      Real.cos θ * fderiv ℝ P z 1 + Real.sin θ * fderiv ℝ P z Complex.I := by
  have : Complex.exp (θ * Complex.I) = (Real.cos θ : ℝ) • (1 : ℂ) + (Real.sin θ : ℝ) • Complex.I := by
    rw [Complex.exp_mul_I]
    simp [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- **Divergence theorem on the unit disk** for `C¹` vector fields `(P, Q)`. -/
theorem divergence_disk {P Q : ℂ → ℝ} (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    ∫ z in Metric.ball (0:ℂ) 1, (fderiv ℝ P z 1 + fderiv ℝ Q z Complex.I) =
      ∫ θ in (0:ℝ)..(2 * π), (P (Complex.exp (θ * Complex.I)) * Real.cos θ +
        Q (Complex.exp (θ * Complex.I)) * Real.sin θ) := by
  set e : ℝ → ℂ := fun θ => Complex.exp (θ * Complex.I) with he
  set pt : ℝ → ℝ → ℂ := fun r θ => (r : ℂ) * e θ with hpt
  have hPd : Differentiable ℝ P := hP.differentiable one_ne_zero
  have hQd : Differentiable ℝ Q := hQ.differentiable one_ne_zero
  have hPc : Continuous (fderiv ℝ P) := hP.continuous_fderiv one_ne_zero
  have hQc : Continuous (fderiv ℝ Q) := hQ.continuous_fderiv one_ne_zero
  have hec : Continuous e := by simp only [he]; fun_prop
  -- `e θ * I = exp((θ) I) I`
  have heI : ∀ θ : ℝ, e θ * Complex.I = ((-Real.sin θ : ℝ) : ℂ) * 1 +
      ((Real.cos θ : ℝ) : ℂ) * Complex.I := by
    intro θ; simp only [he, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hfdI : ∀ (F : ℂ → ℝ) z θ, fderiv ℝ F z (e θ * Complex.I) =
      -Real.sin θ * fderiv ℝ F z 1 + Real.cos θ * fderiv ℝ F z Complex.I := by
    intro F z θ
    rw [heI θ]
    have h1 : ((-Real.sin θ : ℝ) : ℂ) * 1 = (-Real.sin θ) • (1 : ℂ) := by simp
    have h2 : ((Real.cos θ : ℝ) : ℂ) * Complex.I = (Real.cos θ) • Complex.I := by simp
    rw [h1, h2, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  -- radial and angular functions
  set f : ℝ → ℝ → ℝ := fun r θ => r * (P (pt r θ) * Real.cos θ + Q (pt r θ) * Real.sin θ)
  set g : ℝ → ℝ → ℝ := fun r θ => -P (pt r θ) * Real.sin θ + Q (pt r θ) * Real.cos θ
  set Fr : ℝ → ℝ → ℝ := fun r θ => (P (pt r θ) * Real.cos θ + Q (pt r θ) * Real.sin θ) +
    r * (fderiv ℝ P (pt r θ) (e θ) * Real.cos θ + fderiv ℝ Q (pt r θ) (e θ) * Real.sin θ)
  set Gt : ℝ → ℝ → ℝ := fun r θ =>
    -(r * fderiv ℝ P (pt r θ) (e θ * Complex.I)) * Real.sin θ - P (pt r θ) * Real.cos θ +
    (r * fderiv ℝ Q (pt r θ) (e θ * Complex.I) * Real.cos θ - Q (pt r θ) * Real.sin θ)
  have hptr : ∀ r θ, HasDerivAt (fun r => pt r θ) (e θ) r := by
    intro r θ
    simpa [hpt] using ((Complex.ofRealCLM.hasDerivAt (x := r)).mul_const (e θ))
  have hptt : ∀ r θ, HasDerivAt (fun θ => pt r θ) ((r : ℂ) * (e θ * Complex.I)) θ := by
    intro r θ
    have h1 : HasDerivAt (fun θ : ℝ => (θ : ℂ) * Complex.I) Complex.I θ := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := θ)).mul_const Complex.I
    have h2 := (h1.cexp).const_mul (r : ℂ)
    first
      | simpa [hpt, he, mul_comm, mul_left_comm, mul_assoc] using h2
      | simpa [hpt, he, mul_comm, mul_left_comm, mul_assoc, Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.neg_def, Function.comp_def] using h2
      | exact (h2.congr_deriv (by first | rfl | simp | (simp; ring))).congr_of_eventuallyEq
          (Filter.Eventually.of_forall fun _ => by first | rfl | simp | (simp; ring))
  have hFr : ∀ r θ, HasDerivAt (fun r => f r θ) (Fr r θ) r := by
    intro r θ
    have hP1 := (hPd (pt r θ)).hasFDerivAt.comp_hasDerivAt r (hptr r θ)
    have hQ1 := (hQd (pt r θ)).hasFDerivAt.comp_hasDerivAt r (hptr r θ)
    have := (hasDerivAt_id r).mul ((hP1.mul_const (Real.cos θ)).add (hQ1.mul_const (Real.sin θ)))
    -- Lean 4.35 / new Mathlib: `HasDerivAt.mul` is stated for the pointwise product `c * d`
    -- (not a lambda), so we transfer along an explicit pointwise equality and an explicit
    -- equality of derivative values instead of `convert`.
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · simp only [Fr, id_eq, id, Function.comp_apply, Pi.add_apply, Pi.mul_apply, one_mul]
      ring
    · simp only [f, id_eq, id, Function.comp_apply, Pi.add_apply, Pi.mul_apply]
      try ring1
  have hGt : ∀ r θ, HasDerivAt (fun θ => g r θ) (Gt r θ) θ := by
    intro r θ
    have hP1 := (hPd (pt r θ)).hasFDerivAt.comp_hasDerivAt θ (hptt r θ)
    have hQ1 := (hQd (pt r θ)).hasFDerivAt.comp_hasDerivAt θ (hptt r θ)
    have := ((hP1.neg).mul (Real.hasDerivAt_sin θ)).add (hQ1.mul (Real.hasDerivAt_cos θ))
    -- See `hFr`: explicit value equality and pointwise function equality instead of `convert`
    -- (unapplied `Function.comp` is no longer unfolded by `simp only [Function.comp]`).
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)
    · simp only [Gt, Function.comp_apply, Pi.neg_apply]
      have e1 : fderiv ℝ P (pt r θ) ((r : ℂ) * (e θ * Complex.I)) =
          r * fderiv ℝ P (pt r θ) (e θ * Complex.I) := by
        rw [show ((r : ℂ) * (e θ * Complex.I)) = r • (e θ * Complex.I) by simp, map_smul,
          smul_eq_mul]
      have e2 : fderiv ℝ Q (pt r θ) ((r : ℂ) * (e θ * Complex.I)) =
          r * fderiv ℝ Q (pt r θ) (e θ * Complex.I) := by
        rw [show ((r : ℂ) * (e θ * Complex.I)) = r • (e θ * Complex.I) by simp, map_smul,
          smul_eq_mul]
      rw [e1, e2]; ring
    · simp only [g, Function.comp_apply, Pi.neg_apply, Pi.add_apply, Pi.mul_apply]
      try ring1
  have hsum : ∀ r θ, Fr r θ + Gt r θ =
      r * (fderiv ℝ P (pt r θ) 1 + fderiv ℝ Q (pt r θ) Complex.I) := by
    intro r θ
    simp only [Fr, Gt, he] at *
    rw [fderiv_exp P, fderiv_exp Q]
    have h1 := hfdI P (pt r θ) θ
    have h2 := hfdI Q (pt r θ) θ
    rw [h1, h2]
    linear_combination (r * (fderiv ℝ P (pt r θ) 1 + fderiv ℝ Q (pt r θ) Complex.I)) *
      Real.sin_sq_add_cos_sq θ
  -- continuity
  have hptc : Continuous (Function.uncurry pt) := by
    simp only [hpt]; fun_prop
  have hFrc : Continuous (Function.uncurry Fr) := by
    have h1 : Continuous fun p : ℝ × ℝ => fderiv ℝ P (pt p.1 p.2) :=
      hPc.comp hptc
    have h2 : Continuous fun p : ℝ × ℝ => fderiv ℝ Q (pt p.1 p.2) :=
      hQc.comp hptc
    have h3 : Continuous fun p : ℝ × ℝ => pt p.1 p.2 := hptc
    have hPc0 := hP.continuous
    have hQc0 := hQ.continuous
    simp only [Fr]
    fun_prop
  have hGtc : Continuous (Function.uncurry Gt) := by
    have h1 : Continuous fun p : ℝ × ℝ => fderiv ℝ P (pt p.1 p.2) :=
      hPc.comp hptc
    have h2 : Continuous fun p : ℝ × ℝ => fderiv ℝ Q (pt p.1 p.2) :=
      hQc.comp hptc
    have h3 : Continuous fun p : ℝ × ℝ => pt p.1 p.2 := hptc
    have hPc0 := hP.continuous
    have hQc0 := hQ.continuous
    simp only [Gt]
    fun_prop
  have hHc : Continuous fun z => fderiv ℝ P z 1 + fderiv ℝ Q z Complex.I := by fun_prop
  rw [← SteklovH1.integral_rays_eq_disk hHc]
  -- inner integrals
  have hinner : ∀ θ : ℝ, ∫ r in (0:ℝ)..1, r * (fderiv ℝ P ((r : ℂ) * Complex.exp (θ * Complex.I)) 1 +
      fderiv ℝ Q ((r : ℂ) * Complex.exp (θ * Complex.I)) Complex.I) =
      (P (e θ) * Real.cos θ + Q (e θ) * Real.sin θ) + ∫ r in (0:ℝ)..1, Gt r θ := by
    intro θ
    have hc1 : Continuous fun r => Fr r θ := hFrc.comp (Continuous.prodMk_left θ)
    have hc2 : Continuous fun r => Gt r θ := hGtc.comp (Continuous.prodMk_left θ)
    have e1 : ∫ r in (0:ℝ)..1, r * (fderiv ℝ P ((r : ℂ) * Complex.exp (θ * Complex.I)) 1 +
        fderiv ℝ Q ((r : ℂ) * Complex.exp (θ * Complex.I)) Complex.I) =
        ∫ r in (0:ℝ)..1, (Fr r θ + Gt r θ) := by
      refine intervalIntegral.integral_congr fun r _ => ?_
      rw [hsum]
    rw [e1, intervalIntegral.integral_add (hc1.intervalIntegrable _ _) (hc2.intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun r _ => hFr r θ)
        (hc1.intervalIntegrable _ _)]
    simp [f, pt]
  simp_rw [hinner]
  have hcb : Continuous fun θ : ℝ => P (e θ) * Real.cos θ + Q (e θ) * Real.sin θ := by
    have := hP.continuous; have := hQ.continuous; fun_prop
  have hcg : Continuous fun θ => ∫ r in (0:ℝ)..1, Gt r θ := by
    have : Continuous (Function.uncurry fun θ r => Gt r θ) :=
      hGtc.comp continuous_swap
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' this 0 1
  rw [intervalIntegral.integral_add (hcb.intervalIntegrable _ _) (hcg.intervalIntegrable _ _)]
  have hzero : ∫ θ in (0:ℝ)..(2 * π), ∫ r in (0:ℝ)..1, Gt r θ = 0 := by
    rw [swap_rect (f := fun θ r => Gt r θ) (hGtc.comp continuous_swap) (by positivity)
      zero_le_one]
    have : ∀ r : ℝ, ∫ θ in (0:ℝ)..(2 * π), Gt r θ = 0 := by
      intro r
      have hc : Continuous fun θ => Gt r θ := hGtc.comp (Continuous.prodMk_right r)
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hGt r θ)
        (hc.intervalIntegrable _ _)]
      simp only [g, pt, he]
      have : Complex.exp (((2 * π : ℝ) : ℂ) * Complex.I) = Complex.exp (((0 : ℝ) : ℂ) * Complex.I) := by
        rw [show ((2 * π : ℝ) : ℂ) * Complex.I = 2 * π * Complex.I by push_cast; ring,
          Complex.exp_two_pi_mul_I]; simp
      rw [this]; simp
    simp [this]
  rw [hzero, add_zero]

/-- **Green's first identity on the unit disk**: for `u ∈ C²(ℂ)` and `v ∈ C¹(ℂ)`,
`∫_𝔻 ⟨∇u, ∇v⟩ + ∫_𝔻 v Δu = ∫_0^{2π} v(e^{iθ}) ∂_r u(e^{iθ}) dθ`, where
`∂_r u(e^{iθ}) = Du(e^{iθ})[e^{iθ}]` is the outward normal derivative. -/
theorem green_disk {u v : ℂ → ℝ} (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 1 v) :
    (∫ z in Metric.ball (0:ℂ) 1, ⟪SteklovH1.grad u z, SteklovH1.grad v z⟫) +
      ∫ z in Metric.ball (0:ℂ) 1, v z * Δ u z =
      ∫ θ in (0:ℝ)..(2 * π), v (Complex.exp (θ * Complex.I)) *
        fderiv ℝ u (Complex.exp (θ * Complex.I)) (Complex.exp (θ * Complex.I)) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hd2 : ContDiff ℝ 1 (fderiv ℝ u) := hu.fderiv_right (m := 1) (by norm_num)
  have hdu : ∀ w : ℂ, ContDiff ℝ 1 (fun z => fderiv ℝ u z w) := fun w =>
    hd2.clm_apply contDiff_const
  set P : ℂ → ℝ := fun z => v z * fderiv ℝ u z 1 with hP
  set Q : ℂ → ℝ := fun z => v z * fderiv ℝ u z Complex.I with hQ
  have hPc : ContDiff ℝ 1 P := hv.mul (hdu 1)
  have hQc : ContDiff ℝ 1 Q := hv.mul (hdu Complex.I)
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hdud : ∀ w : ℂ, Differentiable ℝ (fun z => fderiv ℝ u z w) := fun w =>
    (hdu w).differentiable one_ne_zero
  have hdiv : ∀ z, fderiv ℝ P z 1 + fderiv ℝ Q z Complex.I =
      ⟪SteklovH1.grad u z, SteklovH1.grad v z⟫ + v z * Δ u z := by
    intro z
    have e1 : fderiv ℝ P z 1 = fderiv ℝ v z 1 * fderiv ℝ u z 1 +
        v z * fderiv ℝ (fun z => fderiv ℝ u z 1) z 1 := by
      have := ((hvd z).hasFDerivAt.mul (hdud 1 z).hasFDerivAt).fderiv
      rw [hP, show (fun z => v z * fderiv ℝ u z 1) = v * (fun z => fderiv ℝ u z 1) from rfl,
        this]; simp; ring
    have e2 : fderiv ℝ Q z Complex.I = fderiv ℝ v z Complex.I * fderiv ℝ u z Complex.I +
        v z * fderiv ℝ (fun z => fderiv ℝ u z Complex.I) z Complex.I := by
      have := ((hvd z).hasFDerivAt.mul (hdud Complex.I z).hasFDerivAt).fderiv
      rw [hQ, show (fun z => v z * fderiv ℝ u z Complex.I) =
        v * (fun z => fderiv ℝ u z Complex.I) from rfl, this]; simp; ring
    rw [e1, e2, SteklovWeyl.laplacian_eq_fderiv_fderiv hu.contDiffAt,
      SteklovWeyl.inner_eq_re_im]
    have g1 : (SteklovH1.grad v z).re = fderiv ℝ v z 1 := by
      rw [← SteklovH1.inner_grad]; simp [Complex.inner]
    have g2 : (SteklovH1.grad v z).im = fderiv ℝ v z Complex.I := by
      rw [← SteklovH1.inner_grad]; simp [Complex.inner]
    rw [g1, g2, SteklovH1.inner_grad, SteklovH1.inner_grad]
    ring
  have hdisk := divergence_disk hPc hQc
  simp_rw [hdiv] at hdisk
  have hc1 : Continuous fun z => ⟪SteklovH1.grad u z, SteklovH1.grad v z⟫ :=
    (SteklovH1.continuous_grad hu1).inner (SteklovH1.continuous_grad hv)
  have hc2 : Continuous fun z => v z * Δ u z := by
    have : Continuous (Δ u) := by
      have : ∀ z, Δ u z = fderiv ℝ (fun z => fderiv ℝ u z 1) z 1 +
          fderiv ℝ (fun z => fderiv ℝ u z Complex.I) z Complex.I := fun z =>
        SteklovWeyl.laplacian_eq_fderiv_fderiv hu.contDiffAt
      rw [show Δ u = fun z => fderiv ℝ (fun z => fderiv ℝ u z 1) z 1 +
          fderiv ℝ (fun z => fderiv ℝ u z Complex.I) z Complex.I from funext this]
      have h1 := (hdu 1).continuous_fderiv one_ne_zero
      have h2 := (hdu Complex.I).continuous_fderiv one_ne_zero
      fun_prop
    exact hv.continuous.mul this
  have hint : ∀ {F : ℂ → ℝ}, Continuous F → IntegrableOn F (Metric.ball (0:ℂ) 1) := fun hF =>
    (hF.continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
      Metric.ball_subset_closedBall
  refine (integral_add (hint hc1) (hint hc2)).symm.trans (hdisk.trans ?_)
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [hP, hQ]
  rw [fderiv_exp u]; ring

end SteklovGreen
