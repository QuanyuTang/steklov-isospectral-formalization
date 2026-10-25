module

public import Mathlib

/-!
# A Friedrichs-type inequality on small disks

For a continuous function `v : ℂ → ℝ` that is `C¹` on the disk `|w| < 2a` (`0 < a ≤ 1/4`):

`∫_{|w|<a} v² ≤ 9 ∫_{a≤|w|<2a} v² + 4a ∫_{|w|<2a} |dv|²`   (`friedrichs_ball`).

The proof is elementary: along horizontal segments, `v(x)² ≤ v(x')² + ∫ (v² + |dv|²)` by the
fundamental theorem of calculus (`sq_le_segment`), integrated over a square containing the inner
disk and a rectangle contained in the annulus (Tonelli on `ℝ × ℝ ≃ ℂ`).

It is used to control the metric `L²` norm of orbifold functions near a cone point.
-/

@[expose] public section

open MeasureTheory Set Complex Metric
open scoped ENNReal

noncomputable section

namespace SteklovFriedrichs

lemma preimage_symm_equivRealProd (s t : Set ℝ) :
    (measurableEquivRealProd.symm ⁻¹' {z : ℂ | z.re ∈ s ∧ z.im ∈ t}) = s ×ˢ t := by
  ext p; simp [measurableEquivRealProd]

lemma lintegral_rect_eq (g : ℂ → ℝ≥0∞) (s t : Set ℝ) :
    ∫⁻ z in {z : ℂ | z.re ∈ s ∧ z.im ∈ t}, g z =
      ∫⁻ p in s ×ˢ t, g (p.1 + p.2 * I) := by
  have h := (Complex.volume_preserving_equiv_real_prod.symm).setLIntegral_comp_preimage_emb
    measurableEquivRealProd.symm.measurableEmbedding g {z : ℂ | z.re ∈ s ∧ z.im ∈ t}
  rw [← h, preimage_symm_equivRealProd]
  congr 1; funext p
  congr 1
  apply Complex.ext <;> simp [measurableEquivRealProd]

/-- One-dimensional estimate along a horizontal segment. -/
lemma sq_le_segment {v : ℂ → ℝ} {W : Set ℂ} (hW : IsOpen W) (hv : ContDiffOn ℝ 1 v W)
    {α β y x x' : ℝ} (hseg : ∀ t ∈ Icc α β, (t : ℂ) + y * I ∈ W) (hx : α ≤ x) (hxx' : x ≤ x')
    (hx' : x' ≤ β) :
    v (x + y * I) ^ 2 ≤ v (x' + y * I) ^ 2 +
      ∫ t in α..β, (v (t + y * I) ^ 2 + ‖fderiv ℝ v (t + y * I)‖ ^ 2) := by
  set γ : ℝ → ℂ := fun t => (t : ℂ) + y * I
  have hγ : ∀ t, HasDerivAt γ 1 t := fun t =>
    (Complex.ofRealCLM.hasDerivAt (x := t)).add_const (y * I)
  have hd : ∀ t ∈ Icc α β, HasDerivAt (fun t => v (γ t) ^ 2)
      (2 * v (γ t) * fderiv ℝ v (γ t) 1) t := by
    intro t ht
    have h1 : HasFDerivAt v (fderiv ℝ v (γ t)) (γ t) :=
      ((hv.contDiffAt (hW.mem_nhds (hseg t ht))).differentiableAt (by norm_num)).hasFDerivAt
    have h2 := h1.comp_hasDerivAt t (hγ t)
    have h3 := h2.pow 2
    convert h3 using 1
    simp
  have hfc : ContinuousOn (fderiv ℝ v) W := hv.continuousOn_fderiv_of_isOpen hW le_rfl
  have hvc : ContinuousOn v W := hv.continuousOn
  have hγc : Continuous γ := by fun_prop
  have hcont : ContinuousOn (fun t => 2 * v (γ t) * fderiv ℝ v (γ t) 1) (Icc α β) := by
    have a1 : ContinuousOn (fun t => v (γ t)) (Icc α β) :=
      hvc.comp hγc.continuousOn (fun t ht => hseg t ht)
    have a2 : ContinuousOn (fun t => fderiv ℝ v (γ t)) (Icc α β) :=
      hfc.comp hγc.continuousOn (fun t ht => hseg t ht)
    exact (continuousOn_const.mul a1).mul (a2.clm_apply continuousOn_const)
  have hsub : Icc x x' ⊆ Icc α β := Icc_subset_Icc hx hx'
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := x')
    (fun t ht => hd t (hsub (by rwa [uIcc_of_le hxx'] at ht)))
    ((hcont.mono hsub).intervalIntegrable_of_Icc hxx')
  have hHc : ContinuousOn (fun t => v (γ t) ^ 2 + ‖fderiv ℝ v (γ t)‖ ^ 2) (Icc α β) := by
    have a1 : ContinuousOn (fun t => v (γ t)) (Icc α β) :=
      hvc.comp hγc.continuousOn (fun t ht => hseg t ht)
    have a2 : ContinuousOn (fun t => fderiv ℝ v (γ t)) (Icc α β) :=
      hfc.comp hγc.continuousOn (fun t ht => hseg t ht)
    exact (a1.pow 2).add (a2.norm.pow 2)
  have hpt : ∀ t, |2 * v (γ t) * fderiv ℝ v (γ t) 1| ≤ v (γ t) ^ 2 + ‖fderiv ℝ v (γ t)‖ ^ 2 := by
    intro t
    have h1 : |fderiv ℝ v (γ t) 1| ≤ ‖fderiv ℝ v (γ t)‖ := by
      have := (fderiv ℝ v (γ t)).le_opNorm 1
      simpa using this
    rw [abs_mul, abs_mul, abs_two]
    nlinarith [abs_nonneg (v (γ t)), abs_nonneg (fderiv ℝ v (γ t) 1), sq_abs (v (γ t)),
      sq_nonneg (|v (γ t)| - ‖fderiv ℝ v (γ t)‖), norm_nonneg (fderiv ℝ v (γ t))]
  have hle1 : -(∫ t in x..x', 2 * v (γ t) * fderiv ℝ v (γ t) 1) ≤
      ∫ t in x..x', (v (γ t) ^ 2 + ‖fderiv ℝ v (γ t)‖ ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_mono_on hxx' ?_ ?_ fun t _ => ?_
    · exact ((hcont.mono hsub).intervalIntegrable_of_Icc hxx').neg
    · exact (hHc.mono hsub).intervalIntegrable_of_Icc hxx'
    · exact (neg_le_abs _).trans (hpt t)
  have hle2 : ∫ t in x..x', (v (γ t) ^ 2 + ‖fderiv ℝ v (γ t)‖ ^ 2) ≤
      ∫ t in α..β, (v (γ t) ^ 2 + ‖fderiv ℝ v (γ t)‖ ^ 2) := by
    rw [intervalIntegral.integral_of_le hxx',
      intervalIntegral.integral_of_le (hx.trans (hxx'.trans hx'))]
    refine setIntegral_mono_set ?_ ?_ ?_
    · exact (hHc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    · exact Filter.Eventually.of_forall fun t => by positivity
    · exact (Ioc_subset_Ioc hx hx').eventuallyLE
  show v (γ x) ^ 2 ≤ v (γ x') ^ 2 + _
  linarith

lemma setLIntegral_prod_symm' (f : ℝ × ℝ → ℝ≥0∞) (hf : Measurable f) (s t : Set ℝ) :
    ∫⁻ p in s ×ˢ t, f p = ∫⁻ y in t, ∫⁻ x in s, f (x, y) := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hf.aemeasurable]

/-- Integration of the segment estimate over rectangles. -/
lemma rect_ineq (F H : ℝ × ℝ → ℝ≥0∞) (hF : Measurable F) (hH : Measurable H) {a : ℝ}
    (ha : 0 < a)
    (hpt : ∀ y ∈ Icc (-a) a, ∀ x ∈ Icc (-a) a, ∀ x' ∈ Icc a (3 * a / 2),
      F (x, y) ≤ F (x', y) + ∫⁻ t in Icc (-a) (3 * a / 2), H (t, y)) :
    ENNReal.ofReal (a / 2) * (∫⁻ p in Icc (-a) a ×ˢ Icc (-a) a, F p) ≤
      ENNReal.ofReal (2 * a) * (∫⁻ p in Icc a (3 * a / 2) ×ˢ Icc (-a) a, F p) +
      ENNReal.ofReal (a ^ 2) * (∫⁻ p in Icc (-a) (3 * a / 2) ×ˢ Icc (-a) a, H p) := by
  rw [setLIntegral_prod_symm' F hF, setLIntegral_prod_symm' F hF, setLIntegral_prod_symm' H hH,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← lintegral_add_left]
  swap
  · exact (hF.lintegral_prod_left').const_mul _
  refine setLIntegral_mono' measurableSet_Icc fun y hy => ?_
  set K := ∫⁻ t in Icc (-a) (3 * a / 2), H (t, y)
  have hI2 : volume (Icc a (3 * a / 2)) = ENNReal.ofReal (a / 2) := by
    rw [Real.volume_Icc]; congr 1; ring
  have hI1 : volume (Icc (-a) a) = ENNReal.ofReal (2 * a) := by
    rw [Real.volume_Icc]; congr 1; ring
  have hx : ∀ x ∈ Icc (-a) a, ENNReal.ofReal (a / 2) * F (x, y) ≤
      (∫⁻ x' in Icc a (3 * a / 2), F (x', y)) + ENNReal.ofReal (a / 2) * K := by
    intro x hx
    calc ENNReal.ofReal (a / 2) * F (x, y) = ∫⁻ x' in Icc a (3 * a / 2), F (x, y) := by
          rw [setLIntegral_const, hI2, mul_comm]
      _ ≤ ∫⁻ x' in Icc a (3 * a / 2), (F (x', y) + K) :=
          setLIntegral_mono' measurableSet_Icc fun x' hx' => hpt y hy x hx x' hx'
      _ = _ := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const, hI2, mul_comm K]
  calc ENNReal.ofReal (a / 2) * ∫⁻ x in Icc (-a) a, F (x, y)
      = ∫⁻ x in Icc (-a) a, ENNReal.ofReal (a / 2) * F (x, y) :=
        (lintegral_const_mul _ (hF.comp (measurable_id.prodMk measurable_const))).symm
    _ ≤ ∫⁻ x in Icc (-a) a,
          ((∫⁻ x' in Icc a (3 * a / 2), F (x', y)) + ENNReal.ofReal (a / 2) * K) :=
        setLIntegral_mono' measurableSet_Icc hx
    _ = ENNReal.ofReal (2 * a) * (∫⁻ x' in Icc a (3 * a / 2), F (x', y)) +
          ENNReal.ofReal (a ^ 2) * K := by
        rw [setLIntegral_const, hI1, mul_comm, mul_add, ← mul_assoc,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 3; ring

lemma pointwise_enn {v : ℂ → ℝ} (hvc : Continuous v) {a : ℝ} (ha : 0 < a)
    (hv : ContDiffOn ℝ 1 v (ball 0 (2 * a))) {y x x' : ℝ} (hy : y ∈ Icc (-a) a)
    (hx : x ∈ Icc (-a) a) (hx' : x' ∈ Icc a (3 * a / 2)) :
    ‖v (x + y * I)‖ₑ ^ 2 ≤ ‖v (x' + y * I)‖ₑ ^ 2 +
      ∫⁻ t in Icc (-a) (3 * a / 2), (‖v (t + y * I)‖ₑ ^ 2 + ‖fderiv ℝ v (t + y * I)‖ₑ ^ 2) := by
  have hseg : ∀ t ∈ Icc (-a) (3 * a / 2), (t : ℂ) + y * I ∈ ball (0 : ℂ) (2 * a) := by
    intro t ht
    rw [mem_ball_zero_iff, ← sq_lt_sq₀ (norm_nonneg _) (by positivity),
      ← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply]
    nlinarith [ht.1, ht.2, hy.1, hy.2]
  have h := sq_le_segment isOpen_ball hv hseg hx.1 (hx.2.trans hx'.1) hx'.2
  have hfc : ContinuousOn (fderiv ℝ v) (ball 0 (2 * a)) :=
    hv.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl
  have hγc : Continuous fun t : ℝ => (t : ℂ) + y * I := by fun_prop
  have hHc : ContinuousOn (fun t : ℝ => v (t + y * I) ^ 2 + ‖fderiv ℝ v (t + y * I)‖ ^ 2)
      (Icc (-a) (3 * a / 2)) :=
    ((hvc.comp hγc).continuousOn.pow 2).add
      ((hfc.comp hγc.continuousOn fun t ht => hseg t ht).norm.pow 2)
  have hab : -a ≤ 3 * a / 2 := by linarith
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun t => by positivity)
      hHc.integrableOn_Icc.aestronglyMeasurable] at h
  have hfin : ∫⁻ t in Icc (-a) (3 * a / 2),
      ENNReal.ofReal (v (t + y * I) ^ 2 + ‖fderiv ℝ v (t + y * I)‖ ^ 2) ≠ ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun t => by positivity)).1
      hHc.integrableOn_Icc.2 |>.ne
  have h2 := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_add (by positivity) ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin] at h2
  convert h2 using 2
  · rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  · rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  · refine setLIntegral_congr_fun measurableSet_Icc fun t _ => ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]

lemma enn_alg {X T G : ℝ≥0∞} {a : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4) (hX : X < ⊤)
    (h : ENNReal.ofReal (a / 2) * X ≤ ENNReal.ofReal (2 * a) * T +
      ENNReal.ofReal (a ^ 2) * (X + T + G)) :
    X ≤ 9 * T + ENNReal.ofReal (4 * a) * G := by
  by_cases hT : T = ⊤
  · simp [hT]
  by_cases hG : G = ⊤
  · rw [hG, ENNReal.mul_top (by simp; linarith)]; simp
  lift X to NNReal using hX.ne
  lift T to NNReal using hT
  lift G to NNReal using hG
  rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_coe_nnreal (p := T),
    ← ENNReal.ofReal_coe_nnreal (p := G)] at h ⊢
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 by simp, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hX0 : (0 : ℝ) ≤ X := X.2
  have hT0 : (0 : ℝ) ≤ T := T.2
  have hG0 : (0 : ℝ) ≤ G := G.2
  nlinarith [mul_nonneg ha.le hX0, mul_nonneg ha.le hT0, mul_nonneg ha.le hG0,
    mul_nonneg (mul_nonneg ha.le ha.le) hX0, mul_nonneg (sub_nonneg.2 ha4) hX0]

/-- **Friedrichs-type inequality on a small disk.** -/
theorem friedrichs_ball {v : ℂ → ℝ} (hvc : Continuous v) {a : ℝ} (ha : 0 < a) (ha4 : a ≤ 1 / 4)
    (hv : ContDiffOn ℝ 1 v (ball 0 (2 * a))) :
    ∫⁻ w in ball (0 : ℂ) a, ‖v w‖ₑ ^ 2 ≤
      9 * (∫⁻ w in ball (0 : ℂ) (2 * a) \ ball 0 a, ‖v w‖ₑ ^ 2) +
      ENNReal.ofReal (4 * a) * ∫⁻ w in ball (0 : ℂ) (2 * a), ‖fderiv ℝ v w‖ₑ ^ 2 := by
  set Fc : ℂ → ℝ≥0∞ := fun w => ‖v w‖ₑ ^ 2
  set Gc : ℂ → ℝ≥0∞ := fun w => ‖fderiv ℝ v w‖ₑ ^ 2
  show ∫⁻ w in ball (0 : ℂ) a, Fc w ≤ 9 * (∫⁻ w in ball (0 : ℂ) (2 * a) \ ball 0 a, Fc w) +
      ENNReal.ofReal (4 * a) * ∫⁻ w in ball (0 : ℂ) (2 * a), Gc w
  have hFc : Measurable Fc := hvc.measurable.enorm.pow_const 2
  have hGc : Measurable Gc := (measurable_fderiv ℝ v).enorm.pow_const 2
  have hemb : Measurable fun p : ℝ × ℝ => (p.1 : ℂ) + p.2 * I := by fun_prop
  set A := {z : ℂ | z.re ∈ Icc (-a) a ∧ z.im ∈ Icc (-a) a}
  set T := {z : ℂ | z.re ∈ Icc a (3 * a / 2) ∧ z.im ∈ Icc (-a) a}
  set R := {z : ℂ | z.re ∈ Icc (-a) (3 * a / 2) ∧ z.im ∈ Icc (-a) a}
  have key := rect_ineq (fun p => Fc (p.1 + p.2 * I))
    (fun p => Fc (p.1 + p.2 * I) + Gc (p.1 + p.2 * I))
    (hFc.comp hemb) ((hFc.comp hemb).add (hGc.comp hemb)) ha
    (fun y hy x hx x' hx' => pointwise_enn hvc ha hv hy hx hx')
  rw [← lintegral_rect_eq Fc, ← lintegral_rect_eq Fc,
    ← lintegral_rect_eq (fun z => Fc z + Gc z)] at key
  rw [lintegral_add_left hFc] at key
  have hBA : ball (0 : ℂ) a ⊆ A := fun z hz => by
    have h1 := abs_re_le_norm z; have h2 := abs_im_le_norm z
    rw [mem_ball_zero_iff] at hz
    exact ⟨abs_le.1 (h1.trans hz.le), abs_le.1 (h2.trans hz.le)⟩
  have hTann : T ⊆ ball (0 : ℂ) (2 * a) \ ball 0 a := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff, ← sq_lt_sq₀ (norm_nonneg _) (by positivity),
        ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith
    · rw [mem_ball_zero_iff, not_lt]
      exact h1.trans ((le_abs_self _).trans (abs_re_le_norm z))
  have hRb : R ⊆ ball (0 : ℂ) (2 * a) := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
    rw [mem_ball_zero_iff, ← sq_lt_sq₀ (norm_nonneg _) (by positivity),
      ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    nlinarith
  have hRAT : R ⊆ A ∪ T := fun z hz => by
    obtain ⟨⟨h1, h2⟩, h3⟩ := hz
    by_cases hz : z.re ≤ a
    · exact Or.inl ⟨⟨h1, hz⟩, h3⟩
    · exact Or.inr ⟨⟨(not_le.1 hz).le, h2⟩, h3⟩
  set X := ∫⁻ z in A, Fc z
  set Tm := ∫⁻ z in T, Fc z
  have hXfin : X < ⊤ := by
    have hAc : A ⊆ closedBall (0 : ℂ) (2 * a) := fun z hz => by
      obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
      rw [mem_closedBall_zero_iff, ← sq_le_sq₀ (norm_nonneg _) (by positivity),
        ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      nlinarith
    have hi := ((hvc.pow 2).continuousOn.integrableOn_compact (μ := volume)
      (isCompact_closedBall (0 : ℂ) (2 * a))).2
    refine lt_of_le_of_lt (lintegral_mono_set hAc)
      (lt_of_eq_of_lt (lintegral_congr fun z => ?_) hi)
    simp [Fc, enorm_pow]
  have hRF : ∫⁻ z in R, Fc z ≤ X + Tm :=
    (lintegral_mono_set hRAT).trans (lintegral_union_le _ _ _)
  have hRG : ∫⁻ z in R, Gc z ≤ ∫⁻ w in ball (0 : ℂ) (2 * a), Gc w := lintegral_mono_set hRb
  have hTT : Tm ≤ ∫⁻ w in ball (0 : ℂ) (2 * a) \ ball 0 a, Fc w := lintegral_mono_set hTann
  have hXA : ∫⁻ w in ball (0 : ℂ) a, Fc w ≤ X := lintegral_mono_set hBA
  have key2 : ENNReal.ofReal (a / 2) * X ≤
      ENNReal.ofReal (2 * a) * (∫⁻ w in ball (0 : ℂ) (2 * a) \ ball 0 a, Fc w) +
      ENNReal.ofReal (a ^ 2) * (X + (∫⁻ w in ball (0 : ℂ) (2 * a) \ ball 0 a, Fc w) +
        ∫⁻ w in ball (0 : ℂ) (2 * a), Gc w) := by
    refine key.trans (add_le_add (mul_le_mul_right hTT _) (mul_le_mul_right ?_ _))
    exact add_le_add (hRF.trans (add_le_add le_rfl hTT)) hRG
  exact hXA.trans (enn_alg ha ha4 hXfin key2)

end SteklovFriedrichs
