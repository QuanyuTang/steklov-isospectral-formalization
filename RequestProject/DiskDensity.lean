module

public import Mathlib
public import RequestProject.DiskH1

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff Convolution

noncomputable section

namespace SteklovDensity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma eLpNorm_comp_smul {h : ℂ → E} (hh : AEStronglyMeasurable h volume) {r : ℝ} (hr : 0 < r) :
    eLpNorm (fun x => h (r • x)) 2 volume = ENNReal.ofReal r⁻¹ * eLpNorm h 2 volume := by
  have hmap := Measure.map_addHaar_smul (volume : Measure ℂ) hr.ne'
  rw [Complex.finrank_real_complex] at hmap
  have h1 : eLpNorm (fun x => h (r • x)) 2 volume =
      eLpNorm h 2 (Measure.map (fun x : ℂ => r • x) volume) := by
    rw [eLpNorm_map_measure]
    · rfl
    · rw [hmap]; exact hh.smul_measure _
    · exact (measurable_const_smul r).aemeasurable
  rw [h1, hmap, eLpNorm_smul_measure_of_ne_top (by simp) _ _ hh]
  congr 1
  rw [abs_of_pos (by positivity), ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
  congr 1
  rw [show ((1 / 2 : ℝ≥0∞).toReal) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, Real.sqrt_inv,
    Real.sqrt_sq hr.le]

/-- Mollification with a normalized bump `η = b.normed volume`. -/
abbrev moll (b : ContDiffBump (0 : ℂ)) (h : ℂ → E) : ℂ → E :=
  b.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h

lemma moll_apply (b : ContDiffBump (0 : ℂ)) (h : ℂ → E) (x : ℂ) :
    moll b h x = ∫ t, b.normed volume t • h (x - t) := by
  simp [moll, convolution_def]

/-- Pointwise Cauchy–Schwarz (Jensen) bound for a mollification. -/
lemma enorm_moll_sq_le (b : ContDiffBump (0 : ℂ)) (h : ℂ → E) (hh : StronglyMeasurable h) (x : ℂ) :
    ‖moll b h x‖ₑ ^ (2:ℝ) ≤ ∫⁻ t, ‖b.normed volume t‖ₑ * ‖h (x - t)‖ₑ ^ (2:ℝ) := by
  set a : ℂ → ℝ≥0∞ := fun t => ‖b.normed volume t‖ₑ
  have ha : Measurable a := (b.continuous_normed (μ := volume)).enorm.measurable
  have hc : Measurable fun t => ‖h (x - t)‖ₑ := (hh.comp_measurable (measurable_const.sub measurable_id)).enorm
  have hint : ∫⁻ t, a t = 1 := by
    have := ofReal_integral_eq_lintegral_ofReal (b.integrable_normed (μ := volume))
      (Eventually.of_forall fun t => b.nonneg_normed t)
    rw [b.integral_normed, ENNReal.ofReal_one] at this
    rw [this]
    refine lintegral_congr fun t => ?_
    simp [a, Real.enorm_eq_ofReal (b.nonneg_normed t)]
  have h1 : ‖moll b h x‖ₑ ≤ ∫⁻ t, a t * ‖h (x - t)‖ₑ := by
    rw [moll_apply]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun t => ?_
    simp [a, enorm_smul]
  have h2 : ∫⁻ t, a t * ‖h (x - t)‖ₑ ≤
      (∫⁻ t, a t) ^ (1/2:ℝ) * (∫⁻ t, a t * ‖h (x - t)‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ) := by
    have hpq : (2:ℝ).HolderConjugate 2 := by
      rw [Real.holderConjugate_iff]; norm_num
    have := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hpq
      (f := fun t => a t ^ (1/2:ℝ)) (g := fun t => a t ^ (1/2:ℝ) * ‖h (x - t)‖ₑ)
      (ha.pow_const _).aemeasurable ((ha.pow_const _).mul hc).aemeasurable
    have e1 : ∫⁻ t, a t * ‖h (x - t)‖ₑ =
        ∫⁻ t, a t ^ (1/2:ℝ) * (a t ^ (1/2:ℝ) * ‖h (x - t)‖ₑ) := by
      refine lintegral_congr fun t => ?_
      rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    have e2 : ∫⁻ t, a t = ∫⁻ t, (a t ^ (1/2:ℝ)) ^ (2:ℝ) := by
      refine lintegral_congr fun t => ?_
      rw [← ENNReal.rpow_mul]; norm_num
    have e3 : ∫⁻ t, a t * ‖h (x - t)‖ₑ ^ (2:ℝ) =
        ∫⁻ t, (a t ^ (1/2:ℝ) * ‖h (x - t)‖ₑ) ^ (2:ℝ) := by
      refine lintegral_congr fun t => ?_
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]; norm_num
    rw [e1, e2, e3]
    exact this
  rw [hint, ENNReal.one_rpow, one_mul] at h2
  calc ‖moll b h x‖ₑ ^ (2:ℝ) ≤ ((∫⁻ t, a t * ‖h (x - t)‖ₑ ^ (2:ℝ)) ^ (1/2:ℝ)) ^ (2:ℝ) :=
        ENNReal.rpow_le_rpow (h1.trans h2) (by norm_num)
    _ = ∫⁻ t, a t * ‖h (x - t)‖ₑ ^ (2:ℝ) := by
        rw [← ENNReal.rpow_mul]; norm_num

/-- **Mollification is an `L²` contraction.** -/
lemma eLpNorm_moll_le (b : ContDiffBump (0 : ℂ)) (h : ℂ → E) (hh : StronglyMeasurable h)
    (hm : AEStronglyMeasurable (moll b h) volume) :
    eLpNorm (moll b h) 2 volume ≤ eLpNorm h 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) hm,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp) hh.aestronglyMeasurable]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  simp only [show ((2 : ℝ≥0∞).toReal) = 2 by norm_num]
  set a : ℂ → ℝ≥0∞ := fun t => ‖b.normed volume t‖ₑ
  have ha : Measurable a := (b.continuous_normed (μ := volume)).enorm.measurable
  have hint : ∫⁻ t, a t = 1 := by
    have := ofReal_integral_eq_lintegral_ofReal (b.integrable_normed (μ := volume))
      (Eventually.of_forall fun t => b.nonneg_normed t)
    rw [b.integral_normed, ENNReal.ofReal_one] at this
    rw [this]
    refine lintegral_congr fun t => ?_
    simp [a, Real.enorm_eq_ofReal (b.nonneg_normed t)]
  calc ∫⁻ x, ‖moll b h x‖ₑ ^ (2:ℝ)
      ≤ ∫⁻ x, ∫⁻ t, a t * ‖h (x - t)‖ₑ ^ (2:ℝ) :=
        lintegral_mono fun x => enorm_moll_sq_le b h hh x
    _ = ∫⁻ t, ∫⁻ x, a t * ‖h (x - t)‖ₑ ^ (2:ℝ) := by
        refine lintegral_lintegral_swap ?_
        refine ((ha.comp measurable_snd).mul ?_).aemeasurable
        exact ((hh.comp_measurable (measurable_fst.sub measurable_snd)).enorm.pow_const _)
    _ = ∫⁻ t, a t * ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) := by
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ (by simp [a]),
          lintegral_sub_right_eq_self (fun x => ‖h x‖ₑ ^ (2:ℝ)) t]
    _ = ∫⁻ x, ‖h x‖ₑ ^ (2:ℝ) := by
        rw [lintegral_mul_const _ ha, hint, one_mul]

omit [NormedSpace ℝ E] in
/-- A uniformly small function supported in a fixed ball has small `L²` norm. -/
lemma exists_bound_eLpNorm (R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ k : ℂ → E, AEStronglyMeasurable k volume → (∀ x, ‖k x‖ ≤ c) →
      (∀ x, R < ‖x‖ → k x = 0) → eLpNorm k 2 volume ≤ ENNReal.ofReal ε := by
  set V : ℝ≥0∞ := volume (Metric.closedBall (0:ℂ) R) ^ ((2:ℝ≥0∞).toReal⁻¹)
  have hV : V ≠ (⊤ : ℝ≥0∞) := by
    refine ENNReal.rpow_ne_top_of_nonneg (by positivity) ?_
    exact measure_closedBall_lt_top.ne
  refine ⟨ε / (V.toReal + 1), by positivity, fun k hkm hk hs => ?_⟩
  have hsupp : Function.support k ⊆ Metric.closedBall 0 R := by
    intro x hx
    by_contra h'
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at h'
    exact hx (hs x h')
  rw [← eLpNorm_restrict_eq_of_support_subset hkm hsupp]
  refine (eLpNorm_le_of_ae_bound (C := ε / (V.toReal + 1)) hkm.restrict
    (Eventually.of_forall fun x => hk x)).trans ?_
  rw [Measure.restrict_apply_univ]
  change V * _ ≤ _
  rw [← ENNReal.ofReal_toReal (a := V) hV, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith [ENNReal.toReal_nonneg (a := V)]

omit [NormedSpace ℝ E] in
lemma exists_support_bound {h : ℂ → E} (hs : HasCompactSupport h) :
    ∃ R, 0 ≤ R ∧ ∀ x, R < ‖x‖ → h x = 0 := by
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  refine image_eq_zero_of_notMem_tsupport fun hx' => ?_
  have := hR hx'
  simp only [Metric.mem_closedBall, dist_zero_right] at this
  linarith [le_max_left R 0]

lemma continuous_moll (b : ContDiffBump (0 : ℂ)) {h : ℂ → E} (hh : LocallyIntegrable h volume) :
    Continuous (moll b h) :=
  b.hasCompactSupport_normed.continuous_convolution_left _ (b.continuous_normed (μ := volume)) hh

/-- Mollifications of a continuous compactly supported function converge in `L²`. -/
lemma cc_moll [CompleteSpace E] {h : ℂ → E} (hc : Continuous h) (hs : HasCompactSupport h) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ b : ContDiffBump (0 : ℂ), b.rOut < δ →
      eLpNorm (h - moll b h) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨R, hR0, hR⟩ := exists_support_bound hs
  obtain ⟨c, hc0, hcb⟩ := exists_bound_eLpNorm (E := E) (R + 1) hε
  obtain ⟨δ0, hδ0, hu⟩ := Metric.uniformContinuous_iff.mp
    (hs.uniformContinuous_of_continuous hc) c hc0
  refine ⟨min δ0 1, lt_min hδ0 one_pos, fun b hb => hcb (h - moll b h)
    (hc.aestronglyMeasurable.sub
      (continuous_moll b (hc.locallyIntegrable (μ := volume))).aestronglyMeasurable)
    (fun x => ?_) (fun x hx => ?_)⟩
  · rw [Pi.sub_apply, ← dist_eq_norm, dist_comm]
    refine b.dist_normed_convolution_le hc.aestronglyMeasurable (fun y hy => (hu ?_).le)
    exact (Metric.mem_ball.mp hy).trans (hb.trans_le (min_le_left _ _))
  · have h1 : h x = 0 := hR x (by linarith)
    have h2 : moll b h x = 0 := by
      rw [moll_apply]
      refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
      by_cases ht : ‖t‖ < 1
      · have : h (x - t) = 0 := hR _ (by
          have := norm_sub_norm_le x t
          linarith)
        simp [this]
      · have : b.normed volume t = 0 := by
          rw [← Function.notMem_support, b.support_normed_eq]
          simp only [Metric.mem_ball, dist_zero_right, not_lt]
          have := hb.trans_le (min_le_right _ _)
          linarith
        simp [this]
    simp [h1, h2]

omit [NormedSpace ℝ E] in
/-- Dilations of a continuous compactly supported function converge in `L²` as `r → 1`. -/
lemma cc_dil {h : ℂ → E} (hc : Continuous h) (hs : HasCompactSupport h) {ε : ℝ} (hε : 0 < ε) :
    ∃ r₀ : ℝ, 1/2 ≤ r₀ ∧ r₀ < 1 ∧ ∀ r : ℝ, r₀ ≤ r → r ≤ 1 →
      eLpNorm (h - fun x => h (r • x)) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨R, hR0, hR⟩ := exists_support_bound hs
  obtain ⟨c, hc0, hcb⟩ := exists_bound_eLpNorm (E := E) (2 * R + 1) hε
  obtain ⟨δ0, hδ0, hu⟩ := Metric.uniformContinuous_iff.mp
    (hs.uniformContinuous_of_continuous hc) c hc0
  refine ⟨max (1/2) (1 - δ0 / (2 * R + 2)), le_max_left _ _, max_lt (by norm_num)
    (by have : 0 < δ0 / (2 * R + 2) := by positivity
        linarith), fun r hr0 hr1 => hcb (h - fun x => h (r • x))
      (hc.aestronglyMeasurable.sub
        (by fun_prop : Continuous fun x : ℂ => h (r • x)).aestronglyMeasurable)
      (fun x => ?_) (fun x hx => ?_)⟩
  · have hr2 : 1/2 ≤ r := (le_max_left _ _).trans hr0
    have hr3 : 1 - δ0 / (2 * R + 2) ≤ r := (le_max_right _ _).trans hr0
    rw [Pi.sub_apply]
    by_cases hx : ‖x‖ ≤ 2 * R + 1
    · rw [← dist_eq_norm]
      refine (hu ?_).le
      rw [dist_eq_norm, show x - r • x = (1 - r) • x by rw [sub_smul, one_smul], norm_smul,
        Real.norm_of_nonneg (by linarith)]
      have h4 : 1 - r ≤ δ0 / (2 * R + 2) := by linarith
      calc (1 - r) * ‖x‖ ≤ δ0 / (2 * R + 2) * (2 * R + 1) :=
            mul_le_mul h4 hx (norm_nonneg _) (by positivity)
        _ < δ0 := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith
    · push_neg at hx
      have h1 : h x = 0 := hR x (by linarith)
      have h2 : h (r • x) = 0 := hR _ (by
        rw [norm_smul, Real.norm_of_nonneg (by linarith)]
        nlinarith)
      simp only [h1, h2, sub_zero, norm_zero]; exact hc0.le
  · have hr2 : 1/2 ≤ r := (le_max_left _ _).trans hr0
    have h1 : h x = 0 := hR x (by linarith)
    have h2 : h (r • x) = 0 := hR _ (by
      rw [norm_smul, Real.norm_of_nonneg (by linarith)]
      nlinarith)
    simp only [Pi.sub_apply, h1, h2, sub_zero]

lemma integrable_moll (b : ContDiffBump (0 : ℂ)) {h : ℂ → E} (hh : LocallyIntegrable h volume)
    (x : ℂ) : Integrable (fun t => b.normed volume t • h (x - t)) volume := by
  have := b.hasCompactSupport_normed.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ)
    (b.continuous_normed (μ := volume)) hh x
  simpa [ConvolutionExistsAt] using this

lemma moll_sub (b : ContDiffBump (0 : ℂ)) {h k : ℂ → E} (hh : LocallyIntegrable h volume)
    (hk : LocallyIntegrable k volume) : moll b (h - k) = moll b h - moll b k := by
  funext x
  simp only [moll_apply, Pi.sub_apply, smul_sub]
  exact integral_sub (integrable_moll b hh x) (integrable_moll b hk x)

lemma ofReal_third {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (ε/3) + (ENNReal.ofReal (ε/3) + ENNReal.ofReal (ε/3)) = ENNReal.ofReal ε := by
  rw [← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  congr 1; ring

/-- **Mollifications of an `L²` function converge to it in `L²`.** -/
lemma moll_tendsto [CompleteSpace E] {F : ℂ → E} (hF : MemLp F 2 volume) (hFm : StronglyMeasurable F) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ b : ContDiffBump (0 : ℂ), b.rOut < δ →
      eLpNorm (F - moll b F) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨h, hhs, hFh, hhc, hhm⟩ := hF.exists_hasCompactSupport_eLpNorm_sub_le
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (ε := ENNReal.ofReal (ε/3))
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨δ, hδ, hmol⟩ := cc_moll hhc hhs (ε := ε/3) (by positivity)
  refine ⟨δ, hδ, fun b hb => ?_⟩
  have hFl := hF.locallyIntegrable one_le_two
  have hhl := hhc.locallyIntegrable (μ := volume)
  have hdec : F - moll b F = (F - h) + ((h - moll b h) + moll b (h - F)) := by
    rw [moll_sub b hhl hFl]; abel
  rw [hdec]
  have hm3 : AEStronglyMeasurable (moll b (h - F)) volume :=
    (continuous_moll b (hhl.sub hFl)).aestronglyMeasurable
  calc eLpNorm ((F - h) + ((h - moll b h) + moll b (h - F))) 2 volume
      ≤ eLpNorm (F - h) 2 volume + (eLpNorm (h - moll b h) 2 volume +
          eLpNorm (moll b (h - F)) 2 volume) :=
        (eLpNorm_add_le (f := F - h) (g := (h - moll b h) + moll b (h - F)) one_le_two).trans
          (add_le_add_right (eLpNorm_add_le (f := h - moll b h) (g := moll b (h - F))
            one_le_two) _)
    _ ≤ ENNReal.ofReal (ε/3) + (ENNReal.ofReal (ε/3) + ENNReal.ofReal (ε/3)) := by
        refine add_le_add hFh (add_le_add (hmol b hb) ?_)
        refine (eLpNorm_moll_le b _ (hhc.stronglyMeasurable.sub hFm) hm3).trans ?_
        rw [eLpNorm_sub_comm]; exact hFh
    _ = ENNReal.ofReal ε := ofReal_third hε

/-- **Dilations of an `L²` function converge to it in `L²` as `r → 1⁻`.** -/
lemma dil_tendsto {F : ℂ → E} (hF : MemLp F 2 volume) (hFm : StronglyMeasurable F) {ε : ℝ}
    (hε : 0 < ε) : ∃ r₀ : ℝ, 1/2 ≤ r₀ ∧ r₀ < 1 ∧ ∀ r : ℝ, r₀ ≤ r → r ≤ 1 →
      eLpNorm (F - fun x => F (r • x)) 2 volume ≤ ENNReal.ofReal ε := by
  obtain ⟨h, hhs, hFh, hhc, hhm⟩ := hF.exists_hasCompactSupport_eLpNorm_sub_le
    (by simp : (2:ℝ≥0∞) ≠ ⊤) (ε := ENNReal.ofReal (ε/6))
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  obtain ⟨r₀, hr₀, hr₁, hdil⟩ := cc_dil hhc hhs (ε := ε/3) (by positivity)
  refine ⟨r₀, hr₀, hr₁, fun r hr0 hr1 => ?_⟩
  have hr : 0 < r := by linarith
  have hdec : (F - fun x => F (r • x)) =
      (F - h) + ((h - fun x => h (r • x)) + fun x => (h - F) (r • x)) := by
    funext x; simp only [Pi.add_apply, Pi.sub_apply]; abel
  rw [hdec]
  have h3 : eLpNorm (fun x => (h - F) (r • x)) 2 volume ≤ ENNReal.ofReal (ε/3) := by
    rw [eLpNorm_comp_smul (hhc.stronglyMeasurable.sub hFm).aestronglyMeasurable hr,
      eLpNorm_sub_comm]
    calc ENNReal.ofReal r⁻¹ * eLpNorm (F - h) 2 volume
        ≤ ENNReal.ofReal 2 * ENNReal.ofReal (ε/6) := by
          refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) hFh
          rw [inv_le_comm₀ hr (by norm_num)]; linarith
      _ = ENNReal.ofReal (ε/3) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
  calc eLpNorm ((F - h) + ((h - fun x => h (r • x)) + fun x => (h - F) (r • x))) 2 volume
      ≤ eLpNorm (F - h) 2 volume + (eLpNorm (h - fun x => h (r • x)) 2 volume +
          eLpNorm (fun x => (h - F) (r • x)) 2 volume) :=
        (eLpNorm_add_le (f := F - h)
          (g := (h - fun x => h (r • x)) + fun x => (h - F) (r • x)) one_le_two).trans
          (add_le_add_right (eLpNorm_add_le (f := h - fun x => h (r • x))
            (g := fun x => (h - F) (r • x)) one_le_two) _)
    _ ≤ ENNReal.ofReal (ε/3) + (ENNReal.ofReal (ε/3) + ENNReal.ofReal (ε/3)) := by
        refine add_le_add (hFh.trans (ENNReal.ofReal_le_ofReal (by linarith)))
          (add_le_add (hdil r hr0 hr1) h3)
    _ = ENNReal.ofReal ε := ofReal_third hε

/-! ### Gradient of a mollified weak pair -/

/-- The reflected, translated bump `s ↦ η(x - s)` used as a test function. -/
lemma reflected_bump_props (b : ContDiffBump (0 : ℂ)) (x : ℂ) :
    ContDiff ℝ ∞ (fun s => b.normed volume (x - s)) ∧
    HasCompactSupport (fun s => b.normed volume (x - s)) ∧
    tsupport (fun s => b.normed volume (x - s)) ⊆ Metric.closedBall x b.rOut := by
  have hsupp : ∀ s, b.normed volume (x - s) ≠ 0 → s ∈ Metric.closedBall x b.rOut := by
    intro s hs
    have : x - s ∈ Function.support (b.normed volume) := hs
    rw [b.support_normed_eq, Metric.mem_ball, dist_zero_right] at this
    rw [Metric.mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]; exact this.le
  have hts : tsupport (fun s => b.normed volume (x - s)) ⊆ Metric.closedBall x b.rOut :=
    closure_minimal (fun s hs => hsupp s hs) Metric.isClosed_closedBall
  refine ⟨(b.contDiff_normed (n := ⊤)).comp (contDiff_const.sub contDiff_id), ?_, hts⟩
  exact HasCompactSupport.intro (isCompact_closedBall x b.rOut)
    (fun s hs => by by_contra h; exact hs (hsupp s h))

lemma fderiv_reflected_bump (b : ContDiffBump (0 : ℂ)) (x s v : ℂ) :
    fderiv ℝ (fun s => b.normed volume (x - s)) s v = - fderiv ℝ (b.normed volume) (x - s) v := by
  have h1 : HasFDerivAt (b.normed volume) (fderiv ℝ (b.normed volume) (x - s)) (x - s) :=
    ((b.contDiff_normed (n := 1)).differentiable one_ne_zero _).hasFDerivAt
  have h2 : HasFDerivAt (fun s => b.normed volume (x - s))
      ((fderiv ℝ (b.normed volume) (x - s)).comp (-ContinuousLinearMap.id ℝ ℂ)) s :=
    h1.comp s ((hasFDerivAt_id s).const_sub x)
  rw [h2.fderiv]
  simp

/-- **The gradient of a mollified weak pair is the mollified weak gradient.** If `G` is the weak
gradient of `F` on an open set `U` (tested against compactly supported smooth functions with
support in `U`), then at every `x` with `closedBall x rOut ⊆ U`, `∇(η ⋆ F)(x) = (η ⋆ G)(x)`. -/
lemma grad_moll (U : Set ℂ) {F : ℂ → ℝ} {G : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (hG : LocallyIntegrable G volume)
    (hw : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v : ℂ,
      ∫ t, F t * fderiv ℝ φ t v = - ∫ t, inner ℝ (G t) v * φ t)
    (b : ContDiffBump (0 : ℂ)) (x : ℂ) (hx : Metric.closedBall x b.rOut ⊆ U) :
    SteklovH1.grad (moll b F) x = moll b G x := by
  set η := b.normed volume with hη
  have hd := (b.hasCompactSupport_normed (μ := volume)).hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (b.contDiff_normed (μ := volume) (n := 1)) hF x
  have hcf : HasCompactSupport (fderiv ℝ η) :=
    (b.hasCompactSupport_normed (μ := volume)).fderiv (𝕜 := ℝ)
  have hcf' : Continuous (fderiv ℝ η) :=
    (b.contDiff_normed (μ := volume) (n := 1)).continuous_fderiv one_ne_zero
  have hint := hcf.convolutionExists_left
    (L := (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL ℂ) hcf' hF x
  obtain ⟨hφ1, hφ2, hφ3⟩ := reflected_bump_props b x
  refine ext_inner_right ℝ fun v => ?_
  rw [SteklovH1.inner_grad, hd.fderiv]
  -- the left side
  have eL : (fderiv ℝ η ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL ℂ,
      volume] F) x v = ∫ s, fderiv ℝ η (x - s) v * F s := by
    rw [convolution_def, ContinuousLinearMap.integral_apply hint]
    simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
    have := integral_sub_left_eq_self (fun s => fderiv ℝ η (x - s) v * F s) (μ := volume) x
    simp only [sub_sub_cancel] at this
    rw [← this]
  -- the right side
  have hintG := integrable_moll b hG x
  have eR : inner ℝ (moll b G x) v = ∫ s, inner ℝ (G s) v * η (x - s) := by
    rw [moll_apply, real_inner_comm, ← integral_inner hintG]
    have := integral_sub_left_eq_self (fun s => inner ℝ (G s) v * η (x - s)) (μ := volume) x
    simp only [sub_sub_cancel] at this
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [real_inner_smul_right, real_inner_comm v, hη]
    ring
  rw [eL, eR]
  have key := hw _ hφ1 hφ2 (hφ3.trans hx) v
  simp only [fderiv_reflected_bump] at key
  rw [← hη] at key
  have e3 : ∫ s, fderiv ℝ η (x - s) v * F s = - ∫ t, F t * -fderiv ℝ η (x - t) v := by
    rw [← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only; ring
  rw [e3, key, neg_neg]

lemma contDiff_moll (b : ContDiffBump (0 : ℂ)) {F : ℂ → ℝ} (hF : LocallyIntegrable F volume) :
    ContDiff ℝ ∞ (moll b F) :=
  (b.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left _
    (b.contDiff_normed (μ := volume) (n := ⊤)) hF

/-- Gradient of a dilated mollification. -/
lemma grad_dil_moll (U : Set ℂ) {F : ℂ → ℝ} {G : ℂ → ℂ} (hF : LocallyIntegrable F volume)
    (hG : LocallyIntegrable G volume)
    (hw : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U → ∀ v : ℂ,
      ∫ t, F t * fderiv ℝ φ t v = - ∫ t, inner ℝ (G t) v * φ t)
    (b : ContDiffBump (0 : ℂ)) (r : ℝ) (z : ℂ)
    (hz : Metric.closedBall (r • z) b.rOut ⊆ U) :
    SteklovH1.grad (fun z => moll b F (r • z)) z = r • moll b G (r • z) := by
  have hdiff : DifferentiableAt ℝ (moll b F) (r • z) :=
    ((contDiff_moll b hF).differentiable (by simp)) _
  have hd : HasFDerivAt (fun z => moll b F (r • z))
      ((fderiv ℝ (moll b F) (r • z)).comp (r • ContinuousLinearMap.id ℝ ℂ)) z :=
    hdiff.hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul r)
  refine ext_inner_right ℝ fun v => ?_
  rw [SteklovH1.inner_grad, hd.fderiv, real_inner_smul_left,
    ← grad_moll U hF hG hw b (r • z) hz, SteklovH1.inner_grad]
  simp

end SteklovDensity

namespace SteklovH1

open SteklovDensity

lemma norm_amb_le (x : Amb) : ‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 x
  nlinarith [norm_nonneg x, norm_nonneg x.fst, norm_nonneg x.snd]

lemma eLpNorm_add3_le {E : Type*} [NormedAddCommGroup E] {a b c : ℂ → E} :
    eLpNorm (a + b + c) 2 volume ≤ eLpNorm a 2 volume + eLpNorm b 2 volume + eLpNorm c 2 volume :=
  (eLpNorm_add_le (f := a + b) (g := c) one_le_two).trans
    (add_le_add_left (eLpNorm_add_le (f := a) (g := b) one_le_two) _)

/-- **Converse weak-gradient identification on the disk.** If `f ∈ L²(𝔻)` and `g ∈ L²(𝔻; ℝ²)`
satisfy `∫_𝔻 f ∂_v φ = -∫_𝔻 ⟪g, v⟫ φ` for every compactly supported smooth `φ` in `𝔻` and every
constant vector `v`, then `(f, g)` lies in `H¹(𝔻)`, the closure of the smooth graphs.
The proof dilates (`z ↦ r z`, `r < 1`) and mollifies, with explicit `L²` estimates. -/
theorem mem_H1_of_weak_gradient (f : Lp ℝ 2 μD) (g : Lp ℂ 2 μD)
    (hw : ∀ φ : ℂ → ℝ, IsDiskTest φ → ∀ v : ℂ,
      ∫ z in Metric.ball (0:ℂ) 1, f z * fderiv ℝ φ z v =
        - ∫ z in Metric.ball (0:ℂ) 1, inner ℝ (g z) v * φ z) :
    (WithLp.toLp 2 (f, g) : Amb) ∈ H1 := by
  set B : Set ℂ := Metric.ball (0:ℂ) 1 with hB
  have hBm : MeasurableSet B := measurableSet_ball
  set F : ℂ → ℝ := B.indicator (f : ℂ → ℝ) with hFdef
  set G : ℂ → ℂ := B.indicator (g : ℂ → ℂ) with hGdef
  have hFm : StronglyMeasurable F := (Lp.stronglyMeasurable f).indicator hBm
  have hGm : StronglyMeasurable G := (Lp.stronglyMeasurable g).indicator hBm
  have hFL : MemLp F 2 volume := (memLp_indicator_iff_restrict hBm).2 (Lp.memLp f)
  have hGL : MemLp G 2 volume := (memLp_indicator_iff_restrict hBm).2 (Lp.memLp g)
  have hFl := hFL.locallyIntegrable one_le_two
  have hGl := hGL.locallyIntegrable one_le_two
  have hwF : ∀ φ : ℂ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ B →
      ∀ v : ℂ, ∫ t, F t * fderiv ℝ φ t v = - ∫ t, inner ℝ (G t) v * φ t := by
    intro φ h1 h2 h3 v
    have e1 : (fun t => F t * fderiv ℝ φ t v) = B.indicator (fun t => f t * fderiv ℝ φ t v) := by
      funext t; by_cases ht : t ∈ B <;> simp [hFdef, ht]
    have e2 : (fun t => inner ℝ (G t) v * φ t) = B.indicator (fun t => inner ℝ (g t) v * φ t) := by
      funext t; by_cases ht : t ∈ B <;> simp [hGdef, ht]
    rw [e1, e2, integral_indicator hBm, integral_indicator hBm]
    exact hw φ ⟨h1, h2, h3⟩ v
  rw [← SetLike.mem_coe, H1, Submodule.topologicalClosure_coe, Metric.mem_closure_iff]
  intro ε hε
  set e : ℝ := ε / 8 with he
  have he0 : 0 < e := by positivity
  -- choice of the dilation
  obtain ⟨r₁, hr₁a, hr₁b, hdF⟩ := dil_tendsto hFL hFm he0
  obtain ⟨r₂, hr₂a, hr₂b, hdG⟩ := dil_tendsto hGL hGm he0
  set M : ℝ := (eLpNorm G 2 volume).toReal with hM
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  set r : ℝ := max (max r₁ r₂) (1 - e / (2 * M + 1)) with hr
  have hr1 : r < 1 := max_lt (max_lt hr₁b hr₂b) (by
    have : 0 < e / (2 * M + 1) := by positivity
    linarith)
  have hrF : r₁ ≤ r := (le_max_left _ _).trans (le_max_left _ _)
  have hrG : r₂ ≤ r := (le_max_right _ _).trans (le_max_left _ _)
  have hr3 : 1 - e / (2 * M + 1) ≤ r := le_max_right _ _
  have hr12 : 1/2 ≤ r := hr₁a.trans hrF
  have hr0 : 0 < r := by linarith
  -- choice of the mollifier
  obtain ⟨δ₁, hδ₁, hmF⟩ := moll_tendsto hFL hFm he0
  obtain ⟨δ₂, hδ₂, hmG⟩ := moll_tendsto hGL hGm he0
  set ρ : ℝ := min (min δ₁ δ₂) (1 - r) / 2 with hρ
  have hρ0 : 0 < ρ := by
    have : 0 < min (min δ₁ δ₂) (1 - r) := lt_min (lt_min hδ₁ hδ₂) (by linarith)
    positivity
  have hρm : ρ < min (min δ₁ δ₂) (1 - r) := by
    have : 0 < min (min δ₁ δ₂) (1 - r) := lt_min (lt_min hδ₁ hδ₂) (by linarith)
    rw [hρ]; linarith
  let b : ContDiffBump (0 : ℂ) := ⟨ρ / 2, ρ, by positivity, by linarith⟩
  have hb : b.rOut = ρ := rfl
  have hb1 : b.rOut < δ₁ := by rw [hb]; exact hρm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hb2 : b.rOut < δ₂ := by rw [hb]; exact hρm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hb3 : r + b.rOut < 1 := by
    have := hρm.trans_le (min_le_right _ _); rw [hb]; linarith
  -- the smooth approximant
  set u : ℂ → ℝ := fun z => moll b F (r • z) with hu
  have husmooth : u ∈ smoothFns :=
    (contDiff_moll b hFl).comp (contDiff_const_smul r)
  refine ⟨embed ⟨u, husmooth⟩, LinearMap.mem_range_self _ _, ?_⟩
  rw [dist_eq_norm]
  refine (norm_amb_le _).trans_lt ?_
  simp only [WithLp.sub_fst, WithLp.sub_snd, embed_fst, embed_snd]
  -- gradient identity on the disk
  have hgradu : ∀ z ∈ B, grad u z = r • moll b G (r • z) := by
    intro z hz
    refine grad_dil_moll B hFl hGl hwF b r z ?_
    intro y hy
    rw [Metric.mem_closedBall] at hy
    rw [hB, Metric.mem_ball, dist_zero_right] at hz ⊢
    have h1 : ‖r • z‖ ≤ r := by
      rw [norm_smul, Real.norm_of_nonneg hr0.le]
      nlinarith [norm_nonneg z]
    have h2 := norm_le_norm_add_norm_sub' y (r • z)
    rw [dist_eq_norm] at hy
    linarith
  have hcmF := continuous_moll b hFl
  have hcmG := continuous_moll b hGl
  -- the function estimate
  have hfun : ‖(f - toL2 ⟨u, husmooth⟩ : Lp ℝ 2 μD)‖ ≤ 3 * e := by
    rw [Lp.norm_def]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have hae : ((f - toL2 ⟨u, husmooth⟩ : Lp ℝ 2 μD) : ℂ → ℝ) =ᵐ[μD]
        (F - fun z => F (r • z)) + fun z => (F - moll b F) (r • z) := by
      filter_upwards [Lp.coeFn_sub f (toL2 ⟨u, husmooth⟩), toL2_ae ⟨u, husmooth⟩,
        ae_restrict_mem hBm] with z h1 h2 h3
      have hFz : F z = f z := Set.indicator_of_mem h3 _
      rw [h1, Pi.sub_apply, h2]
      simp only [Pi.add_apply, Pi.sub_apply, hFz, hu]
      ring
    rw [eLpNorm_congr_ae hae]
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    refine (eLpNorm_add_le (f := F - fun z => F (r • z))
      (g := fun z => (F - moll b F) (r • z)) one_le_two).trans ?_
    rw [eLpNorm_comp_smul (hFm.sub hcmF.stronglyMeasurable).aestronglyMeasurable hr0]
    calc eLpNorm (F - fun z => F (r • z)) 2 volume +
          ENNReal.ofReal r⁻¹ * eLpNorm (F - moll b F) 2 volume
        ≤ ENNReal.ofReal e + ENNReal.ofReal 2 * ENNReal.ofReal e := by
          refine add_le_add (hdF r hrF hr1.le) (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_)
            (hmF b hb1))
          rw [inv_le_comm₀ hr0 (by norm_num)]; linarith
      _ = ENNReal.ofReal (3 * e) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add he0.le (by positivity)]
          congr 1; ring
  -- the gradient estimate
  have hgr : ‖(g - gradL2 ⟨u, husmooth⟩ : Lp ℂ 2 μD)‖ ≤ 3 * e := by
    rw [Lp.norm_def]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    have hae : ((g - gradL2 ⟨u, husmooth⟩ : Lp ℂ 2 μD) : ℂ → ℂ) =ᵐ[μD]
        (G - fun z => G (r • z)) + (1 - r) • (fun z => G (r • z)) +
          r • (fun z => (G - moll b G) (r • z)) := by
      filter_upwards [Lp.coeFn_sub g (gradL2 ⟨u, husmooth⟩), gradL2_ae ⟨u, husmooth⟩,
        ae_restrict_mem hBm] with z h1 h2 h3
      have hGz : G z = g z := Set.indicator_of_mem h3 _
      rw [h1, Pi.sub_apply, h2]
      change g z - grad u z = _
      rw [hgradu z h3]
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, hGz, smul_sub, sub_smul, one_smul]
      abel
    rw [eLpNorm_congr_ae hae]
    refine (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ?_
    refine eLpNorm_add3_le.trans ?_
    have eA : eLpNorm ((1 - r) • fun z => G (r • z)) 2 volume =
        ENNReal.ofReal (1 - r) * (ENNReal.ofReal r⁻¹ * ENNReal.ofReal M) := by
      rw [eLpNorm_const_smul, eLpNorm_comp_smul hGm.aestronglyMeasurable hr0, hM,
        ENNReal.ofReal_toReal hGL.eLpNorm_ne_top, Real.enorm_eq_ofReal (by linarith)]
    have eB : eLpNorm (r • fun z => (G - moll b G) (r • z)) 2 volume =
        ENNReal.ofReal r * (ENNReal.ofReal r⁻¹ * eLpNorm (G - moll b G) 2 volume) := by
      rw [eLpNorm_const_smul,
        eLpNorm_comp_smul (hGm.sub hcmG.stronglyMeasurable).aestronglyMeasurable hr0,
        Real.enorm_eq_ofReal hr0.le]
    rw [eA, eB]
    have hA : ENNReal.ofReal (1 - r) * (ENNReal.ofReal r⁻¹ * ENNReal.ofReal M) ≤
        ENNReal.ofReal e := by
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by linarith)]
      refine ENNReal.ofReal_le_ofReal ?_
      have h4 : 1 - r ≤ e / (2 * M + 1) := by linarith
      have h5 : r⁻¹ ≤ 2 := by rw [inv_le_comm₀ hr0 (by norm_num)]; linarith
      calc (1 - r) * (r⁻¹ * M) ≤ e / (2 * M + 1) * (2 * M) := by
            refine mul_le_mul h4 ?_ (by positivity) (by positivity)
            nlinarith
        _ ≤ e := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith
    have hB' : ENNReal.ofReal r * (ENNReal.ofReal r⁻¹ * eLpNorm (G - moll b G) 2 volume) ≤
        ENNReal.ofReal e := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hr0.le, mul_inv_cancel₀ hr0.ne', ENNReal.ofReal_one,
        one_mul]
      exact hmG b hb2
    calc eLpNorm (G - fun z => G (r • z)) 2 volume +
          ENNReal.ofReal (1 - r) * (ENNReal.ofReal r⁻¹ * ENNReal.ofReal M) +
          ENNReal.ofReal r * (ENNReal.ofReal r⁻¹ * eLpNorm (G - moll b G) 2 volume)
        ≤ ENNReal.ofReal e + ENNReal.ofReal e + ENNReal.ofReal e :=
          add_le_add (add_le_add (hdG r hrG hr1.le) hA) hB'
      _ = ENNReal.ofReal (3 * e) := by
          rw [← ENNReal.ofReal_add he0.le he0.le, ← ENNReal.ofReal_add (by positivity) he0.le]
          congr 1; ring
  calc _ ≤ 3 * e + 3 * e := add_le_add hfun hgr
    _ < ε := by rw [he]; linarith

end SteklovH1

namespace SteklovH1

/-- `(f, g) ∈ L²(𝔻) × L²(𝔻; ℝ²)` is a **weak-gradient pair**: `g` is the weak gradient of `f`
on the open unit disk, i.e. `∫_𝔻 f ∂_v φ = -∫_𝔻 ⟪g, v⟫ φ` for every compactly supported smooth
`φ` with `tsupport φ ⊆ 𝔻` and every constant vector `v`. The set of such pairs is the graph of
`∇ : W^{1,2}(𝔻) → L²(𝔻; ℝ²)` (with `W^{1,2}` defined by weak derivatives). -/
def IsWeakGradientPair (x : Amb) : Prop :=
  ∀ φ : ℂ → ℝ, IsDiskTest φ → ∀ v : ℂ,
    ∫ z in Metric.ball (0:ℂ) 1, x.fst z * fderiv ℝ φ z v =
      - ∫ z in Metric.ball (0:ℂ) 1, inner ℝ (x.snd z) v * φ z

/-- **`H¹(𝔻)` (closure of smooth graphs) equals the weak-gradient Sobolev graph `W^{1,2}(𝔻)`.** -/
theorem mem_H1_iff_isWeakGradientPair (x : Amb) : x ∈ H1 ↔ IsWeakGradientPair x := by
  constructor
  · intro hx φ hφ v
    exact weak_gradient ⟨x, hx⟩ hφ v
  · intro hx
    have := mem_H1_of_weak_gradient x.fst x.snd hx
    simpa using this

theorem H1_coe_eq_weak : (H1 : Set Amb) = {x | IsWeakGradientPair x} :=
  Set.ext mem_H1_iff_isWeakGradientPair

end SteklovH1
