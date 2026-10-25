module

public import Mathlib

/-!
# Arc length as one-dimensional Hausdorff measure

For a `C¹` curve `γ : ℝ → E` and a measurable set `A` of parameters contained in a compact
interval on which `γ` is injective, we prove the area formula

  `μH[1] (γ '' A) = ∫⁻ t in A, ‖γ' t‖ₑ`

and the weighted version `∫⁻ z in γ '' A, f z ∂μH[1] = ∫⁻ t in A, ‖γ' t‖ₑ * f (γ t)`.
No regularity condition `γ' ≠ 0` is needed.

The proof: on a short interval where `γ'` stays within `δ` of a fixed vector `v`, `γ` is
`(‖v‖ + δ)`-Lipschitz and, when `δ < ‖v‖`, co-Lipschitz with constant `‖v‖ - δ`; so both
`μH[1] (γ '' A)` and `∫⁻_A ‖γ'‖` lie between `(‖v‖ - δ) |A|` and `(‖v‖ + δ) |A|`.  Uniform
continuity of `γ'` gives a partition into such intervals, and the error `2 δ |A|` tends to `0`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace ArcLength

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Mean value estimate: if `‖γ' - v‖ ≤ δ` on a convex set, `γ` is affine up to `δ`. -/
lemma norm_sub_affine_le {γ γ' : ℝ → E} {I : Set ℝ} (hI : Convex ℝ I)
    (hγ : ∀ s ∈ I, HasDerivWithinAt γ (γ' s) I s) {v : E} {δ : ℝ}
    (hv : ∀ s ∈ I, ‖γ' s - v‖ ≤ δ) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    ‖γ t - γ s - (t - s) • v‖ ≤ δ * |t - s| := by
  have h := hI.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun r => γ r - r • v)
    (f' := fun r => γ' r - v) (C := δ)
    (fun r hr => by
      have := ((hasDerivWithinAt_id r I).smul_const v)
      simpa using (hγ r hr).sub this)
    hv hs ht
  have e : γ t - t • v - (γ s - s • v) = γ t - γ s - (t - s) • v := by
    rw [sub_smul]; abel
  rw [e, Real.norm_eq_abs] at h
  exact h

lemma dist_le_upper {γ γ' : ℝ → E} {I : Set ℝ} (hI : Convex ℝ I)
    (hγ : ∀ s ∈ I, HasDerivWithinAt γ (γ' s) I s) {v : E} {δ : ℝ}
    (hv : ∀ s ∈ I, ‖γ' s - v‖ ≤ δ) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    ‖γ t - γ s‖ ≤ (‖v‖ + δ) * |t - s| := by
  have h := norm_sub_affine_le hI hγ hv hs ht
  have h2 : ‖(t - s) • v‖ = |t - s| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
  calc ‖γ t - γ s‖ = ‖(γ t - γ s - (t - s) • v) + (t - s) • v‖ := by abel_nf
    _ ≤ ‖γ t - γ s - (t - s) • v‖ + ‖(t - s) • v‖ := norm_add_le _ _
    _ ≤ (‖v‖ + δ) * |t - s| := by rw [h2]; nlinarith

lemma dist_ge_lower {γ γ' : ℝ → E} {I : Set ℝ} (hI : Convex ℝ I)
    (hγ : ∀ s ∈ I, HasDerivWithinAt γ (γ' s) I s) {v : E} {δ : ℝ}
    (hv : ∀ s ∈ I, ‖γ' s - v‖ ≤ δ) {s t : ℝ} (hs : s ∈ I) (ht : t ∈ I) :
    (‖v‖ - δ) * |t - s| ≤ ‖γ t - γ s‖ := by
  have h := norm_sub_affine_le hI hγ hv hs ht
  have h2 : ‖(t - s) • v‖ = |t - s| * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs]
  have h3 : ‖(t - s) • v‖ ≤ ‖γ t - γ s‖ + ‖γ t - γ s - (t - s) • v‖ := by
    calc ‖(t - s) • v‖ = ‖(γ t - γ s) - (γ t - γ s - (t - s) • v)‖ := by abel_nf
      _ ≤ _ := norm_sub_le _ _
  rw [h2] at h3; nlinarith

/-- Upper Hausdorff bound on a piece. -/
lemma hausdorff_image_le_piece {γ γ' : ℝ → E} [MeasurableSpace E] [BorelSpace E]
    {I : Set ℝ} (hI : Convex ℝ I)
    (hγ : ∀ s ∈ I, HasDerivWithinAt γ (γ' s) I s) {v : E} {δ : ℝ} (hδ : 0 ≤ δ)
    (hv : ∀ s ∈ I, ‖γ' s - v‖ ≤ δ) {A : Set ℝ} (hA : A ⊆ I) :
    μH[1] (γ '' A) ≤ ENNReal.ofReal (‖v‖ + δ) * volume A := by
  have hL : LipschitzOnWith (Real.toNNReal (‖v‖ + δ)) γ A := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [dist_eq_norm, Real.dist_eq, Real.coe_toNNReal _ (by positivity)]
    have := dist_le_upper hI hγ hv (hA hy) (hA hx)
    exact this
  have := hL.hausdorffMeasure_image_le (d := 1) zero_le_one
  rw [ENNReal.rpow_one, hausdorffMeasure_real] at this
  simpa [ENNReal.ofReal] using this

/-- Lower Hausdorff bound on a piece. -/
lemma le_hausdorff_image_piece {γ γ' : ℝ → E} [MeasurableSpace E] [BorelSpace E]
    {I : Set ℝ} (hI : Convex ℝ I)
    (hγ : ∀ s ∈ I, HasDerivWithinAt γ (γ' s) I s) {v : E} {δ : ℝ}
    (hv : ∀ s ∈ I, ‖γ' s - v‖ ≤ δ) {A : Set ℝ} (hA : A ⊆ I) :
    ENNReal.ofReal (‖v‖ - δ) * volume A ≤ μH[1] (γ '' A) := by
  rcases le_or_gt (‖v‖ - δ) 0 with h | h
  · simp [ENNReal.ofReal_eq_zero.2 h]
  set c := ‖v‖ - δ with hc
  have hlow : ∀ s ∈ A, ∀ t ∈ A, c * |t - s| ≤ ‖γ t - γ s‖ := fun s hs t ht =>
    dist_ge_lower hI hγ hv (hA hs) (hA ht)
  have hinj : InjOn γ A := by
    intro s hs t ht hst
    have := hlow s hs t ht
    rw [hst, sub_self, norm_zero] at this
    have : |t - s| = 0 := le_antisymm (by nlinarith [abs_nonneg (t - s)]) (abs_nonneg _)
    linarith [abs_eq_zero.1 this]
  set g := Function.invFunOn γ A
  have hgA : g '' (γ '' A) = A := hinj.leftInvOn_invFunOn.image_image
  have hL : LipschitzOnWith (Real.toNNReal c⁻¹) g (γ '' A) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hy
    rw [Real.dist_eq, dist_eq_norm (γ s), Real.coe_toNNReal _ (by positivity)]
    simp only [g]
    rw [hinj.leftInvOn_invFunOn hs, hinj.leftInvOn_invFunOn ht]
    have := hlow t ht s hs
    rw [inv_mul_eq_div, le_div_iff₀ h]
    linarith
  have := hL.hausdorffMeasure_image_le (d := 1) zero_le_one
  rw [ENNReal.rpow_one, hausdorffMeasure_real, hgA] at this
  have hc' : (Real.toNNReal c⁻¹ : ℝ≥0∞) = (ENNReal.ofReal c)⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos h]; rfl
  rw [hc'] at this
  have hne : ENNReal.ofReal c ≠ 0 := by simp [h]
  calc ENNReal.ofReal c * volume A ≤ ENNReal.ofReal c * ((ENNReal.ofReal c)⁻¹ * μH[1] (γ '' A)) :=
        mul_le_mul_right this _
    _ = μH[1] (γ '' A) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hne ENNReal.ofReal_ne_top, one_mul]

omit [NormedSpace ℝ E] in
lemma lintegral_le_piece {γ' : ℝ → E} {I : Set ℝ} {v : E} {δ : ℝ}
    (hv : ∀ s ∈ I, ‖γ' s - v‖ ≤ δ) {A : Set ℝ} (hA : A ⊆ I) :
    ∫⁻ t in A, ‖γ' t‖ₑ ≤ ENNReal.ofReal (‖v‖ + δ) * volume A := by
  rw [← setLIntegral_const]
  refine setLIntegral_mono measurable_const fun t ht => ?_
  rw [← ofReal_norm_eq_enorm]
  refine ENNReal.ofReal_le_ofReal ?_
  have := hv t (hA ht)
  have := norm_le_insert' (γ' t) v
  linarith [norm_sub_norm_le (γ' t) v]

omit [NormedSpace ℝ E] in
lemma le_lintegral_piece {γ' : ℝ → E} {I : Set ℝ} {v : E} {δ : ℝ}
    (hv : ∀ s ∈ I, ‖γ' s - v‖ ≤ δ) {A : Set ℝ} (hA : A ⊆ I) (hAm : MeasurableSet A) :
    ENNReal.ofReal (‖v‖ - δ) * volume A ≤ ∫⁻ t in A, ‖γ' t‖ₑ := by
  rw [← setLIntegral_const]
  refine setLIntegral_mono' hAm fun t ht => ?_
  rw [← ofReal_norm_eq_enorm]
  refine ENNReal.ofReal_le_ofReal ?_
  have := hv t (hA ht)
  have := norm_sub_norm_le v (γ' t)
  rw [norm_sub_rev] at this
  linarith


lemma ofReal_add_le_aux (a δ : ℝ) (m : ℝ≥0∞) :
    ENNReal.ofReal (a + δ) * m ≤ ENNReal.ofReal (a - δ) * m + ENNReal.ofReal (2 * δ) * m := by
  rw [← add_mul]
  refine mul_le_mul_left ?_ _
  calc ENNReal.ofReal (a + δ) = ENNReal.ofReal ((a - δ) + 2 * δ) := by ring_nf
    _ ≤ _ := ENNReal.ofReal_add_le

/-- On a piece where `γ'` is `δ`-close to a constant, the Hausdorff measure of the image and the
integral of the speed differ by at most `2 δ |A|` (upper half). -/
lemma piece_upper {γ γ' : ℝ → E} [MeasurableSpace E] [BorelSpace E]
    {I : Set ℝ} (hI : Convex ℝ I)
    (hγ : ∀ s ∈ I, HasDerivWithinAt γ (γ' s) I s) {v : E} {δ : ℝ} (hδ : 0 ≤ δ)
    (hv : ∀ s ∈ I, ‖γ' s - v‖ ≤ δ) {A : Set ℝ} (hA : A ⊆ I) (hAm : MeasurableSet A) :
    μH[1] (γ '' A) ≤ (∫⁻ t in A, ‖γ' t‖ₑ) + ENNReal.ofReal (2 * δ) * volume A :=
  calc μH[1] (γ '' A) ≤ ENNReal.ofReal (‖v‖ + δ) * volume A :=
        hausdorff_image_le_piece hI hγ hδ hv hA
    _ ≤ ENNReal.ofReal (‖v‖ - δ) * volume A + ENNReal.ofReal (2 * δ) * volume A :=
        ofReal_add_le_aux _ _ _
    _ ≤ _ := add_le_add_left (le_lintegral_piece hv hA hAm) _

/-- Lower half of `piece_upper`. -/
lemma piece_lower {γ γ' : ℝ → E} [MeasurableSpace E] [BorelSpace E]
    {I : Set ℝ} (hI : Convex ℝ I)
    (hγ : ∀ s ∈ I, HasDerivWithinAt γ (γ' s) I s) {v : E} {δ : ℝ}
    (hv : ∀ s ∈ I, ‖γ' s - v‖ ≤ δ) {A : Set ℝ} (hA : A ⊆ I) :
    ∫⁻ t in A, ‖γ' t‖ₑ ≤ μH[1] (γ '' A) + ENNReal.ofReal (2 * δ) * volume A :=
  calc ∫⁻ t in A, ‖γ' t‖ₑ ≤ ENNReal.ofReal (‖v‖ + δ) * volume A := lintegral_le_piece hv hA
    _ ≤ ENNReal.ofReal (‖v‖ - δ) * volume A + ENNReal.ofReal (2 * δ) * volume A :=
        ofReal_add_le_aux _ _ _
    _ ≤ _ := add_le_add_left (le_hausdorff_image_piece hI hγ hv hA) _


/-- Partition of a compact parameter interval into short pieces on which `γ'` is `δ`-close to a
constant, giving both error estimates for the whole set `A`. -/
lemma global_estimates {γ γ' : ℝ → E} [MeasurableSpace E] [BorelSpace E]
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : Continuous γ') {a b : ℝ} {A : Set ℝ}
    (hA : A ⊆ Icc a b) (hAm : MeasurableSet A) (hinj : InjOn γ A) {δ : ℝ} (hδ : 0 < δ) :
    μH[1] (γ '' A) ≤ (∫⁻ t in A, ‖γ' t‖ₑ) + ENNReal.ofReal (2 * δ) * volume A ∧
    ∫⁻ t in A, ‖γ' t‖ₑ ≤ μH[1] (γ '' A) + ENNReal.ofReal (2 * δ) * volume A := by
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hγ'.continuousOn) δ hδ
  set h := η / 2 with hh
  have hpos : 0 < h := by positivity
  set P : ℤ → Set ℝ := fun n => Ico (a + n • h) (a + (n + 1) • h) with hP
  set Ap : ℤ → Set ℝ := fun n => A ∩ P n with hAp
  have hU' : A = ⋃ n, Ap n := by
    simp only [Ap, ← inter_iUnion, P, iUnion_Ico_add_zsmul hpos, inter_univ]
  have hdisj : Pairwise (Function.onFun Disjoint Ap) := fun m n hmn =>
    ((pairwise_disjoint_Ico_add_zsmul a h) hmn).mono inter_subset_right inter_subset_right
  have hmeas : ∀ n, MeasurableSet (Ap n) := fun n => hAm.inter measurableSet_Ico
  -- the local estimates on each piece
  have hloc : ∀ n, μH[1] (γ '' Ap n) ≤ (∫⁻ t in Ap n, ‖γ' t‖ₑ) +
      ENNReal.ofReal (2 * δ) * volume (Ap n) ∧
      ∫⁻ t in Ap n, ‖γ' t‖ₑ ≤ μH[1] (γ '' Ap n) + ENNReal.ofReal (2 * δ) * volume (Ap n) := by
    intro n
    rcases (Ap n).eq_empty_or_nonempty with he | ⟨c, hc⟩
    · simp [he]
    set I := Icc a b ∩ P n
    have hI : Convex ℝ I := (convex_Icc a b).inter (convex_Ico _ _)
    have hAI : Ap n ⊆ I := fun x hx => ⟨hA hx.1, hx.2⟩
    have hcI : c ∈ I := hAI hc
    have hγI : ∀ s ∈ I, HasDerivWithinAt γ (γ' s) I s := fun s _ => (hγ s).hasDerivWithinAt
    have hv : ∀ s ∈ I, ‖γ' s - γ' c‖ ≤ δ := by
      intro s hs
      rw [← dist_eq_norm]
      refine (hU s hs.1 c hcI.1 ?_).le
      have h1 := hs.2; have h2 := hcI.2
      simp only [P, mem_Ico, add_smul, one_smul] at h1 h2
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    exact ⟨piece_upper hI hγI hδ.le hv hAI (hmeas n), piece_lower hI hγI hv hAI⟩
  have himg_disj : Pairwise (Function.onFun Disjoint fun n => γ '' Ap n) := by
    intro m n hmn
    rw [Function.onFun, Set.disjoint_left]
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    have := hinj hy.1 hx.1 hxy
    subst this
    exact Set.disjoint_left.1 (hdisj hmn) hx hy
  have himg_meas : ∀ n, MeasurableSet (γ '' Ap n) := fun n =>
    (hmeas n).image_of_continuousOn_injOn
      (fun t _ => (hγ t).continuousAt.continuousWithinAt) (hinj.mono inter_subset_left)
  have hvol : volume A = ∑' n, volume (Ap n) := by
    conv_lhs => rw [hU']
    exact measure_iUnion hdisj hmeas
  have hint : ∫⁻ t in A, ‖γ' t‖ₑ = ∑' n, ∫⁻ t in Ap n, ‖γ' t‖ₑ := by
    conv_lhs => rw [hU']
    exact lintegral_iUnion hmeas hdisj _
  have himg : γ '' A = ⋃ n, γ '' Ap n := by
    conv_lhs => rw [hU']
    exact image_iUnion
  constructor
  · calc μH[1] (γ '' A) ≤ ∑' n, μH[1] (γ '' Ap n) := by rw [himg]; exact measure_iUnion_le _
      _ ≤ ∑' n, ((∫⁻ t in Ap n, ‖γ' t‖ₑ) + ENNReal.ofReal (2 * δ) * volume (Ap n)) :=
          ENNReal.tsum_le_tsum fun n => (hloc n).1
      _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ← hvol, ← hint]
  · calc ∫⁻ t in A, ‖γ' t‖ₑ = ∑' n, ∫⁻ t in Ap n, ‖γ' t‖ₑ := hint
      _ ≤ ∑' n, (μH[1] (γ '' Ap n) + ENNReal.ofReal (2 * δ) * volume (Ap n)) :=
          ENNReal.tsum_le_tsum fun n => (hloc n).2
      _ = _ := by
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ← hvol, himg,
            measure_iUnion himg_disj himg_meas]


lemma error_small {a b : ℝ} {A : Set ℝ} (hA : A ⊆ Icc a b) (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ δ > 0, ENNReal.ofReal (2 * δ) * volume A ≤ ε := by
  set L := max (b - a) 0 + 1 with hL
  have hLpos : 0 < L := by positivity
  refine ⟨ε / (2 * L), by positivity, ?_⟩
  have hvol : volume A ≤ ENNReal.ofReal L :=
    (measure_mono hA).trans (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_le_ofReal (by simp only [L]; linarith [le_max_left (b - a) 0]))
  calc ENNReal.ofReal (2 * (ε / (2 * L))) * volume A
      ≤ ENNReal.ofReal (2 * (ε / (2 * L))) * ENNReal.ofReal L := by gcongr
    _ = ENNReal.ofReal (2 * (ε / (2 * L)) * L) := (ENNReal.ofReal_mul (by positivity)).symm
    _ = ε := by
        rw [show 2 * ((ε : ℝ) / (2 * L)) * L = ε by field_simp]
        exact ENNReal.ofReal_coe_nnreal

/-- **Area formula for `C¹` curves.**  If `γ : ℝ → E` has a continuous derivative `γ'`, and `γ`
is injective on a measurable set `A` of parameters contained in a compact interval, then the
one-dimensional Hausdorff measure of `γ '' A` is the integral of the speed over `A`. -/
theorem hausdorffMeasure_image_eq_lintegral {γ γ' : ℝ → E} [MeasurableSpace E] [BorelSpace E]
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : Continuous γ') {a b : ℝ} {A : Set ℝ}
    (hA : A ⊆ Icc a b) (hAm : MeasurableSet A) (hinj : InjOn γ A) :
    μH[1] (γ '' A) = ∫⁻ t in A, ‖γ' t‖ₑ := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨δ, hδ, hsmall⟩ := error_small hA ε hε
    exact (global_estimates hγ hγ' hA hAm hinj hδ).1.trans (by gcongr)
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    obtain ⟨δ, hδ, hsmall⟩ := error_small hA ε hε
    exact (global_estimates hγ hγ' hA hAm hinj hδ).2.trans (by gcongr)

/-- The arc-length measure on `γ '' S` is the push-forward of `‖γ'‖ dt` on `S`. -/
theorem hausdorffMeasure_restrict_image_eq_map {γ γ' : ℝ → E} [MeasurableSpace E] [BorelSpace E]
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : Continuous γ') {a b : ℝ} {S : Set ℝ}
    (hS : S ⊆ Icc a b) (hSm : MeasurableSet S) (hinj : InjOn γ S) :
    (μH[1] : Measure E).restrict (γ '' S) =
      Measure.map γ ((volume.restrict S).withDensity fun t => ‖γ' t‖ₑ) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
  ext B hB
  rw [Measure.restrict_apply hB, Measure.map_apply hγc.measurable hB,
    withDensity_apply _ (hγc.measurable hB), Measure.restrict_restrict (hγc.measurable hB)]
  have hsub : γ ⁻¹' B ∩ S ⊆ S := inter_subset_right
  rw [← hausdorffMeasure_image_eq_lintegral hγ hγ' (hsub.trans hS)
    ((hγc.measurable hB).inter hSm) (hinj.mono hsub)]
  congr 1
  ext z
  constructor
  · rintro ⟨hzB, t, ht, rfl⟩; exact ⟨t, ⟨hzB, ht⟩, rfl⟩
  · rintro ⟨t, ⟨htB, ht⟩, rfl⟩; exact ⟨htB, t, ht, rfl⟩

/-- **Weighted arc-length formula.**  For a measurable weight `f ≥ 0`,
`∫_{γ(S)} f dμH¹ = ∫_S f(γ t) ‖γ' t‖ dt`. -/
theorem lintegral_image_hausdorffMeasure {γ γ' : ℝ → E} [MeasurableSpace E] [BorelSpace E]
    (hγ : ∀ t, HasDerivAt γ (γ' t) t) (hγ' : Continuous γ') {a b : ℝ} {S : Set ℝ}
    (hS : S ⊆ Icc a b) (hSm : MeasurableSet S) (hinj : InjOn γ S) {f : E → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ z in γ '' S, f z ∂μH[1] = ∫⁻ t in S, ‖γ' t‖ₑ * f (γ t) := by
  have hγc : Continuous γ := continuous_iff_continuousAt.2 fun t => (hγ t).continuousAt
  rw [hausdorffMeasure_restrict_image_eq_map hγ hγ' hS hSm hinj, lintegral_map hf hγc.measurable]
  exact lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (hf.comp hγc.measurable)

end ArcLength
