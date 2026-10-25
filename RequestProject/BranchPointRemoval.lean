module

public import RequestProject.LogCutoff
public import RequestProject.Defs

/-!
# Removal of interior branch points in the weighted Steklov min–max

Transplanted test functions (sums of a smooth function over local branches of a branched
cover) are continuous but only smooth away from finitely many interior branch points.  Here we
show that they may nevertheless be used in the min–max principle defining
`Spec_St(𝔻, ρ)` (`Steklov.weightedSteklovEigenvalue`): near each singular point `s` the function
is replaced by its value `f(s)` using the logarithmic cut-offs of `LogCutoff.lean`.  Because a
point has zero capacity in the plane, the Dirichlet energy changes by an arbitrarily small amount,
while the boundary values (on `𝕋`) are unchanged.

Main results:
* `corr_contDiff`: the corrected function is `C^∞` on the plane;
* `tendsto_eLpNorm_fderiv_corr_sub`: the energy of the correction tends to `0`;
* `minMax_le_of_singular_transfer`: **min–max transfer with singular test functions** — a linear
  map of test functions which preserves energy and weighted boundary mass and takes values in
  functions that are continuous and smooth off a fixed finite subset of the open disk does not
  increase the weighted Steklov eigenvalues.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace SteklovBranch

open Steklov

/-- The corrected function: near each `s ∈ S` the function is replaced by the constant `f s`. -/
def corr (S : Finset ℂ) (r : ℝ) (f : ℂ → ℝ) : ℂ → ℝ :=
  fun z => f z + ∑ s ∈ S, logCut s r z * (f s - f z)

/-- The correction as a linear map. -/
def corrL (S : Finset ℂ) (r : ℝ) : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ) where
  toFun := corr S r
  map_add' f g := by
    ext z; simp only [corr, Pi.add_apply]
    rw [← add_add_add_comm, ← Finset.sum_add_distrib]
    congr 1; refine Finset.sum_congr rfl fun s _ => by ring
  map_smul' a f := by
    ext z; simp only [corr, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [mul_add, Finset.mul_sum]
    congr 1; refine Finset.sum_congr rfl fun s _ => by ring

/-- Admissible radii: small, cut-off supports inside the disk and pairwise disjoint. -/
def GoodRadius (S : Finset ℂ) (r : ℝ) : Prop :=
  0 < r ∧ r < 1 ∧ (∀ s ∈ S, r ≤ 1 - ‖s‖) ∧ (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → 2 * r ≤ ‖s - s'‖)

theorem eventually_goodRadius (S : Finset ℂ) (hS : ∀ s ∈ S, ‖s‖ < 1) :
    ∀ᶠ r in 𝓝[>] (0:ℝ), GoodRadius S r := by
  have hsmall : ∀ c : ℝ, 0 < c → ∀ᶠ r in 𝓝[>] (0:ℝ), r ≤ c := fun c hc =>
    nhdsWithin_le_nhds (eventually_le_nhds hc)
  have hpos : ∀ᶠ r in 𝓝[>] (0:ℝ), 0 < r := self_mem_nhdsWithin
  have hpair : ∀ s ∈ S, ∀ s' ∈ S, ∀ᶠ r in 𝓝[>] (0:ℝ), s ≠ s' → 2 * r ≤ ‖s - s'‖ := by
    intro s _ s' _
    by_cases h : s = s'
    · exact Eventually.of_forall fun r h' => absurd h h'
    · filter_upwards [hsmall (‖s - s'‖ / 2)
        (by have := norm_pos_iff.2 (sub_ne_zero.2 h); positivity)] with r hr _
      linarith
  have hin : ∀ s ∈ S, ∀ᶠ r in 𝓝[>] (0:ℝ), r ≤ 1 - ‖s‖ := fun s hs =>
    hsmall (1 - ‖s‖) (by linarith [hS s hs])
  filter_upwards [hpos, hsmall (1/2) (by norm_num), (Finset.eventually_all S).2 hin,
    (Finset.eventually_all S).2 fun s hs => (Finset.eventually_all S).2 fun s' hs' =>
      hpair s hs s' hs'] with r h0 h1 h2 h3
  exact ⟨h0, by linarith, h2, fun s hs s' hs' => h3 s hs s' hs'⟩

theorem corr_eq_on_circle {S : Finset ℂ} {r : ℝ} (hr : GoodRadius S r) (f : ℂ → ℝ) {z : ℂ}
    (hz : 1 ≤ ‖z‖) : corr S r f z = f z := by
  obtain ⟨h0, h1, h2, -⟩ := hr
  unfold corr
  rw [Finset.sum_eq_zero, add_zero]
  intro s hs
  rw [logCut_eq_zero h0 h1, zero_mul]
  have := norm_sub_norm_le z s
  linarith [h2 s hs]

theorem corr_contDiff {S : Finset ℂ} {r : ℝ} (hr : GoodRadius S r) {f : ℂ → ℝ}
    (hfs : ContDiffOn ℝ ∞ f (↑S)ᶜ) : ContDiff ℝ ∞ (corr S r f) := by
  obtain ⟨h0, h1, h2, h3⟩ := hr
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ S
  · have : corr S r f =ᶠ[𝓝 z] fun _ => f z := by
      have hball : Metric.ball z (r ^ 2) ∈ 𝓝 z := Metric.ball_mem_nhds _ (by positivity)
      filter_upwards [hball] with w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      unfold corr
      rw [Finset.sum_eq_single z]
      · rw [logCut_eq_one hw.le]; ring
      · intro s' hs' hne
        rw [logCut_eq_zero h0 h1, zero_mul]
        have h4 := h3 z hz s' hs' (Ne.symm hne)
        have h5 : ‖z - s'‖ ≤ ‖w - s'‖ + ‖w - z‖ := by
          rw [← norm_neg (w - z)]
          calc ‖z - s'‖ = ‖(w - s') + -(w - z)‖ := by congr 1; ring
            _ ≤ _ := norm_add_le _ _
        nlinarith
      · intro h; exact absurd hz h
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have hopen : IsOpen ((↑S : Set ℂ)ᶜ) := S.finite_toSet.isClosed.isOpen_compl
    have hf : ContDiffAt ℝ ∞ f z := hfs.contDiffAt (hopen.mem_nhds hz)
    unfold corr
    refine hf.add ?_
    refine ContDiffAt.sum fun s _ => ?_
    exact (contDiff_logCut h0 h1).contDiffAt.mul (contDiffAt_const.sub hf)

/-- A function smooth off a finite set is measurable. -/
theorem measurable_of_contDiffOn_compl {S : Finset ℂ} {f : ℂ → ℝ}
    (hfs : ContDiffOn ℝ ∞ f (↑S)ᶜ) : Measurable f :=
  measurable_of_measurable_on_compl_finite _ S.finite_toSet
    (continuousOn_iff_continuous_restrict.1 hfs.continuousOn).measurable

theorem eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] (f : α → E)
    (μ : Measure α) : eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have := eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := 2) two_ne_zero
  simpa using this

/-- The Dirichlet energy is the square of an `L²` seminorm of the gradient. -/
theorem dirichletEnergy_eq_eLpNorm_sq (Ω : Set ℂ) (f : ℂ → ℝ) :
    dirichletEnergy Ω f = eLpNorm (fderiv ℝ f) 2 (volume.restrict Ω) ^ 2 := by
  rw [eLpNorm_two_sq]; rfl

theorem corr_sub_eq (S : Finset ℂ) (r : ℝ) (f : ℂ → ℝ) :
    corr S r f - f = fun z => ∑ s ∈ S, logCut s r z * (f s - f z) := by
  ext z; simp [corr]

theorem norm_fderiv_corr_sub_le {S : Finset ℂ} {r : ℝ} (hr : GoodRadius S r) {f : ℂ → ℝ}
    (hfs : ContDiffOn ℝ ∞ f (↑S)ᶜ) {z : ℂ} (hz : z ∉ S) :
    ‖fderiv ℝ (corr S r f - f) z‖ ≤
      ∑ s ∈ S, (|f s - f z| * ‖fderiv ℝ (logCut s r) z‖ + logCut s r z * ‖fderiv ℝ f z‖) := by
  obtain ⟨h0, h1, -, -⟩ := hr
  have hopen : IsOpen ((↑S : Set ℂ)ᶜ) := S.finite_toSet.isClosed.isOpen_compl
  have hf : DifferentiableAt ℝ f z :=
    (hfs.contDiffAt (hopen.mem_nhds hz)).differentiableAt (by simp)
  have hχ : ∀ s, DifferentiableAt ℝ (logCut s r) z := fun s =>
    (contDiff_logCut h0 h1).contDiffAt.differentiableAt (by simp)
  have hterm : ∀ s ∈ S, HasFDerivAt (fun w => logCut s r w * (f s - f w))
      (logCut s r z • (-fderiv ℝ f z) + (f s - f z) • fderiv ℝ (logCut s r) z) z := by
    intro s _
    have h2 : HasFDerivAt (fun w => f s - f w) (-fderiv ℝ f z) z := by
      simpa using (hasFDerivAt_const (f s) z).sub hf.hasFDerivAt
    exact (hχ s).hasFDerivAt.mul h2
  have hsum := HasFDerivAt.sum hterm
  rw [corr_sub_eq]
  have hsum' : HasFDerivAt (fun w => ∑ s ∈ S, logCut s r w * (f s - f w))
      (∑ s ∈ S, (logCut s r z • (-fderiv ℝ f z) + (f s - f z) • fderiv ℝ (logCut s r) z)) z := by
    convert hsum using 1; ext w; simp
  rw [hsum'.fderiv]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (logCut_nonneg z)]
  linarith

/-- `L²` bound for the gradient of the correction term. -/
theorem eLpNorm_fderiv_corr_sub_le {S : Finset ℂ} {r : ℝ} (hr : GoodRadius S r) {f : ℂ → ℝ}
    (hfs : ContDiffOn ℝ ∞ f (↑S)ᶜ) (hS : ∀ s ∈ S, ‖s‖ < 1) {M : ℝ}
    (hM : ∀ z ∈ Metric.ball (0:ℂ) 1, |f z| ≤ M) :
    eLpNorm (fderiv ℝ (corr S r f - f)) 2 (volume.restrict (Metric.ball 0 1)) ≤
      ∑ s ∈ S, (ENNReal.ofReal (2 * M) * eLpNorm (fderiv ℝ (logCut s r)) 2 volume +
        eLpNorm (fderiv ℝ f) 2
          ((volume.restrict (Metric.ball 0 1)).restrict (Metric.ball s r))) := by
  set μB := volume.restrict (Metric.ball (0:ℂ) 1)
  obtain ⟨h0, h1, -, -⟩ := id hr
  have hfm : Measurable f := measurable_of_contDiffOn_compl hfs
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 (by simp))
  have hnull : ∀ᵐ z ∂μB, z ∉ S := by
    apply ae_restrict_of_ae
    have : volume (↑S : Set ℂ) = 0 := S.finite_toSet.measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with z hz using hz
  have hχc : ∀ s, Continuous (logCut s r) := fun s => (contDiff_logCut h0 h1).continuous
  have hmeas : ∀ g : ℂ → ℝ, Measurable (fun z => ‖fderiv ℝ g z‖) := fun g =>
    (measurable_fderiv ℝ g).norm
  calc eLpNorm (fderiv ℝ (corr S r f - f)) 2 μB
      ≤ eLpNorm (fun z => ∑ s ∈ S, (|f s - f z| * ‖fderiv ℝ (logCut s r) z‖ +
          logCut s r z * ‖fderiv ℝ f z‖)) 2 μB := by
        apply eLpNorm_mono_ae_real
        filter_upwards [hnull] with z hz using norm_fderiv_corr_sub_le hr hfs hz
    _ = eLpNorm (∑ s ∈ S, fun z => (|f s - f z| * ‖fderiv ℝ (logCut s r) z‖ +
          logCut s r z * ‖fderiv ℝ f z‖)) 2 μB := by
        congr 1; ext z; simp
    _ ≤ ∑ s ∈ S, eLpNorm (fun z => (|f s - f z| * ‖fderiv ℝ (logCut s r) z‖ +
          logCut s r z * ‖fderiv ℝ f z‖)) 2 μB := by
        refine eLpNorm_sum_le (fun s _ => ?_) (by norm_num)
        exact ((((measurable_const.sub hfm).abs.mul (hmeas _)).add
          ((hχc s).measurable.mul (hmeas f)))).aestronglyMeasurable
    _ ≤ _ := by
        refine Finset.sum_le_sum fun s hs => ?_
        refine (eLpNorm_add_le ?_ ?_ (by norm_num)).trans (add_le_add ?_ ?_)
        · exact ((measurable_const.sub hfm).abs.mul (hmeas _)).aestronglyMeasurable
        · exact ((hχc s).measurable.mul (hmeas f)).aestronglyMeasurable
        · have h2 : eLpNorm (fun z => |f s - f z| * ‖fderiv ℝ (logCut s r) z‖) 2 μB ≤
              (Real.toNNReal (2 * M)) • eLpNorm (fderiv ℝ (logCut s r)) 2 μB := by
            apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
            filter_upwards [ae_restrict_mem Metric.isOpen_ball.measurableSet] with z hz
            rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_mul, coe_nnnorm,
              Real.coe_toNNReal _ (by positivity), Real.norm_eq_abs, abs_mul, abs_abs, abs_norm]
            gcongr
            have := abs_sub (f s) (f z)
            linarith [hM z hz, hM s (by simpa using hS s hs)]
          refine h2.trans ?_
          rw [ENNReal.smul_def, smul_eq_mul]
          exact mul_le_mul_right (eLpNorm_mono_measure _ Measure.restrict_le_self) _
        · rw [← eLpNorm_indicator_eq_eLpNorm_restrict (f := fderiv ℝ f) (μ := μB)
            Metric.isOpen_ball.measurableSet]
          refine eLpNorm_mono fun z => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_norm, abs_of_nonneg (logCut_nonneg z)]
          by_cases hz : z ∈ Metric.ball s r
          · rw [indicator_of_mem hz]
            exact mul_le_of_le_one_left (norm_nonneg _) (logCut_le_one z)
          · rw [indicator_of_notMem hz, logCut_eq_zero h0 h1, zero_mul]
            · simp
            · simpa [Metric.mem_ball, dist_eq_norm] using hz

theorem ennreal_le_of_sq_le {a b : ℝ≥0∞} (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  by_contra hc
  push_neg at hc
  exact absurd h (not_le.2 (ENNReal.pow_lt_pow_left (n := 2) two_ne_zero hc))

theorem tendsto_zero_of_sq {α : Type*} {l : Filter α} {e : α → ℝ≥0∞}
    (h : Tendsto (fun a => e a ^ 2) l (𝓝 0)) : Tendsto e l (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at h ⊢
  intro ε hε
  filter_upwards [h (ε ^ 2) (by positivity)] with a ha
  exact ennreal_le_of_sq_le ha

/-- The energy of the logarithmic cut-offs tends to zero. -/
theorem tendsto_eLpNorm_fderiv_logCut (s : ℂ) :
    Tendsto (fun r => eLpNorm (fderiv ℝ (logCut s r)) 2 volume) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := exists_deriv_smoothTransition_bound
  apply tendsto_zero_of_sq
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (2 * π * K ^ 2 / |Real.log r|)) (𝓝[>] 0)
      (𝓝 0) := by
    rw [← ENNReal.ofReal_zero]
    apply ENNReal.tendsto_ofReal
    exact tendsto_const_nhds.div_atTop
      (tendsto_abs_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le _) ?_
  have h1 : ∀ᶠ r in 𝓝[>] (0:ℝ), r < 1 := nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
  filter_upwards [self_mem_nhdsWithin, h1] with r hr0 hr1
  rw [eLpNorm_two_sq]
  exact lintegral_fderiv_logCut_le hr0 hr1 hK0 hK

theorem tendsto_eLpNorm_restrict_ball {μ : Measure ℂ} (hμ : μ ≤ volume)
    {g : ℂ → (ℂ →L[ℝ] ℝ)} (hg : eLpNorm g 2 μ ≠ ⊤) (s : ℂ) :
    Tendsto (fun r => eLpNorm g 2 (μ.restrict (Metric.ball s r))) (𝓝[>] 0) (𝓝 0) := by
  apply tendsto_zero_of_sq
  simp_rw [eLpNorm_two_sq]
  have hfin : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ ≠ ⊤ := by
    rw [← eLpNorm_two_sq]; exact ENNReal.pow_ne_top hg
  apply tendsto_setLIntegral_zero hfin
  have : Tendsto (fun r : ℝ => ENNReal.ofReal r ^ 2 * NNReal.pi) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Tendsto (fun r : ℝ => ENNReal.ofReal r ^ 2) (𝓝 0) (𝓝 0) := by
      have := ((ENNReal.continuous_pow 2).tendsto _).comp (ENNReal.continuous_ofReal.tendsto 0)
      simpa using this
    have h := ENNReal.Tendsto.mul_const h0 (Or.inr (ENNReal.coe_ne_top (r := NNReal.pi)))
    rw [zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this
    (fun _ => zero_le _) (fun r => ?_)
  simp only [Function.comp_apply]
  exact (hμ _).trans (Complex.volume_ball s r).le

/-- **Energy of the correction tends to zero.** For `f` bounded on the disk, smooth off a finite set
of points `S` of the open disk, and of finite Dirichlet energy on the disk, the gradient of
`corr S r f - f` tends to `0` in `L²(𝔻)` as `r → 0⁺`. -/
theorem tendsto_eLpNorm_fderiv_corr_sub {S : Finset ℂ} (hS : ∀ s ∈ S, ‖s‖ < 1) {f : ℂ → ℝ}
    (hfb : ∃ M, ∀ z ∈ Metric.ball (0:ℂ) 1, |f z| ≤ M) (hfs : ContDiffOn ℝ ∞ f (↑S)ᶜ)
    (hfE : eLpNorm (fderiv ℝ f) 2 (volume.restrict (Metric.ball 0 1)) ≠ ⊤) :
    Tendsto (fun r => eLpNorm (fderiv ℝ (corr S r f - f)) 2
      (volume.restrict (Metric.ball 0 1))) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨M, hM'⟩ := hfb
  have hlim : Tendsto (fun r => ∑ s ∈ S, (ENNReal.ofReal (2 * M) *
      eLpNorm (fderiv ℝ (logCut s r)) 2 volume + eLpNorm (fderiv ℝ f) 2
        ((volume.restrict (Metric.ball 0 1)).restrict (Metric.ball s r)))) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finset_sum S (fun s _ =>
      ((ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 * M)) (tendsto_eLpNorm_fderiv_logCut s)
        (Or.inr ENNReal.ofReal_ne_top)).add
        (tendsto_eLpNorm_restrict_ball Measure.restrict_le_self hfE s)))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ => zero_le _) ?_
  filter_upwards [eventually_goodRadius S hS] with r hr
  exact eLpNorm_fderiv_corr_sub_le hr hfs hS hM'

end SteklovBranch
