module

public import Mathlib
public import RequestProject.NearDiskDomain
public import RequestProject.Defs

/-!
# The boundary of `Q⁻¹(𝔻)` is a real-analytic Jordan curve

For a nearly monomial polynomial `Q(z) = zⁿ + ∑_{k<n} q_k z^k` (`|q_k| ≤ s`, `3 n s 16ⁿ < 1`,
`n ≥ 1`), `|Q|` is strictly increasing along every ray on `1/2 ≤ |z| ≤ 2`, `|Q| < 1` on
`|z| ≤ 1/2` and `|Q| > 1` on `|z| ≥ 2`.  Hence each ray `t ↦ t e^{iθ}` meets `{|Q| = 1}` in
exactly one point `bdryRad θ · e^{iθ}`, and the real-analytic implicit function theorem
(applied to `(θ, r) ↦ |Q(r e^{iθ})|²`) shows that `θ ↦ bdryRad θ` is real-analytic.

Main results:
* `frontier_preimage_eq`: `∂ Q⁻¹(𝔻) = {|Q| = 1}`;
* `range_bdryCurve`: `{|Q| = 1}` is the range of `θ ↦ bdryRad θ · e^{iθ}`;
* `isRealAnalyticJordanBoundary_preimage`: `Q⁻¹(𝔻)` has real-analytic Jordan boundary.
-/

@[expose] public section

open Set Filter Topology Metric Complex PlaneDomain
open scoped ContDiff

noncomputable section

namespace SteklovCoalescence

variable {n : ℕ} {q : Fin n → ℂ} {s : ℝ}

/-- `|Q(r e^{iθ})|²`. -/
def radF (n : ℕ) (q : Fin n → ℂ) (θ r : ℝ) : ℝ :=
  ‖polyQ n q ((r : ℂ) * Complex.exp (θ * I))‖ ^ 2

lemma norm_ofReal_mul_exp {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖(r : ℂ) * Complex.exp (θ * I)‖ = r := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr]

lemma radF_continuous (n : ℕ) (q : Fin n → ℂ) (θ : ℝ) : Continuous (radF n q θ) := by
  unfold radF
  have := polyQ_continuous n q
  fun_prop

lemma hasDerivAt_radF (n : ℕ) (q : Fin n → ℂ) (θ r : ℝ) :
    HasDerivAt (radF n q θ)
      (2 * inner ℝ (polyQ n q ((r : ℂ) * Complex.exp (θ * I)))
        (dpolyQ n q ((r : ℂ) * Complex.exp (θ * I)) * Complex.exp (θ * I))) r := by
  have h1 : HasDerivAt (fun u : ℂ => polyQ n q (u * Complex.exp (θ * I)))
      (dpolyQ n q ((r : ℂ) * Complex.exp (θ * I)) * Complex.exp (θ * I)) (r : ℂ) :=
    (hasDerivAt_polyQ n q _).comp (r : ℂ) (by simpa using hasDerivAt_mul_const (Complex.exp (θ * I)))
  exact h1.comp_ofReal.norm_sq

section bounds

variable (hq : ∀ k, ‖q k‖ ≤ s) (hs : 3 * n * s * 16 ^ n < 1) (hn : 1 ≤ n)
include hq hs hn

omit hq hn in
lemma ns_lt_third : (n : ℝ) * s < 1 / 3 := by
  have h16 : (1 : ℝ) ≤ 16 ^ n := one_le_pow₀ (by norm_num)
  nlinarith

lemma norm_polyQ_lt_one_of_le_half {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖polyQ n q z‖ < 1 := by
  have hns := ns_lt_third hs
  calc ‖polyQ n q z‖ ≤ ‖z‖ ^ n + n * s := norm_polyQ_le hq (by linarith)
    _ ≤ ‖z‖ ^ 1 + n * s :=
        add_le_add_left (pow_le_pow_of_le_one (norm_nonneg _) (by linarith) hn) _
    _ < 1 := by rw [pow_one]; linarith

lemma one_lt_norm_polyQ_of_two_le {z : ℂ} (hz : 2 ≤ ‖z‖) : 1 < ‖polyQ n q z‖ := by
  have hns := ns_lt_third hs
  have := norm_polyQ_ge hn hq (show 1 ≤ ‖z‖ by linarith)
  linarith

lemma deriv_radF_pos (θ : ℝ) {r : ℝ} (hr1 : 1 / 2 ≤ r) (hr2 : r ≤ 2) :
    0 < deriv (radF n q θ) r := by
  rw [(hasDerivAt_radF n q θ r).deriv]
  set w := (r : ℂ) * Complex.exp (θ * I) with hw
  have hr0 : 0 < r := by linarith
  have hwn : ‖w‖ = r := norm_ofReal_mul_exp hr0.le θ
  have hpos := re_polyQ_deriv_pos hq ((norm_nonneg _).trans (hq ⟨0, hn⟩)) hs (w := w) (by rw [hwn]; exact hr1)
    (by rw [hwn]; exact hr2) hn
  rw [Complex.inner]
  have : (dpolyQ n q w * Complex.exp (θ * I) * (starRingEnd ℂ) (polyQ n q w)).re =
      r⁻¹ * (w * dpolyQ n q w * (starRingEnd ℂ) (polyQ n q w)).re := by
    rw [← Complex.re_ofReal_mul]
    congr 1
    have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    rw [hw]; push_cast; field_simp
  have h2 : ((starRingEnd ℂ) (polyQ n q w) * (dpolyQ n q w * Complex.exp (θ * I))).re =
      (dpolyQ n q w * Complex.exp (θ * I) * (starRingEnd ℂ) (polyQ n q w)).re := by
    rw [mul_comm]
  rw [this]
  have : 0 < r⁻¹ := inv_pos.2 hr0
  positivity

lemma radF_strictMonoOn (θ : ℝ) : StrictMonoOn (radF n q θ) (Icc (1 / 2) 2) := by
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (radF_continuous n q θ).continuousOn ?_
  intro r hr
  rw [interior_Icc] at hr
  exact deriv_radF_pos hq hs hn θ hr.1.le hr.2.le

lemma radF_half_lt_one (θ : ℝ) : radF n q θ (1 / 2) < 1 := by
  have h := norm_polyQ_lt_one_of_le_half hq hs hn
    (z := ((1 / 2 : ℝ) : ℂ) * Complex.exp (θ * I))
    (by rw [norm_ofReal_mul_exp (by norm_num)])
  unfold radF
  have h0 := norm_nonneg (polyQ n q (((1 / 2 : ℝ) : ℂ) * Complex.exp (θ * I)))
  nlinarith

lemma one_lt_radF_two (θ : ℝ) : 1 < radF n q θ 2 := by
  have h := one_lt_norm_polyQ_of_two_le hq hs hn
    (z := ((2 : ℝ) : ℂ) * Complex.exp (θ * I)) (by rw [norm_ofReal_mul_exp (by norm_num)])
  unfold radF
  nlinarith

lemma exists_radF_eq_one (θ : ℝ) : ∃ r ∈ Icc (1 / 2 : ℝ) 2, radF n q θ r = 1 := by
  have := intermediate_value_Icc (show (1 / 2 : ℝ) ≤ 2 by norm_num)
    (radF_continuous n q θ).continuousOn
    ⟨(radF_half_lt_one hq hs hn θ).le, (one_lt_radF_two hq hs hn θ).le⟩
  obtain ⟨r, hr, h⟩ := this
  exact ⟨r, hr, h⟩

end bounds

/-- The radius at which the ray of angle `θ` meets `{|Q| = 1}` (junk value `1` if there is no
such radius in `[1/2, 2]`, which does not happen under the standing hypotheses). -/
def bdryRad (n : ℕ) (q : Fin n → ℂ) (θ : ℝ) : ℝ :=
  open Classical in
  if h : ∃ r ∈ Icc (1 / 2 : ℝ) 2, radF n q θ r = 1 then h.choose else 1

/-- The boundary curve `θ ↦ bdryRad θ · e^{iθ}`. -/
def bdryCurve (n : ℕ) (q : Fin n → ℂ) (θ : ℝ) : ℂ :=
  (bdryRad n q θ : ℂ) * Complex.exp (θ * I)

section bounds2

variable (hq : ∀ k, ‖q k‖ ≤ s) (hs : 3 * n * s * 16 ^ n < 1) (hn : 1 ≤ n)
include hq hs hn

lemma bdryRad_spec (θ : ℝ) :
    bdryRad n q θ ∈ Icc (1 / 2 : ℝ) 2 ∧ radF n q θ (bdryRad n q θ) = 1 := by
  have h := exists_radF_eq_one hq hs hn θ
  unfold bdryRad
  rw [dif_pos h]
  exact h.choose_spec

lemma eq_bdryRad {θ r : ℝ} (hr : r ∈ Icc (1 / 2 : ℝ) 2) (h : radF n q θ r = 1) :
    r = bdryRad n q θ :=
  (radF_strictMonoOn hq hs hn θ).injOn hr (bdryRad_spec hq hs hn θ).1
    (h.trans (bdryRad_spec hq hs hn θ).2.symm)

lemma bdryRad_mem_Ioo (θ : ℝ) : bdryRad n q θ ∈ Ioo (1 / 2 : ℝ) 2 := by
  obtain ⟨⟨h1, h2⟩, h⟩ := bdryRad_spec hq hs hn θ
  refine ⟨lt_of_le_of_ne h1 ?_, lt_of_le_of_ne h2 ?_⟩
  · intro he; have := radF_half_lt_one hq hs hn (q := q) θ; rw [he, h] at this
    exact lt_irrefl _ this
  · intro he; have := one_lt_radF_two hq hs hn (q := q) θ; rw [← he, h] at this
    exact lt_irrefl _ this

lemma bdryRad_periodic : Function.Periodic (bdryRad n q) (2 * Real.pi) := by
  intro θ
  symm
  apply eq_bdryRad hq hs hn (bdryRad_spec hq hs hn θ).1
  have h := (bdryRad_spec hq hs hn θ).2
  unfold radF at h ⊢
  have : Complex.exp (((θ + 2 * Real.pi : ℝ) : ℂ) * I) = Complex.exp ((θ : ℂ) * I) := by
    push_cast
    rw [add_mul, Complex.exp_add]
    simp
  rw [this]; exact h

omit hq hs hn in
lemma radF_contDiff : ContDiff ℝ ω (fun p : ℝ × ℝ => radF n q p.1 p.2) := by
  have hf : ContDiff ℂ ω (polyQ n q) := (polyQ_differentiable n q).contDiff
  have h1 : ContDiff ℝ ω (polyQ n q) := hf.restrict_scalars (𝕜' := ℂ) ℝ
  have hexp : ContDiff ℝ ω Complex.exp := Complex.contDiff_exp.restrict_scalars (𝕜' := ℂ) ℝ
  have h2 : ContDiff ℝ ω (fun p : ℝ × ℝ => polyQ n q ((p.2 : ℂ) * Complex.exp (p.1 * I))) := by
    refine h1.comp ?_
    have : ContDiff ℝ ω (fun p : ℝ × ℝ => (p.2 : ℂ)) := ofRealCLM.contDiff.comp contDiff_snd
    have h3 : ContDiff ℝ ω (fun p : ℝ × ℝ => Complex.exp (p.1 * I)) :=
      hexp.comp ((ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const)
    exact this.mul h3
  have hre := reCLM.contDiff.comp h2
  have him := imCLM.contDiff.comp h2
  have := (hre.pow 2).add (him.pow 2)
  convert this using 1
  ext p
  simp only [radF, Function.comp_apply, reCLM_apply, imCLM_apply]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

omit hq hs hn in
lemma clm_bijective_of_apply_one_ne_zero (L : ℝ →L[ℝ] ℝ) (h : L 1 ≠ 0) :
    Function.Bijective L := by
  have hL : ∀ v, L v = v * L 1 := fun v => by
    simpa [smul_eq_mul] using L.map_smul v (1 : ℝ)
  refine ⟨fun a b hab => ?_, fun y => ⟨y / L 1, by rw [hL]; field_simp⟩⟩
  rw [hL a, hL b] at hab
  exact mul_right_cancel₀ h hab

lemma bdryRad_analyticAt (θ₀ : ℝ) : AnalyticAt ℝ (bdryRad n q) θ₀ := by
  set f : ℝ × ℝ → ℝ := fun p => radF n q p.1 p.2 with hfdef
  have hf : ContDiff ℝ ω f := radF_contDiff
  set r₀ := bdryRad n q θ₀
  set a : ℝ × ℝ := (θ₀, r₀)
  have hd : HasFDerivAt f (fderiv ℝ f a) a :=
    ((hf.differentiable (by simp)) a).hasFDerivAt
  have hbij : Function.Bijective ((fderiv ℝ f a).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) := by
    apply clm_bijective_of_apply_one_ne_zero
    have hcomp : HasFDerivAt (fun r : ℝ => f (θ₀, r))
        ((fderiv ℝ f a).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) r₀ := by
      have hin : HasFDerivAt (fun r : ℝ => ((θ₀, r) : ℝ × ℝ)) (ContinuousLinearMap.inr ℝ ℝ ℝ) r₀ :=
        (hasFDerivAt_const θ₀ r₀).prodMk (hasFDerivAt_id r₀)
      exact hd.comp r₀ hin
    have h2 : HasDerivAt (fun r : ℝ => f (θ₀, r)) (deriv (radF n q θ₀) r₀) r₀ :=
      (hasDerivAt_radF n q θ₀ r₀).congr_deriv ((hasDerivAt_radF n q θ₀ r₀).deriv.symm)
    have h3 := hcomp.hasDerivAt.unique h2
    rw [h3]
    have hm := bdryRad_mem_Ioo hq hs hn (q := q) θ₀
    exact (deriv_radF_pos hq hs hn θ₀ hm.1.le hm.2.le).ne'
  have hinv : ((fderiv ℝ f a).comp (ContinuousLinearMap.inr ℝ ℝ ℝ)).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofBijective _ (LinearMap.ker_eq_bot.mpr hbij.1)
      (LinearMap.range_eq_top.mpr hbij.2), rfl⟩
  have hI : ContDiffAt ℝ ω f a := hf.contDiffAt
  have hφa : AnalyticAt ℝ (hI.implicitFunction (by simp) hinv) θ₀ :=
    (hI.contDiffAt_implicitFunction (by simp) hinv).analyticAt
  have hφ0 : hI.implicitFunction (by simp) hinv θ₀ = r₀ :=
    hI.implicitFunction_apply_self (by simp) hinv
  have hfa : f a = 1 := (bdryRad_spec hq hs hn θ₀).2
  have hev1 := hI.eventually_apply_implicitFunction (by simp) hinv
  have hev2 : ∀ᶠ θ in 𝓝 θ₀, hI.implicitFunction (by simp) hinv θ ∈ Ioo (1 / 2 : ℝ) 2 := by
    have := hφa.continuousAt
    rw [ContinuousAt, hφ0] at this
    exact this (Ioo_mem_nhds (bdryRad_mem_Ioo hq hs hn θ₀).1 (bdryRad_mem_Ioo hq hs hn θ₀).2)
  refine hφa.congr ?_
  filter_upwards [hev1, hev2] with θ h1 h2
  rw [hfa] at h1
  exact eq_bdryRad hq hs hn (Ioo_subset_Icc_self h2) h1

lemma norm_polyQ_bdryCurve (θ : ℝ) : ‖polyQ n q (bdryCurve n q θ)‖ = 1 := by
  have h := (bdryRad_spec hq hs hn θ).2
  unfold radF at h
  unfold bdryCurve
  nlinarith [norm_nonneg (polyQ n q ((bdryRad n q θ : ℂ) * Complex.exp (θ * I)))]

lemma norm_mem_Icc_of_norm_polyQ_eq_one {z : ℂ} (hz : ‖polyQ n q z‖ = 1) :
    ‖z‖ ∈ Icc (1 / 2 : ℝ) 2 := by
  constructor
  · by_contra h; push_neg at h
    have := norm_polyQ_lt_one_of_le_half hq hs hn (q := q) h.le
    linarith
  · by_contra h; push_neg at h
    have := one_lt_norm_polyQ_of_two_le hq hs hn (q := q) h.le
    linarith

lemma eq_bdryCurve_arg {z : ℂ} (hz : ‖polyQ n q z‖ = 1) : bdryCurve n q z.arg = z := by
  have hI := norm_mem_Icc_of_norm_polyQ_eq_one hq hs hn hz
  have hr : ‖z‖ = bdryRad n q z.arg := by
    apply eq_bdryRad hq hs hn hI
    unfold radF
    rw [Complex.norm_mul_exp_arg_mul_I, hz, one_pow]
  unfold bdryCurve
  rw [← hr, Complex.norm_mul_exp_arg_mul_I]

lemma range_bdryCurve : range (bdryCurve n q) = {z | ‖polyQ n q z‖ = 1} := by
  ext z
  constructor
  · rintro ⟨θ, rfl⟩; exact norm_polyQ_bdryCurve hq hs hn θ
  · intro hz; exact ⟨z.arg, eq_bdryCurve_arg hq hs hn hz⟩

lemma frontier_preimage_eq :
    frontier (polyQ n q ⁻¹' ball 0 1) = {z | ‖polyQ n q z‖ = 1} := by
  have hc := polyQ_continuous n q
  rw [(isOpen_ball.preimage hc).frontier_eq]
  ext z
  simp only [mem_diff, mem_preimage, mem_ball_zero_iff, mem_setOf_eq]
  constructor
  · rintro ⟨hcl, hnot⟩
    have hle : ‖polyQ n q z‖ ≤ 1 := by
      have hsub : closure (polyQ n q ⁻¹' ball 0 1) ⊆ polyQ n q ⁻¹' closedBall 0 1 :=
        closure_minimal (preimage_mono ball_subset_closedBall)
          (isClosed_closedBall.preimage hc)
      have := hsub hcl
      rwa [mem_preimage, mem_closedBall_zero_iff] at this
    push_neg at hnot
    exact le_antisymm hle hnot
  · intro hz
    refine ⟨?_, by rw [hz]; exact lt_irrefl 1⟩
    rw [← eq_bdryCurve_arg hq hs hn hz]
    set θ := z.arg
    set r₀ := bdryRad n q θ
    have hr₀ := bdryRad_mem_Ioo hq hs hn (q := q) θ
    have hspec := bdryRad_spec hq hs hn (q := q) θ
    have ht : Tendsto (fun t : ℝ => (t : ℂ) * Complex.exp (θ * I)) (𝓝[<] r₀)
        (𝓝 (bdryCurve n q θ)) := by
      unfold bdryCurve
      apply Tendsto.mono_left _ nhdsWithin_le_nhds
      exact ((Complex.continuous_ofReal.tendsto r₀).mul_const _)
    refine mem_closure_of_tendsto ht ?_
    have hev : ∀ᶠ t in 𝓝[<] r₀, t ∈ Ioo (1 / 2 : ℝ) r₀ := Ioo_mem_nhdsLT hr₀.1
    filter_upwards [hev] with t ht
    have hlt : radF n q θ t < radF n q θ r₀ :=
      radF_strictMonoOn hq hs hn θ ⟨ht.1.le, ht.2.le.trans hr₀.2.le⟩ hspec.1 ht.2
    rw [hspec.2] at hlt
    unfold radF at hlt
    rw [mem_preimage, mem_ball_zero_iff]
    nlinarith [norm_nonneg (polyQ n q ((t : ℂ) * Complex.exp (θ * I)))]

/-- **Real-analytic Jordan boundary of the lemniscate domain.** -/
theorem isRealAnalyticJordanBoundary_preimage :
    IsRealAnalyticJordanBoundary (polyQ n q ⁻¹' ball 0 1) := by
  have hexpA : ∀ θ : ℝ, AnalyticAt ℝ (fun t : ℝ => Complex.exp (t * I)) θ := fun θ =>
    (analyticAt_cexp.restrictScalars (𝕜 := ℝ)).comp
      ((Complex.ofRealCLM.analyticAt θ).mul analyticAt_const)
  have hrA : ∀ θ : ℝ, AnalyticAt ℝ (fun t : ℝ => (bdryRad n q t : ℂ)) θ := fun θ =>
    (Complex.ofRealCLM.analyticAt _).comp (bdryRad_analyticAt hq hs hn θ)
  have hpos : ∀ θ, 0 < bdryRad n q θ := fun θ => by
    have := (bdryRad_mem_Ioo hq hs hn (q := q) θ).1; linarith
  have hnorm : ∀ θ, ‖bdryCurve n q θ‖ = bdryRad n q θ := fun θ =>
    norm_ofReal_mul_exp (hpos θ).le θ
  refine ⟨bdryCurve n q, fun θ _ => (hrA θ).mul (hexpA θ), ?_, ?_, ?_, ?_⟩
  · intro θ
    unfold bdryCurve
    rw [bdryRad_periodic hq hs hn θ]
    congr 1
    push_cast
    rw [add_mul, Complex.exp_add]
    simp
  · intro θ₁ h₁ θ₂ h₂ heq
    have hr : bdryRad n q θ₁ = bdryRad n q θ₂ := by rw [← hnorm, ← hnorm, heq]
    have he : Complex.exp (θ₁ * I) = Complex.exp (θ₂ * I) := by
      unfold bdryCurve at heq
      rw [hr] at heq
      have h0 : (bdryRad n q θ₂ : ℂ) ≠ 0 := by exact_mod_cast (hpos θ₂).ne'
      exact mul_left_cancel₀ h0 heq
    have hinj := injOn_circleMap_of_abs_sub_le' (a := 0) (b := 2 * Real.pi) (c := 0) (R := 1)
      one_ne_zero (by simp)
    exact hinj h₁ h₂ (by simpa [circleMap] using he)
  · intro θ
    have hd1 : HasDerivAt (fun t : ℝ => (bdryRad n q t : ℂ)) ((deriv (bdryRad n q) θ : ℝ) : ℂ) θ :=
      ((bdryRad_analyticAt hq hs hn θ).differentiableAt.hasDerivAt).ofReal_comp
    have hd2 : HasDerivAt (fun t : ℝ => Complex.exp (t * I)) (Complex.exp (θ * I) * I) θ := by
      have h := ((hasDerivAt_id (θ : ℂ)).mul_const I).cexp
      simpa using h.comp_ofReal
    have hd := hd1.mul hd2
    have hfun : ((fun t : ℝ => (bdryRad n q t : ℂ)) * fun t : ℝ => Complex.exp (t * I)) =
        bdryCurve n q := rfl
    rw [hfun] at hd
    rw [hd.deriv]
    intro h0
    have h1 : Complex.exp (θ * I) * (((deriv (bdryRad n q) θ : ℝ) : ℂ) + (bdryRad n q θ : ℂ) * I) = 0 := by
      rw [← h0]; ring
    rcases mul_eq_zero.1 h1 with h | h
    · exact Complex.exp_ne_zero _ h
    · have := congrArg Complex.im h
      simp at this
      exact (hpos θ).ne' this
  · rw [range_bdryCurve hq hs hn, frontier_preimage_eq hq hs hn]

end bounds2

end SteklovCoalescence
