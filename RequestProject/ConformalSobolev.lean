module

public import Mathlib
public import RequestProject.DiskDensity
public import RequestProject.DomainTrace
public import RequestProject.DiskSpectral

/-!
# Sobolev pullback along a conformal map `G : 𝔻̄ → Ω̄`

Setting (`SteklovH1.ConfMap`): `G` holomorphic and injective on an open `U ⊇ 𝔻̄` with `G' ≠ 0`
on `U`; `Ω = G(𝔻)`. (Every `G` holomorphic near `𝔻̄`, injective on `𝔻̄` with `G' ≠ 0` on `𝕋`
gives such data: `ConfMap.ofHyp`.)

This file contains the change-of-variables formulas and the composition estimates used for the
Sobolev pullback `H¹(Ω) ≅ H¹(𝔻)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Real ComplexConjugate

noncomputable section

namespace SteklovH1

/-- A conformal map near the closed unit disk. -/
structure ConfMap where
  G : ℂ → ℂ
  U : Set ℂ
  isOpen : IsOpen U
  cb : closedBall (0 : ℂ) 1 ⊆ U
  diff : DifferentiableOn ℂ G U
  inj : InjOn G U
  deriv_ne : ∀ z ∈ U, deriv G z ≠ 0


/-! ### Weighted composition operators on `L²` -/

section WComp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The weighted composition `f ↦ (z ↦ a z (f (Φ z)))` as a linear map `L²(μs) → L²(μt)`,
given that it preserves `L²` and pulls back null sets. -/
def wcomp (Φ : ℂ → ℂ) (a : ℂ → E →L[ℝ] E) (μs μt : Measure ℂ)
    (hmem : ∀ f : Lp E 2 μs, MemLp (fun z => a z ((f : ℂ → E) (Φ z))) 2 μt)
    (hae : ∀ {p : ℂ → Prop}, (∀ᵐ w ∂μs, p w) → ∀ᵐ z ∂μt, p (Φ z)) :
    Lp E 2 μs →ₗ[ℝ] Lp E 2 μt where
  toFun f := (hmem f).toLp _
  map_add' f g := by
    ext1
    filter_upwards [(hmem (f + g)).coeFn_toLp, (hmem f).coeFn_toLp, (hmem g).coeFn_toLp,
      Lp.coeFn_add ((hmem f).toLp _) ((hmem g).toLp _), hae (Lp.coeFn_add f g)]
      with z h1 h2 h3 h4 h5
    rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply, map_add]
  map_smul' r f := by
    rw [RingHom.id_apply]
    ext1
    filter_upwards [(hmem (r • f)).coeFn_toLp, (hmem f).coeFn_toLp,
      Lp.coeFn_smul r ((hmem f).toLp _), hae (Lp.coeFn_smul r f)]
      with z h1 h2 h3 h4
    rw [h1, h3, Pi.smul_apply, h2, h4, Pi.smul_apply, map_smul]

lemma wcomp_ae (Φ : ℂ → ℂ) (a : ℂ → E →L[ℝ] E) (μs μt : Measure ℂ) hmem
    (hae : ∀ {p : ℂ → Prop}, (∀ᵐ w ∂μs, p w) → ∀ᵐ z ∂μt, p (Φ z)) (f : Lp E 2 μs) :
    (wcomp Φ a μs μt hmem hae f : ℂ → E) =ᵐ[μt] fun z => a z ((f : ℂ → E) (Φ z)) :=
  (hmem f).coeFn_toLp

lemma wcomp_ae' (Φ : ℂ → ℂ) (a : ℂ → E →L[ℝ] E) (μs μt : Measure ℂ) hmem
    (hae : ∀ {p : ℂ → Prop}, (∀ᵐ w ∂μs, p w) → ∀ᵐ z ∂μt, p (Φ z)) (f : Lp E 2 μs)
    {h : ℂ → E} (hf : (f : ℂ → E) =ᵐ[μs] h) :
    (wcomp Φ a μs μt hmem hae f : ℂ → E) =ᵐ[μt] fun z => a z (h (Φ z)) := by
  filter_upwards [wcomp_ae Φ a μs μt hmem hae f, hae hf] with z h1 h2
  rw [h1, h2]

end WComp

lemma memLp_two_of_lintegral {E : Type*} [NormedAddCommGroup E] {μ : Measure ℂ} {f : ℂ → E}
    (hm : AEStronglyMeasurable f μ) (h : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ⊤) : MemLp f 2 μ := by
  refine ⟨hm, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
  have e : ∀ x : ℝ≥0∞, x ^ ((2:ℝ≥0∞).toReal) = x ^ (2:ℕ) := fun x => by
    rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]; norm_num
  simp_rw [e]; exact h

lemma lintegral_lt_top_of_memLp {E : Type*} [NormedAddCommGroup E] {μ : Measure ℂ} {f : ℂ → E}
    (hf : MemLp f 2 μ) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ < ⊤ := by
  have := hf.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at this
  have e : ∀ x : ℝ≥0∞, x ^ ((2:ℝ≥0∞).toReal) = x ^ (2:ℕ) := fun x => by
    rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]; norm_num
  simp_rw [e] at this; exact this

/-- A continuous linear map on `ℓ²`-products built from bounded component maps. -/
def prodMapL {X₁ X₂ Y₁ Y₂ : Type*} [NormedAddCommGroup X₁] [NormedSpace ℝ X₁]
    [NormedAddCommGroup X₂] [NormedSpace ℝ X₂] [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁]
    [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂] (A : X₁ →ₗ[ℝ] Y₁) (B : X₂ →ₗ[ℝ] Y₂) (C : ℝ)
    (hC : 0 ≤ C) (hA : ∀ x, ‖A x‖ ≤ C * ‖x‖) (hB : ∀ x, ‖B x‖ ≤ C * ‖x‖) :
    WithLp 2 (X₁ × X₂) →L[ℝ] WithLp 2 (Y₁ × Y₂) :=
  LinearMap.mkContinuous
    { toFun := fun x => WithLp.toLp 2 (A x.fst, B x.snd)
      map_add' := fun x y => by simp only [WithLp.add_fst, WithLp.add_snd, map_add]; rfl
      map_smul' := fun r x => by
        simp only [WithLp.smul_fst, WithLp.smul_snd, map_smul, RingHom.id_apply]; rfl } C
    (fun x => by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    have h1 := WithLp.prod_norm_sq_eq_of_L2 (WithLp.toLp 2 (A x.fst, B x.snd))
    have h2 := WithLp.prod_norm_sq_eq_of_L2 x
    change _ = ‖A x.fst‖ ^ 2 + ‖B x.snd‖ ^ 2 at h1
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    rw [h1, mul_pow, h2]
    have a1 := hA x.fst
    have a2 := hB x.snd
    have b1 : ‖A x.fst‖ ^ 2 ≤ (C * ‖x.fst‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) a1 2
    have b2 : ‖B x.snd‖ ^ 2 ≤ (C * ‖x.snd‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) a2 2
    nlinarith)

@[simp] lemma prodMapL_fst {X₁ X₂ Y₁ Y₂ : Type*} [NormedAddCommGroup X₁] [NormedSpace ℝ X₁]
    [NormedAddCommGroup X₂] [NormedSpace ℝ X₂] [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁]
    [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂] (A : X₁ →ₗ[ℝ] Y₁) (B : X₂ →ₗ[ℝ] Y₂) (C : ℝ)
    hC hA hB (x : WithLp 2 (X₁ × X₂)) : (prodMapL A B C hC hA hB x).fst = A x.fst := by
  simp only [prodMapL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]; rfl

@[simp] lemma prodMapL_snd {X₁ X₂ Y₁ Y₂ : Type*} [NormedAddCommGroup X₁] [NormedSpace ℝ X₁]
    [NormedAddCommGroup X₂] [NormedSpace ℝ X₂] [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁]
    [NormedAddCommGroup Y₂] [NormedSpace ℝ Y₂] (A : X₁ →ₗ[ℝ] Y₁) (B : X₂ →ₗ[ℝ] Y₂) (C : ℝ)
    hC hA hB (x : WithLp 2 (X₁ × X₂)) : (prodMapL A B C hC hA hB x).snd = B x.snd := by
  simp only [prodMapL, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]; rfl

/-- Gradient of a composition with a holomorphic map: `∇(u ∘ Φ)(z) = conj(Φ'(z)) ∇u(Φ z)`. -/
lemma grad_comp_holo {u : ℂ → ℝ} {Φ : ℂ → ℂ} {z a : ℂ} (hu : DifferentiableAt ℝ u (Φ z))
    (hΦ : HasDerivAt Φ a z) : grad (fun z => u (Φ z)) z = conj a * grad u (Φ z) := by
  have hd : HasFDerivAt (fun z => u (Φ z))
      ((fderiv ℝ u (Φ z)).comp (ConformalPullback.mulR a)) z :=
    hu.hasFDerivAt.comp z (hΦ.hasFDerivAt.restrictScalars ℝ)
  refine ext_inner_right ℝ fun v => ?_
  rw [inner_grad, hd.fderiv, ContinuousLinearMap.comp_apply, ConformalPullback.mulR_apply,
    ← inner_grad]
  simp only [Complex.inner, map_mul, Complex.conj_conj]
  ring_nf

namespace ConfMap

/-- The hypotheses used throughout the paper (holomorphic near `𝔻̄`, injective on `𝔻̄`,
`G' ≠ 0` on `𝕋`) give conformal-map data with the same `G`. -/
theorem ofHyp {G : ℂ → ℂ}
    (hG : ∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ G U)
    (hinj : InjOn G (closedBall 0 1)) (hder : ∀ z ∈ sphere (0 : ℂ) 1, deriv G z ≠ 0) :
    ∃ c : ConfMap, c.G = G := by
  obtain ⟨U, hU, hcb, hGd⟩ := hG
  obtain ⟨U', hU', hcb', hU'U, hinj', hd'⟩ :=
    HolInv.exists_open_nbhd_injOn_deriv_ne_zero hU hcb hGd hinj hder
  exact ⟨⟨G, U', hU', hcb', hGd.mono hU'U, hinj', hd'⟩, rfl⟩

variable (c : ConfMap)

/-- `Ω = G(𝔻)`. -/
def Ω : Set ℂ := c.G '' ball 0 1

lemma ball_sub : ball (0 : ℂ) 1 ⊆ c.U := ball_subset_closedBall.trans c.cb

lemma hasDerivAt (z : ℂ) (hz : z ∈ c.U) : HasDerivAt c.G (deriv c.G z) z :=
  (c.diff.differentiableAt (c.isOpen.mem_nhds hz)).hasDerivAt

lemma hasFDerivAt (z : ℂ) (hz : z ∈ c.U) :
    HasFDerivAt c.G (ConformalPullback.mulR (deriv c.G z)) z :=
  (c.hasDerivAt z hz).hasFDerivAt.restrictScalars ℝ

lemma isOpen_Ω : IsOpen c.Ω :=
  HolInv.isOpen_image c.diff c.inj c.ball_sub isOpen_ball

lemma bdd : IsOpen c.Ω ∧ Bornology.IsBounded c.Ω ∧
    Measure.hausdorffMeasure 1 (frontier c.Ω) ≠ ⊤ :=
  bddDomain_image c.isOpen c.cb c.diff (c.inj.mono c.cb)
    (fun z hz => c.deriv_ne z (c.cb (sphere_subset_closedBall hz)))

/-- `Ω = G(𝔻)` as a bounded domain with finite boundary length. -/
def dom : BddDomain := ⟨c.Ω, c.bdd.1, c.bdd.2.1, c.bdd.2.2⟩

lemma dom_carrier : c.dom.carrier = c.Ω := rfl

lemma measurableSet_Ω : MeasurableSet c.Ω := c.isOpen_Ω.measurableSet

/-- Bounds `m ≤ |G'| ≤ M` on the closed disk. -/
lemma exists_bounds : ∃ m M : ℝ, 0 < m ∧ ∀ z ∈ closedBall (0 : ℂ) 1,
    m ≤ ‖deriv c.G z‖ ∧ ‖deriv c.G z‖ ≤ M := by
  have hdc : ContinuousOn (fun z => ‖deriv c.G z‖) c.U :=
    ((c.diff.deriv c.isOpen).continuousOn).norm
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0:ℂ) 1).exists_bound_of_continuousOn
    ((c.diff.deriv c.isOpen).continuousOn.mono c.cb)
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_closedBall (0:ℂ) 1).exists_isMinOn
    ⟨0, mem_closedBall_self zero_le_one⟩ (hdc.mono c.cb)
  refine ⟨‖deriv c.G z₀‖, M, norm_pos_iff.2 (c.deriv_ne z₀ (c.cb hz₀)), fun z hz =>
    ⟨hmin hz, hM z hz⟩⟩

/-- **Change of variables** (Lebesgue integral): `∫_Ω φ = ∫_𝔻 |G'|² φ ∘ G`. -/
theorem lintegral_Ω (φ : ℂ → ℝ≥0∞) :
    ∫⁻ w in c.Ω, φ w = ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv c.G z‖ ^ 2) * φ (c.G z) := by
  rw [Ω, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball
    (fun x hx => (c.hasFDerivAt x (c.ball_sub hx)).hasFDerivWithinAt) (c.inj.mono c.ball_sub)]
  refine setLIntegral_congr_fun measurableSet_ball fun z _ => ?_
  rw [ConformalPullback.det_mulR, abs_of_nonneg (by positivity)]

/-- **Change of variables** (Bochner integral): `∫_Ω φ = ∫_𝔻 |G'|² φ ∘ G`. -/
theorem integral_Ω {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (φ : ℂ → E) :
    ∫ w in c.Ω, φ w = ∫ z in ball (0 : ℂ) 1, (‖deriv c.G z‖ ^ 2) • φ (c.G z) := by
  rw [Ω, integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_ball
    (fun x hx => (c.hasFDerivAt x (c.ball_sub hx)).hasFDerivWithinAt) (c.inj.mono c.ball_sub)]
  refine setIntegral_congr_fun measurableSet_ball fun z _ => ?_
  rw [ConformalPullback.det_mulR, abs_of_nonneg (by positivity)]

lemma mapsTo_ball : MapsTo c.G (ball 0 1) c.Ω := fun z hz => ⟨z, hz, rfl⟩

lemma aemeasurable_G : AEMeasurable c.G (volume.restrict (ball (0 : ℂ) 1)) :=
  (c.diff.continuousOn.mono c.ball_sub).aemeasurable measurableSet_ball

/-- Null sets of `Ω` pull back to null sets of `𝔻`. -/
theorem ae_comp {p : ℂ → Prop} (h : ∀ᵐ w ∂(volume.restrict c.Ω), p w) :
    ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), p (c.G z) := by
  obtain ⟨m, M, hm, hb⟩ := c.exists_bounds
  set N := toMeasurable (volume.restrict c.Ω) {w | ¬ p w}
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume.restrict c.Ω N = 0 := by
    rw [measure_toMeasurable]; exact h
  set f : ℂ → ℝ≥0∞ := (N ∩ c.Ω).indicator 1
  have hf : Measurable f := measurable_one.indicator (hN.inter c.measurableSet_Ω)
  have h1 : ∫⁻ w in c.Ω, f w = 0 := by
    rw [lintegral_indicator (hN.inter c.measurableSet_Ω)]
    simp only [Pi.one_apply, lintegral_const, one_mul, Measure.restrict_apply MeasurableSet.univ,
      univ_inter]
    exact measure_mono_null inter_subset_left hN0
  rw [c.lintegral_Ω] at h1
  have hmeas : AEMeasurable (fun z => ENNReal.ofReal (‖deriv c.G z‖ ^ 2) * f (c.G z))
      (volume.restrict (ball (0 : ℂ) 1)) := by
    refine AEMeasurable.mul ?_ (hf.comp_aemeasurable c.aemeasurable_G)
    exact ((((c.diff.deriv c.isOpen).continuousOn.mono c.ball_sub).norm.pow 2).aemeasurable
      measurableSet_ball).ennreal_ofReal
  have h2 := (lintegral_eq_zero_iff' hmeas).1 h1
  have h2' : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)),
      ENNReal.ofReal (‖deriv c.G z‖ ^ 2) * f (c.G z) = 0 := h2
  rw [ae_restrict_iff' measurableSet_ball] at h2' ⊢
  filter_upwards [h2'] with z hz hzb
  have hz := hz hzb
  have hpos : ENNReal.ofReal (‖deriv c.G z‖ ^ 2) ≠ 0 := by
    have := (hb z (ball_subset_closedBall hzb)).1
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have : 0 < ‖deriv c.G z‖ := hm.trans_le this
    positivity
  simp only [mul_eq_zero, hpos, false_or] at hz
  have hz' : c.G z ∉ N ∩ c.Ω := by
    intro hmem; simp [f, Set.indicator_of_mem hmem] at hz
  by_contra hp
  exact hz' ⟨subset_toMeasurable _ _ hp, c.mapsTo_ball hzb⟩


/-! ### The inverse map `H = G⁻¹` -/

/-- The inverse `H = G⁻¹ : G(U) → U`. -/
def H : ℂ → ℂ := Function.invFunOn c.G c.U

/-- `V = G(U)`, an open neighbourhood of `Ω̄`. -/
def V : Set ℂ := c.G '' c.U

lemma isOpen_V : IsOpen c.V := HolInv.isOpen_image c.diff c.inj subset_rfl c.isOpen

lemma H_G {z : ℂ} (hz : z ∈ c.U) : c.H (c.G z) = z := HolInv.invFunOn_apply_self c.inj hz

lemma H_mem {w : ℂ} (hw : w ∈ c.V) : c.H w ∈ c.U := by
  obtain ⟨z, hz, rfl⟩ := hw; rw [c.H_G hz]; exact hz

lemma G_H {w : ℂ} (hw : w ∈ c.V) : c.G (c.H w) = w := by
  obtain ⟨z, hz, rfl⟩ := hw; rw [c.H_G hz]

lemma Ω_sub_V : c.Ω ⊆ c.V := image_mono c.ball_sub

lemma H_mem_ball {w : ℂ} (hw : w ∈ c.Ω) : c.H w ∈ ball (0 : ℂ) 1 := by
  obtain ⟨z, hz, rfl⟩ := hw; rw [c.H_G (c.ball_sub hz)]; exact hz

lemma hasDerivAt_H {z : ℂ} (hz : z ∈ c.U) : HasDerivAt c.H (deriv c.G z)⁻¹ (c.G z) :=
  HolInv.hasDerivAt_invFunOn c.isOpen c.diff c.inj hz (c.deriv_ne z hz)

lemma deriv_H_G {z : ℂ} (hz : z ∈ c.U) : deriv c.H (c.G z) = (deriv c.G z)⁻¹ :=
  (c.hasDerivAt_H hz).deriv

lemma differentiableOn_H : DifferentiableOn ℂ c.H c.V := by
  rintro _ ⟨z, hz, rfl⟩
  exact (c.hasDerivAt_H hz).differentiableAt.differentiableWithinAt

lemma hasDerivAt_H' {w : ℂ} (hw : w ∈ c.V) : HasDerivAt c.H (deriv c.H w) w :=
  (c.differentiableOn_H.differentiableAt (c.isOpen_V.mem_nhds hw)).hasDerivAt

lemma aemeasurable_H : AEMeasurable c.H (volume.restrict c.Ω) :=
  (c.differentiableOn_H.continuousOn.mono c.Ω_sub_V).aemeasurable c.measurableSet_Ω

/-- **Inverse change of variables**: `∫_Ω φ ∘ H = ∫_𝔻 |G'|² φ`. -/
theorem lintegral_Ω_H (φ : ℂ → ℝ≥0∞) :
    ∫⁻ w in c.Ω, φ (c.H w) = ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv c.G z‖ ^ 2) * φ z := by
  rw [c.lintegral_Ω]
  refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [c.H_G (c.ball_sub hz)]

/-- Null sets of `𝔻` pull back under `H` to null sets of `Ω`. -/
theorem ae_comp_H {p : ℂ → Prop} (h : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), p z) :
    ∀ᵐ w ∂(volume.restrict c.Ω), p (c.H w) := by
  set N := toMeasurable (volume.restrict (ball (0 : ℂ) 1)) {z | ¬ p z}
  have hN : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume.restrict (ball (0 : ℂ) 1) N = 0 := by
    rw [measure_toMeasurable]; exact h
  set f : ℂ → ℝ≥0∞ := N.indicator 1
  have hf : Measurable f := measurable_one.indicator hN
  have h1 : ∫⁻ w in c.Ω, f (c.H w) = 0 := by
    rw [c.lintegral_Ω_H]
    refine le_antisymm ?_ (zero_le _)
    calc ∫⁻ z in ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv c.G z‖ ^ 2) * f z
        ≤ ∫⁻ z in ball (0 : ℂ) 1, (⊤ : ℝ≥0∞) * f z := lintegral_mono fun z => mul_le_mul' le_top le_rfl
      _ = (⊤ : ℝ≥0∞) * ∫⁻ z in ball (0 : ℂ) 1, f z := lintegral_const_mul _ hf
      _ = 0 := by
          rw [lintegral_indicator hN]
          simp only [Pi.one_apply, lintegral_const, one_mul, Measure.restrict_apply
            MeasurableSet.univ, univ_inter]
          rw [hN0, mul_zero]
  have h2 := (lintegral_eq_zero_iff' (hf.comp_aemeasurable c.aemeasurable_H)).1 h1
  have h2' : ∀ᵐ w ∂(volume.restrict c.Ω), f (c.H w) = 0 := h2
  filter_upwards [h2'] with w hw
  by_contra hp
  have : c.H w ∈ N := subset_toMeasurable _ _ hp
  simp [f, Set.indicator_of_mem this] at hw

/-! ### Composition estimates -/

lemma lintegral_comp_G_le {m : ℝ} (hm : 0 < m)
    (hb : ∀ z ∈ closedBall (0 : ℂ) 1, m ≤ ‖deriv c.G z‖) (φ : ℂ → ℝ≥0∞) :
    ∫⁻ z in ball (0 : ℂ) 1, φ (c.G z) ≤ ENNReal.ofReal ((m ^ 2)⁻¹) * ∫⁻ w in c.Ω, φ w := by
  rw [c.lintegral_Ω, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  have h1 : 1 ≤ (m ^ 2)⁻¹ * ‖deriv c.G z‖ ^ 2 := by
    rw [inv_mul_eq_div, one_le_div (by positivity)]
    exact pow_le_pow_left₀ hm.le (hb z (ball_subset_closedBall hz)) 2
  calc φ (c.G z) = 1 * φ (c.G z) := (one_mul _).symm
    _ ≤ _ := by
      refine mul_le_mul' ?_ le_rfl
      rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal h1

lemma lintegral_comp_H_le {M : ℝ} (hb : ∀ z ∈ closedBall (0 : ℂ) 1, ‖deriv c.G z‖ ≤ M)
    (φ : ℂ → ℝ≥0∞) :
    ∫⁻ w in c.Ω, φ (c.H w) ≤ ENNReal.ofReal (M ^ 2) * ∫⁻ z in ball (0 : ℂ) 1, φ z := by
  rw [c.lintegral_Ω_H, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
  refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  exact pow_le_pow_left₀ (norm_nonneg _) (hb z (ball_subset_closedBall hz)) 2

/-- Conformal invariance of the `L²` norm of gradients (pullback direction). -/
lemma lintegral_grad_G (g : ℂ → ℂ) :
    ∫⁻ z in ball (0 : ℂ) 1, ‖conj (deriv c.G z) * g (c.G z)‖ₑ ^ 2 = ∫⁻ w in c.Ω, ‖g w‖ₑ ^ 2 := by
  rw [c.lintegral_Ω]
  refine setLIntegral_congr_fun measurableSet_ball fun z _ => ?_
  rw [enorm_mul, mul_pow, ← ofReal_norm_eq_enorm (conj _), Complex.norm_conj,
    ← ENNReal.ofReal_pow (norm_nonneg _)]

/-- Conformal invariance of the `L²` norm of gradients (pushforward direction). -/
lemma lintegral_grad_H (g : ℂ → ℂ) :
    ∫⁻ w in c.Ω, ‖conj (deriv c.H w) * g (c.H w)‖ₑ ^ 2 = ∫⁻ z in ball (0 : ℂ) 1, ‖g z‖ₑ ^ 2 := by
  rw [c.lintegral_Ω]
  refine setLIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [c.deriv_H_G (c.ball_sub hz), c.H_G (c.ball_sub hz), enorm_mul, mul_pow,
    ← ofReal_norm_eq_enorm (conj _), Complex.norm_conj, norm_inv, ← mul_assoc,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  have : ‖deriv c.G z‖ ^ 2 * ‖deriv c.G z‖⁻¹ ^ 2 = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (norm_ne_zero_iff.2 (c.deriv_ne z (c.ball_sub hz))), one_pow]
  rw [this, ENNReal.ofReal_one, one_mul]

/-! ### The pullback and pushforward operators on `L²` -/

lemma norm_le_of_enorm_sq_le {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    {x : X} {y : Y} {C : ℝ} (hC : 0 ≤ C) (h : ‖x‖ₑ ^ 2 ≤ ENNReal.ofReal (C ^ 2) * ‖y‖ₑ ^ 2) :
    ‖x‖ ≤ C * ‖y‖ := by
  simp only [← ofReal_norm_eq_enorm] at h
  rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff (by positivity),
    ← mul_pow] at h
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero |>.1 h

lemma norm_eq_of_enorm_sq_eq {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    {x : X} {y : Y} (h : ‖x‖ₑ ^ 2 = ‖y‖ₑ ^ 2) : ‖x‖ = ‖y‖ := by
  simp only [← ofReal_norm_eq_enorm] at h
  rw [← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_pow (norm_nonneg _),
    ENNReal.ofReal_eq_ofReal_iff (by positivity) (by positivity)] at h
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h

lemma sm_comp {E : Type*} [NormedAddCommGroup E] {f : ℂ → E} (hf : StronglyMeasurable f)
    {Φ : ℂ → ℂ} {μ : Measure ℂ} (hΦ : AEMeasurable Φ μ) :
    AEStronglyMeasurable (fun z => f (Φ z)) μ :=
  hf.aestronglyMeasurable.comp_aemeasurable hΦ

/-- The multiplier `y ↦ y · conj(c)` as a real-linear map. -/
abbrev cmul (c : ℂ) : ℂ →L[ℝ] ℂ := ConformalPullback.mulR (conj c)

lemma cmul_apply (c y : ℂ) : cmul c y = y * conj c := ConformalPullback.mulR_apply _ _

lemma memLp_pullF (f : Lp ℝ 2 c.dom.μ) :
    MemLp (fun z => (ContinuousLinearMap.id ℝ ℝ) ((f : ℂ → ℝ) (c.G z))) 2 μD := by
  obtain ⟨m, M, hm, hb⟩ := c.exists_bounds
  refine memLp_two_of_lintegral (sm_comp (Lp.stronglyMeasurable f)
    c.aemeasurable_G) ?_
  refine (c.lintegral_comp_G_le hm (fun z hz => (hb z hz).1) (fun w => ‖(f : ℂ → ℝ) w‖ₑ ^ 2)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact lintegral_lt_top_of_memLp (Lp.memLp f)

lemma memLp_pullG (g : Lp ℂ 2 c.dom.μ) :
    MemLp (fun z => cmul (deriv c.G z) ((g : ℂ → ℂ) (c.G z))) 2 μD := by
  refine memLp_two_of_lintegral ?_ ?_
  · simp only [cmul_apply]
    refine (sm_comp (Lp.stronglyMeasurable g) c.aemeasurable_G).mul ?_
    exact (Complex.continuous_conj.comp_continuousOn
      ((c.diff.deriv c.isOpen).continuousOn.mono c.ball_sub)).aestronglyMeasurable
      measurableSet_ball
  · simp only [cmul_apply]
    simp_rw [mul_comm _ (conj _)]
    rw [c.lintegral_grad_G]
    exact lintegral_lt_top_of_memLp (Lp.memLp g)

lemma memLp_pushF (f : Lp ℝ 2 μD) :
    MemLp (fun w => (ContinuousLinearMap.id ℝ ℝ) ((f : ℂ → ℝ) (c.H w))) 2 c.dom.μ := by
  obtain ⟨m, M, hm, hb⟩ := c.exists_bounds
  refine memLp_two_of_lintegral (sm_comp (Lp.stronglyMeasurable f)
    c.aemeasurable_H) ?_
  refine (c.lintegral_comp_H_le (fun z hz => (hb z hz).2) (fun w => ‖(f : ℂ → ℝ) w‖ₑ ^ 2)).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact lintegral_lt_top_of_memLp (Lp.memLp f)

lemma memLp_pushG (g : Lp ℂ 2 μD) :
    MemLp (fun w => cmul (deriv c.H w) ((g : ℂ → ℂ) (c.H w))) 2 c.dom.μ := by
  refine memLp_two_of_lintegral ?_ ?_
  · simp only [cmul_apply]
    refine (sm_comp (Lp.stronglyMeasurable g) c.aemeasurable_H).mul ?_
    exact (Complex.continuous_conj.comp_continuousOn
      ((c.differentiableOn_H.deriv c.isOpen_V).continuousOn.mono c.Ω_sub_V)).aestronglyMeasurable
      c.measurableSet_Ω
  · simp only [cmul_apply]
    simp_rw [mul_comm _ (conj _)]
    change ∫⁻ w in c.Ω, _ < ⊤
    rw [c.lintegral_grad_H]
    exact lintegral_lt_top_of_memLp (Lp.memLp g)

/-- `f ↦ f ∘ G`, `L²(Ω) → L²(𝔻)`. -/
def pullF : Lp ℝ 2 c.dom.μ →ₗ[ℝ] Lp ℝ 2 μD :=
  wcomp c.G (fun _ => ContinuousLinearMap.id ℝ ℝ) _ _ c.memLp_pullF c.ae_comp

/-- `g ↦ conj(G') · g ∘ G`, `L²(Ω; ℝ²) → L²(𝔻; ℝ²)` (pullback of gradients). -/
def pullG : Lp ℂ 2 c.dom.μ →ₗ[ℝ] Lp ℂ 2 μD :=
  wcomp c.G (fun z => cmul (deriv c.G z)) _ _ c.memLp_pullG c.ae_comp

/-- `f ↦ f ∘ H`, `L²(𝔻) → L²(Ω)`. -/
def pushF : Lp ℝ 2 μD →ₗ[ℝ] Lp ℝ 2 c.dom.μ :=
  wcomp c.H (fun _ => ContinuousLinearMap.id ℝ ℝ) _ _ c.memLp_pushF c.ae_comp_H

/-- `g ↦ conj(H') · g ∘ H`, `L²(𝔻; ℝ²) → L²(Ω; ℝ²)`. -/
def pushG : Lp ℂ 2 μD →ₗ[ℝ] Lp ℂ 2 c.dom.μ :=
  wcomp c.H (fun w => cmul (deriv c.H w)) _ _ c.memLp_pushG c.ae_comp_H

lemma pullF_ae (f : Lp ℝ 2 c.dom.μ) : (c.pullF f : ℂ → ℝ) =ᵐ[μD] fun z => (f : ℂ → ℝ) (c.G z) :=
  wcomp_ae _ _ _ _ _ _ f

lemma pullG_ae (g : Lp ℂ 2 c.dom.μ) :
    (c.pullG g : ℂ → ℂ) =ᵐ[μD] fun z => (g : ℂ → ℂ) (c.G z) * conj (deriv c.G z) := by
  filter_upwards [wcomp_ae c.G (fun z => cmul (deriv c.G z)) c.dom.μ μD c.memLp_pullG c.ae_comp g] with z hz
  rw [pullG, hz, cmul_apply]

lemma pushF_ae (f : Lp ℝ 2 μD) : (c.pushF f : ℂ → ℝ) =ᵐ[c.dom.μ] fun w => (f : ℂ → ℝ) (c.H w) :=
  wcomp_ae _ _ _ _ _ _ f

lemma pushG_ae (g : Lp ℂ 2 μD) :
    (c.pushG g : ℂ → ℂ) =ᵐ[c.dom.μ] fun w => (g : ℂ → ℂ) (c.H w) * conj (deriv c.H w) := by
  filter_upwards [wcomp_ae c.H (fun w => cmul (deriv c.H w)) μD c.dom.μ c.memLp_pushG c.ae_comp_H g] with z hz
  rw [pushG, hz, cmul_apply]

lemma norm_pullF_le {m : ℝ} (hm : 0 < m) (hb : ∀ z ∈ closedBall (0 : ℂ) 1, m ≤ ‖deriv c.G z‖)
    (f : Lp ℝ 2 c.dom.μ) : ‖c.pullF f‖ ≤ m⁻¹ * ‖f‖ := by
  refine norm_le_of_enorm_sq_le (by positivity) ?_
  rw [BddDomain.enorm_Lp_sq, BddDomain.enorm_Lp_sq, lintegral_congr_ae ((c.pullF_ae f).mono fun z hz => by rw [hz]),
    inv_pow]
  exact c.lintegral_comp_G_le hm hb (fun w => ‖(f : ℂ → ℝ) w‖ₑ ^ 2)

lemma norm_pushF_le {M : ℝ} (hM : 0 ≤ M) (hb : ∀ z ∈ closedBall (0 : ℂ) 1, ‖deriv c.G z‖ ≤ M)
    (f : Lp ℝ 2 μD) : ‖c.pushF f‖ ≤ M * ‖f‖ := by
  refine norm_le_of_enorm_sq_le hM ?_
  rw [BddDomain.enorm_Lp_sq, BddDomain.enorm_Lp_sq, lintegral_congr_ae ((c.pushF_ae f).mono fun z hz => by rw [hz])]
  exact c.lintegral_comp_H_le hb (fun w => ‖(f : ℂ → ℝ) w‖ₑ ^ 2)

lemma norm_pullG (g : Lp ℂ 2 c.dom.μ) : ‖c.pullG g‖ = ‖g‖ := by
  have h : ‖c.pullG g‖ₑ ^ 2 = ‖g‖ₑ ^ 2 := by
    rw [BddDomain.enorm_Lp_sq, BddDomain.enorm_Lp_sq, lintegral_congr_ae ((c.pullG_ae g).mono fun z hz => by rw [hz])]
    simp_rw [mul_comm _ (conj _)]
    exact c.lintegral_grad_G _
  exact norm_eq_of_enorm_sq_eq h

lemma norm_pushG (g : Lp ℂ 2 μD) : ‖c.pushG g‖ = ‖g‖ := by
  have h : ‖c.pushG g‖ₑ ^ 2 = ‖g‖ₑ ^ 2 := by
    rw [BddDomain.enorm_Lp_sq, BddDomain.enorm_Lp_sq, lintegral_congr_ae ((c.pushG_ae g).mono fun z hz => by rw [hz])]
    simp_rw [mul_comm _ (conj _)]
    exact c.lintegral_grad_H _
  exact norm_eq_of_enorm_sq_eq h

lemma pushF_pullF (f : Lp ℝ 2 c.dom.μ) : c.pushF (c.pullF f) = f := by
  ext1
  filter_upwards [c.pushF_ae (c.pullF f), c.ae_comp_H (c.pullF_ae f),
    ae_restrict_mem c.measurableSet_Ω] with w h1 h2 h3
  rw [h1, h2, c.G_H (c.Ω_sub_V h3)]

lemma pullF_pushF (f : Lp ℝ 2 μD) : c.pullF (c.pushF f) = f := by
  ext1
  filter_upwards [c.pullF_ae (c.pushF f), c.ae_comp (c.pushF_ae f),
    ae_restrict_mem measurableSet_ball] with z h1 h2 h3
  rw [h1, h2, c.H_G (c.ball_sub h3)]

lemma pushG_pullG (g : Lp ℂ 2 c.dom.μ) : c.pushG (c.pullG g) = g := by
  ext1
  filter_upwards [c.pushG_ae (c.pullG g), c.ae_comp_H (c.pullG_ae g),
    ae_restrict_mem c.measurableSet_Ω] with w h1 h2 h3
  obtain ⟨z, hz, rfl⟩ := h3
  rw [h1, h2, c.H_G (c.ball_sub hz), c.deriv_H_G (c.ball_sub hz), map_inv₀, mul_assoc,
    mul_inv_cancel₀ ((map_ne_zero _).2 (c.deriv_ne z (c.ball_sub hz))), mul_one]

lemma pullG_pushG (g : Lp ℂ 2 μD) : c.pullG (c.pushG g) = g := by
  ext1
  filter_upwards [c.pullG_ae (c.pushG g), c.ae_comp (c.pushG_ae g),
    ae_restrict_mem measurableSet_ball] with z h1 h2 h3
  rw [h1, h2, c.H_G (c.ball_sub h3), c.deriv_H_G (c.ball_sub h3), map_inv₀, mul_assoc,
    inv_mul_cancel₀ ((map_ne_zero _).2 (c.deriv_ne z (c.ball_sub h3))), mul_one]

/-! ### The pullback on `L²(Ω) ⊕ L²(Ω; ℝ²)` -/

lemma exists_C : ∃ C : ℝ, 0 ≤ C ∧ (∀ f : Lp ℝ 2 c.dom.μ, ‖c.pullF f‖ ≤ C * ‖f‖) ∧
    (∀ g : Lp ℂ 2 c.dom.μ, ‖c.pullG g‖ ≤ C * ‖g‖) ∧ (∀ f : Lp ℝ 2 μD, ‖c.pushF f‖ ≤ C * ‖f‖) ∧
    (∀ g : Lp ℂ 2 μD, ‖c.pushG g‖ ≤ C * ‖g‖) := by
  obtain ⟨m, M, hm, hb⟩ := c.exists_bounds
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb 0 (mem_closedBall_self zero_le_one)).2
  refine ⟨max (max m⁻¹ M) 1, by positivity, fun f => ?_, fun g => ?_, fun f => ?_, fun g => ?_⟩
  · exact (c.norm_pullF_le hm (fun z hz => (hb z hz).1) f).trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans (le_max_left _ _)) (norm_nonneg _))
  · rw [c.norm_pullG]; exact le_mul_of_one_le_left (norm_nonneg _) (le_max_right _ _)
  · exact (c.norm_pushF_le hM (fun z hz => (hb z hz).2) f).trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans (le_max_left _ _)) (norm_nonneg _))
  · rw [c.norm_pushG]; exact le_mul_of_one_le_left (norm_nonneg _) (le_max_right _ _)

/-- The pullback `(f, g) ↦ (f ∘ G, conj(G') · g ∘ G)` on the ambient spaces. -/
def pullAmb : c.dom.Amb →L[ℝ] Amb :=
  prodMapL c.pullF c.pullG c.exists_C.choose c.exists_C.choose_spec.1
    c.exists_C.choose_spec.2.1 c.exists_C.choose_spec.2.2.1

/-- The pushforward `(f, g) ↦ (f ∘ H, conj(H') · g ∘ H)` on the ambient spaces. -/
def pushAmb : Amb →L[ℝ] c.dom.Amb :=
  prodMapL c.pushF c.pushG c.exists_C.choose c.exists_C.choose_spec.1
    c.exists_C.choose_spec.2.2.2.1 c.exists_C.choose_spec.2.2.2.2

@[simp] lemma pullAmb_fst (x : c.dom.Amb) : (c.pullAmb x).fst = c.pullF x.fst := by
  simp [pullAmb]
@[simp] lemma pullAmb_snd (x : c.dom.Amb) : (c.pullAmb x).snd = c.pullG x.snd := by
  simp [pullAmb]
@[simp] lemma pushAmb_fst (x : Amb) : (c.pushAmb x).fst = c.pushF x.fst := by
  simp [pushAmb]
@[simp] lemma pushAmb_snd (x : Amb) : (c.pushAmb x).snd = c.pushG x.snd := by
  simp [pushAmb]

lemma amb_ext {x y : Amb} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  WithLp.ofLp_injective _ (Prod.ext h1 h2)

lemma dom_amb_ext {D : BddDomain} {x y : D.Amb} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) :
    x = y :=
  WithLp.ofLp_injective _ (Prod.ext h1 h2)

lemma pushAmb_pullAmb (x : c.dom.Amb) : c.pushAmb (c.pullAmb x) = x :=
  dom_amb_ext (by simp [pushF_pullF]) (by simp [pushG_pullG])

lemma pullAmb_pushAmb (x : Amb) : c.pullAmb (c.pushAmb x) = x :=
  amb_ext (by simp [pullF_pushF]) (by simp [pullG_pushG])

/-! ### Smooth functions -/

lemma exists_cutoff₁ : ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧
    (∃ W, IsOpen W ∧ closedBall (0 : ℂ) 1 ⊆ W ∧ ∀ z ∈ W, χ z = 1) ∧ tsupport χ ⊆ c.U :=
  ConformalPullback.exists_cutoff (isCompact_closedBall 0 1) c.isOpen c.cb

lemma isCompact_K₂ : IsCompact (c.G '' closedBall 0 1) :=
  (isCompact_closedBall 0 1).image_of_continuousOn (c.diff.continuousOn.mono c.cb)

lemma exists_cutoff₂ : ∃ χ : ℂ → ℝ, ContDiff ℝ ∞ χ ∧
    (∃ W, IsOpen W ∧ c.G '' closedBall (0 : ℂ) 1 ⊆ W ∧ ∀ z ∈ W, χ z = 1) ∧ tsupport χ ⊆ c.V :=
  ConformalPullback.exists_cutoff c.isCompact_K₂ c.isOpen_V (image_mono c.cb)

lemma contDiffOn_G : ContDiffOn ℝ ∞ c.G c.U :=
  ConformalPullback.contDiffOn_of_differentiableOn c.isOpen c.diff

lemma contDiffOn_H : ContDiffOn ℝ ∞ c.H c.V :=
  ConformalPullback.contDiffOn_of_differentiableOn c.isOpen_V c.differentiableOn_H

/-- The smooth pullback `u ↦ χ₁ · (u ∘ G)` (with `χ₁ = 1` near `𝔻̄`). -/
def pullSmooth (u : smoothFns) : smoothFns :=
  ⟨fun z => c.exists_cutoff₁.choose z * (u : ℂ → ℝ) (c.G z),
    ConformalPullback.contDiff_mul_comp c.isOpen c.exists_cutoff₁.choose_spec.1
      c.exists_cutoff₁.choose_spec.2.2 c.contDiffOn_G u.2⟩

/-- The smooth pushforward `u ↦ χ₂ · (u ∘ H)` (with `χ₂ = 1` near `Ω̄`). -/
def pushSmooth (u : smoothFns) : smoothFns :=
  ⟨fun w => c.exists_cutoff₂.choose w * (u : ℂ → ℝ) (c.H w),
    ConformalPullback.contDiff_mul_comp c.isOpen_V c.exists_cutoff₂.choose_spec.1
      c.exists_cutoff₂.choose_spec.2.2 c.contDiffOn_H u.2⟩

lemma pullSmooth_eventually (u : smoothFns) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    ((c.pullSmooth u : smoothFns) : ℂ → ℝ) =ᶠ[𝓝 z] fun z => (u : ℂ → ℝ) (c.G z) := by
  obtain ⟨W, hW, hKW, h1⟩ := c.exists_cutoff₁.choose_spec.2.1
  filter_upwards [hW.mem_nhds (hKW hz)] with y hy
  change c.exists_cutoff₁.choose y * _ = _
  rw [h1 y hy, one_mul]

lemma pushSmooth_eventually (u : smoothFns) {w : ℂ} (hw : w ∈ c.G '' closedBall (0 : ℂ) 1) :
    ((c.pushSmooth u : smoothFns) : ℂ → ℝ) =ᶠ[𝓝 w] fun w => (u : ℂ → ℝ) (c.H w) := by
  obtain ⟨W, hW, hKW, h1⟩ := c.exists_cutoff₂.choose_spec.2.1
  filter_upwards [hW.mem_nhds (hKW hw)] with y hy
  change c.exists_cutoff₂.choose y * _ = _
  rw [h1 y hy, one_mul]

lemma grad_pullSmooth (u : smoothFns) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    grad (c.pullSmooth u : ℂ → ℝ) z = conj (deriv c.G z) * grad u (c.G z) := by
  unfold grad
  rw [(c.pullSmooth_eventually u hz).fderiv_eq]
  exact grad_comp_holo (((contDiff_one_of_mem u.2).differentiable one_ne_zero) _)
    (c.hasDerivAt z (c.cb hz))

lemma grad_pushSmooth (u : smoothFns) {w : ℂ} (hw : w ∈ c.G '' closedBall (0 : ℂ) 1) :
    grad (c.pushSmooth u : ℂ → ℝ) w = conj (deriv c.H w) * grad u (c.H w) := by
  unfold grad
  rw [(c.pushSmooth_eventually u hw).fderiv_eq]
  exact grad_comp_holo (((contDiff_one_of_mem u.2).differentiable one_ne_zero) _)
    (c.hasDerivAt_H' (image_mono c.cb hw))

lemma pullAmb_embed (u : smoothFns) : c.pullAmb (c.dom.embed u) = embed (c.pullSmooth u) := by
  refine amb_ext ?_ ?_
  · rw [pullAmb_fst, BddDomain.embed_fst, embed_fst]
    ext1
    filter_upwards [c.pullF_ae (c.dom.toL2 u), c.ae_comp (c.dom.toL2_ae u), toL2_ae (c.pullSmooth u),
      ae_restrict_mem measurableSet_ball] with z h1 h2 h3 hz
    rw [h1, h2, h3]
    exact ((c.pullSmooth_eventually u (ball_subset_closedBall hz)).eq_of_nhds).symm
  · rw [pullAmb_snd, BddDomain.embed_snd, embed_snd]
    ext1
    filter_upwards [c.pullG_ae (c.dom.gradL2 u), c.ae_comp (c.dom.gradL2_ae u),
      gradL2_ae (c.pullSmooth u), ae_restrict_mem measurableSet_ball] with z h1 h2 h3 hz
    rw [h1, h2, h3, c.grad_pullSmooth u (ball_subset_closedBall hz), mul_comm]

lemma pushAmb_embed (u : smoothFns) : c.pushAmb (embed u) = c.dom.embed (c.pushSmooth u) := by
  have hK : ∀ w ∈ c.Ω, w ∈ c.G '' closedBall (0 : ℂ) 1 := fun w hw => image_mono
    ball_subset_closedBall hw
  refine dom_amb_ext ?_ ?_
  · rw [pushAmb_fst, BddDomain.embed_fst, embed_fst]
    ext1
    filter_upwards [c.pushF_ae (toL2 u), c.ae_comp_H (toL2_ae u), c.dom.toL2_ae (c.pushSmooth u),
      ae_restrict_mem c.measurableSet_Ω] with z h1 h2 h3 hz
    rw [h1, h2, h3]
    exact ((c.pushSmooth_eventually u (hK z hz)).eq_of_nhds).symm
  · rw [pushAmb_snd, BddDomain.embed_snd, embed_snd]
    ext1
    filter_upwards [c.pushG_ae (gradL2 u), c.ae_comp_H (gradL2_ae u),
      c.dom.gradL2_ae (c.pushSmooth u), ae_restrict_mem c.measurableSet_Ω] with z h1 h2 h3 hz
    rw [h1, h2, h3, c.grad_pushSmooth u (hK z hz), mul_comm]

/-! ### The Sobolev pullback `H¹(Ω) ≅ H¹(𝔻)` -/

lemma pullAmb_mem (x : c.dom.H1) : c.pullAmb x ∈ H1 := by
  have hx : (x : c.dom.Amb) ∈ closure (LinearMap.range c.dom.embed : Set c.dom.Amb) := x.2
  have h1 := image_closure_subset_closure_image c.pullAmb.continuous ⟨_, hx, rfl⟩
  show c.pullAmb x ∈ closure (LinearMap.range embed : Set Amb)
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  exact ⟨c.pullSmooth u, (c.pullAmb_embed u).symm⟩

lemma pushAmb_mem (x : H1) : c.pushAmb x ∈ c.dom.H1 := by
  have hx : (x : Amb) ∈ closure (LinearMap.range embed : Set Amb) := x.2
  have h1 := image_closure_subset_closure_image c.pushAmb.continuous ⟨_, hx, rfl⟩
  show c.pushAmb x ∈ closure (LinearMap.range c.dom.embed : Set c.dom.Amb)
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨u, rfl⟩, rfl⟩
  exact ⟨c.pushSmooth u, (c.pushAmb_embed u).symm⟩

/-- The Sobolev pullback `H¹(Ω) → H¹(𝔻)`, `u ↦ u ∘ G`. -/
def pullH1 : c.dom.H1 →L[ℝ] H1 :=
  (c.pullAmb.comp c.dom.H1.subtypeL).codRestrict H1 c.pullAmb_mem

/-- The Sobolev pushforward `H¹(𝔻) → H¹(Ω)`, `v ↦ v ∘ G⁻¹`. -/
def pushH1 : H1 →L[ℝ] c.dom.H1 :=
  (c.pushAmb.comp H1.subtypeL).codRestrict c.dom.H1 c.pushAmb_mem

@[simp] lemma coe_pullH1 (x : c.dom.H1) : (c.pullH1 x : Amb) = c.pullAmb x := rfl
@[simp] lemma coe_pushH1 (x : H1) : (c.pushH1 x : c.dom.Amb) = c.pushAmb x := rfl

/-- **Sobolev pullback isomorphism** `H¹(G(𝔻)) ≃ H¹(𝔻)`: `(f, g) ↦ (f ∘ G, conj(G') · g ∘ G)`,
a continuous linear equivalence with inverse `(f, g) ↦ (f ∘ G⁻¹, conj((G⁻¹)') · g ∘ G⁻¹)`. -/
def sobolevPullback : c.dom.H1 ≃L[ℝ] H1 :=
  ContinuousLinearEquiv.equivOfInverse c.pullH1 c.pushH1
    (fun x => Subtype.ext (c.pushAmb_pullAmb x)) (fun x => Subtype.ext (c.pullAmb_pushAmb x))

lemma sobolevPullback_apply (x : c.dom.H1) : (c.sobolevPullback x : Amb) = c.pullAmb x := rfl

lemma sobolevPullback_symm_apply (x : H1) :
    (c.sobolevPullback.symm x : c.dom.Amb) = c.pushAmb x := rfl

lemma sobolevPullback_embedH (u : smoothFns) :
    c.sobolevPullback (c.dom.embedH u) = embedH (c.pullSmooth u) :=
  Subtype.ext (c.pullAmb_embed u)

end ConfMap

end SteklovH1
