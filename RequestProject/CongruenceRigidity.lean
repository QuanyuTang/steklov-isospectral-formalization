module

public import RequestProject.DiskAut
public import RequestProject.PaperStatements

/-!
# From a congruence of realized domains to an equivalence of Blaschke products

Let `F₁, F₂` be normalized realizing maps of the weights `|B₁'|, |B₂'|` (finite Blaschke products),
and `Ω_k = c · F_k(𝔻)`.

* `blaschke_of_congr_hol`: if `z ↦ a z + b` (`|a| = 1`) maps `Ω₁` onto `Ω₂`, there are a disk
  automorphism `φ` and `|η| = 1` with `B₁ = η · B₂ ∘ φ` on `𝔻̄`.
* `blaschke_of_congr_anti`: if `z ↦ a z̄ + b` (`|a| = 1`, `c` real) maps `Ω₁` onto `Ω₂`, there are an
  antiholomorphic disk automorphism `ψ` and `|η| = 1` with `B₁ = η · conj (B₂ ∘ ψ)` on `𝔻̄`.

The proof: `F₂⁻¹ ∘ (normalized congruence) ∘ F₁` is a holomorphic automorphism of `𝔻`, hence Möbius
(`DiskAut.exists_diskAut`); the identity extends across the circle by the identity theorem, which
gives `|B₁'| = |(B₂ ∘ φ)'|` on `𝕋`; then the boundary rigidity Lemma 2.4.1 applies
(`blaschke_boundary_rigidity`, `blaschke_boundary_rigidity_anti`).
-/

@[expose] public section

open Complex Metric Set Filter Topology

noncomputable section

namespace CongrRigid

open SteklovBlaschke DiskAut

lemma differentiableAt_bfac_of_ne {b z : ℂ} (h : 1 - (starRingEnd ℂ) b * z ≠ 0) :
    DifferentiableAt ℂ (bfac b) z := by
  unfold bfac
  exact (differentiableAt_id.sub_const b).div
    ((differentiableAt_const _).sub (differentiableAt_const _ |>.mul differentiableAt_id)) h

lemma norm_diskAut_eq_one {φ : ℂ → ℂ} (hφ : IsDiskAut φ) {z : ℂ} (hz : ‖z‖ = 1) : ‖φ z‖ = 1 := by
  obtain ⟨μ, b, hμ, hb, rfl⟩ := hφ
  rw [norm_mul, hμ, one_mul, norm_bfac_eq_one hb hz]

/-- Derivative along the circle. -/
lemma norm_deriv_circ {G : ℂ → ℂ} {t : ℝ} (hG : DifferentiableAt ℂ G (exp (t * I))) :
    ‖deriv (fun s : ℝ => G (exp (s * I))) t‖ = ‖deriv G (exp (t * I))‖ := by
  have h1 : HasDerivAt (fun z : ℂ => exp (z * I)) (exp (t * I) * (1 * I)) (t : ℂ) :=
    ((hasDerivAt_id (t : ℂ)).mul_const I).cexp
  have h2 := (hG.hasDerivAt.comp (t : ℂ) h1).comp_ofReal
  rw [show (fun s : ℝ => G (exp (s * I))) = (fun y : ℝ => (G ∘ fun z => exp (z * I)) ↑y) from rfl,
    h2.deriv, norm_mul, norm_mul, one_mul, norm_I, mul_one, norm_exp_ofReal_mul_I, mul_one]

/-- Derivative along the reflected circle. -/
lemma norm_deriv_circ_conj {G : ℂ → ℂ} {t : ℝ}
    (hG : DifferentiableAt ℂ G ((starRingEnd ℂ) (exp (t * I)))) :
    ‖deriv (fun s : ℝ => G ((starRingEnd ℂ) (exp (s * I)))) t‖ =
      ‖deriv G ((starRingEnd ℂ) (exp (t * I)))‖ := by
  have e : ∀ s : ℝ, (starRingEnd ℂ) (exp (s * I)) = exp (-(s : ℂ) * I) := by
    intro s; rw [← exp_conj]; congr 1; simp [conj_ofReal]
  simp only [e] at hG ⊢
  have h1 : HasDerivAt (fun z : ℂ => exp (-z * I)) (exp (-(t : ℂ) * I) * (-1 * I)) (t : ℂ) :=
    (((hasDerivAt_id (t : ℂ)).neg).mul_const I).cexp
  have h2 := (hG.hasDerivAt.comp (t : ℂ) h1).comp_ofReal
  rw [show (fun s : ℝ => G (exp (-(s : ℂ) * I))) =
      (fun y : ℝ => (G ∘ fun z => exp (-z * I)) ↑y) from rfl,
    h2.deriv, norm_mul, norm_mul, norm_mul, norm_neg, norm_one, one_mul, norm_I, mul_one,
    show -(t : ℂ) * I = ((-t : ℝ) : ℂ) * I by push_cast; ring, norm_exp_ofReal_mul_I, mul_one]

/-- **Core step**: a holomorphic `H`, injective on `𝔻`, with `H(𝔻) = F₂(𝔻)`, factors as
`F₂ ∘ φ` with `φ` a disk automorphism, and `|H'| = |F₂' ∘ φ| |φ'|` on the circle. -/
theorem core {F₂ H : ℂ → ℂ} {ρ : ℂ → ℝ} (hF : IsNormalizedRealizing F₂ ρ) {U : Set ℂ}
    (hU : IsOpen U) (hcb : closedBall 0 1 ⊆ U) (hHd : DifferentiableOn ℂ H U)
    (hHinj : InjOn H (ball 0 1)) (him : H '' ball 0 1 = F₂ '' ball 0 1) :
    ∃ φ, IsDiskAut φ ∧ ∀ ζ ∈ sphere (0 : ℂ) 1,
      ‖deriv H ζ‖ = ‖deriv F₂ (φ ζ)‖ * ‖deriv φ ζ‖ := by
  obtain ⟨⟨U₂, hU₂, hcb₂, hd₂⟩, hinj₂, -⟩ := hF
  have hd2b : DifferentiableOn ℂ F₂ (ball 0 1) := hd₂.mono (ball_subset_closedBall.trans hcb₂)
  have hinj2b : InjOn F₂ (ball 0 1) := hinj₂.mono ball_subset_closedBall
  set g := Function.invFunOn F₂ (ball 0 1) with hg
  set f : ℂ → ℂ := fun w => g (H w) with hf
  have hHmem : ∀ w ∈ ball (0 : ℂ) 1, H w ∈ F₂ '' ball 0 1 := fun w hw => him ▸ ⟨w, hw, rfl⟩
  have hF₂f : ∀ w ∈ ball (0 : ℂ) 1, F₂ (f w) = H w := fun w hw => Function.invFunOn_eq (hHmem w hw)
  have hfmem : ∀ w ∈ ball (0 : ℂ) 1, f w ∈ ball (0 : ℂ) 1 :=
    fun w hw => Function.invFunOn_mem (hHmem w hw)
  have hf_im : f '' ball 0 1 = ball 0 1 := by
    ext z; constructor
    · rintro ⟨w, hw, rfl⟩; exact hfmem w hw
    · intro hz
      have : F₂ z ∈ H '' ball 0 1 := him ▸ ⟨z, hz, rfl⟩
      obtain ⟨w, hw, hwz⟩ := this
      refine ⟨w, hw, ?_⟩
      show g (H w) = z
      rw [hwz, hg, HolInv.invFunOn_apply_self hinj2b hz]
  have hf_inj : InjOn f (ball 0 1) := by
    intro w hw w' hw' h
    have := congrArg F₂ h
    rw [hF₂f w hw, hF₂f w' hw'] at this
    exact hHinj hw hw' this
  have hf_d : DifferentiableOn ℂ f (ball 0 1) := by
    intro w hw
    obtain ⟨z, hz, hzw⟩ := hHmem w hw
    have hgd := HolInv.hasDerivAt_invFunOn isOpen_ball hd2b hinj2b hz
      (HolInv.deriv_ne_zero_of_injOn isOpen_ball hd2b hinj2b hz)
    rw [hzw] at hgd
    exact (hgd.differentiableAt.comp w
      (hHd.differentiableAt (hU.mem_nhds (hcb (ball_subset_closedBall hw))))).differentiableWithinAt
  obtain ⟨φ, hφ, hfφ⟩ := exists_diskAut hf_d hf_inj hf_im
  have hrel : ∀ w ∈ ball (0 : ℂ) 1, F₂ (φ w) = H w := fun w hw => by rw [← hfφ hw, hF₂f w hw]
  refine ⟨φ, hφ, fun ζ hζ => ?_⟩
  have hζ1 : ‖ζ‖ = 1 := by simpa using hζ
  obtain ⟨μ, b, hμ, hb, hφdef⟩ := hφ
  have hφd : ∀ z, 1 - (starRingEnd ℂ) b * z ≠ 0 → DifferentiableAt ℂ φ z := by
    intro z hz; rw [hφdef]; exact (differentiableAt_bfac_of_ne hz).const_mul μ
  set W : Set ℂ := {z | 1 - (starRingEnd ℂ) b * z ≠ 0} with hW
  have hWo : IsOpen W := isOpen_ne_fun (by fun_prop) (by fun_prop)
  have hφc : ContinuousOn φ W := fun z hz => (hφd z hz).continuousAt.continuousWithinAt
  set V : Set ℂ := U ∩ (W ∩ φ ⁻¹' U₂) with hV
  have hVo : IsOpen V := hU.inter (hφc.isOpen_inter_preimage hWo hU₂)
  have hφζ : ‖φ ζ‖ = 1 := norm_diskAut_eq_one ⟨μ, b, hμ, hb, hφdef⟩ hζ1
  have hζV : ζ ∈ V := ⟨hcb (by simp [hζ1]), denom_ne_zero hb hζ1.le,
    hcb₂ (by simp [hφζ])⟩
  obtain ⟨r, hr, hrV⟩ := Metric.isOpen_iff.1 hVo ζ hζV
  set r' := min r 1 with hr'
  have hr'0 : 0 < r' := lt_min hr one_pos
  have hr'V : ball ζ r' ⊆ V := (ball_subset_ball (min_le_left _ _)).trans hrV
  -- both sides holomorphic on `ball ζ r'`
  have hA1 : AnalyticOnNhd ℂ H (ball ζ r') :=
    (hHd.mono fun z hz => (hr'V hz).1).analyticOnNhd isOpen_ball
  have hA2 : AnalyticOnNhd ℂ (F₂ ∘ φ) (ball ζ r') := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_ball
    have hzV := hr'V hz
    exact ((hd₂.differentiableAt (hU₂.mem_nhds hzV.2.2)).comp z
      (hφd z hzV.2.1)).differentiableWithinAt
  -- a point of `𝔻 ∩ ball ζ r'`
  set z₀ : ℂ := ((1 - r' / 2 : ℝ) : ℂ) * ζ with hz₀
  have hz₀b : z₀ ∈ ball ζ r' := by
    rw [mem_ball, dist_eq_norm, hz₀,
      show ((1 - r' / 2 : ℝ) : ℂ) * ζ - ζ = ((-(r' / 2) : ℝ) : ℂ) * ζ by push_cast; ring,
      norm_mul, hζ1, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_neg,
      abs_of_pos (by linarith)]
    linarith
  have hz₀d : z₀ ∈ ball (0 : ℂ) 1 := by
    have h1 : r' ≤ 1 := min_le_right _ _
    rw [mem_ball_zero_iff, hz₀, norm_mul, hζ1, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  have hev : H =ᶠ[𝓝 z₀] F₂ ∘ φ := by
    filter_upwards [isOpen_ball.mem_nhds hz₀d] with w hw
    exact (hrel w hw).symm
  have heq := hA1.eqOn_of_preconnected_of_eventuallyEq hA2 (convex_ball ζ r').isPreconnected
    hz₀b hev
  have hevζ : H =ᶠ[𝓝 ζ] F₂ ∘ φ := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hr'0)] with w hw
    exact heq hw
  rw [hevζ.deriv_eq, deriv_comp ζ (hd₂.differentiableAt (hU₂.mem_nhds hζV.2.2))
    (hφd ζ hζV.2.1), norm_mul]

/-- The norm of a derivative along the circle of a Blaschke product composed with a disk
automorphism. -/
lemma norm_deriv_comp_aut {B φ : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n) (hφ : IsDiskAut φ)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖deriv (B ∘ φ) ζ‖ = ‖deriv B (φ ζ)‖ * ‖deriv φ ζ‖ := by
  obtain ⟨μ, b, hμ, hb, hφdef⟩ := hφ
  have hφd : DifferentiableAt ℂ φ ζ := by
    rw [hφdef]; exact (differentiableAt_bfac hb hζ.le).const_mul μ
  have hφζ : ‖φ ζ‖ = 1 := norm_diskAut_eq_one ⟨μ, b, hμ, hb, hφdef⟩ hζ
  rw [deriv_comp ζ (hB.differentiableAt hφζ.le) hφd, norm_mul]

lemma diskAut_differentiableAt {φ : ℂ → ℂ} (hφ : IsDiskAut φ) {ζ : ℂ} (hζ : ‖ζ‖ ≤ 1) :
    DifferentiableAt ℂ φ ζ := by
  obtain ⟨μ, b, hμ, hb, rfl⟩ := hφ
  exact (differentiableAt_bfac hb hζ).const_mul μ

/-- **Orientation-preserving congruence ⇒ Blaschke equivalence.** -/
theorem blaschke_of_congr_hol {B₁ B₂ F₁ F₂ : ℂ → ℂ} {n m : ℕ} (hB₁ : IsFiniteBlaschke B₁ n)
    (hB₂ : IsFiniteBlaschke B₂ m) (hF₁ : IsNormalizedRealizing F₁ (fun z => ‖deriv B₁ z‖))
    (hF₂ : IsNormalizedRealizing F₂ (fun z => ‖deriv B₂ z‖)) {c : ℂ} (hc : c ≠ 0) {a b : ℂ}
    (ha : ‖a‖ = 1)
    (hJ : (fun z => a * z + b) '' ((fun w => c * F₁ w) '' ball 0 1) =
      (fun w => c * F₂ w) '' ball 0 1) :
    ∃ φ, IsDiskAut φ ∧ ∃ η : ℂ, ‖η‖ = 1 ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → B₁ z = η * B₂ (φ z) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  obtain ⟨⟨U₁, hU₁, hcb₁, hd₁⟩, hinj₁, -, -, -, hρ₁'⟩ := hF₁
  have hρ₁ : ∀ z ∈ sphere (0 : ℂ) 1, ‖deriv F₁ z‖ = ‖deriv B₁ z‖ := hρ₁'
  set H : ℂ → ℂ := fun w => a * F₁ w + b / c with hH
  have hHd : DifferentiableOn ℂ H U₁ := (hd₁.const_mul a).add_const _
  have hHinj : InjOn H (ball 0 1) := by
    intro w hw w' hw' h
    simp only [hH, add_left_inj] at h
    exact hinj₁ (ball_subset_closedBall hw) (ball_subset_closedBall hw')
      (mul_left_cancel₀ ha0 h)
  have hcH : ∀ w, c * H w = a * (c * F₁ w) + b := fun w => by
    simp only [hH]; field_simp
  have him : H '' ball 0 1 = F₂ '' ball 0 1 := by
    ext y; constructor
    · rintro ⟨w, hw, rfl⟩
      have : c * H w ∈ (fun w => c * F₂ w) '' ball 0 1 :=
        hJ ▸ ⟨c * F₁ w, ⟨w, hw, rfl⟩, (hcH w).symm⟩
      obtain ⟨w', hw', h⟩ := this
      exact ⟨w', hw', mul_left_cancel₀ hc h⟩
    · rintro ⟨w', hw', rfl⟩
      have : c * F₂ w' ∈ (fun z => a * z + b) '' ((fun w => c * F₁ w) '' ball 0 1) :=
        hJ ▸ ⟨w', hw', rfl⟩
      obtain ⟨_, ⟨v, hv, rfl⟩, h⟩ := this
      exact ⟨v, hv, mul_left_cancel₀ hc (by rw [hcH]; exact h)⟩
  obtain ⟨φ, hφ, hder⟩ := core hF₂ hU₁ hcb₁ hHd hHinj him
  refine ⟨φ, hφ, ?_⟩
  obtain ⟨-, -, -, -, -, hρ₂'⟩ := hF₂
  have hρ₂ : ∀ z ∈ sphere (0 : ℂ) 1, ‖deriv F₂ z‖ = ‖deriv B₂ z‖ := hρ₂'
  apply blaschke_boundary_rigidity hB₁ hB₂ hφ
  intro t
  set ζ := exp (t * I) with hζ
  have hζ1 : ‖ζ‖ = 1 := norm_exp_ofReal_mul_I t
  have hζs : ζ ∈ sphere (0 : ℂ) 1 := by simp [hζ1]
  have hφζs : φ ζ ∈ sphere (0 : ℂ) 1 := by simp [norm_diskAut_eq_one hφ hζ1]
  rw [norm_deriv_circ (hB₁.differentiableAt hζ1.le), ← hζ]
  have hcomp : DifferentiableAt ℂ (B₂ ∘ φ) ζ :=
    (hB₂.differentiableAt (norm_diskAut_eq_one hφ hζ1).le).comp ζ
      (diskAut_differentiableAt hφ hζ1.le)
  rw [show (fun s : ℝ => B₂ (φ (exp (s * I)))) = fun s : ℝ => (B₂ ∘ φ) (exp (s * I)) from rfl,
    norm_deriv_circ hcomp, norm_deriv_comp_aut hB₂ hφ hζ1, ← hρ₁ ζ hζs, ← hρ₂ (φ ζ) hφζs,
    ← hder ζ hζs]
  have hHder : deriv H ζ = a * deriv F₁ ζ := by
    simp only [hH]
    rw [deriv_add_const, deriv_const_mul _ (hd₁.differentiableAt (hU₁.mem_nhds (hcb₁ (by
      simp [hζ1]))))]
  rw [hHder, norm_mul, ha, one_mul]

/-- **Orientation-reversing congruence ⇒ anti-equivalence.** -/
theorem blaschke_of_congr_anti {B₁ B₂ F₁ F₂ : ℂ → ℂ} {n m : ℕ} (hB₁ : IsFiniteBlaschke B₁ n)
    (hB₂ : IsFiniteBlaschke B₂ m) (hF₁ : IsNormalizedRealizing F₁ (fun z => ‖deriv B₁ z‖))
    (hF₂ : IsNormalizedRealizing F₂ (fun z => ‖deriv B₂ z‖)) {c : ℂ} (hc : c ≠ 0)
    (hcr : (starRingEnd ℂ) c = c) {a b : ℂ} (ha : ‖a‖ = 1)
    (hJ : (fun z => a * (starRingEnd ℂ) z + b) '' ((fun w => c * F₁ w) '' ball 0 1) =
      (fun w => c * F₂ w) '' ball 0 1) :
    ∃ ψ, IsAntiDiskAut ψ ∧ ∃ η : ℂ, ‖η‖ = 1 ∧
      ∀ z : ℂ, ‖z‖ ≤ 1 → B₁ z = η * (starRingEnd ℂ) (B₂ (ψ z)) := by
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  obtain ⟨⟨U₁, hU₁, hcb₁, hd₁⟩, hinj₁, -, -, -, hρ₁'⟩ := hF₁
  have hρ₁ : ∀ z ∈ sphere (0 : ℂ) 1, ‖deriv F₁ z‖ = ‖deriv B₁ z‖ := hρ₁'
  set H : ℂ → ℂ := fun w => a * (starRingEnd ℂ) (F₁ ((starRingEnd ℂ) w)) + b / c with hH
  set U : Set ℂ := (starRingEnd ℂ) ⁻¹' U₁ with hUdef
  have hUo : IsOpen U := hU₁.preimage Complex.continuous_conj
  have hcbU : closedBall (0 : ℂ) 1 ⊆ U := fun z hz => hcb₁ (by simpa using hz)
  have hcd : ∀ w ∈ U, HasDerivAt (fun w => (starRingEnd ℂ) (F₁ ((starRingEnd ℂ) w)))
      ((starRingEnd ℂ) (deriv F₁ ((starRingEnd ℂ) w))) w := by
    intro w hw
    have := (hd₁.differentiableAt (hU₁.mem_nhds hw)).hasDerivAt.conj_conj
    rwa [Complex.conj_conj] at this
  have hHder : ∀ w ∈ U, HasDerivAt H (a * (starRingEnd ℂ) (deriv F₁ ((starRingEnd ℂ) w))) w :=
    fun w hw => ((hcd w hw).const_mul a).add_const _
  have hHd : DifferentiableOn ℂ H U :=
    fun w hw => (hHder w hw).differentiableAt.differentiableWithinAt
  have hconjb : ∀ w ∈ ball (0 : ℂ) 1, (starRingEnd ℂ) w ∈ ball (0 : ℂ) 1 := by
    intro w hw; simpa using hw
  have hHinj : InjOn H (ball 0 1) := by
    intro w hw w' hw' h
    simp only [hH, add_left_inj] at h
    have h1 := (starRingEnd ℂ).injective (mul_left_cancel₀ ha0 h)
    have h2 := hinj₁ (ball_subset_closedBall (hconjb w hw))
      (ball_subset_closedBall (hconjb w' hw')) h1
    exact (starRingEnd ℂ).injective h2
  have hcH : ∀ w, c * H w = a * (starRingEnd ℂ) (c * F₁ ((starRingEnd ℂ) w)) + b := fun w => by
    simp only [hH, map_mul, hcr]; field_simp
  have him : H '' ball 0 1 = F₂ '' ball 0 1 := by
    ext y; constructor
    · rintro ⟨w, hw, rfl⟩
      have : c * H w ∈ (fun w => c * F₂ w) '' ball 0 1 :=
        hJ ▸ ⟨c * F₁ ((starRingEnd ℂ) w), ⟨_, hconjb w hw, rfl⟩, (hcH w).symm⟩
      obtain ⟨w', hw', h⟩ := this
      exact ⟨w', hw', mul_left_cancel₀ hc h⟩
    · rintro ⟨w', hw', rfl⟩
      have : c * F₂ w' ∈
          (fun z => a * (starRingEnd ℂ) z + b) '' ((fun w => c * F₁ w) '' ball 0 1) :=
        hJ ▸ ⟨w', hw', rfl⟩
      obtain ⟨_, ⟨v, hv, rfl⟩, h⟩ := this
      refine ⟨(starRingEnd ℂ) v, hconjb v hv, mul_left_cancel₀ hc ?_⟩
      rw [hcH, Complex.conj_conj]; exact h
  obtain ⟨φ, hφ, hder⟩ := core hF₂ hUo hcbU hHd hHinj him
  refine ⟨fun z => φ ((starRingEnd ℂ) z), ⟨φ, hφ, rfl⟩, ?_⟩
  obtain ⟨-, -, -, -, -, hρ₂'⟩ := hF₂
  have hρ₂ : ∀ z ∈ sphere (0 : ℂ) 1, ‖deriv F₂ z‖ = ‖deriv B₂ z‖ := hρ₂'
  apply blaschke_boundary_rigidity_anti hB₁ hB₂ ⟨φ, hφ, rfl⟩
  intro t
  set ζ := exp (t * I) with hζ
  have hζ1 : ‖ζ‖ = 1 := norm_exp_ofReal_mul_I t
  have hζs : ζ ∈ sphere (0 : ℂ) 1 := by rw [mem_sphere_zero_iff_norm]; exact hζ1
  have hζc1 : ‖(starRingEnd ℂ) ζ‖ = 1 := by rw [Complex.norm_conj, hζ1]
  have hζcs : (starRingEnd ℂ) ζ ∈ sphere (0 : ℂ) 1 := by
    rw [mem_sphere_zero_iff_norm]; exact hζc1
  have hφζs : φ ((starRingEnd ℂ) ζ) ∈ sphere (0 : ℂ) 1 := by
    simp [norm_diskAut_eq_one hφ hζc1]
  rw [norm_deriv_circ (hB₁.differentiableAt hζ1.le), ← hζ]
  have hcomp : DifferentiableAt ℂ (B₂ ∘ φ) ((starRingEnd ℂ) ζ) :=
    (hB₂.differentiableAt (norm_diskAut_eq_one hφ hζc1).le).comp _
      (diskAut_differentiableAt hφ hζc1.le)
  rw [show (fun s : ℝ => B₂ ((fun z => φ ((starRingEnd ℂ) z)) (exp (s * I)))) =
      fun s : ℝ => (B₂ ∘ φ) ((starRingEnd ℂ) (exp (s * I))) from rfl,
    norm_deriv_circ_conj hcomp, norm_deriv_comp_aut hB₂ hφ hζc1, ← hρ₁ ζ hζs,
    ← hρ₂ _ hφζs, ← hder _ hζcs, (hHder _ (hcbU (mem_closedBall_zero_iff.2 hζc1.le))).deriv, norm_mul, ha, one_mul,
    Complex.norm_conj, Complex.conj_conj]

end CongrRigid

end
