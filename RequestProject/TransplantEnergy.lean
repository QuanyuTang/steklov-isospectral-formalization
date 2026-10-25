module

public import RequestProject.Transplant

/-!
# Transplantation preserves the Dirichlet energy

Let `B₁, B₂` be holomorphic self-maps of `𝔻` and `K` a kernel on the fibre product which is
fibrewise orthogonal over the base `𝔻 \ C` (`C` countable) and locally constant along the local
branches of `B₁⁻¹ ∘ B₂`.  Then the transplantation `T u` has the same Dirichlet energy on `𝔻`
as `u` (`dirichletEnergy_transplant`).  The proof computes both energies on the base with the
area formula with multiplicity and compares the fibre sums pointwise: on a regular fibre,
`|∇(T u)|²/|B₂'|²` summed over the `B₂`-fibre equals `|∇u|²/|B₁'|²` summed over the `B₁`-fibre,
by orthogonality of `K`.
-/

@[expose] public section

open Complex Metric Set MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace SteklovTransplant

open SteklovBlaschke Steklov SteklovArea ConformalPullback

lemma comp_mulR_mul (L : ℂ →L[ℝ] ℝ) (a b : ℂ) :
    L.comp (mulR (a * b)) = (L.comp (mulR a)).comp (mulR b) := by
  ext z
  simp only [ContinuousLinearMap.comp_apply, mulR_apply]
  ring_nf

/-- Near a regular point the transplantation is a fixed linear combination of `u` composed with
local branches. -/
lemma transplant_eventuallyEq {W₁ : Set ℂ} {B₁ B₂ : ℂ → ℂ} {K : ℂ → ℂ → ℝ} {z' : ℂ}
    {P : Set ℂ} (hP : P.Finite) {σ : ℂ → ℂ → ℂ}
    (hev : ∀ᶠ z'' in 𝓝 z', {p | p ∈ W₁ ∧ B₁ p = B₂ z''} = (fun p => σ p (B₂ z'')) '' P ∧
      InjOn (fun p => σ p (B₂ z'')) P ∧ ∀ p ∈ P, K z'' (σ p (B₂ z'')) = K z' p)
    (u : ℂ → ℝ) :
    ∀ᶠ z'' in 𝓝 z', transplant W₁ B₁ B₂ K u z'' =
      ∑ p ∈ hP.toFinset, K z' p * u (σ p (B₂ z'')) := by
  filter_upwards [hev] with z'' ⟨hset, hinj, hK⟩
  unfold transplant
  rw [hset, finsum_mem_image hinj, finsum_mem_eq_finite_toFinset_sum _ hP]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [hK p ((Set.Finite.mem_toFinset hP).1 hp)]

/-- The derivative of the local expression. -/
lemma hasFDerivAt_local_sum {B₁ B₂ : ℂ → ℂ} {z' : ℂ} (Pf : Finset ℂ) (k : ℂ → ℝ)
    {σ : ℂ → ℂ → ℂ}
    (hσ : ∀ p ∈ Pf, σ p (B₂ z') = p ∧ HasDerivAt (σ p) (deriv B₁ p)⁻¹ (B₂ z'))
    (hB₂ : HasDerivAt B₂ (deriv B₂ z') z') {u : ℂ → ℝ} (hu : Differentiable ℝ u) :
    HasFDerivAt (fun z'' => ∑ p ∈ Pf, k p * u (σ p (B₂ z'')))
      ((∑ p ∈ Pf, k p • (fderiv ℝ u p).comp (mulR (deriv B₁ p)⁻¹)).comp
        (mulR (deriv B₂ z'))) z' := by
  rw [ContinuousLinearMap.finset_sum_comp]
  refine HasFDerivAt.fun_sum fun p hp => ?_
  obtain ⟨h1, h2⟩ := hσ p hp
  have hc : HasDerivAt (fun z'' => σ p (B₂ z'')) ((deriv B₁ p)⁻¹ * deriv B₂ z') z' :=
    h2.comp z' hB₂
  have hcf : HasFDerivAt (fun z'' => σ p (B₂ z'')) (mulR ((deriv B₁ p)⁻¹ * deriv B₂ z')) z' :=
    hc.hasFDerivAt.restrictScalars ℝ
  have hup : HasFDerivAt u (fderiv ℝ u (σ p (B₂ z'))) (σ p (B₂ z')) :=
    (hu _).hasFDerivAt
  have := (hup.comp z' hcf).const_mul (k p)
  rw [h1, comp_mulR_mul] at this
  convert this using 1

/-- The Dirichlet energy on `𝔻` computed on the base of a holomorphic map. -/
lemma dirichletEnergy_eq_lintegral_fibreSum {B : ℂ → ℂ} (hB : DifferentiableOn ℂ B (ball 0 1))
    (hcrit : {z ∈ ball (0:ℂ) 1 | deriv B z = 0}.Countable) (f : ℂ → ℝ) :
    dirichletEnergy (ball 0 1) f =
      ∫⁻ w, fibreSum B (ball 0 1) (fun z => ‖fderiv ℝ f z‖ₑ ^ 2 / ‖deriv B z‖ₑ ^ 2) w := by
  have hm : Measurable fun z => ‖fderiv ℝ f z‖ₑ ^ 2 / ‖deriv B z‖ₑ ^ 2 :=
    ((measurable_fderiv ℝ f).enorm.pow_const 2).div ((measurable_deriv B).enorm.pow_const 2)
  rw [← lintegral_deriv_sq_mul_eq_fibreSum isOpen_ball hB measurableSet_ball subset_rfl hcrit _ hm]
  unfold dirichletEnergy
  refine setLIntegral_congr_fun_ae measurableSet_ball ?_
  filter_upwards [hcrit.ae_notMem volume] with z hz hzb
  have h0 : deriv B z ≠ 0 := fun h => hz ⟨hzb, h⟩
  rw [ENNReal.mul_div_cancel (by simpa using h0) (by simp)]

/-- Critical points of `B` in `𝔻` are countable when they lie over a countable set and the
fibres are finite. -/
lemma countable_crit {B : ℂ → ℂ} {C : Set ℂ} (hC : C.Countable)
    (hfin : ∀ w, {z : ℂ | ‖z‖ < 1 ∧ B z = w}.Finite)
    (hcrit : ∀ z, ‖z‖ < 1 → B z ∉ C → deriv B z ≠ 0) :
    {z ∈ ball (0:ℂ) 1 | deriv B z = 0}.Countable := by
  refine (hC.biUnion fun c _ => (hfin c).countable).mono fun z ⟨hz, hd⟩ => ?_
  rw [mem_ball_zero_iff] at hz
  by_contra hn
  have hBC : B z ∉ C := fun h => hn (mem_biUnion h ⟨hz, rfl⟩)
  exact hcrit z hz hBC hd

lemma fibreSum_ball_eq_sum {B : ℂ → ℂ} {w : ℂ} (hA : {z : ℂ | ‖z‖ < 1 ∧ B z = w}.Finite)
    (F : ℂ → ℝ≥0∞) : fibreSum B (ball 0 1) F w = ∑ z ∈ hA.toFinset, F z := by
  unfold fibreSum
  have hs : {z : ℂ | z ∈ ball (0:ℂ) 1 ∧ B z = w} = {z : ℂ | ‖z‖ < 1 ∧ B z = w} := by
    ext z; simp
  change ∑' z : ({z : ℂ | z ∈ ball (0:ℂ) 1 ∧ B z = w} : Set ℂ), F z = _
  rw [hs]
  conv_lhs => rw [← hA.coe_toFinset]
  exact Finset.tsum_subtype' hA.toFinset F

lemma fibreSum_ball_eq_zero {B : ℂ → ℂ} {w : ℂ} (hmaps : ∀ z, ‖z‖ < 1 → ‖B z‖ < 1)
    (hw : 1 ≤ ‖w‖) (F : ℂ → ℝ≥0∞) : fibreSum B (ball 0 1) F w = 0 := by
  unfold fibreSum
  haveI : IsEmpty {z // z ∈ ball (0:ℂ) 1 ∧ B z = w} := ⟨fun ⟨z, hz, hBz⟩ => by
    rw [mem_ball_zero_iff] at hz
    have := hmaps z hz; rw [hBz] at this; linarith⟩
  simp

lemma enorm_sq_div_enorm_sq {E : Type*} [SeminormedAddCommGroup E] (L : E) {b : ℂ} {X : ℝ}
    (hb : b ≠ 0) (hX : 0 ≤ X) (hL : ‖L‖ = X * ‖b‖) :
    ‖L‖ₑ ^ 2 / ‖b‖ₑ ^ 2 = ENNReal.ofReal (X ^ 2) := by
  have hbpos : 0 < ‖b‖ := norm_pos_iff.2 hb
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, hL,
    ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (norm_nonneg _),
    ← ENNReal.ofReal_div_of_pos (by positivity)]
  congr 1
  field_simp

/-- **Transplantation preserves the Dirichlet energy.**  Let `B₁, B₂` be holomorphic self-maps
of `𝔻` with finite fibres, `C` a countable set of base points containing all critical values
in `𝔻`, and `K` a kernel which is fibrewise orthogonal over `𝔻 \ C` and, near each regular
point `z'`, constant along local holomorphic branches `σ_p` of `B₁⁻¹` (with `σ_p(B₂ z') = p`)
that parametrize the fibres.  Then `∫_𝔻 |∇(T u)|² = ∫_𝔻 |∇u|²` for every differentiable `u`. -/
theorem dirichletEnergy_transplant {B₁ B₂ : ℂ → ℂ}
    (hB₁ : DifferentiableOn ℂ B₁ (ball 0 1)) (hB₂ : DifferentiableOn ℂ B₂ (ball 0 1))
    (hmaps₁ : ∀ z, ‖z‖ < 1 → ‖B₁ z‖ < 1) (hmaps₂ : ∀ z, ‖z‖ < 1 → ‖B₂ z‖ < 1)
    {W₁ : Set ℂ} (K : ℂ → ℂ → ℝ) {C : Set ℂ} (hC : C.Countable)
    (hfin₁ : ∀ w, {p : ℂ | ‖p‖ < 1 ∧ B₁ p = w}.Finite)
    (hfin₂ : ∀ w, {z : ℂ | ‖z‖ < 1 ∧ B₂ z = w}.Finite)
    (hcrit₁ : ∀ p, ‖p‖ < 1 → B₁ p ∉ C → deriv B₁ p ≠ 0)
    (hcrit₂ : ∀ z, ‖z‖ < 1 → B₂ z ∉ C → deriv B₂ z ≠ 0)
    (horth : ∀ w, ‖w‖ < 1 → w ∉ C → ∀ p p', ‖p‖ < 1 → B₁ p = w → ‖p'‖ < 1 → B₁ p' = w →
      ∑ᶠ z' ∈ {z' : ℂ | ‖z'‖ < 1 ∧ B₂ z' = w}, K z' p * K z' p' = if p = p' then 1 else 0)
    (hloc : ∀ z', ‖z'‖ < 1 → B₂ z' ∉ C → ∃ σ : ℂ → ℂ → ℂ,
      (∀ p ∈ {p : ℂ | ‖p‖ < 1 ∧ B₁ p = B₂ z'},
        σ p (B₂ z') = p ∧ HasDerivAt (σ p) (deriv B₁ p)⁻¹ (B₂ z')) ∧
      ∀ᶠ z'' in 𝓝 z', {p | p ∈ W₁ ∧ B₁ p = B₂ z''} =
          (fun p => σ p (B₂ z'')) '' {p : ℂ | ‖p‖ < 1 ∧ B₁ p = B₂ z'} ∧
        InjOn (fun p => σ p (B₂ z'')) {p : ℂ | ‖p‖ < 1 ∧ B₁ p = B₂ z'} ∧
        ∀ p ∈ {p : ℂ | ‖p‖ < 1 ∧ B₁ p = B₂ z'}, K z'' (σ p (B₂ z'')) = K z' p)
    (u : ℂ → ℝ) (hu : Differentiable ℝ u) :
    dirichletEnergy (ball 0 1) (transplant W₁ B₁ B₂ K u) = dirichletEnergy (ball 0 1) u := by
  classical
  rw [dirichletEnergy_eq_lintegral_fibreSum hB₂ (countable_crit hC hfin₂ hcrit₂),
    dirichletEnergy_eq_lintegral_fibreSum hB₁ (countable_crit hC hfin₁ hcrit₁)]
  refine lintegral_congr_ae ?_
  filter_upwards [hC.ae_notMem volume] with w hwC
  rcases le_or_gt 1 ‖w‖ with hw | hw
  · rw [fibreSum_ball_eq_zero hmaps₂ hw, fibreSum_ball_eq_zero hmaps₁ hw]
  set P := {p : ℂ | ‖p‖ < 1 ∧ B₁ p = w} with hPdef
  set A := {z : ℂ | ‖z‖ < 1 ∧ B₂ z = w} with hAdef
  have hP := hfin₁ w
  have hA := hfin₂ w
  set v : ℂ → (ℂ →L[ℝ] ℝ) := fun p => (fderiv ℝ u p).comp (mulR (deriv B₁ p)⁻¹) with hv
  rw [fibreSum_ball_eq_sum hA, fibreSum_ball_eq_sum hP]
  -- the `B₂` side
  have h2 : ∀ z' ∈ hA.toFinset, ‖fderiv ℝ (transplant W₁ B₁ B₂ K u) z'‖ₑ ^ 2 /
      ‖deriv B₂ z'‖ₑ ^ 2 = ENNReal.ofReal (‖∑ p ∈ hP.toFinset, K z' p • v p‖ ^ 2) := by
    intro z' hz'
    rw [Set.Finite.mem_toFinset] at hz'
    obtain ⟨hz'1, hz'w⟩ := hz'
    have hwC' : B₂ z' ∉ C := by rw [hz'w]; exact hwC
    obtain ⟨σ, hσ, hev⟩ := hloc z' hz'1 hwC'
    rw [hz'w] at hσ hev
    have hB₂d : HasDerivAt B₂ (deriv B₂ z') z' :=
      (hB₂.differentiableAt (isOpen_ball.mem_nhds (by simpa using hz'1))).hasDerivAt
    have hσ' : ∀ p ∈ hP.toFinset, σ p (B₂ z') = p ∧ HasDerivAt (σ p) (deriv B₁ p)⁻¹ (B₂ z') := by
      intro p hp
      rw [hz'w]
      exact hσ p ((Set.Finite.mem_toFinset hP).1 hp)
    have hev' : ∀ᶠ z'' in 𝓝 z', {p | p ∈ W₁ ∧ B₁ p = B₂ z''} =
        (fun p => σ p (B₂ z'')) '' P ∧ InjOn (fun p => σ p (B₂ z'')) P ∧
        ∀ p ∈ P, K z'' (σ p (B₂ z'')) = K z' p := hev
    have heq := transplant_eventuallyEq hP hev' u
    have hd := hasFDerivAt_local_sum hP.toFinset (K z') hσ' hB₂d hu
    rw [Filter.EventuallyEq.fderiv_eq heq, hd.fderiv]
    refine enorm_sq_div_enorm_sq _ (hcrit₂ z' hz'1 hwC') (norm_nonneg _) ?_
    exact norm_comp_mulR _ _
  -- the `B₁` side
  have h1 : ∀ p ∈ hP.toFinset, ‖fderiv ℝ u p‖ₑ ^ 2 / ‖deriv B₁ p‖ₑ ^ 2 =
      ENNReal.ofReal (‖v p‖ ^ 2) := by
    intro p hp
    rw [Set.Finite.mem_toFinset] at hp
    have hd : deriv B₁ p ≠ 0 := hcrit₁ p hp.1 (by rw [hp.2]; exact hwC)
    refine enorm_sq_div_enorm_sq _ hd (norm_nonneg _) ?_
    have hdpos : 0 < ‖deriv B₁ p‖ := norm_pos_iff.2 hd
    rw [hv]; simp only
    rw [norm_comp_mulR, norm_inv]
    field_simp
  rw [Finset.sum_congr rfl h2, Finset.sum_congr rfl h1,
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _),
    ← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
  congr 1
  refine sum_norm_sq_orth _ _ K (fun p hp p' hp' => ?_) v
  rw [Set.Finite.mem_toFinset] at hp hp'
  rw [← horth w hw hwC p p' hp.1 hp.2 hp'.1 hp'.2, finsum_mem_eq_finite_toFinset_sum _ hA]

end SteklovTransplant

end
