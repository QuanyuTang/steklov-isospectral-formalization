module

public import RequestProject.PaperStatements

/-!
# Dilation law for the Steklov spectrum (used in §3.5)

We prove `SteklovDilation`: for every set `Ω ⊆ ℂ`, every `c > 0` and every `k`,
`σ_k(cΩ) = σ_k(Ω)/c`.  This is the step "a common dilation multiplies every Steklov eigenvalue
in both spectra by the same reciprocal factor" in the normalization `Ω̂ = Ω/n` of §3.5.  The proof
works directly with the variational definition: `u ↦ u(·/c)` is a linear bijection of test
functions, the Dirichlet energy is dilation invariant in dimension two, and the boundary mass
(one-dimensional Hausdorff measure) is multiplied by `c`.
-/

@[expose] public section

open MeasureTheory Set Steklov
open scoped ENNReal Pointwise ContDiff

noncomputable section

namespace SteklovDilationProof

variable {c : ℝ}

/-- Change of variables for a measure that scales by `κ` under `z ↦ c z`. -/
lemma lintegral_image_smul (hc : c ≠ 0) (μ : Measure ℂ) (κ : ℝ≥0∞) (hκ0 : κ ≠ 0)
    (hκt : κ ≠ ⊤) (hmap : μ.map (fun z : ℂ => c • z) = κ⁻¹ • μ) (A : Set ℂ) (g : ℂ → ℝ≥0∞) :
    ∫⁻ z in (fun z : ℂ => c • z) '' A, g z ∂μ = κ * ∫⁻ w in A, g (c • w) ∂μ := by
  let e : ℂ ≃ᵐ ℂ := MeasurableEquiv.smul₀ c hc
  have he : (e : ℂ → ℂ) = fun z => c • z := rfl
  have hμ : μ = κ • μ.map e := by
    rw [he, hmap, smul_smul, ENNReal.mul_inv_cancel hκ0 hκt, one_smul]
  conv_lhs => rw [hμ]
  rw [Measure.restrict_smul, lintegral_smul_measure, ← he, e.restrict_map,
    lintegral_map_equiv, e.preimage_image]
  rfl

lemma map_smul_volume (hc : 0 < c) :
    (volume : Measure ℂ).map (fun z : ℂ => c • z) = (ENNReal.ofReal (c ^ 2))⁻¹ • volume := by
  rw [Measure.map_addHaar_smul volume hc.ne', Complex.finrank_real_complex,
    abs_of_pos (by positivity), ENNReal.ofReal_inv_of_pos (by positivity)]

lemma map_smul_hausdorff (hc : 0 < c) :
    (Measure.hausdorffMeasure 1 : Measure ℂ).map (fun z : ℂ => c • z) =
      (ENNReal.ofReal c)⁻¹ • Measure.hausdorffMeasure 1 := by
  ext s hs
  rw [Measure.map_apply (measurable_const_smul c) hs, Measure.smul_apply]
  have hpre : (fun z : ℂ => c • z) ⁻¹' s = c⁻¹ • s := by
    rw [← Set.image_smul, Set.image_eq_preimage_of_inverse]
    · intro z; simp [hc.ne']
    · intro z; simp [hc.ne']
  rw [hpre, Measure.hausdorffMeasure_smul₀ zero_le_one (inv_ne_zero hc.ne')]
  have hn : (‖c⁻¹‖₊ : ℝ≥0∞) = (ENNReal.ofReal c)⁻¹ := by
    rw [← ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_eq_coe_nnreal (inv_pos.2 hc).le]
    congr 1
    ext
    simp [abs_of_pos hc]
  simp only [NNReal.rpow_one]
  rw [ENNReal.smul_def, smul_eq_mul, hn, smul_eq_mul]

/-- The continuous linear equivalence `z ↦ c⁻¹ z`. -/
def invScale (hc : 0 < c) : ℂ ≃L[ℝ] ℂ :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 c⁻¹ (inv_ne_zero hc.ne'))

lemma invScale_apply (hc : 0 < c) (z : ℂ) : invScale hc z = c⁻¹ • z := rfl

lemma enorm_fderiv_comp_invScale (hc : 0 < c) (u : ℂ → ℝ) (z : ℂ) :
    ‖fderiv ℝ (fun w => u (c⁻¹ • w)) z‖ₑ = ENNReal.ofReal c⁻¹ * ‖fderiv ℝ u (c⁻¹ • z)‖ₑ := by
  have h := (invScale hc).comp_right_fderiv (f := u) (x := z)
  have hfun : (u ∘ invScale hc) = fun w => u (c⁻¹ • w) := rfl
  rw [hfun, invScale_apply] at h
  rw [h]
  have : (fderiv ℝ u (c⁻¹ • z)).comp (invScale hc : ℂ →L[ℝ] ℂ) =
      c⁻¹ • fderiv ℝ u (c⁻¹ • z) := by
    ext w
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, invScale_apply,
      map_smul, ContinuousLinearMap.smul_apply]
  rw [this, enorm_smul, ← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hc)]

lemma dirichletEnergy_scale (hc : 0 < c) (Ω : Set ℂ) (u : ℂ → ℝ) :
    dirichletEnergy ((fun z : ℂ => c • z) '' Ω) (fun w => u (c⁻¹ • w)) = dirichletEnergy Ω u := by
  unfold dirichletEnergy
  simp_rw [enorm_fderiv_comp_invScale hc]
  rw [lintegral_image_smul hc.ne' volume (ENNReal.ofReal (c ^ 2))
    (by simp [ENNReal.ofReal_eq_zero]; positivity) ENNReal.ofReal_ne_top
    (map_smul_volume hc)]
  simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, mul_pow]
  rw [lintegral_const_mul' _ _ (by simp), ← mul_assoc, ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← mul_pow, mul_inv_cancel₀ hc.ne', one_pow,
    ENNReal.ofReal_one, one_mul]

lemma boundaryMass_scale (hc : 0 < c) (Ω : Set ℂ) (u : ℂ → ℝ) :
    boundaryMass ((fun z : ℂ => c • z) '' Ω) (fun w => u (c⁻¹ • w)) =
      ENNReal.ofReal c * boundaryMass Ω u := by
  unfold boundaryMass
  have hfr : frontier ((fun z : ℂ => c • z) '' Ω) = (fun z : ℂ => c • z) '' frontier Ω :=
    ((Homeomorph.smulOfNeZero c hc.ne').image_frontier Ω).symm
  rw [hfr, lintegral_image_smul hc.ne' _ (ENNReal.ofReal c)
    (by simp [ENNReal.ofReal_eq_zero, not_le, hc]) ENNReal.ofReal_ne_top (map_smul_hausdorff hc)]
  simp only [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- The test-function transformation `u ↦ u(·/c)`. -/
def Φ (hc : 0 < c) : (ℂ → ℝ) ≃ₗ[ℝ] (ℂ → ℝ) :=
  LinearEquiv.funCongrLeft ℝ ℝ (Homeomorph.smulOfNeZero c⁻¹ (inv_ne_zero hc.ne')).toEquiv

lemma Φ_apply (hc : 0 < c) (u : ℂ → ℝ) : Φ hc u = fun w => u (c⁻¹ • w) := rfl

lemma contDiff_Φ_iff (hc : 0 < c) (u : ℂ → ℝ) : ContDiff ℝ ∞ (Φ hc u) ↔ ContDiff ℝ ∞ u := by
  constructor
  · intro h
    have : u = fun w => Φ hc u (c • w) := by
      ext w; simp only [Φ_apply, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
    rw [this]
    exact h.comp (contDiff_const_smul c)
  · intro h
    exact h.comp (contDiff_const_smul c⁻¹)

lemma ennreal_div_mul (a b κ : ℝ≥0∞) (h0 : κ ≠ 0) (ht : κ ≠ ⊤) :
    a / (κ * b) = a / b / κ := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl h0) (Or.inl ht)]
  ring

/-- **Dilation law.** `σ_k(cΩ) = σ_k(Ω)/c` for every `Ω ⊆ ℂ`, `c > 0`, `k`. -/
theorem steklovDilation : SteklovDilation := by
  intro Ω c hc k
  have hsm : (fun z : ℂ => (c : ℂ) * z) = fun z : ℂ => c • z := by
    ext z; simp [Complex.real_smul]
  rw [hsm]
  set Ω' := (fun z : ℂ => c • z) '' Ω
  set κ := ENNReal.ofReal c with hκ
  have hκ0 : κ ≠ 0 := by simp [κ, ENNReal.ofReal_eq_zero, not_le, hc]
  have hκt : κ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hE : ∀ u, dirichletEnergy Ω' (Φ hc u) = dirichletEnergy Ω u :=
    fun u => dirichletEnergy_scale hc Ω u
  have hB : ∀ u, boundaryMass Ω' (Φ hc u) = κ * boundaryMass Ω u :=
    fun u => boundaryMass_scale hc Ω u
  -- admissible spaces correspond
  have hadm : ∀ V : Submodule ℝ (ℂ → ℝ),
      AdmissibleSpace (boundaryMass Ω') k (V.map (Φ hc : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ))) ↔
        AdmissibleSpace (boundaryMass Ω) k V := by
    intro V
    simp only [AdmissibleSpace, Submodule.mem_map_equiv, LinearEquiv.finrank_map_eq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun u hu => ?_, h2, fun u hu hu0 => ?_⟩
      · have := h1 (Φ hc u) (by simpa using hu)
        exact (contDiff_Φ_iff hc u).1 this
      · have := h3 (Φ hc u) (by simpa using hu) (by simpa using hu0)
        rw [hB] at this
        exact fun h => this (by rw [h, mul_zero])
    · rintro ⟨h1, h2, h3⟩
      refine ⟨fun v hv => ?_, h2, fun v hv hv0 => ?_⟩
      · have := (contDiff_Φ_iff hc ((Φ hc).symm v)).2 (h1 _ hv)
        simpa using this
      · have h' := h3 _ hv (by simpa using hv0)
        have : v = Φ hc ((Φ hc).symm v) := by simp
        rw [this, hB]
        exact mul_ne_zero hκ0 h'
  -- the sup over a transformed space
  have hsup : ∀ V : Submodule ℝ (ℂ → ℝ),
      (⨆ (v : ℂ → ℝ) (_ : v ∈ V.map (Φ hc : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ))) (_ : v ≠ 0),
        dirichletEnergy Ω' v / boundaryMass Ω' v) =
      (⨆ (u : ℂ → ℝ) (_ : u ∈ V) (_ : u ≠ 0),
        dirichletEnergy Ω u / boundaryMass Ω u) / κ := by
    intro V
    rw [← (Φ hc).toEquiv.iSup_comp]
    simp only [LinearEquiv.coe_toEquiv, Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
      ne_eq, LinearEquiv.map_eq_zero_iff, hE, hB]
    simp only [ENNReal.iSup_div]
    simp_rw [ennreal_div_mul _ _ _ hκ0 hκt]
  unfold steklovEigenvalue minMax
  rw [← (Submodule.orderIsoMapComap (Φ hc)).toEquiv.iInf_comp]
  simp only [RelIso.coe_fn_toEquiv, Submodule.orderIsoMapComap_apply, hadm, hsup]
  rw [div_eq_mul_inv, ENNReal.iInf_mul_of_ne (ENNReal.inv_ne_zero.2 hκt)
    (ENNReal.inv_ne_top.2 hκ0)]
  congr 1
  ext V
  rw [ENNReal.iInf_mul_of_ne (ENNReal.inv_ne_zero.2 hκt) (ENNReal.inv_ne_top.2 hκ0)]
  simp only [div_eq_mul_inv]

end SteklovDilationProof

end
