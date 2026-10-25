module

public import RequestProject.ApproxMinMax
public import RequestProject.C1Mollify

/-!
# Min–max transfer along compositions with `C¹` maps

`SteklovC1.minMax_le_of_C1_comp`: let `Φ : ℂ → ℂ` be `C¹` with compact support, `Ω₂` a set of
finite area and `ν` a finite measure.  If the functionals `E₁, B₁` are given on smooth `u` by
`E₁(u) = ∫_{Ω₂} |∇(u ∘ Φ)|²` and `B₁(u) = ∫ |u ∘ Φ|² dν`, then the min–max values of the
"pulled-back" problem `(∫_{Ω₂} |∇w|², ∫ |w|² dν)` (with smooth test functions `w`) are at most
those of `(E₁, B₁)`.  The functions `u ∘ Φ` are only `C¹`; the proof replaces `Φ` by smooth
mollified maps `Ψ` and controls the error uniformly on each finite-dimensional test space.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric Steklov
open scoped ENNReal ContDiff

noncomputable section

namespace SteklovC1

lemma enorm_sq_eq_ofReal' {F : Type*} [NormedAddCommGroup F] (y : F) :
    ‖y‖ₑ ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- Pointwise `(q + c)² ≤ (1+η) q² + (1 + 1/η) c²`. -/
lemma sq_le_of_le_add {p q c η : ℝ} (hp : 0 ≤ p) (hη : 0 < η)
    (h : p ≤ q + c) : p ^ 2 ≤ (1 + η) * q ^ 2 + (1 + 1 / η) * c ^ 2 := by
  have h1 : p ^ 2 ≤ (q + c) ^ 2 := pow_le_pow_left₀ hp h 2
  have h2 : 2 * q * c ≤ η * q ^ 2 + c ^ 2 / η := by
    have : 0 ≤ (η * q - c) ^ 2 / η := by positivity
    have e : (η * q - c) ^ 2 / η = η * q ^ 2 - 2 * q * c + c ^ 2 / η := by
      field_simp; ring
    linarith
  have e2 : (1 + 1 / η) * c ^ 2 = c ^ 2 + c ^ 2 / η := by field_simp
  nlinarith

/-- **Integrated form.**  If `‖P x‖ ≤ ‖Q x‖ + c` everywhere, then
`∫ ‖P‖² ≤ (1+η) ∫ ‖Q‖² + (1 + 1/η) c² μ(univ)`. -/
lemma lintegral_sq_le {F G : Type*} [NormedAddCommGroup F] [NormedAddCommGroup G]
    {μ : Measure ℂ} {P : ℂ → F} {Q : ℂ → G} {c η : ℝ} (hη : 0 < η) (h : ∀ x, ‖P x‖ ≤ ‖Q x‖ + c) :
    ∫⁻ x, ‖P x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (1 + η) * ∫⁻ x, ‖Q x‖ₑ ^ 2 ∂μ +
      ENNReal.ofReal ((1 + 1 / η) * c ^ 2) * μ univ := by
  calc ∫⁻ x, ‖P x‖ₑ ^ 2 ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (1 + η) * ‖Q x‖ₑ ^ 2 + ENNReal.ofReal ((1 + 1 / η) * c ^ 2)) ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [enorm_sq_eq_ofReal', enorm_sq_eq_ofReal', ← ENNReal.ofReal_mul (by linarith),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        exact ENNReal.ofReal_le_ofReal
          (sq_le_of_le_add (norm_nonneg _) hη (h x))
    _ = ENNReal.ofReal (1 + η) * ∫⁻ x, ‖Q x‖ₑ ^ 2 ∂μ +
          ENNReal.ofReal ((1 + 1 / η) * c ^ 2) * μ univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const]

/-- `eLpNorm g 2 μ ^ 2 = ∫ ‖g‖²`. -/
lemma eLpNorm_two_sq {F : Type*} [NormedAddCommGroup F] {μ : Measure ℂ} (g : ℂ → F) :
    eLpNorm g 2 μ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  simp only [ENNReal.toReal_ofNat]
  norm_num


lemma Lp_coeFn_sum {ι : Type*} {μ : Measure ℂ} (h : ι → Lp ℝ 2 μ) (s : Finset ι) :
    ((∑ i ∈ s, h i : Lp ℝ 2 μ) : ℂ → ℝ) =ᵐ[μ] ∑ i ∈ s, (h i : ℂ → ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Lp.coeFn_zero ℝ 2 μ
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (h j) (∑ i ∈ s, h i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Pi.add_apply]

/-- An injective linear map on `ℝ^m` is bounded below. -/
lemma exists_lower_of_injective {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}
    (L : (Fin m → ℝ) →ₗ[ℝ] X) (hinj : Function.Injective L) :
    ∃ c > 0, ∀ a, c * ‖a‖ ≤ ‖L a‖ := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨1, one_pos, fun a => ?_⟩
    rw [Subsingleton.elim a 0, norm_zero, mul_zero]; exact norm_nonneg _
  have hLc : Continuous L := L.continuous_of_finiteDimensional
  have hne : (sphere (0 : Fin m → ℝ) 1).Nonempty := by
    refine ⟨Pi.single ⟨0, hm⟩ 1, ?_⟩
    rw [mem_sphere_zero_iff_norm, Pi.norm_single, norm_one]
  obtain ⟨a₀, ha₀, hmin⟩ := (isCompact_sphere (0 : Fin m → ℝ) 1).exists_isMinOn hne
    (hLc.norm.continuousOn)
  have ha₀0 : a₀ ≠ 0 := by
    rintro rfl; rw [mem_sphere_zero_iff_norm, norm_zero] at ha₀; exact zero_ne_one ha₀
  have hc : 0 < ‖L a₀‖ := norm_pos_iff.2 fun h => ha₀0 (hinj (by rw [h, map_zero]))
  refine ⟨‖L a₀‖, hc, fun a => ?_⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  have hna : 0 < ‖a‖ := norm_pos_iff.2 ha
  have hmem : ‖a‖⁻¹ • a ∈ sphere (0 : Fin m → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hna.ne']
  have h1 : ‖L a₀‖ ≤ ‖L (‖a‖⁻¹ • a)‖ := hmin hmem
  rw [map_smul, norm_smul, norm_inv, norm_norm] at h1
  rw [mul_comm]
  calc ‖a‖ * ‖L a₀‖ ≤ ‖a‖ * (‖a‖⁻¹ * ‖L a‖) := by gcongr
    _ = ‖L a‖ := by field_simp

/-- **Coefficient bound on a finite-dimensional test space.**  If bounded continuous functions
`f₁, …, f_m` are linearly independent in `L²(ν)` (no nontrivial combination has zero mass), then
the `L²(ν)`-mass of `∑ aᵢ fᵢ` controls `‖a‖²` from below. -/
lemma exists_coeff_lower_bound {ν : Measure ℂ} [IsFiniteMeasure ν] {m : ℕ} (f : Fin m → ℂ → ℝ)
    (hf : ∀ i, Continuous (f i)) (hb : ∀ i, ∃ C, ∀ x, |f i x| ≤ C)
    (hpos : ∀ a : Fin m → ℝ, a ≠ 0 → ∫⁻ x, ‖∑ i, a i * f i x‖ₑ ^ 2 ∂ν ≠ 0) :
    ∃ m₀ > 0, ∀ a : Fin m → ℝ,
      ENNReal.ofReal (m₀ * ‖a‖ ^ 2) ≤ ∫⁻ x, ‖∑ i, a i * f i x‖ₑ ^ 2 ∂ν := by
  have hmem : ∀ i, MemLp (f i) 2 ν := fun i =>
    MemLp.of_bound (hf i).aestronglyMeasurable (hb i).choose
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (hb i).choose_spec x)
  set g : Fin m → Lp ℝ 2 ν := fun i => (hmem i).toLp (f i)
  set L : (Fin m → ℝ) →ₗ[ℝ] Lp ℝ 2 ν := Fintype.linearCombination ℝ g
  have hLae : ∀ a, (L a : ℂ → ℝ) =ᵐ[ν] fun x => ∑ i, a i * f i x := by
    intro a
    simp only [L, Fintype.linearCombination_apply]
    have h1 := Lp_coeFn_sum (fun i => a i • g i) Finset.univ (μ := ν)
    have h2 : ∀ i, (((a i • g i : Lp ℝ 2 ν)) : ℂ → ℝ) =ᵐ[ν] fun x => a i * f i x := fun i => by
      filter_upwards [Lp.coeFn_smul (a i) (g i), (hmem i).coeFn_toLp] with x hx hx'
      rw [hx, Pi.smul_apply, hx', smul_eq_mul]
    have h3 : ∀ᵐ x ∂ν, ∀ i, (((a i • g i : Lp ℝ 2 ν)) : ℂ → ℝ) x = a i * f i x :=
      ae_all_iff.2 h2
    filter_upwards [h1, h3] with x hx hx3
    rw [hx, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => hx3 i
  have hnorm : ∀ a, ENNReal.ofReal (‖L a‖ ^ 2) = ∫⁻ x, ‖∑ i, a i * f i x‖ₑ ^ 2 ∂ν := by
    intro a
    rw [Lp.norm_def, eLpNorm_congr_ae (hLae a), ← ENNReal.toReal_pow, eLpNorm_two_sq,
      ENNReal.ofReal_toReal]
    rw [← eLpNorm_two_sq]
    exact ENNReal.pow_ne_top (eLpNorm_congr_ae (hLae a) ▸ (Lp.memLp (L a)).eLpNorm_ne_top)
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    by_contra hne
    apply hpos a hne
    rw [← hnorm, ha, norm_zero]
    simp
  obtain ⟨c, hc, hcL⟩ := exists_lower_of_injective L hinj
  set K := 1 / c
  have hK : ∀ a, ‖a‖ ≤ K * ‖L a‖ := fun a => by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hc, mul_comm]; exact hcL a
  have hK0 : 0 ≤ K := by positivity
  refine ⟨1 / (K + 1) ^ 2, by positivity, fun a => ?_⟩
  rw [← hnorm]
  apply ENNReal.ofReal_le_ofReal
  have h1 : ‖a‖ ≤ (K + 1) * ‖L a‖ := (hK a).trans (by nlinarith [norm_nonneg (L a)])
  have h2 : ‖a‖ ^ 2 ≤ ((K + 1) * ‖L a‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [mul_pow] at h2
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]
  linarith

lemma lintegral_enorm_sq_ne_top_of_bound {F : Type*} [NormedAddCommGroup F] {ν : Measure ℂ}
    [IsFiniteMeasure ν] {g : ℂ → F} {C : ℝ} (h : ∀ x, ‖g x‖ ≤ C) :
    ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _x, ENNReal.ofReal (C ^ 2) ∂ν) ?_ ?_
  · rw [lintegral_const]; exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  · refine lintegral_mono fun x => ?_
    rw [enorm_sq_eq_ofReal']
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) (h x) 2)

/-- The value of a function of a finite-dimensional space in terms of basis coefficients. -/
lemma eq_sum_basis {V : Submodule ℝ (ℂ → ℝ)} {m : ℕ} (bV : Module.Basis (Fin m) ℝ V) {u : ℂ → ℝ}
    (hu : u ∈ V) : u = ∑ i, bV.repr ⟨u, hu⟩ i • (bV i : ℂ → ℝ) := by
  have h := congrArg Subtype.val (bV.sum_repr ⟨u, hu⟩)
  rw [Submodule.coe_sum] at h
  simp only [Submodule.coe_smul] at h
  exact h.symm


lemma boundary_real_step {X Y η e : ℝ} (hη : 0 < η) (hY : 0 ≤ Y)
    (h : X ≤ (1 + η / 3) * Y + e) (he : e ≤ η / (3 * (1 + η)) * X) : X ≤ (1 + η) * Y := by
  set q := η / (3 * (1 + η)) with hqdef
  have hcoef : q * (1 + η) = η / 3 := by rw [hqdef]; field_simp
  have hq1 : q < 1 := by rw [hqdef, div_lt_one (by positivity)]; linarith
  have h1q : 0 < 1 - q := by linarith
  have hA : X * (1 - q) ≤ (1 + η / 3) * Y := by nlinarith
  have hB : (1 + η / 3) ≤ (1 + η) * (1 - q) := by
    have : (1 + η) * (1 - q) = 1 + η - q * (1 + η) := by ring
    rw [this, hcoef]; linarith
  have hC : X * (1 - q) ≤ ((1 + η) * Y) * (1 - q) := by
    calc X * (1 - q) ≤ (1 + η / 3) * Y := hA
      _ ≤ ((1 + η) * (1 - q)) * Y := mul_le_mul_of_nonneg_right hB hY
      _ = ((1 + η) * Y) * (1 - q) := by ring
  exact le_of_mul_le_mul_right hC h1q

/-- **Min–max transfer along a `C¹` composition.** -/
theorem minMax_le_of_C1_comp {Ω₂ : Set ℂ} (hΩ : volume Ω₂ ≠ ⊤) {ν : Measure ℂ}
    [IsFiniteMeasure ν] {Φ : ℂ → ℂ} (hΦ : ContDiff ℝ 1 Φ) (hΦc : HasCompactSupport Φ)
    {E₁ B₁ : (ℂ → ℝ) → ℝ≥0∞}
    (hE : ∀ u, ContDiff ℝ ∞ u → E₁ u = ∫⁻ x in Ω₂, ‖fderiv ℝ (u ∘ Φ) x‖ₑ ^ 2)
    (hB : ∀ u, ContDiff ℝ ∞ u → B₁ u = ∫⁻ x, ‖u (Φ x)‖ₑ ^ 2 ∂ν) (k : ℕ) :
    minMax (dirichletEnergy Ω₂) (fun w => ∫⁻ x, ‖w x‖ₑ ^ 2 ∂ν) k ≤ minMax E₁ B₁ k := by
  have hrange : IsCompact (range Φ) := hΦc.isCompact_range hΦ.continuous
  have hbdd : ∀ u : ℂ → ℝ, Continuous u → ∃ C, ∀ x, |u (Φ x)| ≤ C := by
    intro u hu
    obtain ⟨C, hC⟩ := (hrange.image hu).isBounded.subset_closedBall 0
    exact ⟨C, fun x => by simpa using hC ⟨Φ x, ⟨x, rfl⟩, rfl⟩⟩
  refine minMax_le_of_approx (by simp) (fun u hu => ?_) ?_
  · obtain ⟨C, hC⟩ := hbdd u hu.continuous
    rw [hB u hu]
    exact lintegral_enorm_sq_ne_top_of_bound (C := C) fun x => by
      rw [Real.norm_eq_abs]; exact hC x
  intro V hV η hη
  obtain ⟨hsm, hdim, hpos⟩ := hV
  haveI : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by omega)
  set bV := Module.finBasisOfFinrankEq ℝ V hdim
  set e : Fin (k + 1) → ℂ → ℝ := fun i => (bV i : ℂ → ℝ)
  have he : ∀ i, ContDiff ℝ ∞ (e i) := fun i => hsm _ (bV i).2
  have he1 : ∀ i, ContDiff ℝ 1 (e i) := fun i => (he i).of_le (by norm_cast)
  set f : Fin (k + 1) → ℂ → ℝ := fun i x => e i (Φ x)
  have hrep : ∀ u (hu : u ∈ V) y, u y = ∑ i, bV.repr ⟨u, hu⟩ i * e i y := by
    intro u hu y
    conv_lhs => rw [eq_sum_basis bV hu]
    simp [e, Finset.sum_apply]
  -- coefficient lower bound
  have hposf : ∀ a : Fin (k + 1) → ℝ, a ≠ 0 →
      ∫⁻ x, ‖∑ i, a i * f i x‖ₑ ^ 2 ∂ν ≠ 0 := by
    intro a ha
    set u : ℂ → ℝ := ∑ i, a i • e i with hudef
    have huV : u ∈ V := Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (bV i).2
    have hu0 : u ≠ 0 := by
      intro h0
      apply ha
      have hlin := bV.linearIndependent
      have : ∑ i, a i • bV i = 0 := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        simpa [e, hudef] using h0
      exact funext (Fintype.linearIndependent_iff.1 hlin a this)
    have hBu := hpos u huV hu0
    rw [hB u (hsm u huV)] at hBu
    convert hBu using 3 with x
    simp [hudef, f, Finset.sum_apply]
  obtain ⟨m₀, hm₀, hlow⟩ := exists_coeff_lower_bound f
    (fun i => (he i).continuous.comp hΦ.continuous)
    (fun i => hbdd (e i) (he i).continuous) hposf
  -- choice of `ε`
  set M : ℝ := ((k + 1 : ℕ) : ℝ)
  have hM : 0 < M := by positivity
  set VΩ := (volume Ω₂).toReal
  set Vν := (ν univ).toReal
  have hVΩ : 0 ≤ VΩ := ENNReal.toReal_nonneg
  have hVν : 0 ≤ Vν := ENNReal.toReal_nonneg
  set D := (1 + 3 / η) * M ^ 2 * (VΩ + Vν + 1)
  have hD : 0 < D := by positivity
  set ε := min 1 (η * m₀ / (3 * (1 + η) * D))
  have hε0 : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hDε : D * ε ^ 2 ≤ η * m₀ / (3 * (1 + η)) := by
    have h1 : ε ≤ η * m₀ / (3 * (1 + η) * D) := min_le_right _ _
    have h2 : ε ^ 2 ≤ ε := by nlinarith
    calc D * ε ^ 2 ≤ D * (η * m₀ / (3 * (1 + η) * D)) := by gcongr; linarith
      _ = η * m₀ / (3 * (1 + η)) := by field_simp
  -- choice of `δ` and of the smooth approximation `Ψ`
  have hδex : ∀ i, ∃ δ > 0, ∀ Ψ : ℂ → ℂ, Differentiable ℝ Ψ → (∀ x, ‖Ψ x - Φ x‖ ≤ δ) →
      (∀ x, ‖fderiv ℝ Ψ x - fderiv ℝ Φ x‖ ≤ δ) → ∀ x,
        |e i (Ψ x) - e i (Φ x)| ≤ ε ∧ ‖fderiv ℝ (e i ∘ Ψ) x - fderiv ℝ (e i ∘ Φ) x‖ ≤ ε :=
    fun i => comp_C1_close (he1 i) hΦ hΦc hε0
  choose δs hδs hδΨ using hδex
  set δ := Finset.univ.inf' ⟨0, Finset.mem_univ _⟩ δs
  have hδ0 : 0 < δ := (Finset.lt_inf'_iff _).2 fun i _ => hδs i
  have hδle : ∀ i, δ ≤ δs i := fun i => Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨Ψ, hΨs, hΨ0, hΨ1⟩ := exists_smooth_C1_approx hΦ hΦc hδ0
  have hΨd : Differentiable ℝ Ψ := hΨs.differentiable (by simp)
  have hclose : ∀ i x, |e i (Ψ x) - e i (Φ x)| ≤ ε ∧
      ‖fderiv ℝ (e i ∘ Ψ) x - fderiv ℝ (e i ∘ Φ) x‖ ≤ ε := fun i =>
    hδΨ i Ψ hΨd (fun x => (hΨ0 x).trans (hδle i)) (fun x => (hΨ1 x).trans (hδle i))
  refine ⟨LinearMap.funLeft ℝ ℝ Ψ, fun u hu => ?_⟩
  set a : Fin (k + 1) → ℝ := ⇑(bV.repr ⟨u, hu⟩)
  have hTu : (LinearMap.funLeft ℝ ℝ Ψ u) = u ∘ Ψ := rfl
  rw [hTu]
  have hus := hsm u hu
  have hcoef : ∀ i, |a i| ≤ ‖a‖ := fun i => by
    rw [← Real.norm_eq_abs]; exact norm_le_pi_norm a i
  -- pointwise estimates
  have hval : ∀ x, ‖u (Φ x)‖ ≤ ‖u (Ψ x)‖ + M * ε * ‖a‖ := by
    intro x
    have hdiff : u (Φ x) - u (Ψ x) = ∑ i, a i * (e i (Φ x) - e i (Ψ x)) := by
      rw [hrep u hu, hrep u hu, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hb : ‖u (Φ x) - u (Ψ x)‖ ≤ M * ε * ‖a‖ := by
      rw [hdiff]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖a i * (e i (Φ x) - e i (Ψ x))‖ ≤ ∑ _i : Fin (k + 1), ‖a‖ * ε := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm]
            exact mul_le_mul (hcoef i) (hclose i x).1 (abs_nonneg _) (norm_nonneg _)
        _ = M * ε * ‖a‖ := by simp [M]; ring
    have := norm_le_norm_add_norm_sub' (u (Φ x)) (u (Ψ x))
    linarith
  have hfd : ∀ (Θ : ℂ → ℂ), Differentiable ℝ Θ → ∀ x,
      fderiv ℝ (u ∘ Θ) x = ∑ i, a i • fderiv ℝ (e i ∘ Θ) x := by
    intro Θ hΘ x
    have hfun : u ∘ Θ = fun y => ∑ i, a i * e i (Θ y) := by
      ext y; simp only [Function.comp]; exact hrep u hu (Θ y)
    rw [hfun]
    have hd : ∀ i, HasFDerivAt (fun y => a i * e i (Θ y)) (a i • fderiv ℝ (e i ∘ Θ) x) x :=
      fun i => (((he1 i).differentiable one_ne_zero).comp hΘ x).hasFDerivAt.const_mul (a i)
    exact (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hd i).fderiv
  have hder : ∀ x, ‖fderiv ℝ (u ∘ Ψ) x‖ ≤ ‖fderiv ℝ (u ∘ Φ) x‖ + M * ε * ‖a‖ := by
    intro x
    have hdiff : fderiv ℝ (u ∘ Ψ) x - fderiv ℝ (u ∘ Φ) x =
        ∑ i, a i • (fderiv ℝ (e i ∘ Ψ) x - fderiv ℝ (e i ∘ Φ) x) := by
      rw [hfd Ψ hΨd x, hfd Φ (hΦ.differentiable one_ne_zero) x, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => (smul_sub _ _ _).symm
    have hb : ‖fderiv ℝ (u ∘ Ψ) x - fderiv ℝ (u ∘ Φ) x‖ ≤ M * ε * ‖a‖ := by
      rw [hdiff]
      refine (norm_sum_le _ _).trans ?_
      calc ∑ i, ‖a i • (fderiv ℝ (e i ∘ Ψ) x - fderiv ℝ (e i ∘ Φ) x)‖
          ≤ ∑ _i : Fin (k + 1), ‖a‖ * ε := by
            refine Finset.sum_le_sum fun i _ => ?_
            rw [norm_smul, Real.norm_eq_abs]
            exact mul_le_mul (hcoef i) (hclose i x).2 (norm_nonneg _) (norm_nonneg _)
        _ = M * ε * ‖a‖ := by simp [M]; ring
    have := norm_le_norm_add_norm_sub' (fderiv ℝ (u ∘ Ψ) x) (fderiv ℝ (u ∘ Φ) x)
    linarith
  -- the lower bound `m₀ ‖a‖² ≤ B₁ u`
  have hBlow : ENNReal.ofReal (m₀ * ‖a‖ ^ 2) ≤ B₁ u := by
    rw [hB u hus]
    convert hlow a using 3 with x
    rw [hrep u hu (Φ x)]
  have hcε : 0 ≤ M * ε * ‖a‖ := by positivity
  refine ⟨hus.comp hΨs, ?_, ?_⟩
  · -- energy
    have h1 := lintegral_sq_le (μ := volume.restrict Ω₂) (P := fun x => fderiv ℝ (u ∘ Ψ) x)
      (Q := fun x => fderiv ℝ (u ∘ Φ) x) (c := M * ε * ‖a‖) hη hder
    rw [Measure.restrict_apply_univ] at h1
    unfold dirichletEnergy
    rw [hE u hus]
    refine h1.trans (add_le_add le_rfl ?_)
    refine le_trans ?_ (mul_le_mul_right hBlow _)
    rw [← ENNReal.ofReal_toReal hΩ, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul hη.le]
    apply ENNReal.ofReal_le_ofReal
    have hk : (1 + 1 / η) * M ^ 2 * VΩ ≤ D := by
      have : 1 / η ≤ 3 / η := by gcongr; norm_num
      calc (1 + 1 / η) * M ^ 2 * VΩ ≤ (1 + 3 / η) * M ^ 2 * (VΩ + Vν + 1) := by
            gcongr; linarith
        _ = D := rfl
    have hk2 : D * ε ^ 2 ≤ η * m₀ := hDε.trans (by
      rw [div_le_iff₀ (by positivity)]; nlinarith [mul_pos hη hm₀])
    have : (1 + 1 / η) * (M * ε * ‖a‖) ^ 2 * VΩ = ((1 + 1 / η) * M ^ 2 * VΩ) * ε ^ 2 * ‖a‖ ^ 2 := by
      ring
    rw [this]
    calc ((1 + 1 / η) * M ^ 2 * VΩ) * ε ^ 2 * ‖a‖ ^ 2 ≤ D * ε ^ 2 * ‖a‖ ^ 2 := by gcongr
      _ ≤ η * m₀ * ‖a‖ ^ 2 := by gcongr
      _ = η * (m₀ * ‖a‖ ^ 2) := by ring
  · -- boundary mass
    have hη3 : 0 < η / 3 := by positivity
    have h1 := lintegral_sq_le (μ := ν) (P := fun x => u (Φ x)) (Q := fun x => u (Ψ x))
      (c := M * ε * ‖a‖) hη3 hval
    rw [← hB u hus] at h1
    have hXt : B₁ u ≠ ⊤ := by
      obtain ⟨C, hC⟩ := hbdd u hus.continuous
      rw [hB u hus]
      exact lintegral_enorm_sq_ne_top_of_bound (C := C) fun x => by
        rw [Real.norm_eq_abs]; exact hC x
    set X := B₁ u
    set Y := ∫⁻ x, ‖(u ∘ Ψ) x‖ₑ ^ 2 ∂ν
    rcases eq_or_ne Y ⊤ with hY | hY
    · rw [hY, ENNReal.mul_top (by rw [ENNReal.ofReal_ne_zero_iff]; linarith)]; exact le_top
    -- pass to real numbers
    set c := (1 + 1 / (η / 3)) * (M * ε * ‖a‖) ^ 2 with hcdef
    have hνr : ENNReal.ofReal Vν = ν univ := ENNReal.ofReal_toReal (measure_ne_top ν univ)
    have h1c : X ≤ ENNReal.ofReal ((1 + η / 3) * Y.toReal + c * Vν) := by
      have e : ENNReal.ofReal ((1 + η / 3) * Y.toReal + c * Vν) =
          ENNReal.ofReal (1 + η / 3) * Y + ENNReal.ofReal c * ν univ := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hY, hνr]
      rw [e]; exact h1
    have h1' : X.toReal ≤ (1 + η / 3) * Y.toReal + c * Vν := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1c
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hlow' : m₀ * ‖a‖ ^ 2 ≤ X.toReal := by
      have := ENNReal.toReal_mono hXt hBlow
      rwa [ENNReal.toReal_ofReal (by positivity)] at this
    have hY0 : 0 ≤ Y.toReal := ENNReal.toReal_nonneg
    have hc3 : 1 + 1 / (η / 3) = 1 + 3 / η := by rw [one_div_div]
    have hk : (1 + 3 / η) * M ^ 2 * Vν ≤ D :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have herr : c * Vν ≤ η / (3 * (1 + η)) * X.toReal := by
      have e1 : c * Vν = ((1 + 3 / η) * M ^ 2 * Vν) * ε ^ 2 * ‖a‖ ^ 2 := by
        rw [hcdef, hc3]; ring
      rw [e1]
      calc ((1 + 3 / η) * M ^ 2 * Vν) * ε ^ 2 * ‖a‖ ^ 2 ≤ D * ε ^ 2 * ‖a‖ ^ 2 := by gcongr
        _ ≤ η * m₀ / (3 * (1 + η)) * ‖a‖ ^ 2 := by gcongr
        _ = η / (3 * (1 + η)) * (m₀ * ‖a‖ ^ 2) := by ring
        _ ≤ η / (3 * (1 + η)) * X.toReal := by gcongr
    rw [← ENNReal.ofReal_toReal hXt, ← ENNReal.ofReal_toReal hY, ← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal (boundary_real_step hη hY0 h1' herr)

end SteklovC1
