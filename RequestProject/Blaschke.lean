module

public import Mathlib

/-!
# Lemma 2.4.1: boundary rigidity for finite Blaschke products

A finite Blaschke product of degree `n` is `B(z) = η ∏_{l<n} (z - a_l)/(1 - ā_l z)` with
`|η| = 1`, `|a_l| < 1`.  A holomorphic automorphism of `𝔻` is `φ(z) = μ (z - b)/(1 - b̄ z)` with
`|μ| = 1`, `|b| < 1`; an antiholomorphic one is `z ↦ ψ(z̄)` with `ψ` holomorphic.

We prove both parts of Lemma 2.4.1:
(i) if `|d/dt B₁(e^{it})| = |d/dt B₂(φ(e^{it}))|` for all `t`, then `B₁ = η B₂ ∘ φ` on `𝔻̄`;
(ii) for antiholomorphic `φ`, the same hypothesis gives `B₁ = η · conj (B₂ ∘ φ)` on `𝔻̄`.

The proof follows the paper: on the circle, `d/dt B(e^{it}) = i B(e^{it}) P(e^{it})` with
`P = ∑ (1 - |a_l|²)/|e^{it} - a_l|² ≥ 0` (boundary orientation is preserved), so the hypothesis
says the two arguments have equal derivatives and the boundary values differ by a unimodular
constant; the maximum modulus principle extends the identity to `𝔻̄`.
(The hypothesis "of the same degree" in the paper is not needed for the conclusion.)
-/

@[expose] public section

open Complex Metric Set

noncomputable section

namespace SteklovBlaschke

/-- The Blaschke factor `(z - a)/(1 - ā z)`. -/
def bfac (a z : ℂ) : ℂ := (z - a) / (1 - (starRingEnd ℂ) a * z)

/-- `B` is a finite Blaschke product of degree `n`. -/
def IsFiniteBlaschke (B : ℂ → ℂ) (n : ℕ) : Prop :=
  ∃ (η : ℂ) (a : Fin n → ℂ), ‖η‖ = 1 ∧ (∀ l, ‖a l‖ < 1) ∧ B = fun z => η * ∏ l, bfac (a l) z

/-- `φ` is a holomorphic automorphism of the unit disk `𝔻`: `φ(z) = μ (z - b)/(1 - b̄ z)`. -/
def IsDiskAut (φ : ℂ → ℂ) : Prop :=
  ∃ μ b : ℂ, ‖μ‖ = 1 ∧ ‖b‖ < 1 ∧ φ = fun z => μ * bfac b z

/-- `φ` is an antiholomorphic automorphism of `𝔻`: `φ(z) = ψ(z̄)` with `ψ ∈ Aut(𝔻)`. -/
def IsAntiDiskAut (φ : ℂ → ℂ) : Prop :=
  ∃ ψ, IsDiskAut ψ ∧ φ = fun z => ψ ((starRingEnd ℂ) z)

/-! ### Blaschke factors -/

section factor

variable {a : ℂ}

lemma denom_ne_zero (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) : 1 - (starRingEnd ℂ) a * z ≠ 0 := by
  intro h
  have h1 : (starRingEnd ℂ) a * z = 1 := by linear_combination -h
  have : ‖(starRingEnd ℂ) a * z‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc ‖a‖ * ‖z‖ ≤ ‖a‖ * 1 := by gcongr
      _ < 1 := by simpa using ha
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

lemma normSq_denom_sub (a z : ℂ) :
    normSq (1 - (starRingEnd ℂ) a * z) - normSq (z - a) = (1 - normSq a) * (1 - normSq z) := by
  simp only [normSq_apply, sub_re, one_re, mul_re, conj_re, conj_im, sub_im, one_im, mul_im]
  ring

lemma norm_bfac_le (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖bfac a z‖ ≤ 1 := by
  have hd := denom_ne_zero ha hz
  rw [bfac, norm_div, div_le_one (norm_pos_iff.2 hd)]
  have h1 : normSq a ≤ 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have h2 : normSq z ≤ 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have := normSq_denom_sub a z
  have h3 : normSq (z - a) ≤ normSq (1 - (starRingEnd ℂ) a * z) := by nlinarith
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at h3
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]

lemma norm_bfac_eq_one (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) : ‖bfac a z‖ = 1 := by
  have hd := denom_ne_zero ha hz.le
  rw [bfac, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.2 hd)]
  have h2 : normSq z = 1 := by rw [normSq_eq_norm_sq, hz]; norm_num
  have := normSq_denom_sub a z
  rw [h2, sub_self, mul_zero, sub_eq_zero] at this
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at this
  have := congrArg Real.sqrt this
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), eq_comm] at this

lemma hasDerivAt_bfac (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    HasDerivAt (bfac a) ((1 - (normSq a : ℂ)) / (1 - (starRingEnd ℂ) a * z) ^ 2) z := by
  have hd := denom_ne_zero ha hz
  have h1 : HasDerivAt (fun w : ℂ => w - a) 1 z := (hasDerivAt_id z).sub_const a
  have h2 : HasDerivAt (fun w : ℂ => 1 - (starRingEnd ℂ) a * w) (-(starRingEnd ℂ) a) z := by
    simpa using ((hasDerivAt_id z).const_mul ((starRingEnd ℂ) a)).const_sub 1
  have := h1.div h2 hd
  convert this using 1
  rw [← Complex.mul_conj a]
  field_simp
  ring

lemma differentiableAt_bfac (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    DifferentiableAt ℂ (bfac a) z := (hasDerivAt_bfac ha hz).differentiableAt

/-- The boundary density `(1 - |a|²)/|z - a|²` of a Blaschke factor. -/
def bdens (a z : ℂ) : ℝ := (1 - normSq a) / normSq (z - a)

lemma bdens_nonneg (ha : ‖a‖ < 1) (z : ℂ) : 0 ≤ bdens a z := by
  have : normSq a < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  exact div_nonneg (by linarith) (normSq_nonneg _)

/-- On the circle, `B'(z) = B(z) P(z)/z` for a Blaschke factor. -/
lemma hasDerivAt_bfac_circle (ha : ‖a‖ < 1) {z : ℂ} (hz : ‖z‖ = 1) :
    HasDerivAt (bfac a) (bfac a z * bdens a z / z) z := by
  convert hasDerivAt_bfac ha hz.le using 1
  have hd := denom_ne_zero ha hz.le
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hza : z - a ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; subst h; rw [hz] at ha; exact lt_irrefl _ ha
  have hn : (normSq (z - a) : ℂ) ≠ 0 := by exact_mod_cast (normSq_pos.2 hza).ne'
  have hzc : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, normSq_eq_norm_sq, hz]; norm_num
  -- key identity: (z - a)(1 - ā z) = z |z - a|²
  have key : (z - a) * (1 - (starRingEnd ℂ) a * z) = z * (normSq (z - a) : ℂ) := by
    rw [← Complex.mul_conj (z - a), map_sub]
    linear_combination (-(z - a)) * hzc
  have hza' : (z - a) / (1 - (starRingEnd ℂ) a * z) =
      z * (normSq (z - a) : ℂ) / (1 - (starRingEnd ℂ) a * z) ^ 2 := by
    rw [← key]; field_simp
  rw [bfac, bdens, hza']
  push_cast
  field_simp
end factor

/-! ### Boundary structure -/

/-- `B` has *positive boundary argument derivative with density `Q`*: on the unit circle
`|B| = 1`, `Q ≥ 0`, and `B'(z) = B(z) Q(z)/z`. -/
def BdryArg (B : ℂ → ℂ) (Q : ℂ → ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ = 1 → ‖B z‖ = 1 ∧ 0 ≤ Q z ∧ HasDerivAt B (B z * Q z / z) z

lemma bdryArg_prod {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℂ) (ha : ∀ l, ‖a l‖ < 1) :
    BdryArg (fun z => ∏ l ∈ s, bfac (a l) z) (fun z => ∑ l ∈ s, bdens (a l) z) := by
  induction s using Finset.induction_on with
  | empty =>
    intro z hz
    simpa using hasDerivAt_const z (1 : ℂ)
  | insert i s hi ih =>
    intro z hz
    obtain ⟨h1, h2, h3⟩ := ih z hz
    simp only at h1 h2 h3 ⊢
    have hz0 : z ≠ 0 := by rintro rfl; simp at hz
    refine ⟨?_, ?_, ?_⟩
    · rw [Finset.prod_insert hi, norm_mul, norm_bfac_eq_one (ha i) hz, h1, one_mul]
    · rw [Finset.sum_insert hi]
      exact add_nonneg (bdens_nonneg (ha i) z) h2
    · have := (hasDerivAt_bfac_circle (ha i) hz).mul h3
      simp only [Finset.prod_insert hi, Finset.sum_insert hi]
      convert this using 1
      push_cast
      field_simp

/-- Finite Blaschke products have positive boundary argument derivative. -/
lemma IsFiniteBlaschke.bdryArg {B : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n) :
    ∃ Q, BdryArg B Q := by
  obtain ⟨η, a, hη, ha, rfl⟩ := hB
  refine ⟨fun z => ∑ l, bdens (a l) z, fun z hz => ?_⟩
  obtain ⟨h1, h2, h3⟩ := bdryArg_prod Finset.univ a ha z hz
  refine ⟨by rw [norm_mul, hη, one_mul]; exact h1, h2, ?_⟩
  have := h3.const_mul η
  convert this using 1
  ring

lemma IsFiniteBlaschke.differentiableAt {B : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : DifferentiableAt ℂ B z := by
  obtain ⟨η, a, hη, ha, rfl⟩ := hB
  have : DifferentiableAt ℂ (∏ l, bfac (a l)) z :=
    DifferentiableAt.finset_prod (fun l _ => differentiableAt_bfac (ha l) hz)
  have := this.const_mul η
  convert this using 1
  ext w; simp [Finset.prod_apply]

lemma IsDiskAut.isFiniteBlaschke {φ : ℂ → ℂ} (hφ : IsDiskAut φ) : IsFiniteBlaschke φ 1 := by
  obtain ⟨μ, b, hμ, hb, rfl⟩ := hφ
  exact ⟨μ, fun _ => b, hμ, fun _ => hb, by ext z; simp⟩

lemma IsDiskAut.norm_le {φ : ℂ → ℂ} (hφ : IsDiskAut φ) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖φ z‖ ≤ 1 := by
  obtain ⟨μ, b, hμ, hb, rfl⟩ := hφ
  simp only [norm_mul, hμ, one_mul]
  exact norm_bfac_le hb hz

lemma bdryArg_comp {B φ : ℂ → ℂ} {Q Qφ : ℂ → ℝ} (hB : BdryArg B Q) (hφ : BdryArg φ Qφ) :
    BdryArg (B ∘ φ) (fun z => Q (φ z) * Qφ z) := by
  intro z hz
  obtain ⟨h1, h2, h3⟩ := hφ z hz
  obtain ⟨g1, g2, g3⟩ := hB (φ z) h1
  have hφ0 : φ z ≠ 0 := by rintro h; rw [h, norm_zero] at h1; exact zero_ne_one h1
  refine ⟨g1, mul_nonneg g2 h2, ?_⟩
  have := g3.comp z h3
  convert this using 1
  simp only [Function.comp_apply]
  push_cast
  field_simp

/-! ### The boundary curve and the constancy argument -/

/-- On the circle, `d/dt B(e^{it}) = i B(e^{it}) Q(e^{it})`. -/
lemma hasDerivAt_circle {B : ℂ → ℂ} {Q : ℂ → ℝ} (hB : BdryArg B Q) (t : ℝ) :
    HasDerivAt (fun s : ℝ => B (exp (s * I)))
      (I * B (exp (t * I)) * Q (exp (t * I))) t := by
  have hz : ‖exp (t * I)‖ = 1 := by rw [norm_exp_ofReal_mul_I]
  obtain ⟨-, -, h3⟩ := hB _ hz
  have he : HasDerivAt (fun s : ℝ => exp (s * I)) (I * exp (t * I)) t := by
    have := ((hasDerivAt_id (t : ℂ)).mul_const I).cexp
    have := this.comp_ofReal
    simpa [mul_comm] using this
  have := h3.comp t he
  convert this using 1
  have hz0 : exp (t * I) ≠ 0 := exp_ne_zero _
  field_simp

lemma norm_deriv_circle {B : ℂ → ℂ} {Q : ℂ → ℝ} (hB : BdryArg B Q) (t : ℝ) :
    ‖deriv (fun s : ℝ => B (exp (s * I))) t‖ = Q (exp (t * I)) := by
  have hz : ‖exp (t * I)‖ = 1 := by rw [norm_exp_ofReal_mul_I]
  obtain ⟨h1, h2, -⟩ := hB _ hz
  rw [(hasDerivAt_circle hB t).deriv, norm_mul, norm_mul, norm_I, h1, norm_real,
    Real.norm_eq_abs, abs_of_nonneg h2]
  ring

/-- Two unimodular curves with `G' = i G q` and the same `q` differ by a unimodular constant. -/
lemma const_of_same_arg {G₁ G₂ : ℝ → ℂ} {q : ℝ → ℝ}
    (h₁ : ∀ t, HasDerivAt G₁ (I * G₁ t * q t) t) (h₂ : ∀ t, HasDerivAt G₂ (I * G₂ t * q t) t)
    (n₁ : ∀ t, ‖G₁ t‖ = 1) (n₂ : ∀ t, ‖G₂ t‖ = 1) :
    ∃ η : ℂ, ‖η‖ = 1 ∧ ∀ t, G₁ t = η * G₂ t := by
  have hne : ∀ t, G₂ t ≠ 0 := fun t h => by have := n₂ t; rw [h, norm_zero] at this; simp at this
  have hd : ∀ t, HasDerivAt (fun s => G₁ s / G₂ s) 0 t := by
    intro t
    have := (h₁ t).div (h₂ t) (hne t)
    convert this using 1
    field_simp
    ring
  have hc := is_const_of_deriv_eq_zero (f := fun s => G₁ s / G₂ s)
    (fun t => (hd t).differentiableAt) (fun t => (hd t).deriv)
  refine ⟨G₁ 0 / G₂ 0, by rw [norm_div, n₁, n₂, div_one], fun t => ?_⟩
  have := hc t 0
  simp only at this
  rw [← this]
  field_simp [hne t]

/-- Maximum modulus: two functions holomorphic near `𝔻̄` agreeing on the circle agree on `𝔻̄`. -/
lemma eqOn_closedBall_of_eqOn_sphere {f g : ℂ → ℂ}
    (hf : ∀ z, ‖z‖ ≤ 1 → DifferentiableAt ℂ f z) (hg : ∀ z, ‖z‖ ≤ 1 → DifferentiableAt ℂ g z)
    (h : ∀ z, ‖z‖ = 1 → f z = g z) {z : ℂ} (hz : ‖z‖ ≤ 1) : f z = g z := by
  have hd : DiffContOnCl ℂ (fun w => f w - g w) (ball 0 1) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball (0 : ℂ) one_ne_zero]
    intro w hw
    rw [mem_closedBall, dist_zero_right] at hw
    exact ((hf w hw).sub (hg w hw)).differentiableWithinAt
  have := Complex.norm_le_of_forall_mem_frontier_norm_le (isBounded_ball) hd (C := 0)
    (fun w hw => by
      rw [frontier_ball (0 : ℂ) one_ne_zero, mem_sphere, dist_zero_right] at hw
      rw [h w hw, sub_self, norm_zero])
    (z := z) (by rw [closure_ball (0 : ℂ) one_ne_zero, mem_closedBall, dist_zero_right]; exact hz)
  have := norm_le_zero_iff.1 this
  exact sub_eq_zero.1 this

lemma circle_surj {z : ℂ} (hz : ‖z‖ = 1) : ∃ t : ℝ, exp (t * I) = z := by
  refine ⟨arg z, ?_⟩
  have := norm_mul_exp_arg_mul_I z
  rw [hz] at this
  simpa using this

/-! ### Lemma 2.4.1 -/

/-- **Lemma 2.4.1 (i).** Let `B₁, B₂` be finite Blaschke products and `φ ∈ Aut(𝔻)`.  If
`|d/dt B₁(e^{it})| = |d/dt B₂(φ(e^{it}))|` for all real `t`, then `B₁ = η · B₂ ∘ φ` on `𝔻̄`
for some `|η| = 1`. -/
theorem blaschke_boundary_rigidity {B₁ B₂ φ : ℂ → ℂ} {n m : ℕ}
    (hB₁ : IsFiniteBlaschke B₁ n) (hB₂ : IsFiniteBlaschke B₂ m) (hφ : IsDiskAut φ)
    (h : ∀ t : ℝ, ‖deriv (fun s : ℝ => B₁ (exp (s * I))) t‖ =
      ‖deriv (fun s : ℝ => B₂ (φ (exp (s * I)))) t‖) :
    ∃ η : ℂ, ‖η‖ = 1 ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → B₁ z = η * B₂ (φ z) := by
  obtain ⟨Q₁, hQ₁⟩ := hB₁.bdryArg
  obtain ⟨Q₂, hQ₂⟩ := hB₂.bdryArg
  obtain ⟨Qφ, hQφ⟩ := hφ.isFiniteBlaschke.bdryArg
  have hC := bdryArg_comp hQ₂ hQφ
  have hq : ∀ t : ℝ, Q₁ (exp (t * I)) = Q₂ (φ (exp (t * I))) * Qφ (exp (t * I)) := by
    intro t
    have := h t
    rw [norm_deriv_circle hQ₁ t] at this
    rw [this]
    exact norm_deriv_circle (B := B₂ ∘ φ) hC t
  have hnorm : ∀ {B : ℂ → ℂ} {Q : ℂ → ℝ}, BdryArg B Q → ∀ t : ℝ, ‖B (exp (t * I))‖ = 1 :=
    fun hB t => (hB _ (by rw [norm_exp_ofReal_mul_I])).1
  obtain ⟨η, hη, hEq⟩ := const_of_same_arg (q := fun t => Q₁ (exp (t * I)))
    (G₁ := fun s => B₁ (exp (s * I))) (G₂ := fun s => B₂ (φ (exp (s * I))))
    (hasDerivAt_circle hQ₁) (fun t => by
      have := hasDerivAt_circle (B := B₂ ∘ φ) hC t
      simp only [Function.comp_apply] at this
      show HasDerivAt _ (I * B₂ (φ (exp (t * I))) * (Q₁ (exp (t * I)) : ℂ)) t
      rw [hq t]
      exact this)
    (hnorm hQ₁) (hnorm (B := B₂ ∘ φ) hC)
  refine ⟨η, hη, fun z hz => ?_⟩
  refine eqOn_closedBall_of_eqOn_sphere (fun w hw => hB₁.differentiableAt hw)
    (fun w hw => ((hB₂.differentiableAt (hφ.norm_le hw)).comp w
      (hφ.isFiniteBlaschke.differentiableAt hw)).const_mul η) ?_ hz
  intro w hw
  obtain ⟨t, rfl⟩ := circle_surj hw
  exact hEq t

/-- **Lemma 2.4.1 (ii).** Let `B₁, B₂` be finite Blaschke products and `φ` an antiholomorphic
automorphism of `𝔻`.  If `|d/dt B₁(e^{it})| = |d/dt B₂(φ(e^{it}))|` for all real `t`, then
`B₁(z) = η · conj (B₂(φ(z)))` on `𝔻̄` for some `|η| = 1`. -/
theorem blaschke_boundary_rigidity_anti {B₁ B₂ φ : ℂ → ℂ} {n m : ℕ}
    (hB₁ : IsFiniteBlaschke B₁ n) (hB₂ : IsFiniteBlaschke B₂ m) (hφ : IsAntiDiskAut φ)
    (h : ∀ t : ℝ, ‖deriv (fun s : ℝ => B₁ (exp (s * I))) t‖ =
      ‖deriv (fun s : ℝ => B₂ (φ (exp (s * I)))) t‖) :
    ∃ η : ℂ, ‖η‖ = 1 ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → B₁ z = η * (starRingEnd ℂ) (B₂ (φ z)) := by
  obtain ⟨ψ, hψ, rfl⟩ := hφ
  obtain ⟨Q₁, hQ₁⟩ := hB₁.bdryArg
  obtain ⟨Q₂, hQ₂⟩ := hB₂.bdryArg
  obtain ⟨Qψ, hQψ⟩ := hψ.isFiniteBlaschke.bdryArg
  have hD := bdryArg_comp hQ₂ hQψ
  set D := B₂ ∘ ψ with hD_def
  set QD : ℂ → ℝ := fun z => Q₂ (ψ z) * Qψ z
  -- `C(z) = conj (D (conj z))`
  set C : ℂ → ℂ := fun z => (starRingEnd ℂ) (D ((starRingEnd ℂ) z)) with hC_def
  have hCb : BdryArg C (fun z => QD ((starRingEnd ℂ) z)) := by
    intro z hz
    have hz' : ‖(starRingEnd ℂ) z‖ = 1 := by rw [Complex.norm_conj, hz]
    obtain ⟨g1, g2, g3⟩ := hD _ hz'
    refine ⟨by simp only [C, Complex.norm_conj]; exact g1, g2, ?_⟩
    have := g3.conj_conj
    simp only [Complex.conj_conj] at this
    convert this using 1
    simp only [C, map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  -- derivative of the hypothesis curve `t ↦ D(conj e^{it})`
  have hcurve : ∀ t : ℝ, ‖deriv (fun s : ℝ => D ((starRingEnd ℂ) (exp (s * I)))) t‖ =
      QD ((starRingEnd ℂ) (exp (t * I))) := by
    intro t
    have e1 : (fun s : ℝ => D ((starRingEnd ℂ) (exp (s * I)))) =
        fun s : ℝ => (starRingEnd ℂ) (C (exp (s * I))) := by
      ext s; simp [C]
    rw [e1]
    have hd := (hasDerivAt_circle hCb t).star
    rw [show (fun s : ℝ => (starRingEnd ℂ) (C (exp (s * I)))) =
      fun x : ℝ => star (C (exp (x * I))) from rfl, hd.deriv]
    simp only [norm_star]
    rw [← (hasDerivAt_circle hCb t).deriv, norm_deriv_circle hCb t]
  have hq : ∀ t : ℝ, Q₁ (exp (t * I)) = QD ((starRingEnd ℂ) (exp (t * I))) := by
    intro t
    have := h t
    rw [norm_deriv_circle hQ₁ t] at this
    rw [this]
    exact hcurve t
  have hnorm : ∀ {B : ℂ → ℂ} {Q : ℂ → ℝ}, BdryArg B Q → ∀ t : ℝ, ‖B (exp (t * I))‖ = 1 :=
    fun hB t => (hB _ (by rw [norm_exp_ofReal_mul_I])).1
  obtain ⟨η, hη, hEq⟩ := const_of_same_arg (q := fun t => Q₁ (exp (t * I)))
    (G₁ := fun s => B₁ (exp (s * I))) (G₂ := fun s => C (exp (s * I)))
    (hasDerivAt_circle hQ₁) (fun t => by
      show HasDerivAt _ (I * C (exp (t * I)) * (Q₁ (exp (t * I)) : ℂ)) t
      rw [hq t]; exact hasDerivAt_circle hCb t)
    (hnorm hQ₁) (hnorm hCb)
  refine ⟨η, hη, fun z hz => ?_⟩
  have hCd : ∀ w : ℂ, ‖w‖ ≤ 1 → DifferentiableAt ℂ C w := by
    intro w hw
    have hw' : ‖(starRingEnd ℂ) w‖ ≤ 1 := by rwa [Complex.norm_conj]
    have hDd : DifferentiableAt ℂ D ((starRingEnd ℂ) w) :=
      (hB₂.differentiableAt (hψ.norm_le hw')).comp _
        (hψ.isFiniteBlaschke.differentiableAt hw')
    have := hDd.conj_conj
    simp only [Complex.conj_conj] at this
    exact this
  have := eqOn_closedBall_of_eqOn_sphere (fun w hw => hB₁.differentiableAt hw)
    (fun w hw => (hCd w hw).const_mul η) (fun w hw => by
      obtain ⟨t, rfl⟩ := circle_surj hw
      exact hEq t) hz
  simpa [C, D] using this

end SteklovBlaschke

end
