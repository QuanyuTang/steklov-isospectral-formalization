module

public import Mathlib
public import RequestProject.Blaschke
public import RequestProject.HolomorphicInverse

/-!
# Proper products over a univalent map are finite Blaschke products

* `norm_le_one_of_boundary`: maximum principle with boundary values in the limit — if `H` is
  holomorphic on `𝔻` and `limsup_{|w|→1} |H(w)| ≤ 1`, then `|H| ≤ 1` on `𝔻`.
* `blaschke_prod_norm_ge`: `|∏ bfac a_l (w)| → 1` uniformly as `|w| → 1`.
* `eq_blaschke_of_proper`: let `ψ` be holomorphic and injective on `𝔻`, `a_l ∈ 𝔻`
  (`l < n`, repetitions allowed) and `G(w) = ∏_l (ψ(w) - ψ(a_l))`.  If `|G| < 1` on `𝔻` and
  `|G(w)| → 1` as `|w| → 1` (properness), then `G = η ∏_l bfac a_l` on `𝔻` with `|η| = 1`.

  Proof: `ψ(w) - ψ(a) = bfac a (w) · (1 - ā w) · dslope ψ a (w)` and `dslope ψ a` is holomorphic
  and zero-free on `𝔻` (injectivity; `ψ'(a) ≠ 0`), so `G = P·H` with `P = ∏ bfac a_l` and `H`
  holomorphic and zero-free; `|H| → 1` and `|1/H| → 1` at the boundary, so `|H| ≡ 1` by the
  maximum principle applied to `H` and `1/H`, and `H` is constant by the maximum modulus principle.
  (All multiplicities are carried by the repetitions in the list `a`; no zero counting is needed.)
-/

@[expose] public section

open Set Filter Topology Metric Complex SteklovBlaschke

noncomputable section

namespace SteklovRiemann

/-- **Maximum principle with boundary limit.** -/
theorem norm_le_one_of_boundary {H : ℂ → ℂ} (hH : DifferentiableOn ℂ H (ball 0 1))
    (hlim : ∀ C : ℝ, 1 < C → ∃ ρ < 1, ∀ w : ℂ, ρ < ‖w‖ → ‖w‖ < 1 → ‖H w‖ ≤ C) :
    ∀ w ∈ ball (0 : ℂ) 1, ‖H w‖ ≤ 1 := by
  intro w hw
  have hw1 := mem_ball_zero_iff.1 hw
  refine le_of_forall_gt_imp_ge_of_dense fun C hC => ?_
  obtain ⟨ρ, hρ1, hρ⟩ := hlim C hC
  set m := max (max ρ ‖w‖) 0 with hm
  have hm1 : m < 1 := max_lt (max_lt hρ1 hw1) one_pos
  set r := (m + 1) / 2 with hr
  have hr1 : r < 1 := by rw [hr]; linarith
  have hmr : m < r := by rw [hr]; linarith
  have hr0 : 0 < r := lt_of_le_of_lt (le_max_right _ _) hmr
  have hcl : DiffContOnCl ℂ H (ball 0 r) := hH.diffContOnCl_ball (closedBall_subset_ball hr1)
  refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hcl (fun z hz => ?_)
    (subset_closure (mem_ball_zero_iff.2 ?_))
  · rw [frontier_ball 0 hr0.ne', mem_sphere_zero_iff_norm] at hz
    refine hρ z ?_ (by rw [hz]; exact hr1)
    rw [hz]
    exact lt_of_le_of_lt ((le_max_left _ _).trans (le_max_left _ _)) hmr
  · exact lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hmr

lemma continuousOn_bfac {a : ℂ} (ha : ‖a‖ < 1) : ContinuousOn (bfac a) (closedBall 0 1) :=
  fun _ hz => (differentiableAt_bfac ha (mem_closedBall_zero_iff.1 hz)).continuousAt.continuousWithinAt

/-- **Finite Blaschke products tend to modulus one at the circle.** -/
theorem blaschke_prod_norm_ge {n : ℕ} {a : Fin n → ℂ} (ha : ∀ l, ‖a l‖ < 1) {δ : ℝ}
    (hδ : δ < 1) : ∃ ρ < 1, ∀ w : ℂ, ρ < ‖w‖ → ‖w‖ ≤ 1 → δ ≤ ‖∏ l, bfac (a l) w‖ := by
  set P : ℂ → ℂ := fun w => ∏ l, bfac (a l) w with hP
  have hPc : ContinuousOn P (closedBall 0 1) :=
    continuousOn_finset_prod _ fun l _ => continuousOn_bfac (ha l)
  have huc := (isCompact_closedBall (0 : ℂ) 1).uniformContinuousOn_of_continuous hPc
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨η, hη, hηP⟩ := huc (1 - δ) (by linarith)
  set η' := min η (1 / 2) with hη'
  have hη'0 : 0 < η' := lt_min hη (by norm_num)
  refine ⟨1 - η', by linarith, fun w hw1 hw2 => ?_⟩
  have hwpos : 0 < ‖w‖ := by
    have : η' ≤ 1 / 2 := min_le_right _ _
    linarith
  set u : ℂ := w / (‖w‖ : ℂ) with hu
  have hwc : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast hwpos.ne'
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hwpos, div_self hwpos.ne']
  have hdist : dist w u < η := by
    have : w - u = ((‖w‖ - 1 : ℝ) : ℂ) * u := by
      rw [hu]; push_cast; field_simp
    rw [dist_eq_norm, this, norm_mul, hun, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    have : η' ≤ η := min_le_left _ _
    linarith
  have h := hηP w (mem_closedBall_zero_iff.2 hw2) u (mem_closedBall_zero_iff.2 hun.le) hdist
  have hPu : ‖P u‖ = 1 := by
    rw [hP]; simp only [norm_prod]
    exact Finset.prod_eq_one fun l _ => norm_bfac_eq_one (ha l) hun
  rw [dist_eq_norm] at h
  have := norm_sub_norm_le (P u) (P w)
  rw [norm_sub_rev] at h
  show δ ≤ ‖P w‖
  linarith

lemma norm_blaschke_prod_le {n : ℕ} {a : Fin n → ℂ} (ha : ∀ l, ‖a l‖ < 1) {w : ℂ}
    (hw : ‖w‖ ≤ 1) : ‖∏ l, bfac (a l) w‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun l _ => norm_bfac_le (ha l) hw

/-- `ψ(w) - ψ(a) = bfac a (w) · ((1 - ā w) · dslope ψ a w)` on `𝔻̄`. -/
lemma sub_eq_bfac_mul {ψ : ℂ → ℂ} {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) :
    ψ w - ψ a = bfac a w * ((1 - (starRingEnd ℂ) a * w) * dslope ψ a w) := by
  have hd := denom_ne_zero ha hw
  have hd' : 1 - w * (starRingEnd ℂ) a ≠ 0 := by rwa [mul_comm]
  rw [← sub_smul_dslope ψ a w, smul_eq_mul, bfac]
  field_simp

/-- **Proper products over a univalent map are finite Blaschke products.** -/
theorem eq_blaschke_of_proper {ψ : ℂ → ℂ} (hψd : DifferentiableOn ℂ ψ (ball 0 1))
    (hψi : InjOn ψ (ball 0 1)) {n : ℕ} {a : Fin n → ℂ} (ha : ∀ l, ‖a l‖ < 1)
    (hlt : ∀ w ∈ ball (0 : ℂ) 1, ‖∏ l, (ψ w - ψ (a l))‖ < 1)
    (hprop : ∀ δ < 1, ∃ ρ < 1, ∀ w : ℂ, ρ < ‖w‖ → ‖w‖ < 1 → δ ≤ ‖∏ l, (ψ w - ψ (a l))‖) :
    ∃ η : ℂ, ‖η‖ = 1 ∧ ∀ w ∈ ball (0 : ℂ) 1, ∏ l, (ψ w - ψ (a l)) = η * ∏ l, bfac (a l) w := by
  set G : ℂ → ℂ := fun w => ∏ l, (ψ w - ψ (a l)) with hG
  set P : ℂ → ℂ := fun w => ∏ l, bfac (a l) w with hP
  set H : ℂ → ℂ := fun w => ∏ l, ((1 - (starRingEnd ℂ) (a l) * w) * dslope ψ (a l) w) with hH
  have haball : ∀ l, a l ∈ ball (0 : ℂ) 1 := fun l => mem_ball_zero_iff.2 (ha l)
  have hGPH : ∀ w ∈ ball (0 : ℂ) 1, G w = P w * H w := by
    intro w hw
    simp only [hG, hP, hH, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun l _ => sub_eq_bfac_mul (ha l) (mem_ball_zero_iff.1 hw).le
  have hslope : ∀ l, DifferentiableOn ℂ (dslope ψ (a l)) (ball 0 1) := fun l =>
    (differentiableOn_dslope (isOpen_ball.mem_nhds (haball l))).2 hψd
  have hHd : DifferentiableOn ℂ H (ball 0 1) := by
    have := DifferentiableOn.finset_prod (u := Finset.univ) (s := ball (0 : ℂ) 1)
      (f := fun l w => (1 - (starRingEnd ℂ) (a l) * w) * dslope ψ (a l) w)
      (fun l _ => ((differentiableOn_const _).sub
        ((differentiableOn_const _).mul differentiableOn_id)).mul (hslope l))
    convert this using 1
    ext w; simp [hH]
  have hH0 : ∀ w ∈ ball (0 : ℂ) 1, H w ≠ 0 := by
    intro w hw
    simp only [hH]
    rw [Finset.prod_ne_zero_iff]
    intro l _
    refine mul_ne_zero (denom_ne_zero (ha l) (mem_ball_zero_iff.1 hw).le) ?_
    by_cases hwa : w = a l
    · rw [hwa, dslope_same]
      exact HolInv.deriv_ne_zero_of_injOn isOpen_ball hψd hψi (haball l)
    · rw [dslope_of_ne _ hwa, slope_def_field]
      refine div_ne_zero (fun h => hwa ?_) (sub_ne_zero.2 hwa)
      exact hψi hw (haball l) (sub_eq_zero.1 h)
  -- boundary behaviour
  have hbd : ∀ C : ℝ, 1 < C → ∃ ρ < 1, ∀ w : ℂ, ρ < ‖w‖ → ‖w‖ < 1 →
      ‖H w‖ ≤ C ∧ ‖(H w)⁻¹‖ ≤ C := by
    intro C hC
    have hδ1 : 1 / C < 1 := by rw [div_lt_one (by linarith)]; exact hC
    have hδ0 : 0 < 1 / C := by positivity
    obtain ⟨ρ₁, hρ₁, h₁⟩ := hprop (1 / C) hδ1
    obtain ⟨ρ₂, hρ₂, h₂⟩ := blaschke_prod_norm_ge ha hδ1
    refine ⟨max ρ₁ ρ₂, max_lt hρ₁ hρ₂, fun w hw1 hw2 => ?_⟩
    have hwb : w ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.2 hw2
    have hG1 := h₁ w (lt_of_le_of_lt (le_max_left _ _) hw1) hw2
    have hP1 := h₂ w (lt_of_le_of_lt (le_max_right _ _) hw1) hw2.le
    have hGlt := hlt w hwb
    have hPle := norm_blaschke_prod_le ha hw2.le
    have heq : ‖G w‖ = ‖P w‖ * ‖H w‖ := by rw [hGPH w hwb, norm_mul]
    have hPpos : 0 < ‖P w‖ := lt_of_lt_of_le hδ0 hP1
    have hGpos : 0 < ‖G w‖ := lt_of_lt_of_le hδ0 hG1
    have hHpos : 0 < ‖H w‖ := norm_pos_iff.2 (hH0 w hwb)
    have hCinv : C = 1 / (1 / C) := by field_simp
    constructor
    · -- `‖H‖ = ‖G‖/‖P‖ ≤ 1/(1/C)`
      have : ‖P w‖ * ‖H w‖ < 1 := heq ▸ hGlt
      have h3 : (1 / C) * ‖H w‖ ≤ ‖P w‖ * ‖H w‖ := mul_le_mul_of_nonneg_right hP1 hHpos.le
      rw [hCinv, le_div_iff₀ hδ0]
      linarith
    · rw [norm_inv, hCinv, inv_le_comm₀ hHpos (by positivity), one_div_one_div]
      -- `‖H‖ = ‖G‖/‖P‖ ≥ (1/C)/1`
      have h3 : 1 / C ≤ ‖P w‖ * ‖H w‖ := heq ▸ hG1
      have h4 : ‖P w‖ * ‖H w‖ ≤ 1 * ‖H w‖ := mul_le_mul_of_nonneg_right hPle hHpos.le
      simp only [one_div] at h3 ⊢
      linarith
  have hHle := norm_le_one_of_boundary hHd fun C hC => by
    obtain ⟨ρ, hρ, h⟩ := hbd C hC
    exact ⟨ρ, hρ, fun w h1 h2 => (h w h1 h2).1⟩
  have hHinvle := norm_le_one_of_boundary (H := fun w => (H w)⁻¹) (hHd.inv hH0) fun C hC => by
    obtain ⟨ρ, hρ, h⟩ := hbd C hC
    exact ⟨ρ, hρ, fun w h1 h2 => (h w h1 h2).2⟩
  have hH1 : ∀ w ∈ ball (0 : ℂ) 1, ‖H w‖ = 1 := by
    intro w hw
    refine le_antisymm (hHle w hw) ?_
    have := hHinvle w hw
    simp only [norm_inv] at this
    have hpos : 0 < ‖H w‖ := norm_pos_iff.2 (hH0 w hw)
    rwa [inv_le_one₀ hpos] at this
  have h0b : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  have hmax : IsMaxOn (norm ∘ H) (ball 0 1) 0 := fun w hw => by
    simp only [mem_setOf_eq, Function.comp]; rw [hH1 w hw, hH1 0 h0b]
  have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
    (convex_ball (0 : ℂ) 1).isPreconnected isOpen_ball hHd h0b hmax
  refine ⟨H 0, hH1 0 h0b, fun w hw => ?_⟩
  have := hGPH w hw
  rw [hconst hw] at this
  simp only [Function.const_apply] at this
  simp only [hG, hP] at this
  rw [this, mul_comm]

end SteklovRiemann
