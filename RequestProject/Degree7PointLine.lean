module

public import RequestProject.ConjugateMonodromy

/-!
# The two candidates realize the point and the line actions of `GL(3, 𝔽₂)`

For `s² = -7` we compare the *actual* monodromy of `p_s` and of `p_{-s}` along the *same*
standard generators `γ₀, γ₁` at the base point `-r` (described by explicit parametrizations,
`IsStdLoops`):

* `monodromy_point_line`: after labelling each fibre by `Fin 7`, both polynomials send `γ₀` to
  `x₇`, and `γ₁` goes to `y₁` for one of them and to `y₂` for the other;
* `monodromy_rho`: equivalently, on the standard generators the monodromy of one polynomial is the
  line action `ρ_L` and that of the other is the point action `ρ_P` of the generators `x, y` of
  `G = GL(3, 𝔽₂)`.

The proof uses: the monodromy pair of `p_s` (`monodromy_pair`, from the local monodromy at `0`,
`1`, `∞` and the exact passports), the kernel-checked two-orbit classification
(`admissible_normal_form`), and complex conjugation, which maps `p_s` to `p_{-s}` and acts on the
standard generators by `γ₀ ↦ γ₀⁻¹`, `γ₁ ↦ γ₀ γ₁⁻¹ γ₀⁻¹` (`ConjMonodromy.std_conj`); an explicit
permutation (`τ₇`) then identifies the transported pair with the other orbit.
-/

@[expose] public section

open Polynomial Set Equiv PolyCover LocalMonodromy MonodromyRelation MonodromyTriple
open ComplexConjugate Complex

noncomputable section

namespace Degree7

variable {s : ℂ}

theorem conj_of_sq (hs : s ^ 2 = -7) : conj s = -s := by
  have hre : s.re = 0 := by
    have h1 := congrArg Complex.re hs
    have h2 := congrArg Complex.im hs
    simp only [sq, mul_re, mul_im, neg_re, neg_im] at h1 h2
    norm_num at h1 h2
    rcases mul_eq_zero.1 (show s.re * s.im = 0 by linarith) with h | h
    · exact h
    · rw [h] at h1; nlinarith [sq_nonneg s.re]
  apply Complex.ext <;> simp [hre]

theorem neg_sq_seven (hs : s ^ 2 = -7) : (-s) ^ 2 = -7 := by rw [_root_.neg_sq, hs]

theorem pPoly_conj (hs : s ^ 2 = -7) (z : ℂ) :
    (pPoly (-s)).eval (conj z) = conj ((pPoly s).eval z) := by
  have hc := conj_of_sq hs
  rw [pPoly_eval, pPoly_eval]
  simp only [pfun, Apoly, cc, bconst, map_sub, map_one, map_div₀, map_mul, map_pow, map_add,
    map_ofNat, hc]

theorem critVals_conj (hs : s ^ 2 = -7) (z : ℂ) :
    z ∈ critVals (pPoly (-s)) ↔ conj z ∈ critVals (pPoly s) := by
  rw [critVals_pPoly (neg_sq_seven hs), critVals_pPoly hs]
  simp only [mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro (rfl | rfl) <;> simp
  · rintro (h | h)
    · left; simpa using congrArg conj h
    · right; simpa using congrArg conj h

theorem circ_sub (w0 : ℂ) (r t : ℝ) : ‖circ w0 r t - w0‖ = |r| := by
  simp only [circ, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [show (2 * (Real.pi : ℂ) * I * t) = ((2 * Real.pi * t : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]

theorem circ_notMem {P : ℂ[X]} (hcrit : critVals P ⊆ {0, 1}) {w0 : ℂ} {r : ℝ}
    (h0 : ‖w0‖ ≠ |r|) (h1 : ‖1 - w0‖ ≠ |r|) (t : ℝ) : circ w0 r t ∉ critVals P := by
  intro h
  rcases hcrit h with h | h
  · apply h0; rw [← circ_sub w0 r t, h, zero_sub, norm_neg]
  · apply h1; rw [← circ_sub w0 r t, h]

theorem perm_permCongr (τ σ : Perm (Fin 7)) : τ.permCongr σ = τ * σ * τ⁻¹ := by
  ext i; simp

theorem permCongr_inv' {α β : Type*} (e : α ≃ β) (σ : Perm α) :
    e.permCongr σ⁻¹ = (e.permCongr σ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← permCongr_mul, inv_mul_cancel, permCongr_one']

/-- The permutation identifying the transported pair with the other orbit. -/
def tau7 : Perm (Fin 7) := c[0, 1] * c[2, 3] * c[5, 6]

set_option maxRecDepth 100000 in
theorem tau7_facts : tau7 * x7⁻¹ * tau7⁻¹ = x7 ∧
    tau7 * (x7⁻¹ * y1⁻¹ * x7) * tau7⁻¹ = y2 ∧ tau7 * (x7⁻¹ * y2⁻¹ * x7) * tau7⁻¹ = y1 := by
  decide +kernel

/-- **The actual monodromies of `p_s` and `p_{-s}` on the same standard generators.**  There are
`0 < r < 1/2`, standard generators `γ₀, γ₁` of `ℂ \ {0,1}` at `-r` (for the covering `p_s`) and
`γ₀', γ₁'` (the same explicitly parametrized loops, for the covering `p_{-s}`), and labellings of
the two fibres over `-r` by `Fin 7`, such that both monodromies send the loop around `0` to `x₇`,
while the loop around `1` goes to `y₁` for one polynomial and to `y₂` for the other. -/
theorem monodromy_point_line (hs : s ^ 2 = -7) :
    ∃ (r : ℝ) (A : Base (pPoly s)) (γ0 γ1 : Path.Homotopic.Quotient A A)
      (A' : Base (pPoly (-s))) (γ0' γ1' : Path.Homotopic.Quotient A' A')
      (L : proj (pPoly s) ⁻¹' {A} ≃ Fin 7) (L' : proj (pPoly (-s)) ⁻¹' {A'} ≃ Fin 7),
      0 < r ∧ r < 1 / 2 ∧ (A : ℂ) = -r ∧ (A' : ℂ) = -r ∧
      IsStdLoops r γ0 γ1 ∧ IsStdLoops r γ0' γ1' ∧
      L.permCongr (monodromyPerm (pPoly s) γ0) = x7 ∧
      L'.permCongr (monodromyPerm (pPoly (-s)) γ0') = x7 ∧
      ((L.permCongr (monodromyPerm (pPoly s) γ1) = y1 ∧
          L'.permCongr (monodromyPerm (pPoly (-s)) γ1') = y2) ∨
        (L.permCongr (monodromyPerm (pPoly s) γ1) = y2 ∧
          L'.permCongr (monodromyPerm (pPoly (-s)) γ1') = y1)) := by
  obtain ⟨A, γ0, γ1, L0, h0, h1, -, h7, r, hr, hr2, hstd, -⟩ := monodromy_pair hs
  obtain ⟨τ, hx, hy⟩ := admissible_normal_form _ _ h0 h1 h7
  have hA : (A : ℂ) = -r := by
    obtain ⟨_, _, _, U0, _, _, _, _, hU0, -⟩ := hstd
    rw [← congrArg Subtype.val U0.target, hU0]; simp [upper_one]
  have hcritQ : critVals (pPoly (-s)) ⊆ {0, 1} := (critVals_pPoly (neg_sq_seven hs)).le
  have habs : |r| = r := abs_of_pos hr
  have hc0 := circ_notMem hcritQ (w0 := 0) (r := r) (by simp [habs]; exact hr.ne)
    (by simp [habs]; linarith)
  have hc1 := circ_notMem hcritQ (w0 := 1) (r := r) (by simp [habs]; linarith)
    (by simp [habs]; exact hr.ne)
  have hcR := circ_notMem hcritQ (w0 := 0) (r := 2) (by norm_num) (by norm_num)
  obtain ⟨A', w0, w1, -, hA', -, hstdQ⟩ :=
    loop_relation hcritQ hr hr2 (by norm_num : (1 : ℝ) < 2) hc0 hc1 hcR
  obtain ⟨F, e0, e1⟩ := ConjMonodromy.std_conj (pPoly_conj hs) (critVals_conj hs) hstd hstdQ
  let L := L0.trans τ
  let L' := (F.trans L).trans tau7
  have hL : ∀ σ, L.permCongr σ = τ * L0.permCongr σ * τ⁻¹ := fun σ => by
    rw [← permCongr_trans', perm_permCongr]
  have hL' : ∀ σ, L'.permCongr (F.symm.permCongr σ) = tau7 * L.permCongr σ * tau7⁻¹ := fun σ => by
    have hFF : F.permCongr (F.symm.permCongr σ) = σ := by ext; simp [permCongr_apply]
    show ((F.trans L).trans tau7).permCongr _ = _
    rw [← permCongr_trans' (F.trans L) tau7, ← permCongr_trans' F L, perm_permCongr, hFF]
  have hxL : L.permCongr (monodromyPerm (pPoly s) γ0) = x7 := by rw [hL, hx]
  obtain ⟨t1, t2, t3⟩ := tau7_facts
  refine ⟨r, A, γ0, γ1, A', conjLoop w0 (circleLoop 0 r hc0), conjLoop w1 (circleLoop 1 r hc1),
    L, L', hr, hr2, hA, hA', hstd, hstdQ, hxL, ?_, ?_⟩
  · rw [e0, hL', permCongr_inv', hxL, t1]
  · rw [e1, hL', permCongr_mul, permCongr_mul, permCongr_inv', permCongr_inv', hxL]
    rcases hy with hy | hy
    · left; refine ⟨by rw [hL, hy], ?_⟩
      rw [hL, hy, t2]
    · right; refine ⟨by rw [hL, hy], ?_⟩
      rw [hL, hy, t3]

open GL3F2 in
/-- **Identification with the point and line actions of `G = GL(3, 𝔽₂)`.**  On the standard
generators `γ₀, γ₁` (resp. the same loops `γ₀', γ₁'` for `p_{-s}`), the monodromy of one of the two
polynomials is the line action `ρ_L` and that of the other is the point action `ρ_P` of the
generators `x, y` of `G`; in particular the subgroups generated by the monodromies of the standard
generators are the images `ρ_L(G)` and `ρ_P(G)` (each of order `168`). -/
theorem monodromy_rho (hs : s ^ 2 = -7) :
    ∃ (r : ℝ) (A : Base (pPoly s)) (γ0 γ1 : Path.Homotopic.Quotient A A)
      (A' : Base (pPoly (-s))) (γ0' γ1' : Path.Homotopic.Quotient A' A')
      (L : proj (pPoly s) ⁻¹' {A} ≃ Fin 7) (L' : proj (pPoly (-s)) ⁻¹' {A'} ≃ Fin 7),
      0 < r ∧ r < 1 / 2 ∧ (A : ℂ) = -r ∧ (A' : ℂ) = -r ∧
      IsStdLoops r γ0 γ1 ∧ IsStdLoops r γ0' γ1' ∧
      ((L.permCongr (monodromyPerm (pPoly s) γ0) = rhoL x ∧
          L.permCongr (monodromyPerm (pPoly s) γ1) = rhoL y ∧
          L'.permCongr (monodromyPerm (pPoly (-s)) γ0') = rhoP x ∧
          L'.permCongr (monodromyPerm (pPoly (-s)) γ1') = rhoP y) ∨
        (L.permCongr (monodromyPerm (pPoly s) γ0) = rhoP x ∧
          L.permCongr (monodromyPerm (pPoly s) γ1) = rhoP y ∧
          L'.permCongr (monodromyPerm (pPoly (-s)) γ0') = rhoL x ∧
          L'.permCongr (monodromyPerm (pPoly (-s)) γ1') = rhoL y)) := by
  obtain ⟨r, A, γ0, γ1, A', γ0', γ1', L, L', hr, hr2, hA, hA', hs1, hs2, h0, h0', hy⟩ :=
    monodromy_point_line hs
  refine ⟨r, A, γ0, γ1, A', γ0', γ1', L, L', hr, hr2, hA, hA', hs1, hs2, ?_⟩
  rw [rhoL_x, rhoL_y, rhoP_x, rhoP_y, h0, h0']
  rcases hy with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
  · exact Or.inl ⟨rfl, h1, rfl, h1'⟩
  · exact Or.inr ⟨rfl, h1, rfl, h1'⟩

end Degree7
