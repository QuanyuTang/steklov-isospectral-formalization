module

public import RequestProject.LocalMonodromy

/-!
# Monodromy of a polynomial covering around infinity

For a polynomial `P` of degree `n ≥ 1`, write `P(1/v) = 1/h(v)^n` near `v = 0` with `h` a local
biholomorphism, `h(0) = 0` (`exists_infinity_root`).  Consequently, for every sufficiently large
`R`, the circle `t ↦ R e^{2π i t}` avoids the critical values and its monodromy is an `n`-cycle:
there is a labelling `Fin n ≃` fibre conjugating it to `finRotate n` (`infinity_monodromy`).
-/

@[expose] public section

open Polynomial Set Filter Topology Metric Complex PolyCover LocalMonodromy
open scoped Real

noncomputable section

namespace InfinityMonodromy

theorem reflect_eval (P : ℂ[X]) {v : ℂ} (hv : v ≠ 0) :
    (P.reflect P.natDegree).eval v = v ^ P.natDegree * P.eval (1 / v) := by
  letI : Invertible (1 / v) := invertibleOfNonzero (by simpa using hv)
  have := eval₂_reflect_mul_pow (RingHom.id ℂ) (1 / v) P.natDegree P le_rfl
  rw [invOf_eq_inv, one_div, inv_inv] at this
  simp only [eval₂_id] at this
  rw [one_div, ← this, mul_left_comm, ← mul_pow, mul_inv_cancel₀ hv, one_pow, mul_one]

theorem reflect_eval_zero (P : ℂ[X]) : (P.reflect P.natDegree).eval 0 = P.leadingCoeff := by
  rw [← coeff_zero_eq_eval_zero, coeff_reflect, revAt_le (Nat.zero_le _), Nat.sub_zero]; rfl

/-- **Normal form at infinity.**  For `P` of degree `n ≥ 1` there is `h`, holomorphic near `0`
with `h(0) = 0`, `h'(0) ≠ 0`, such that `P(1/v) · h(v)^n = 1` for small `v ≠ 0`. -/
theorem exists_infinity_root {P : ℂ[X]} (hn : 0 < P.natDegree) :
    ∃ h : ℂ → ℂ, ∃ ε > 0,
      (∀ v ∈ ball (0 : ℂ) ε, v ≠ 0 → P.eval (1 / v) * h v ^ P.natDegree = 1) ∧
      h 0 = 0 ∧ DifferentiableOn ℂ h (ball 0 ε) ∧ deriv h 0 ≠ 0 := by
  set n := P.natDegree
  set Q := P.reflect n
  have hP0 : P ≠ 0 := by rintro rfl; simp [n] at hn
  have hQ0 : Q.eval 0 ≠ 0 := by rw [reflect_eval_zero]; exact leadingCoeff_ne_zero.2 hP0
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (Q.eval 0)⁻¹ hn
  have hc0 : c ≠ 0 := by
    rintro rfl; rw [zero_pow hn.ne'] at hc; exact inv_ne_zero hQ0 hc.symm
  set u : ℂ → ℂ := fun v => Q.eval v / Q.eval 0
  have hu_cont : ContinuousAt u 0 := (Q.continuous.continuousAt).div_const _
  have hua : u 0 = 1 := div_self hQ0
  obtain ⟨ε, hε, hεu⟩ := Metric.continuousAt_iff.1 hu_cont 1 one_pos
  have hslit : ∀ v ∈ ball (0 : ℂ) ε, u v ∈ slitPlane := by
    intro v hv
    have := hεu (mem_ball.1 hv)
    rw [hua, dist_eq_norm] at this
    simpa using mem_slitPlane_of_norm_lt_one this
  have hu0 : ∀ v ∈ ball (0 : ℂ) ε, u v ≠ 0 := fun v hv => slitPlane_ne_zero (hslit v hv)
  set G : ℂ → ℂ := fun v => c * exp (-(log (u v)) / n)
  refine ⟨fun v => v * G v, ε, hε, fun v hv hv0 => ?_, by simp, ?_, ?_⟩
  · have hGn : G v ^ n = (Q.eval 0)⁻¹ / u v := by
      simp only [G, mul_pow, ← Complex.exp_nat_mul, hc]
      rw [mul_div_cancel₀ _ (by exact_mod_cast hn.ne'), exp_neg, exp_log (hu0 v hv), div_eq_mul_inv]
    have hQv : Q.eval v = v ^ n * P.eval (1 / v) := reflect_eval P hv0
    have huv : u v = Q.eval v / Q.eval 0 := rfl
    rw [mul_pow, hGn, huv]
    have hQne : Q.eval v ≠ 0 := by
      intro h; apply hu0 v hv; rw [huv, h, zero_div]
    rw [hQv] at hQne ⊢
    have hPv : P.eval (1 / v) ≠ 0 := right_ne_zero_of_mul hQne
    field_simp
  · intro v hv
    have h1 : DifferentiableAt ℂ u v := (Q.differentiable v).div_const _
    exact (differentiableAt_id.mul ((((differentiableAt_log (hslit v hv)).comp v h1).neg.div_const
      _).cexp.const_mul c)).differentiableWithinAt
  · have hGd : DifferentiableAt ℂ G 0 := by
      have h1 : DifferentiableAt ℂ u 0 := (Q.differentiable 0).div_const _
      exact (((differentiableAt_log (hslit 0 (mem_ball_self hε))).comp 0 h1).neg.div_const
        _).cexp.const_mul c
    have hd : HasDerivAt (fun v => v * G v) (1 * G 0 + 0 * deriv G 0) 0 :=
      (hasDerivAt_id 0).mul hGd.hasDerivAt
    rw [hd.deriv, zero_mul, add_zero, one_mul]
    simp [G, hua, hc0]

/-- Local inverse of a holomorphic map with nonvanishing derivative, vanishing at `a`. -/
theorem exists_local_inverse {h : ℂ → ℂ} {a : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hdiff : DifferentiableOn ℂ h (ball a ε)) (ha : h a = 0) (hder : deriv h a ≠ 0) :
    ∃ δ > 0, ∃ V : Set ℂ, ∃ g : ℂ → ℂ, V ⊆ ball a ε ∧ a ∈ V ∧
      (∀ z ∈ V, h z ∈ ball (0 : ℂ) δ) ∧ (∀ u ∈ ball (0 : ℂ) δ, g u ∈ V) ∧
      (∀ z ∈ V, g (h z) = z) ∧ (∀ u ∈ ball (0 : ℂ) δ, h (g u) = u) ∧
      ContinuousOn g (ball 0 δ) := by
  have han : AnalyticAt ℂ h a := hdiff.analyticAt (ball_mem_nhds a hε)
  have hs := han.hasStrictDerivAt
  let φ := (hs.hasStrictFDerivAt_equiv hder).toOpenPartialHomeomorph h
  have hφ : (φ : ℂ → ℂ) = h := HasStrictFDerivAt.toOpenPartialHomeomorph_coe _
  have haφ : a ∈ φ.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  set S := φ.source ∩ ball a ε
  have hSo : IsOpen S := φ.open_source.inter isOpen_ball
  have hSs : S ⊆ φ.source := inter_subset_left
  have himo : IsOpen (φ '' S) := φ.isOpen_image_of_subset_source hSo hSs
  have h0 : (0 : ℂ) ∈ φ '' S := ⟨a, ⟨haφ, mem_ball_self hε⟩, by rw [hφ, ha]⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 himo 0 h0
  have hbt : ball (0 : ℂ) δ ⊆ φ.target := fun u hu => by
    obtain ⟨z, hz, rfl⟩ := hball hu
    exact φ.map_source (hSs hz)
  refine ⟨δ, hδ, S ∩ h ⁻¹' ball 0 δ, φ.symm, fun z hz => hz.1.2,
    ⟨⟨haφ, mem_ball_self hε⟩, by simp [ha, hδ]⟩, fun z hz => hz.2, ?_, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨z, hz, rfl⟩ := hball hu
    have : φ.symm (φ z) = z := φ.left_inv (hSs hz)
    refine ⟨by rw [this]; exact hz, ?_⟩
    rw [mem_preimage, this, ← hφ]; exact hu
  · intro z hz; rw [← hφ]; exact φ.left_inv (hSs hz.1)
  · intro u hu; rw [← hφ]; exact φ.right_inv (hbt hu)
  · exact φ.continuousOn_symm.mono hbt

/-- **Monodromy around infinity.**  For a polynomial `P` of degree `n ≥ 1` and every sufficiently
large `R`, the circle `t ↦ R e^{2π i t}` avoids the critical values of `P`, and its monodromy on the
fibre over `R` is an `n`-cycle: some labelling `Fin n ≃` fibre conjugates it to `finRotate n`. -/
theorem infinity_monodromy {P : ℂ[X]} (hn : 0 < P.natDegree) :
    ∃ R0 > 0, ∀ R : ℝ, R0 < R → ∃ hcirc : ∀ t, circ 0 R t ∉ critVals P,
      ∃ E : Fin P.natDegree ≃ proj P ⁻¹' {basePt 0 R hcirc},
        ∀ j, monodromyPerm P (Path.Homotopic.Quotient.mk (circleLoop 0 R hcirc)) (E j) =
          E (finRotate _ j) := by
  classical
  set n := P.natDegree with hndef
  have hP : 0 < P.degree := natDegree_pos_iff_degree_pos.1 hn
  obtain ⟨h, ε, hε, hnorm, h0, hdiff, hder⟩ := exists_infinity_root hn
  obtain ⟨δ, hδ, V, g, hVsub, h0V, hmaps, gmaps, gh, hg, gcont⟩ :=
    exists_local_inverse hε hdiff h0 hder
  obtain ⟨M, hM⟩ := ((critVals_finite hP).image norm).bddAbove
  refine ⟨max (|M| + 1) (1 / δ ^ n), lt_max_of_lt_left (by positivity), fun R hR => ?_⟩
  have hR1 : |M| + 1 < R := lt_of_le_of_lt (le_max_left _ _) hR
  have hR2 : 1 / δ ^ n < R := lt_of_le_of_lt (le_max_right _ _) hR
  have hRpos : 0 < R := by linarith [abs_nonneg M]
  have hnormc : ∀ t, ‖circ 0 R t‖ = R := fun t => by
    rw [circ, zero_add, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos,
      show 2 * π * I * t = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, mul_one]
  have hcirc : ∀ t, circ 0 R t ∉ critVals P := by
    intro t hc
    have := hM ⟨_, hc, rfl⟩
    rw [hnormc] at this
    linarith [le_abs_self M]
  refine ⟨hcirc, ?_⟩
  set ω : ℂ := exp (-(2 * π * I / n))
  have hω : IsPrimitiveRoot ω n := by
    have := (isPrimitiveRoot_exp n hn.ne').inv
    simpa [ω, ← Complex.exp_neg] using this
  obtain ⟨u0, hu0⟩ := IsAlgClosed.exists_pow_nat_eq ((1 / R : ℝ) : ℂ) hn
  have hRδ : 1 / R < δ ^ n := by
    rw [div_lt_iff₀ hRpos]; rw [div_lt_iff₀ (pow_pos hδ n)] at hR2; linarith
  have hu0n : ‖u0‖ < δ := norm_lt_of_pow_eq hδ (by positivity) hRδ hu0
  have hu00 : u0 ≠ 0 := by
    rintro rfl; rw [zero_pow hn.ne'] at hu0
    have : (1 / R : ℝ) = 0 := by exact_mod_cast hu0.symm
    simp [hRpos.ne'] at this
  have hball : ∀ (x : ℂ), ‖x‖ = 1 → u0 * x ∈ ball (0 : ℂ) δ := fun x hx => by
    rw [mem_ball_zero_iff, norm_mul, hx, mul_one]; exact hu0n
  have hωn : ∀ j : ℕ, ‖ω ^ j‖ = 1 := fun j => by
    rw [norm_pow, hω.norm'_eq_one hn.ne', one_pow]
  have hgne : ∀ (x : ℂ), ‖x‖ = 1 → g (u0 * x) ≠ 0 := fun x hx hz => by
    have := hg _ (hball x hx)
    rw [hz, h0] at this
    exact mul_ne_zero hu00 (by rintro rfl; simp at hx) this.symm
  have heval : ∀ (x : ℂ), ‖x‖ = 1 → P.eval (1 / g (u0 * x)) = 1 / (u0 * x) ^ n := fun x hx => by
    have h1 := hnorm _ (hVsub (gmaps _ (hball x hx))) (hgne x hx)
    rw [hg _ (hball x hx)] at h1
    have h2 : (u0 * x) ^ n ≠ 0 := pow_ne_zero _ (mul_ne_zero hu00 (by rintro rfl; simp at hx))
    field_simp
    exact h1
  have hval : ∀ j : ℕ, P.eval (1 / g (u0 * ω ^ j)) = circ 0 R 0 := fun j => by
    rw [heval _ (hωn j), mul_pow, ← pow_mul, mul_comm j, pow_mul, hω.pow_eq_one, one_pow,
      mul_one, hu0, circ_zero, zero_add]
    push_cast; field_simp
  have hmem : ∀ j : ℕ, 1 / g (u0 * ω ^ j) ∈ P.eval ⁻¹' (critVals P)ᶜ := fun j => by
    simp only [mem_preimage, hval]; exact hcirc 0
  let F : Fin n → proj P ⁻¹' {basePt 0 R hcirc} := fun j =>
    ⟨⟨1 / g (u0 * ω ^ (j : ℕ)), hmem _⟩, Subtype.ext (hval _)⟩
  have hinj : Function.Injective F := by
    intro i j hij
    have h1 : 1 / g (u0 * ω ^ (i : ℕ)) = 1 / g (u0 * ω ^ (j : ℕ)) := congrArg (fun e => e.1.1) hij
    rw [one_div, one_div, inv_inj] at h1
    have h2 := congrArg h h1
    rw [hg _ (hball _ (hωn _)), hg _ (hball _ (hωn _))] at h2
    exact Fin.ext (hω.pow_inj i.2 j.2 (mul_left_cancel₀ hu00 h2))
  have hcardF := card_fibre hP (basePt 0 R hcirc)
  haveI : Finite (proj P ⁻¹' {basePt 0 R hcirc}) := by
    apply Nat.finite_of_card_ne_zero; rw [hcardF]; exact hn.ne'
  have hbij : Function.Bijective F :=
    hinj.bijective_of_nat_card_le (by rw [hcardF, Nat.card_eq_fintype_card, Fintype.card_fin])
  refine ⟨Equiv.ofBijective F hbij, fun j => ?_⟩
  change monodromyPerm P _ (F j) = F (finRotate n j)
  -- the explicit lift
  let v : ℝ → ℂ := fun t => u0 * (ω ^ (j : ℕ) * exp (-(2 * π * I * t / n)))
  have hvn : ∀ t : ℝ, ‖ω ^ (j : ℕ) * exp (-(2 * π * I * t / n))‖ = 1 := fun t => by
    rw [norm_mul, hωn, one_mul,
      show -(2 * π * I * t / n) = ((-(2 * π * t / n) : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I]
  have hev : ∀ t : ℝ, P.eval (1 / g (v t)) = circ 0 R t := fun t => by
    have hkc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [heval _ (hvn t), mul_pow, mul_pow, ← pow_mul, mul_comm (j : ℕ), pow_mul, hω.pow_eq_one,
      one_pow, one_mul, ← Complex.exp_nat_mul, hu0, circ, zero_add]
    rw [show (n : ℂ) * -(2 * π * I * t / n) = -(2 * π * I * t) by field_simp, exp_neg]
    push_cast; field_simp
  have hvc : Continuous v := by unfold v; fun_prop
  have hc : Continuous (fun t : unitInterval => 1 / g (v t)) := by
    have hgc : Continuous (fun t : unitInterval => g (v t)) :=
      gcont.comp_continuous (hvc.comp continuous_subtype_val) (fun t => hball _ (hvn t))
    exact continuous_const.div hgc (fun t => hgne _ (hvn t))
  have hmem' : ∀ t : unitInterval, 1 / g (v t) ∈ P.eval ⁻¹' (critVals P)ᶜ := fun t => by
    simp only [mem_preimage, hev]; exact hcirc t
  let Γ : C(unitInterval, Total P) := ⟨fun t => ⟨1 / g (v t), hmem' t⟩, hc.subtype_mk hmem'⟩
  have hl : (isCoveringMap P).liftPath ((circleLoop 0 R hcirc : Path _ _) : C(unitInterval, Base P))
      (F j).1 ((circleLoop 0 R hcirc).source.trans (F j).2.symm) = Γ := by
    refine (((isCoveringMap P).eq_liftPath_iff' _).2 ⟨?_, ?_⟩).symm
    · funext t
      exact Subtype.ext (hev t)
    · apply Subtype.ext
      show 1 / g (v 0) = 1 / g (u0 * ω ^ (j : ℕ))
      simp [v]
  have key : v 1 = u0 * ω ^ ((finRotate n j : Fin n) : ℕ) := by
    rw [finRotate_val hn, pow_mod_eq hω.pow_eq_one, pow_succ]
    simp only [v, ω]
    push_cast
    rw [mul_one]
  have hF : ((F (finRotate n j)).1 : ℂ) = 1 / g (u0 * ω ^ ((finRotate n j : Fin n) : ℕ)) := rfl
  apply Subtype.ext; apply Subtype.ext
  show ((isCoveringMap P).liftPath _ (F j).1 _ 1).1 = _
  rw [hl, hF, ← key]
  rfl

end InfinityMonodromy
