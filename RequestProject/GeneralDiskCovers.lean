module

public import Mathlib
public import RequestProject.LemniscateBoundary
public import RequestProject.Coalescence
public import RequestProject.PolynomialCover

/-!
# Lemma 3.2.1 (general disk covers) for an arbitrary monic polynomial

Let `p` be a monic complex polynomial of degree `n ≥ 1`, and put (paper, (3.2))
`q_ε(z) = u_ε + δ_ε p(z)` with `u_ε = ε`, `v_ε = λ_* ε`, `δ_ε = v_ε - u_ε = (λ_* - 1) ε`, and
`Y_ε = q_ε⁻¹(𝔻)` (the **full** preimage).

* `coverDomain_geometry`: for all sufficiently small `ε > 0`, `Y_ε` is a bounded, simply connected
  (indeed star-shaped) domain whose boundary is a real-analytic Jordan curve.  No hypothesis on the
  critical values or the monodromy of `p` is needed.
* `lemma_3_2_1`: if moreover the finite critical values of `p` are exactly `0` and `1`, then for
  all sufficiently small `ε > 0` the restriction `q_ε : Y_ε → 𝔻` is a proper holomorphic map of
  degree `n` (every `w ∈ 𝔻` has exactly `n` preimages in `Y_ε` counted with multiplicity, and
  exactly `n` distinct preimages when `w` is not a critical value), and its critical values are
  exactly `u_ε = ε` and `v_ε = λ_* ε`.

The proof uses the near-monomial normalisation: with `τ_ε^n = (λ_* - 1) ε`, the rescaled
polynomial `Q_ε(w) = q_ε(w / τ_ε)` has the form `wⁿ + ∑_{k<n} q_k w^k` with coefficients tending to
`0`, so `Q_ε⁻¹(𝔻)` is star-shaped with real-analytic Jordan boundary
(`SteklovCoalescence.nearDisk_preimage`, `SteklovCoalescence.isRealAnalyticJordanBoundary_preimage`),
and `Y_ε = τ_ε⁻¹ · Q_ε⁻¹(𝔻)`.  The Riemann–Hurwitz/monodromy argument of the paper is therefore not
needed for this lemma.  (The *construction* of polynomials `p_j` with prescribed monodromy, which
precedes the lemma in the paper, is a separate matter; see `INVENTORY.md`.)
-/

@[expose] public section

open Set Filter Topology Metric Complex PlaneDomain Polynomial
open SteklovCoalescence SteklovCritical

noncomputable section

namespace SteklovDiskCovers

/-- The paper's polynomial `q_ε = u_ε + δ_ε p = ε + (λ_* - 1) ε p`. -/
def coverPoly (p : ℂ[X]) (ε : ℝ) : ℂ[X] := C ((lamStar - 1) * (ε : ℂ)) * p + C (ε : ℂ)

/-- The full preimage `Y_ε = q_ε⁻¹(𝔻)`. -/
def coverDomain (p : ℂ[X]) (ε : ℝ) : Set ℂ := (fun z => (coverPoly p ε).eval z) ⁻¹' ball 0 1

lemma eval_coverPoly (p : ℂ[X]) (ε : ℝ) (z : ℂ) :
    (coverPoly p ε).eval z = ε + (lamStar - 1) * ε * p.eval z := by
  simp [coverPoly]; ring

/-- A choice of `τ_ε` with `τ_ε^n = (λ_* - 1) ε`. -/
def rootScale (n : ℕ) (ε : ℝ) : ℂ := ((lamStar - 1) * (ε : ℂ)) ^ ((n : ℂ)⁻¹)

lemma rootScale_pow {n : ℕ} (hn : n ≠ 0) (ε : ℝ) : rootScale n ε ^ n = (lamStar - 1) * ε :=
  Complex.cpow_nat_inv_pow _ hn

lemma rootScale_ne_zero {n : ℕ} (hn : n ≠ 0) {ε : ℝ} (hε : ε ≠ 0) : rootScale n ε ≠ 0 := by
  intro h
  have := rootScale_pow hn ε
  rw [h, zero_pow hn] at this
  exact mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast hε) this.symm

lemma coverDomain_eq_image (p : ℂ[X]) {τ : ℝ → ℂ} {ε : ℝ} (hτ : τ ε ≠ 0) :
    coverDomain p ε = (fun w => (τ ε)⁻¹ * w) '' (paperQ p τ ε ⁻¹' ball 0 1) := by
  ext z
  simp only [coverDomain, mem_preimage, mem_image]
  constructor
  · intro hz
    refine ⟨τ ε * z, ?_, by field_simp⟩
    rw [paperQ, mul_div_cancel_left₀ _ hτ, ← eval_coverPoly]
    exact hz
  · rintro ⟨w, hw, rfl⟩
    rw [paperQ] at hw
    rw [eval_coverPoly, ← div_eq_inv_mul]
    exact hw

/-- Real-analytic Jordan boundaries are preserved by `w ↦ c w`, `c ≠ 0`. -/
lemma isRealAnalyticJordanBoundary_mul {Ω : Set ℂ} (h : IsRealAnalyticJordanBoundary Ω) {c : ℂ}
    (hc : c ≠ 0) : IsRealAnalyticJordanBoundary ((fun w => c * w) '' Ω) := by
  obtain ⟨γ, hA, hP, hI, hD, hR⟩ := h
  refine ⟨fun t => c * γ t, fun t _ => analyticAt_const.mul (hA t trivial), ?_, ?_, ?_, ?_⟩
  · intro t; simp only [hP t]
  · intro a ha b hb hab
    exact hI ha hb (mul_left_cancel₀ hc hab)
  · intro t
    have hd : HasDerivAt (fun t => c * γ t) (c * deriv γ t) t :=
      ((hA t trivial).differentiableAt.hasDerivAt).const_mul c
    rw [hd.deriv]
    exact mul_ne_zero hc (hD t)
  · have himg := (Homeomorph.mulLeft₀ c hc).image_frontier Ω
    simp only [Homeomorph.coe_mulLeft₀] at himg
    rw [← himg, ← hR, ← range_comp]
    rfl

/-- **Geometry of `Y_ε` (first part of Lemma 3.2.1)**, for every monic `p` of degree `n ≥ 1`. -/
theorem coverDomain_geometry {p : ℂ[X]} (hp : p.Monic) (hn : 1 ≤ p.natDegree) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsDomain (coverDomain p ε) ∧
      Bornology.IsBounded (coverDomain p ε) ∧ StarConvex ℝ 0 (coverDomain p ε) ∧
      SimplyConnectedSpace (coverDomain p ε) ∧ IsRealAnalyticJordanBoundary (coverDomain p ε) := by
  set n := p.natDegree with hndef
  have hn0 : n ≠ 0 := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  set s : ℝ := 1 / (4 * n * 16 ^ n) with hs_def
  have hs0 : 0 < s := by positivity
  have hs : 3 * n * s * 16 ^ n < 1 := by
    rw [hs_def]
    have : (0 : ℝ) < 4 * n * 16 ^ n := by positivity
    field_simp
    nlinarith
  filter_upwards [eventually_coeff_small (paperCoeff_tendsto (P := p) (rootScale_pow hn0)) hs0,
    self_mem_nhdsWithin] with ε hε hpos
  have hpos' : (0 : ℝ) < ε := hpos
  have hτ := rootScale_ne_zero hn0 hpos'.ne'
  have hQ := paperQ_eq_polyQ hp hn rfl hpos'.ne' (rootScale_pow hn0 ε)
  obtain ⟨hVo, hVs, h0, hVb, -⟩ := nearDisk_preimage hε hs0.le hs hn
  have hVj := isRealAnalyticJordanBoundary_preimage hε hs hn
  rw [coverDomain_eq_image p hτ, hQ]
  set V := polyQ n (paperCoeff p (rootScale n) n ε) ⁻¹' ball 0 1
  set c := (rootScale n ε)⁻¹
  have hc : c ≠ 0 := inv_ne_zero hτ
  set hh := Homeomorph.mulLeft₀ c hc
  have himg : (fun w => c * w) '' V = hh '' V := rfl
  have hstar : StarConvex ℝ 0 ((fun w => c * w) '' V) := by
    have := hVs.is_linear_image (f := fun w : ℂ => c * w)
      ⟨fun x y => mul_add c x y, fun r x => by rw [Complex.real_smul, Complex.real_smul]; ring⟩
    simpa using this
  have hne : ((fun w => c * w) '' V).Nonempty := ⟨c * 0, 0, h0, rfl⟩
  refine ⟨⟨?_, ?_⟩, ?_, hstar, ?_, isRealAnalyticJordanBoundary_mul hVj hc⟩
  · rw [himg]; exact hh.isOpenMap V hVo
  · exact (hstar.isPathConnected (by simpa using (show (0:ℂ) ∈ (fun w => c * w) '' V from
      ⟨0, h0, by simp⟩))).isConnected
  · exact ((isBounded_ball.subset hVb).isCompact_closure.image
      (by fun_prop : Continuous fun w : ℂ => c * w)).isBounded.subset (image_mono subset_closure)
  · haveI := hstar.contractibleSpace hne
    exact SimplyConnectedSpace.ofContractible _

lemma natDegree_coverPoly {p : ℂ[X]} {ε : ℝ} (hε : ε ≠ 0) :
    (coverPoly p ε).natDegree = p.natDegree := by
  rw [coverPoly, natDegree_add_C, natDegree_C_mul]
  exact mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast hε)

lemma derivative_coverPoly (p : ℂ[X]) (ε : ℝ) :
    derivative (coverPoly p ε) = C ((lamStar - 1) * (ε : ℂ)) * derivative p := by
  simp [coverPoly]

lemma eval_derivative_coverPoly_eq_zero_iff (p : ℂ[X]) {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    (derivative (coverPoly p ε)).eval z = 0 ↔ (derivative p).eval z = 0 := by
  rw [derivative_coverPoly, eval_mul, eval_C]
  exact ⟨fun h => (mul_eq_zero.1 h).resolve_left
    (mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast hε)), fun h => by rw [h, mul_zero]⟩

/-- The critical values of `q_ε` are `u_ε = ε` and `v_ε = λ_* ε` when those of `p` are `0, 1`. -/
lemma critVals_coverPoly {p : ℂ[X]} (hcv : critVals p = {0, 1}) {ε : ℝ} (hε : ε ≠ 0) :
    critVals (coverPoly p ε) = {(ε : ℂ), lamStar * ε} := by
  have key : critVals (coverPoly p ε) =
      (fun a => (ε : ℂ) + (lamStar - 1) * ε * a) '' critVals p := by
    ext w
    simp only [critVals, mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨p.eval z, ⟨z, (eval_derivative_coverPoly_eq_zero_iff p hε z).1 hz, rfl⟩,
        (eval_coverPoly p ε z).symm⟩
    · rintro ⟨a, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨z, (eval_derivative_coverPoly_eq_zero_iff p hε z).2 hz, eval_coverPoly p ε z⟩
  rw [key, hcv, image_pair]
  have h1 : (ε : ℂ) + (lamStar - 1) * ε * 1 = lamStar * ε := by ring
  simp only [mul_zero, add_zero, h1]

lemma one_le_natDegree_of_critVals {p : ℂ[X]} (hp : p.Monic) (hcv : critVals p = {0, 1}) :
    1 ≤ p.natDegree := by
  by_contra h
  push_neg at h
  have h0 : p = 1 := hp.natDegree_eq_zero.1 (by omega)
  have : (0 : ℂ) ∈ critVals p := by rw [hcv]; exact mem_insert _ _
  obtain ⟨z, -, hz⟩ := this
  rw [h0] at hz
  simp at hz

/-- **Lemma 3.2.1 (general disk covers).**  Let `p` be a monic complex polynomial whose finite
critical values are exactly `0` and `1` (its degree `n = p.natDegree` is then `≥ 1`), and let
`q_ε = ε + (λ_* - 1) ε p`, `Y_ε = q_ε⁻¹(𝔻)`.  For all sufficiently small `ε > 0`:
* `Y_ε` is a bounded simply connected domain with real-analytic Jordan boundary;
* `q_ε : Y_ε → 𝔻` is holomorphic and proper (preimages of compact subsets of `𝔻` are compact);
* it has degree `n`: every `w ∈ 𝔻` has exactly `n` preimages counted with multiplicity, all in
  `Y_ε`, and exactly `n` distinct preimages in `Y_ε` if `w ∉ {ε, λ_* ε}`;
* its critical values (images of critical points in `Y_ε`) are exactly `u_ε = ε` and
  `v_ε = λ_* ε`. -/
theorem lemma_3_2_1 {p : ℂ[X]} (hp : p.Monic) (hcv : critVals p = {0, 1}) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IsDomain (coverDomain p ε) ∧ Bornology.IsBounded (coverDomain p ε) ∧
      SimplyConnectedSpace (coverDomain p ε) ∧ IsRealAnalyticJordanBoundary (coverDomain p ε) ∧
      Differentiable ℂ (fun z => (coverPoly p ε).eval z) ∧
      MapsTo (fun z => (coverPoly p ε).eval z) (coverDomain p ε) (ball 0 1) ∧
      (∀ K ⊆ ball (0 : ℂ) 1, IsCompact K →
        IsCompact (coverDomain p ε ∩ (fun z => (coverPoly p ε).eval z) ⁻¹' K)) ∧
      (∀ w ∈ ball (0 : ℂ) 1, (coverPoly p ε - C w).roots.card = p.natDegree ∧
        ∀ z ∈ (coverPoly p ε - C w).roots, z ∈ coverDomain p ε) ∧
      (∀ w ∈ ball (0 : ℂ) 1, w ∉ ({(ε : ℂ), lamStar * ε} : Set ℂ) →
        Nat.card {z // z ∈ coverDomain p ε ∧ (coverPoly p ε).eval z = w} = p.natDegree) ∧
      (fun z => (coverPoly p ε).eval z) ''
          {z | z ∈ coverDomain p ε ∧ (derivative (coverPoly p ε)).eval z = 0} =
        {(ε : ℂ), lamStar * ε} := by
  have hn := one_le_natDegree_of_critVals hp hcv
  filter_upwards [coverDomain_geometry hp hn, Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 3 by norm_num)]
    with ε hgeo hεI
  obtain ⟨hdom, hbd, -, hsc, hjor⟩ := hgeo
  obtain ⟨hε0, hε1⟩ := hεI
  have hε : ε ≠ 0 := hε0.ne'
  set q := coverPoly p ε with hqdef
  have hqdeg : q.natDegree = p.natDegree := natDegree_coverPoly hε
  have hqpos : 0 < q.degree := by
    rw [degree_eq_natDegree (by intro h; rw [h, natDegree_zero] at hqdeg; omega)]
    exact_mod_cast (show 0 < q.natDegree by omega)
  have hmemY : ∀ z, q.eval z ∈ ball (0 : ℂ) 1 → z ∈ coverDomain p ε := fun z h => h
  obtain ⟨hu, hv⟩ := branchValues_mem_disk hε0 hε1
  refine ⟨hdom, hbd, hsc, hjor, fun z => (Polynomial.differentiable q) z, fun z hz => hz,
    ?_, ?_, ?_, ?_⟩
  · intro K hK hKc
    have hsub : coverDomain p ε ∩ (fun z => q.eval z) ⁻¹' K = (fun z => q.eval z) ⁻¹' K := by
      ext z; exact ⟨fun h => h.2, fun h => ⟨hmemY z (hK h), h⟩⟩
    rw [hsub]
    refine isCompact_of_isClosed_isBounded (hKc.isClosed.preimage q.continuous) ?_
    exact hbd.subset fun z hz => hmemY z (hK hz)
  · intro w hw
    have hne : q - C w ≠ 0 := by
      intro h
      have := congrArg natDegree h
      rw [natDegree_sub_C, natDegree_zero] at this
      omega
    refine ⟨by rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_sub_C, hqdeg], fun z hz => ?_⟩
    rw [mem_roots hne, IsRoot, eval_sub, eval_C, sub_eq_zero] at hz
    exact hmemY z (by rw [hz]; exact hw)
  · intro w hw hwc
    have hcq := critVals_coverPoly hcv hε
    have hwb : w ∈ (critVals q)ᶜ := by rw [← hqdef, hcq] at *; exact hwc
    have h1 := PolyCover.card_fibre hqpos ⟨w, hwb⟩
    rw [Nat.card_congr (PolyCover.fibreEquiv ⟨w, hwb⟩), hqdeg] at h1
    rw [← h1]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun z =>
      ⟨fun h => h.2, fun h => ⟨hmemY z (by rw [h]; exact mem_ball_zero_iff.2 (by
        exact (mem_ball_zero_iff.1 hw))), h⟩⟩)
  · have hcq := critVals_coverPoly hcv hε
    rw [← hcq]
    ext w
    simp only [critVals, mem_image, mem_setOf_eq]
    constructor
    · rintro ⟨z, ⟨-, hz⟩, rfl⟩; exact ⟨z, hz, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z, ⟨hmemY z ?_, hz⟩, rfl⟩
      have : q.eval z ∈ critVals q := ⟨z, hz, rfl⟩
      rw [show critVals q = _ from hcq] at this
      rcases this with h | h
      · rw [h]; exact mem_ball_zero_iff.2 hu
      · rw [mem_singleton_iff.1 h]; exact mem_ball_zero_iff.2 hv

/-- Critical values are invariant under a linear change of variable `z ↦ a z`, `a ≠ 0`. -/
lemma critVals_comp_mul {R : ℂ[X]} {a : ℂ} (ha : a ≠ 0) :
    critVals (R.comp (C a * X)) = critVals R := by
  ext w
  simp only [critVals, mem_image, mem_setOf_eq, derivative_comp, eval_mul, eval_comp,
    derivative_mul, derivative_C, derivative_X, zero_mul, zero_add, mul_one, eval_C, eval_X]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨a * z, (mul_eq_zero.1 hz).resolve_left ha, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z / a, ?_, ?_⟩
    · rw [mul_div_cancel₀ _ ha, hz, mul_zero]
    · rw [mul_div_cancel₀ _ ha]

/-- The monic degree-seven polynomials of the paper (`P = p_s(a ·)`, `a⁷ = -b_s`) have critical
values exactly `0` and `1`, so `lemma_3_2_1` applies to them. -/
theorem critVals_monicP {s a : ℂ} (hs : s ^ 2 = -7) (ha : a ^ 7 = -Degree7.bconst s) :
    critVals (Degree7.monicP s a) = {0, 1} := by
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [zero_pow (by norm_num)] at ha
    exact Degree7.bconst_ne_zero hs (neg_eq_zero.1 ha.symm)
  have hcomp : Degree7.monicP s a = (Degree7.pPoly s).comp (C a * X) := by
    apply Polynomial.funext
    intro z
    rw [Degree7.monicP_eval hs ha, eval_comp, Degree7.pPoly_eval]
    simp
  rw [hcomp, critVals_comp_mul ha0, Degree7.critVals_pPoly hs]

end SteklovDiskCovers
