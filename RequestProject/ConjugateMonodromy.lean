module

public import RequestProject.Degree7Monodromy

/-!
# Transport of monodromy along a morphism of coverings

If `Φ : E → E'` and `φ : X → X'` are continuous with `p' ∘ Φ = φ ∘ p` for coverings `p, p'`, then
lifting commutes with `Φ`: the monodromy of `p'` along `φ ∘ γ`, applied to `Φ e`, equals `Φ` of the
monodromy of `p` along `γ` applied to `e`.
-/

@[expose] public section

open Set

noncomputable section

namespace CoverTransport

variable {E X E' X' : Type*} [TopologicalSpace E] [TopologicalSpace X] [TopologicalSpace E']
  [TopologicalSpace X'] {p : E → X} {p' : E' → X'}

/-- **Monodromy is natural with respect to morphisms of coverings.** -/
theorem monodromy_map_mk (cov : IsCoveringMap p) (cov' : IsCoveringMap p') {Φ : E → E'}
    (hΦ : Continuous Φ) {φ : X → X'} (hφ : Continuous φ) (hcomm : ∀ e, p' (Φ e) = φ (p e))
    {x y : X} (γ : Path x y) (e : p ⁻¹' {x}) (e' : p' ⁻¹' {φ x}) (he' : (e' : E') = Φ e) :
    (cov'.monodromy (Path.Homotopic.Quotient.mk (γ.map hφ)) e' : E') =
      Φ (cov.monodromy (Path.Homotopic.Quotient.mk γ) e) := by
  show cov'.liftPath (γ.map hφ : C(unitInterval, X')) e' _ 1 =
    Φ (cov.liftPath (γ : C(unitInterval, X)) e _ 1)
  have key : (⟨Φ, hΦ⟩ : C(E, E')).comp (cov.liftPath (γ : C(unitInterval, X)) e
      (γ.source.trans e.2.symm)) =
      cov'.liftPath (γ.map hφ : C(unitInterval, X')) e'
        ((γ.map hφ).source.trans e'.2.symm) := by
    rw [cov'.eq_liftPath_iff']
    constructor
    · funext t
      simp only [Function.comp_apply, ContinuousMap.comp_apply, ContinuousMap.coe_mk,
        ContinuousMap.coe_coe, Path.map_coe, hcomm]
      congr 1
      exact congr_fun (cov.liftPath_lifts _ _ _) t
    · simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, cov.liftPath_zero, he']
  rw [← key]
  rfl

end CoverTransport

namespace ConjMonodromy

open Polynomial PolyCover MonodromyRelation LocalMonodromy ComplexConjugate Complex
open scoped Real

/-! ### Complex conjugation as a morphism of polynomial coverings -/

section ConjCover

variable {P Q : ℂ[X]} (hconj : ∀ z, Q.eval (conj z) = conj (P.eval z))
  (hcv : ∀ z, z ∈ critVals Q ↔ conj z ∈ critVals P)

include hconj in
theorem evalP_conj (z : ℂ) : P.eval (conj z) = conj (Q.eval z) := by
  have := hconj (conj z)
  rw [conj_conj] at this
  rw [this, conj_conj]

/-- Complex conjugation `ℂ \ critVals Q → ℂ \ critVals P`. -/
def conjBase (x : Base Q) : Base P := ⟨conj x.1, fun h => x.2 ((hcv _).2 h)⟩

include hcv in
theorem continuous_conjBase : Continuous (conjBase hcv) :=
  (Complex.continuous_conj.comp continuous_subtype_val).subtype_mk _

/-- Complex conjugation `Q⁻¹(ℂ \ critVals Q) → P⁻¹(ℂ \ critVals P)`. -/
def conjTotal (e : Total Q) : Total P :=
  ⟨conj e.1, fun h => e.2 ((hcv _).2 (by rw [← evalP_conj hconj]; exact h))⟩

include hconj hcv in
theorem continuous_conjTotal : Continuous (conjTotal hconj hcv) :=
  (Complex.continuous_conj.comp continuous_subtype_val).subtype_mk _

include hconj hcv in
theorem proj_conjTotal (e : Total Q) :
    proj P (conjTotal hconj hcv e) = conjBase hcv (proj Q e) :=
  Subtype.ext (evalP_conj hconj e.1)

/-- Conjugation identifies the fibre of `Q` over `x` with the fibre of `P` over `x̄`. -/
def fibreConj (x : Base Q) : proj Q ⁻¹' {x} ≃ proj P ⁻¹' {conjBase hcv x} where
  toFun e := ⟨conjTotal hconj hcv e.1, by
    rw [mem_preimage, proj_conjTotal, show proj Q e.1 = x from e.2]; rfl⟩
  invFun f := ⟨⟨conj f.1.1, fun h => f.1.2 (by
      have h' := (hcv _).1 h
      simp only [hconj, conj_conj] at h'
      exact h')⟩, by
    have hf : P.eval f.1.1 = conj x.1 := congrArg Subtype.val f.2
    apply Subtype.ext
    show Q.eval (conj f.1.1) = x.1
    rw [hconj, hf, conj_conj]⟩
  left_inv e := Subtype.ext (Subtype.ext (conj_conj _))
  right_inv f := Subtype.ext (Subtype.ext (conj_conj _))

/-- **Monodromy of `Q` along `δ` is the monodromy of `P` along `δ̄`**, transported by
conjugation of fibres. -/
theorem monodromyPerm_conj {x : Base Q} (δ : Path x x) :
    monodromyPerm Q (Path.Homotopic.Quotient.mk δ) =
      (fibreConj hconj hcv x).symm.permCongr
        (monodromyPerm P (Path.Homotopic.Quotient.mk (δ.map (continuous_conjBase hcv)))) := by
  refine Equiv.ext fun e => ?_
  rw [Equiv.permCongr_apply, Equiv.symm_symm, Equiv.eq_symm_apply]
  apply Subtype.ext
  rw [monodromyPerm_apply, monodromyPerm_apply]
  exact (CoverTransport.monodromy_map_mk (isCoveringMap Q) (isCoveringMap P)
    (continuous_conjTotal hconj hcv) (continuous_conjBase hcv) (proj_conjTotal hconj hcv) δ e
    _ rfl).symm

/-! ### Conjugating the standard generators -/

theorem conj_upper {w0 : ℂ} (hw : conj w0 = w0) (r t : ℝ) :
    conj (upper w0 r t) = lower w0 r (1 - t) := by
  simp only [upper, lower, map_add, map_mul, conj_ofReal, ← exp_conj, conj_I, hw]
  congr 2
  rw [show (π : ℂ) * I * (1 + ((1 - t : ℝ) : ℂ)) = π * -I * t + 2 * π * I by push_cast; ring,
    exp_add, exp_two_pi_mul_I, mul_one]

theorem conj_lower {w0 : ℂ} (hw : conj w0 = w0) (r t : ℝ) :
    conj (lower w0 r t) = upper w0 r (1 - t) := by
  simp only [upper, lower, map_add, map_mul, conj_ofReal, ← exp_conj, conj_I, hw, map_one]
  congr 2
  rw [show (π : ℂ) * -I * (1 + (t : ℂ)) = π * I * ((1 - t : ℝ) : ℂ) + (-1 : ℤ) * (2 * π * I) by
    push_cast; ring, exp_add, exp_int_mul_two_pi_mul_I, mul_one]

theorem conj_seg (a b t : ℝ) : conj (seg a b t) = seg a b t := by
  simp [seg, conj_ofReal]

theorem monodromyPerm_refl {R : ℂ[X]} (x : Base R) :
    monodromyPerm R (Path.Homotopic.Quotient.refl x) = 1 := by
  refine Equiv.ext fun e => ?_
  rw [monodromyPerm_apply, (isCoveringMap R).monodromy_refl]
  rfl

theorem monodromyPerm_symm {R : ℂ[X]} {x : Base R} (γ : Path.Homotopic.Quotient x x) :
    monodromyPerm R γ.symm = (monodromyPerm R γ)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← monodromyPerm_trans, Path.Homotopic.Quotient.trans_symm,
    monodromyPerm_refl]

theorem monodromyPerm_conj_aux {R : ℂ[X]} {x : Base R} (a b : Path.Homotopic.Quotient x x) :
    (monodromyPerm R a)⁻¹ * (monodromyPerm R b)⁻¹ * monodromyPerm R a =
      monodromyPerm R (a.trans (b.symm.trans a.symm)) := by
  rw [monodromyPerm_trans, monodromyPerm_trans, monodromyPerm_symm, monodromyPerm_symm]

include hconj hcv in
/-- **Complex conjugation acts on the standard generators by `γ₀ ↦ γ₀⁻¹`,
`γ₁ ↦ γ₀ γ₁⁻¹ γ₀⁻¹`.**  Consequently, if `γ₀, γ₁` (for `P`) and `γ₀', γ₁'` (for `Q`, with
`Q(z̄) = conj P(z)`) are the standard generators at `-r`, the monodromy of `Q` along `(γ₀', γ₁')` is
conjugate, by the conjugation of fibres, to `(x⁻¹, x⁻¹ y⁻¹ x)` where `x, y` is the monodromy of `P`
along `(γ₀, γ₁)`. -/
theorem std_conj {r : ℝ} {AP : Base P} {AQ : Base Q} {γ0P γ1P : Path.Homotopic.Quotient AP AP}
    {γ0Q γ1Q : Path.Homotopic.Quotient AQ AQ} (hP : IsStdLoops r γ0P γ1P)
    (hQ : IsStdLoops r γ0Q γ1Q) :
    ∃ F : proj Q ⁻¹' {AQ} ≃ proj P ⁻¹' {AP},
      monodromyPerm Q γ0Q = F.symm.permCongr (monodromyPerm P γ0P)⁻¹ ∧
      monodromyPerm Q γ1Q = F.symm.permCongr
        ((monodromyPerm P γ0P)⁻¹ * (monodromyPerm P γ1P)⁻¹ * monodromyPerm P γ0P) := by
  obtain ⟨BP, CP, DP, U0P, L0P, U1P, L1P, sP, hU0P, hL0P, hU1P, hL1P, hsP, rfl, rfl⟩ := hP
  obtain ⟨BQ, CQ, DQ, U0Q, L0Q, U1Q, L1Q, sQ, hU0Q, hL0Q, hU1Q, hL1Q, hsQ, rfl, rfl⟩ := hQ
  have h0 : conj (0 : ℂ) = 0 := map_zero _
  have h1 : conj (1 : ℂ) = 1 := map_one _
  -- the end points correspond under conjugation
  obtain rfl : AP = conjBase hcv AQ := by
    apply Subtype.ext
    show (AP : ℂ) = conj (AQ : ℂ)
    rw [← congrArg Subtype.val U0P.target, ← congrArg Subtype.val U0Q.target, hU0P, hU0Q]
    simp [upper_one, conj_ofReal]
  obtain rfl : BP = conjBase hcv BQ := by
    apply Subtype.ext
    show (BP : ℂ) = conj (BQ : ℂ)
    rw [← congrArg Subtype.val U0P.source, ← congrArg Subtype.val U0Q.source, hU0P, hU0Q]
    simp [upper_zero, conj_ofReal]
  obtain rfl : CP = conjBase hcv CQ := by
    apply Subtype.ext
    show (CP : ℂ) = conj (CQ : ℂ)
    rw [← congrArg Subtype.val U1P.target, ← congrArg Subtype.val U1Q.target, hU1P, hU1Q]
    simp [upper_one, conj_ofReal]
  obtain rfl : DP = conjBase hcv DQ := by
    apply Subtype.ext
    show (DP : ℂ) = conj (DQ : ℂ)
    rw [← congrArg Subtype.val U1P.source, ← congrArg Subtype.val U1Q.source, hU1P, hU1Q]
    simp [upper_zero, conj_ofReal]
  have hφ := continuous_conjBase hcv
  have eU0 : U0Q.map hφ = L0P.symm := by
    ext t
    show conj (U0Q t : ℂ) = (L0P (unitInterval.symm t) : ℂ)
    rw [hU0Q, hL0P, conj_upper h0, unitInterval.coe_symm_eq]
  have eL0 : L0Q.map hφ = U0P.symm := by
    ext t
    show conj (L0Q t : ℂ) = (U0P (unitInterval.symm t) : ℂ)
    rw [hL0Q, hU0P, conj_lower h0, unitInterval.coe_symm_eq]
  have eU1 : U1Q.map hφ = L1P.symm := by
    ext t
    show conj (U1Q t : ℂ) = (L1P (unitInterval.symm t) : ℂ)
    rw [hU1Q, hL1P, conj_upper h1, unitInterval.coe_symm_eq]
  have eL1 : L1Q.map hφ = U1P.symm := by
    ext t
    show conj (L1Q t : ℂ) = (U1P (unitInterval.symm t) : ℂ)
    rw [hL1Q, hU1P, conj_lower h1, unitInterval.coe_symm_eq]
  have es : sQ.map hφ = sP := by
    ext t
    show conj (sQ t : ℂ) = (sP t : ℂ)
    rw [hsQ, hsP, show (1 : ℂ) - (r : ℂ) = ((1 - r : ℝ) : ℂ) by push_cast; ring, conj_seg]
  refine ⟨fibreConj hconj hcv AQ, ?_, ?_⟩
  · rw [← Path.Homotopic.Quotient.mk_trans, monodromyPerm_conj hconj hcv, Path.map_trans, eU0,
      eL0, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm,
      Path.Homotopic.Quotient.mk_symm, ← quot_symm_trans, monodromyPerm_symm]
  · rw [monodromyPerm_conj_aux]
    simp only [← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_trans]
    rw [monodromyPerm_conj hconj hcv]
    congr 2
    simp only [Path.map_trans, ← Path.map_symm, eU0, eU1, eL1, es,
      Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm, quot_symm_trans,
      quot_symm_symm, Path.Homotopic.Quotient.trans_assoc, quot_cancel]

end ConjCover

end ConjMonodromy
