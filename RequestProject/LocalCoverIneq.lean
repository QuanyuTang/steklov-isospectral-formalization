module

public import RequestProject.CoverInequivalence
public import RequestProject.MonodromyTransfer

/-!
# Local inequivalence of the two degree-seven polynomial coverings

`Degree7.covers_not_isomorphic` excludes a *global* isomorphism of the coverings `p_s`, `p_{-s}`.
Here we exclude a *local* one: there is no continuous injective map `h`, defined on an open set
containing `p_s⁻¹(closedBall 0 2)`, with `p_{-s} ∘ h = p_s` there (`no_local_iso`).  The standard
generating loops of `ℂ \ {0,1}` lie in `closedBall 0 2`, so such an `h` would intertwine their
monodromies (`monodromy_local`), contradicting the point/line computation.
-/

@[expose] public section

open Polynomial Set Equiv PolyCover LocalMonodromy MonodromyRelation MonodromyTriple CoverIneq

noncomputable section

namespace Degree7

variable {s : ℂ}

lemma trans_mem {X : Type*} [TopologicalSpace X] {a b c : X} (p : Path a b) (q : Path b c)
    (S : Set X) (hp : ∀ t, p t ∈ S) (hq : ∀ t, q t ∈ S) (t) : (p.trans q) t ∈ S := by
  rw [Path.trans_apply]; split_ifs <;> simp [hp, hq]

lemma symm_mem {X : Type*} [TopologicalSpace X] {a b : X} (p : Path a b)
    (S : Set X) (hp : ∀ t, p t ∈ S) (t) : p.symm t ∈ S := by
  rw [Path.symm_apply]; exact hp _

lemma proj_coe' {P : ℂ[X]} (e : PolyCover.Total P) : ((proj P e : Base P) : ℂ) = P.eval (e : ℂ) :=
  rfl

lemma fibre_eval {P : ℂ[X]} {x : Base P} (e : proj P ⁻¹' {x}) :
    P.eval ((e : PolyCover.Total P) : ℂ) = (x : ℂ) := by
  rw [← proj_coe']; exact congrArg Subtype.val e.2

/-- An element of the fibre from a point with the right value. -/
def fibreMk {P : ℂ[X]} (x : Base P) (u : ℂ) (hu : P.eval u = (x : ℂ)) : proj P ⁻¹' {x} :=
  ⟨⟨u, by show P.eval u ∈ (critVals P)ᶜ; rw [hu]; exact x.2⟩,
    Subtype.ext (by rw [proj_coe']; exact hu)⟩

lemma fibreMk_coe {P : ℂ[X]} (x : Base P) (u : ℂ) (hu : P.eval u = (x : ℂ)) :
    ((fibreMk x u hu : PolyCover.Total P) : ℂ) = u := rfl

/-- **Local monodromy transfer.**  A continuous map `h` on an open set `U ⊇ p_s⁻¹(closedBall 0 M)`
with `p_{-s} ∘ h = p_s` on `U` intertwines the monodromies along every loop in `closedBall 0 M`. -/
theorem monodromy_local {P Q : ℂ[X]} (hcv : critVals P = critVals Q) {M : ℝ} {U : Set ℂ}
    (hU : IsOpen U) (hUM : ∀ u, ‖P.eval u‖ ≤ M → u ∈ U) {h : ℂ → ℂ} (hc : ContinuousOn h U)
    (hh : ∀ u ∈ U, Q.eval (h u) = P.eval u) {x : Base P}
    (γ : Path x x) (hγ : ∀ t, ‖(γ t : ℂ)‖ ≤ M)
    (F : proj P ⁻¹' {x} ≃ proj Q ⁻¹' {idBase hcv x})
    (hF : ∀ e, ((F e : PolyCover.Total Q) : ℂ) = h ((e : PolyCover.Total P) : ℂ)) :
    monodromyPerm Q ((Path.Homotopic.Quotient.mk γ).map (idBaseC hcv)) =
      F.permCongr (monodromyPerm P (Path.Homotopic.Quotient.mk γ)) := by
  refine Equiv.ext fun f => ?_
  erw [Equiv.permCongr_apply]
  apply Subtype.ext; apply Subtype.ext
  rw [← Path.Homotopic.Quotient.mk_map, monodromyPerm_apply, monodromyPerm_apply]
  have hf : f = F (F.symm f) := by simp
  conv_lhs => rw [hf]
  refine Eq.trans ?_ (hF _).symm
  refine MonoTransfer.monodromy_transfer (isCoveringMap P)
    (fun e => h (e : ℂ)) (fun y => (y : ℂ)) γ (γ.map (continuous_idBase hcv)) (fun t => rfl)
    {y | ‖(y : ℂ)‖ ≤ M} hγ ?_ ?_ (F.symm f) (F (F.symm f)) (hF _)
  · intro e' he'
    have hmem : (e' : ℂ) ∈ U := hUM _ (by rw [← proj_coe']; exact he')
    exact (hc.continuousAt (hU.mem_nhds hmem)).comp continuous_subtype_val.continuousAt
  · intro e' he'
    have hmem : (e' : ℂ) ∈ U := hUM _ (by rw [← proj_coe']; exact he')
    show Q.eval (h (e' : ℂ)) = ((proj P e' : Base _) : ℂ)
    rw [proj_coe']; exact hh _ hmem

lemma norm_upper_le {w0 : ℂ} {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : ‖upper w0 r t‖ ≤ ‖w0‖ + r := by
  unfold upper
  calc ‖w0 + r * Complex.exp (Real.pi * Complex.I * t)‖
      ≤ ‖w0‖ + ‖(r : ℂ) * Complex.exp (Real.pi * Complex.I * t)‖ := norm_add_le _ _
    _ = ‖w0‖ + r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
        show Real.pi * Complex.I * t = ((Real.pi * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]

lemma norm_lower_le {w0 : ℂ} {r : ℝ} (hr : 0 ≤ r) (t : ℝ) : ‖lower w0 r t‖ ≤ ‖w0‖ + r := by
  unfold lower
  calc ‖w0 + r * Complex.exp (Real.pi * Complex.I * (1 + t))‖
      ≤ ‖w0‖ + ‖(r : ℂ) * Complex.exp (Real.pi * Complex.I * (1 + t))‖ := norm_add_le _ _
    _ = ‖w0‖ + r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr,
        show Real.pi * Complex.I * (1 + t) = ((Real.pi * (1 + t) : ℝ) : ℂ) * Complex.I by
          push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]

lemma norm_seg_le {r : ℝ} (hr0 : 0 < r) (hr : r < 1 / 2) (t : unitInterval) :
    ‖seg r (1 - r) t‖ ≤ 2 := by
  unfold seg
  have h0 := t.2.1; have h1 := t.2.2
  have : (r : ℂ) + (t : ℝ) * ((1 - r : ℝ) - r) = ((r + t * (1 - 2 * r) : ℝ) : ℂ) := by
    push_cast; ring
  simp only [Complex.ofReal_sub, Complex.ofReal_one] at this ⊢
  rw [show (r : ℂ) + (t : ℝ) * (1 - (r : ℂ) - r) = ((r + t * (1 - 2 * r) : ℝ) : ℂ) by
    push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith

/-- **No local isomorphism** between the coverings `p_s` and `p_{-s}` over `closedBall 0 2`. -/
theorem no_local_iso (hs : s ^ 2 = -7) {U : Set ℂ} (hU : IsOpen U)
    (hUM : ∀ u, ‖(pPoly s).eval u‖ ≤ 2 → u ∈ U) {h : ℂ → ℂ} (hc : ContinuousOn h U)
    (hinj : InjOn h U) (hh : ∀ u ∈ U, (pPoly (-s)).eval (h u) = (pPoly s).eval u) : False := by
  have hcv := critVals_neg hs
  obtain ⟨r, A, γ0, γ1, A', γ0', γ1', L, L', hr0, hr2, hA, hA', hs1, hs2, h0, h0', hy⟩ :=
    monodromy_point_line hs
  obtain rfl : A' = idBase hcv A := Subtype.ext (by rw [hA', idBase_val, hA])
  obtain ⟨rfl, rfl⟩ := isStdLoops_unique hs2 (isStdLoops_map hcv hs1)
  -- the fibre map
  have hm : ∀ e : proj (pPoly s) ⁻¹' {A}, ((e : PolyCover.Total (pPoly s)) : ℂ) ∈ U := by
    intro e
    exact hUM _ (by
      rw [fibre_eval, hA, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0]; linarith)
  have hfib : ∀ e : proj (pPoly s) ⁻¹' {A},
      (pPoly (-s)).eval (h ((e : PolyCover.Total (pPoly s)) : ℂ)) = ((idBase hcv A : Base _) : ℂ) := by
    intro e
    rw [hh _ (hm e), fibre_eval, idBase_val]
  let Φ : proj (pPoly s) ⁻¹' {A} → proj (pPoly (-s)) ⁻¹' {idBase hcv A} := fun e =>
    fibreMk _ (h ((e : PolyCover.Total (pPoly s)) : ℂ)) (hfib e)
  have hΦinj : Function.Injective Φ := by
    intro e e' hee'
    have hv : h ((e : PolyCover.Total (pPoly s)) : ℂ) = h ((e' : PolyCover.Total (pPoly s)) : ℂ) := by
      have := congrArg (fun f : proj (pPoly (-s)) ⁻¹' {idBase hcv A} =>
        ((f : PolyCover.Total (pPoly (-s))) : ℂ)) hee'
      simpa only [Φ, fibreMk_coe] using this
    exact Subtype.ext (Subtype.ext (hinj (hm e) (hm e') hv))
  haveI : Finite (proj (pPoly s) ⁻¹' {A}) :=
    Nat.finite_of_card_ne_zero (by rw [card_fibre_pPoly hs]; norm_num)
  haveI : Finite (proj (pPoly (-s)) ⁻¹' {idBase hcv A}) :=
    Nat.finite_of_card_ne_zero (by rw [card_fibre_pPoly (neg_sq_seven hs)]; norm_num)
  have hΦbij : Function.Bijective Φ := hΦinj.bijective_of_nat_card_le (by
    rw [card_fibre_pPoly hs, card_fibre_pPoly (neg_sq_seven hs)])
  let F := Equiv.ofBijective Φ hΦbij
  have hF : ∀ e, ((F e : PolyCover.Total (pPoly (-s))) : ℂ) =
      h ((e : PolyCover.Total (pPoly s)) : ℂ) := fun e => fibreMk_coe _ _ (hfib e)
  -- the standard loops lie in `closedBall 0 2`
  obtain ⟨Bp, Cp, Dp, U0, L0, U1, L1, sBC, hU0, hL0, hU1, hL1, hsBC, rfl, rfl⟩ := hs1
  have hr : (0 : ℝ) ≤ r := hr0.le
  let S : Set (Base (pPoly s)) := {y | ‖(y : ℂ)‖ ≤ 2}
  have mU0 : ∀ t, U0 t ∈ S := fun t => by
    show ‖(U0 t : ℂ)‖ ≤ 2; rw [hU0]; have := norm_upper_le (w0 := 0) hr t; simp at this; linarith
  have mL0 : ∀ t, L0 t ∈ S := fun t => by
    show ‖(L0 t : ℂ)‖ ≤ 2; rw [hL0]; have := norm_lower_le (w0 := 0) hr t; simp at this; linarith
  have mU1 : ∀ t, U1 t ∈ S := fun t => by
    show ‖(U1 t : ℂ)‖ ≤ 2; rw [hU1]; have := norm_upper_le (w0 := 1) hr t; simp at this; linarith
  have mL1 : ∀ t, L1 t ∈ S := fun t => by
    show ‖(L1 t : ℂ)‖ ≤ 2; rw [hL1]; have := norm_lower_le (w0 := 1) hr t; simp at this; linarith
  have msBC : ∀ t, sBC t ∈ S := fun t => by
    show ‖(sBC t : ℂ)‖ ≤ 2; rw [hsBC]; exact norm_seg_le hr0 hr2 t
  set g0 := L0.trans U0
  set g1 := U0.symm.trans (sBC.trans (L1.trans (U1.trans (sBC.symm.trans U0))))
  have mg0 : ∀ t, g0 t ∈ S := trans_mem _ _ S mL0 mU0
  have mg1 : ∀ t, g1 t ∈ S := trans_mem _ _ S (symm_mem _ S mU0) (trans_mem _ _ S msBC
    (trans_mem _ _ S mL1 (trans_mem _ _ S mU1 (trans_mem _ _ S (symm_mem _ S msBC) mU0))))
  have e0 : (Path.Homotopic.Quotient.mk L0).trans (Path.Homotopic.Quotient.mk U0) =
      Path.Homotopic.Quotient.mk g0 := (Path.Homotopic.Quotient.mk_trans _ _).symm
  have e1 : (Path.Homotopic.Quotient.mk U0).symm.trans ((Path.Homotopic.Quotient.mk sBC).trans
      ((Path.Homotopic.Quotient.mk L1).trans ((Path.Homotopic.Quotient.mk U1).trans
        ((Path.Homotopic.Quotient.mk sBC).symm.trans (Path.Homotopic.Quotient.mk U0))))) =
      Path.Homotopic.Quotient.mk g1 := by
    simp only [g1, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_symm]
  rw [e0] at h0 h0'
  rw [e1] at hy
  rw [monodromy_local hcv hU hUM hc hh g0 mg0 F hF] at h0'
  rw [permCongr_relabel L L', h0] at h0'
  refine no_intertwiner_pair _ h0' ?_
  rcases hy with ⟨h1, h1'⟩ | ⟨h1, h1'⟩
  · rw [monodromy_local hcv hU hUM hc hh g1 mg1 F hF, permCongr_relabel L L', h1] at h1'
    exact Or.inl h1'
  · rw [monodromy_local hcv hU hUM hc hh g1 mg1 F hF, permCongr_relabel L L', h1] at h1'
    exact Or.inr h1'

end Degree7

end
