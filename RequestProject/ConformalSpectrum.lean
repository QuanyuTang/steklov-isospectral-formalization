module

public import Mathlib
public import RequestProject.ConformalSobolev
public import RequestProject.ConformalWeakSpectrum

/-!
# The weak Steklov problem on `Ω = G(𝔻)` itself

Using the Sobolev pullback `SteklovH1.ConfMap.sobolevPullback : H¹(Ω) ≃L H¹(𝔻)` we prove:

* `ConfMap.inner_grad_pull`: `∫_Ω ⟨∇x, ∇y⟩ = ∫_𝔻 ⟨∇(Px), ∇(Py)⟩` (conformal invariance);
* `ConfMap.inner_trace_pull`: `∫_{∂Ω} Tx · Ty dH¹ = ∫_0^{2π} |G'(e^{it})| T(Px) T(Py) dt`
  (the traces match under the pullback);
* `ConfMap.isCompactOperator_trace`: the trace `H¹(Ω) → L²(∂Ω, H¹)` is compact;
* `ConfMap.isWeakSteklovEigenDom_iff`: `x` is a weak Steklov eigenfunction on `Ω` iff `Px` is a
  weak weighted (`ρ = |G'|`) Steklov eigenfunction on `𝔻`;
* `ConfMap.weak_spectral_theorem_dom`: the weak Steklov spectrum of `Ω`, posed on `H¹(Ω)`, with
  multiplicities, equals the Steklov spectrum of `Ω`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Real ComplexConjugate RealInnerProductSpace

noncomputable section

namespace SteklovH1

/-- **Weak Steklov eigenfunction on a domain `Ω`**: `x ∈ H¹(Ω)` with
`∫_Ω ⟨∇x, ∇y⟩ = τ ∫_{∂Ω} Tx · Ty dH¹` for every `y ∈ H¹(Ω)` (weak form of `Δu = 0` in `Ω`,
`∂_ν u = τ u` on `∂Ω`). -/
def IsWeakSteklovEigenDom (D : BddDomain) (τ : ℝ) (x : D.H1) : Prop :=
  ∀ y : D.H1, ∫ w in D.carrier, ⟪((x : D.Amb).snd : ℂ → ℂ) w, ((y : D.Amb).snd : ℂ → ℂ) w⟫ =
    τ * ∫ w, (D.trace x : ℂ → ℝ) w * (D.trace y : ℂ → ℝ) w ∂D.ν

/-- An operator dominated by a compact operator into a complete space is compact. -/
theorem isCompactOperator_of_norm_le {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y] [NormedAddCommGroup Z]
    [NormedSpace ℝ Z] (S : X →L[ℝ] Y) (K : X →L[ℝ] Z) (hK : IsCompactOperator K) (C : ℝ)
    (h : ∀ x, ‖S x‖ ≤ C * ‖K x‖) : IsCompactOperator S := by
  set C' := max C 0 + 1 with hC'
  have hC'0 : 0 < C' := by positivity
  have h' : ∀ x, ‖S x‖ ≤ C' * ‖K x‖ := fun x =>
    (h x).trans (mul_le_mul_of_nonneg_right (by rw [hC']; linarith [le_max_left C 0])
      (norm_nonneg _))
  refine (isCompactOperator_iff_isCompact_closure_image_closedBall (S : X →ₗ[ℝ] Y)
    zero_lt_one).2 ?_
  have hKc := (isCompactOperator_iff_isCompact_closure_image_closedBall (K : X →ₗ[ℝ] Z)
    zero_lt_one).1 hK
  have hKt : TotallyBounded ((K : X →ₗ[ℝ] Z) '' closedBall 0 1) :=
    hKc.totallyBounded.subset subset_closure
  refine TotallyBounded.isCompact_of_isClosed ?_ isClosed_closure
  refine TotallyBounded.closure ?_
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨t, hts, htf, hcov⟩ := Metric.finite_approx_of_totallyBounded hKt (ε / C')
    (by positivity)
  have hpre : ∀ y ∈ t, ∃ b ∈ closedBall (0 : X) 1, K b = y := fun y hy => by
    obtain ⟨b, hb, rfl⟩ := hts hy; exact ⟨b, hb, rfl⟩
  choose! pre hpre1 hpre2 using hpre
  refine ⟨(fun y => S (pre y)) '' t, htf.image _, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.1 (hcov ⟨x, hx, rfl⟩)
  refine mem_iUnion₂.2 ⟨S (pre y), ⟨y, hyt, rfl⟩, ?_⟩
  rw [mem_ball, dist_eq_norm] at hy ⊢
  change ‖S x - S (pre y)‖ < ε
  rw [← map_sub]
  calc ‖S (x - pre y)‖ ≤ C' * ‖K (x - pre y)‖ := h' _
    _ = C' * ‖(K : X →ₗ[ℝ] Z) x - y‖ := by rw [map_sub, hpre2 y hyt]; rfl
    _ < C' * (ε / C') := mul_lt_mul_of_pos_left hy hC'0
    _ = ε := by field_simp

namespace ConfMap

variable (c : ConfMap)

/-- The boundary weight `ρ = |G'|`. -/
def ρ : ℂ → ℝ := fun z => ‖deriv c.G z‖

lemma continuousOn_ρ : ContinuousOn c.ρ (sphere 0 1) :=
  ((c.diff.deriv c.isOpen).continuousOn.mono (sphere_subset_closedBall.trans c.cb)).norm

lemma ρ_pos : ∀ z ∈ sphere (0 : ℂ) 1, 0 < c.ρ z := fun z hz =>
  norm_pos_iff.2 (c.deriv_ne z (c.cb (sphere_subset_closedBall hz)))

lemma exists_hasTraceIneq : ∃ C, c.dom.HasTraceIneq C :=
  traceIneq_image c.isOpen c.cb c.diff (c.inj.mono c.cb)
    (fun z hz => c.deriv_ne z (c.cb (sphere_subset_closedBall hz)))

/-- The weighted trace of the pullback, `x ↦ √ρ · T(Px)`. -/
def wtrace : c.dom.H1 →L[ℝ] Lp ℝ 2 μT :=
  (weightOp c.continuousOn_ρ).comp (c.sobolevPullback : c.dom.H1 →L[ℝ] H1)

lemma wtrace_apply (x : c.dom.H1) :
    c.wtrace x = weightOp c.continuousOn_ρ (c.sobolevPullback x) := by
  rw [wtrace, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

lemma enorm_trace_embedH (u : smoothFns) :
    ‖c.dom.trace (c.dom.embedH u)‖ₑ ^ 2 = ‖c.wtrace (c.dom.embedH u)‖ₑ ^ 2 := by
  obtain ⟨C, hC⟩ := c.exists_hasTraceIneq
  rw [c.dom.trace_embed hC, BddDomain.enorm_traceSmooth_sq, wtrace,
    ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, c.sobolevPullback_embedH,
    ← h1BoundaryMass_eq_weightOp, h1BoundaryMass_embedH, dom_carrier, Ω,
    ConformalPullback.boundaryMass_image c.isOpen c.cb c.diff (c.inj.mono c.cb)
      (continuous_of_mem u.2)]
  refine ConformalPullback.weightedBoundaryMass_congr _ (fun z hz => ?_)
  exact ((c.pullSmooth_eventually u (sphere_subset_closedBall hz)).eq_of_nhds).symm

/-- `‖Tx‖_{L²(∂Ω)} = ‖√ρ · T(Px)‖_{L²(𝕋)}` on all of `H¹(Ω)`. -/
theorem norm_trace_eq (x : c.dom.H1) : ‖c.dom.trace x‖ = ‖c.wtrace x‖ := by
  refine c.dom.denseRange_embedH.induction_on x
    (isClosed_eq (continuous_norm.comp c.dom.trace.continuous)
      (continuous_norm.comp c.wtrace.continuous)) (fun u => ?_)
  exact norm_eq_of_enorm_sq_eq (c.enorm_trace_embedH u)

lemma inner_eq_of_norm_eq {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (A : X →L[ℝ] Y) (B : X →L[ℝ] Z) (h : ∀ x, ‖A x‖ = ‖B x‖) (x y : X) :
    inner ℝ (A x) (A y) = inner ℝ (B x) (B y) := by
  rw [real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two,
    ← map_add, ← map_add, h, h x, h y]

/-- **The traces match under the Sobolev pullback**:
`∫_{∂Ω} Tx · Ty dH¹ = ∫_0^{2π} |G'(e^{it})| · T(Px)(t) · T(Py)(t) dt`. -/
theorem inner_trace_pull (x y : c.dom.H1) :
    ∫ w, (c.dom.trace x : ℂ → ℝ) w * (c.dom.trace y : ℂ → ℝ) w ∂c.dom.ν =
      ∫ t in Ioc 0 (2 * π), c.ρ (Complex.exp (t * Complex.I)) *
        ((trace (c.sobolevPullback x) : ℝ → ℝ) t * (trace (c.sobolevPullback y) : ℝ → ℝ) t) := by
  rw [← inner_weightOp c.continuousOn_ρ c.ρ_pos]
  have := inner_eq_of_norm_eq c.dom.trace c.wtrace c.norm_trace_eq x y
  rw [L2.inner_def, c.wtrace_apply, c.wtrace_apply] at this
  rw [← this]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [real_inner_eq_re_inner, RCLike.inner_apply, RCLike.conj_to_real, RCLike.re_to_real,
    mul_comm]

/-- **Conformal invariance of the Dirichlet form**: `∫_Ω ⟨∇x, ∇y⟩ = ∫_𝔻 ⟨∇(Px), ∇(Py)⟩`. -/
theorem inner_grad_pull (x y : c.dom.H1) :
    ∫ w in c.dom.carrier, ⟪((x : c.dom.Amb).snd : ℂ → ℂ) w, ((y : c.dom.Amb).snd : ℂ → ℂ) w⟫ =
      ∫ z in ball (0 : ℂ) 1, ⟪((c.sobolevPullback x : Amb).snd : ℂ → ℂ) z,
        ((c.sobolevPullback y : Amb).snd : ℂ → ℂ) z⟫ := by
  let L : Lp ℂ 2 c.dom.μ →ₗᵢ[ℝ] Lp ℂ 2 μD := ⟨c.pullG, c.norm_pullG⟩
  have := L.inner_map_map (x : c.dom.Amb).snd (y : c.dom.Amb).snd
  rw [L2.inner_def, L2.inner_def] at this
  rw [← this]
  rfl

/-- **Weak Steklov eigenfunctions of `Ω = G(𝔻)` correspond to weak weighted eigenfunctions of the
disk** under the Sobolev pullback. -/
theorem isWeakSteklovEigenDom_iff (τ : ℝ) (x : c.dom.H1) :
    IsWeakSteklovEigenDom c.dom τ x ↔ IsWeakSteklovEigen c.ρ τ (c.sobolevPullback x) := by
  constructor
  · intro h y
    have := h (c.sobolevPullback.symm y)
    rw [c.inner_grad_pull, c.inner_trace_pull, ContinuousLinearEquiv.apply_symm_apply] at this
    exact this
  · intro h y
    rw [c.inner_grad_pull, c.inner_trace_pull]
    exact h _

/-- **The trace `H¹(Ω) → L²(∂Ω, H¹)` is compact** for `Ω = G(𝔻)`. -/
theorem isCompactOperator_trace : IsCompactOperator c.dom.trace := by
  have hW : IsCompactOperator c.wtrace := by
    have h1 : IsCompactOperator (weightOp c.continuousOn_ρ) := by
      have := SteklovH1.isCompactOperator_trace.clm_comp (mulOp (bdryWeight c.ρ)
        (continuous_bdryWeight c.continuousOn_ρ) _
        (exists_bdryWeight_bound c.continuousOn_ρ).choose_spec)
      exact this
    exact h1.comp_clm _
  exact isCompactOperator_of_norm_le _ _ hW 1 (fun x => by rw [c.norm_trace_eq, one_mul])

/-- **Weak Steklov spectral theorem on `Ω = G(𝔻)`, posed on `H¹(Ω)`**, with multiplicities:
there are weak eigenfunctions `e k ∈ H¹(Ω)` with eigenvalues `σ k`, nondecreasing, `σ 0 = 0`,
`σ k → ∞`; every weak eigenvalue is some `σ k`; the weak eigenspace of `τ` has dimension
`#{k | σ k = τ}`; and `σ k` is the `k`-th Steklov eigenvalue of `Ω`. -/
theorem weak_spectral_theorem_dom :
    ∃ (e : ℕ → c.dom.H1) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = 0 ∧ Tendsto σ atTop atTop ∧
      (∀ k, e k ≠ 0 ∧ IsWeakSteklovEigenDom c.dom (σ k) (e k)) ∧
      (∀ τ, (∃ x : c.dom.H1, x ≠ 0 ∧ IsWeakSteklovEigenDom c.dom τ x) ↔ ∃ k, σ k = τ) ∧
      (∀ τ, ∃ S : Submodule ℝ c.dom.H1, (∀ x, x ∈ S ↔ IsWeakSteklovEigenDom c.dom τ x) ∧
        Module.finrank ℝ S = Set.ncard {k | σ k = τ}) ∧
      (∀ k, Steklov.steklovSpectrum c.Ω k = ENNReal.ofReal (σ k)) := by
  obtain ⟨e, σ, hmono, h0, htend, heig, hiff, hdim, hspec⟩ :=
    conformal_weak_spectrum (F := c.G) ⟨c.U, c.isOpen, c.cb, c.diff⟩ (c.inj.mono c.cb)
      (fun z hz => c.deriv_ne z (c.cb (sphere_subset_closedBall hz)))
  set P := c.sobolevPullback
  refine ⟨fun k => P.symm (e k), σ, hmono, h0, htend, fun k => ⟨?_, ?_⟩, fun τ => ?_,
    fun τ => ?_, hspec⟩
  · first
      | exact fun h => (heig k).1 ((ContinuousLinearEquiv.map_eq_zero_iff P.symm).1 h)
      | exact fun h => (heig k).1 (P.symm.injective (h.trans P.symm.map_zero.symm))
  · rw [c.isWeakSteklovEigenDom_iff, ContinuousLinearEquiv.apply_symm_apply]
    exact (heig k).2
  · rw [← hiff τ]
    constructor
    · rintro ⟨x, hx, hxe⟩
      have hPx : P x ≠ 0 := by
        first
          | exact fun h => hx ((ContinuousLinearEquiv.map_eq_zero_iff P).1 h)
          | exact fun h => hx (P.injective (h.trans P.map_zero.symm))
      exact ⟨P x, hPx, (c.isWeakSteklovEigenDom_iff τ x).1 hxe⟩
    · rintro ⟨y, hy, hye⟩
      have hPy : P.symm y ≠ 0 := by
        first
          | exact fun h => hy ((ContinuousLinearEquiv.map_eq_zero_iff P.symm).1 h)
          | exact fun h => hy (P.symm.injective (h.trans P.symm.map_zero.symm))
      refine ⟨P.symm y, hPy, ?_⟩
      rw [c.isWeakSteklovEigenDom_iff, ContinuousLinearEquiv.apply_symm_apply]
      exact hye
  · obtain ⟨S, hS, hSd⟩ := hdim τ
    refine ⟨S.map (P.symm.toLinearEquiv : H1 →ₗ[ℝ] c.dom.H1), fun x => ?_, ?_⟩
    · rw [Submodule.mem_map_equiv, hS, c.isWeakSteklovEigenDom_iff]
      rfl
    · rw [LinearEquiv.finrank_map_eq, hSd]

end ConfMap

/-- `Ω` is a bounded plane domain whose **weak Steklov spectrum posed on `H¹(Ω)` itself** exists
with multiplicities and equals its Steklov spectrum, and whose trace `H¹(Ω) → L²(∂Ω)` is compact. -/
def HasWeakSteklovSpectrumDom (Ω : Set ℂ) : Prop :=
  ∃ D : BddDomain, D.carrier = Ω ∧ IsCompactOperator D.trace ∧
    ∃ (e : ℕ → D.H1) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = 0 ∧ Tendsto σ atTop atTop ∧
      (∀ k, e k ≠ 0 ∧ IsWeakSteklovEigenDom D (σ k) (e k)) ∧
      (∀ τ, (∃ x : D.H1, x ≠ 0 ∧ IsWeakSteklovEigenDom D τ x) ↔ ∃ k, σ k = τ) ∧
      (∀ τ, ∃ S : Submodule ℝ D.H1, (∀ x, x ∈ S ↔ IsWeakSteklovEigenDom D τ x) ∧
        Module.finrank ℝ S = Set.ncard {k | σ k = τ}) ∧
      (∀ k, Steklov.steklovSpectrum Ω k = ENNReal.ofReal (σ k))

/-- The domain-level weak spectrum for `G(𝔻)`, under the hypotheses of the paper. -/
theorem hasWeakSteklovSpectrumDom_image {G : ℂ → ℂ}
    (hG : ∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ G U)
    (hinj : InjOn G (closedBall 0 1)) (hder : ∀ z ∈ sphere (0 : ℂ) 1, deriv G z ≠ 0) :
    HasWeakSteklovSpectrumDom (G '' ball 0 1) := by
  obtain ⟨c, rfl⟩ := ConfMap.ofHyp hG hinj hder
  exact ⟨c.dom, rfl, c.isCompactOperator_trace, c.weak_spectral_theorem_dom⟩

theorem hasWeakSteklovSpectrumDom_of {Ω : Set ℂ} (h : HasWeakSteklovSpectrum Ω) :
    HasWeakSteklovSpectrumDom Ω := by
  obtain ⟨G, hG, hinj, hder, rfl, -⟩ := h
  exact hasWeakSteklovSpectrumDom_image hG hinj hder

end SteklovH1
