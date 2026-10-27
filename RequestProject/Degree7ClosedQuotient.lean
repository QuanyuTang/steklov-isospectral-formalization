module

public import RequestProject.Degree7Descent
public import RequestProject.DiskBoundaryExtension

/-!
# The closed quotients `M_ε / H` are the closed unit disk, with projection `B`

For a label with polynomial `p_t` (`t = ±s`), its quotient map `Ev` (fibres = `H`-orbits,
`q_ε ∘ Ev = A_ε ∘ π̄`), the paper's normalisation `Q = paperQ (monicP t a) τ ε` and a normalized
disk cover `(ψ, B)` of `Q` with connected `Q⁻¹(𝔻)`:

* `paperQ_form`: `Q z = A_ε(p_t(z/c))`, `c = τ ε / a`; its critical values are `A_ε(0) = ε` and
  `A_ε(1) = λ_* ε`, inside `𝔻` (`paperQ_deriv_ne_zero`), and `{‖Q‖ ≤ 1}` is compact.
* **`closed_quotient_disk`**: the boundary extension `Ψ` of `ψ` (`closed_disk_homeomorph`) gives a
  homeomorphism `Θ̄ : M_ε / H ≃ₜ closed 𝔻` with `Ψ(Θ̄[w]) = τ ε Ev(w)/a` and
  **`B(Θ̄[w]) = b_ε(w)`** on all of `M_ε` (including `∂M_ε`), `Θ̄` maps `∂M_ε / H` onto the circle,
  `Ψ = ψ` on `𝔻`, and near every boundary point `Ψ` is the restriction of a holomorphic map with
  nonvanishing derivative (analytic boundary compatibility in the quotient coordinate `τ ε Ev / a`).
-/

@[expose] public section

open Polynomial Set Filter Topology Metric PolyCover LocalMonodromy SteklovRegularCover
  SteklovPunctured SteklovFill SteklovRiemann Manifold SteklovOrb SteklovCoalescence
  SteklovCritical
open scoped ContDiff

noncomputable section

namespace Degree7

variable {s : ℂ}

lemma paperQ_form {t a : ℂ} (ht : t ^ 2 = -7) (ha : a ^ 7 = -bconst t) (τ : ℝ → ℂ) (ε : ℝ)
    (z : ℂ) : paperQ (monicP t a) τ ε z = affA ε ((pPoly t).eval (z / (τ ε / a))) := by
  rw [paperQ_monicP_eq ht ha, affA_coverPoly]

lemma a_ne_zero {t a : ℂ} (ht : t ^ 2 = -7) (ha : a ^ 7 = -bconst t) : a ≠ 0 := by
  rintro rfl; rw [zero_pow (by norm_num)] at ha
  exact bconst_ne_zero ht (neg_eq_zero.1 ha.symm)

lemma tau_ne_zero {τ : ℝ → ℂ} (hτ : ∀ ε, τ ε ^ 7 = (lamStar - 1) * ε) {ε : ℝ} (h0 : 0 < ε) :
    τ ε ≠ 0 := by
  intro h
  have := hτ ε
  rw [h, zero_pow (by norm_num)] at this
  exact lamc_ne_zero h0 this.symm

lemma hasDerivAt_paperQ {t a : ℂ} (ht : t ^ 2 = -7) (ha : a ^ 7 = -bconst t) (τ : ℝ → ℂ)
    (ε : ℝ) (z : ℂ) :
    HasDerivAt (paperQ (monicP t a) τ ε)
      ((lamStar - 1) * ε * ((pPoly t).derivative.eval (z / (τ ε / a)) * (1 / (τ ε / a)))) z := by
  have h1 : HasDerivAt (fun y : ℂ => y / (τ ε / a)) (1 / (τ ε / a)) z := by
    simpa using (hasDerivAt_id z).div_const (τ ε / a)
  have h2 := ((Polynomial.hasDerivAt (pPoly t) (z / (τ ε / a))).comp z h1)
  have h3 := (h2.const_mul ((lamStar - 1) * (ε : ℂ))).const_add (ε : ℂ)
  refine h3.congr_of_eventuallyEq (Eventually.of_forall fun y => ?_)
  rw [paperQ_form ht ha]; rfl

/-- The critical values of the paper's polynomial are `ε`, `λ_* ε`, inside the unit disk. -/
lemma paperQ_deriv_ne_zero {t a : ℂ} (ht : t ^ 2 = -7) (ha : a ^ 7 = -bconst t)
    {τ : ℝ → ℂ} (hτ : ∀ ε, τ ε ^ 7 = (lamStar - 1) * ε) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 3)
    (y : ℂ) (hy : ‖paperQ (monicP t a) τ ε y‖ = 1) : deriv (paperQ (monicP t a) τ ε) y ≠ 0 := by
  have hc : τ ε / a ≠ 0 := div_ne_zero (tau_ne_zero hτ h0) (a_ne_zero ht ha)
  rw [(hasDerivAt_paperQ ht ha τ ε y).deriv]
  intro h0'
  have hd : (pPoly t).derivative.eval (y / (τ ε / a)) = 0 := by
    rcases mul_eq_zero.1 h0' with h | h
    · exact absurd h (lamc_ne_zero h0)
    · rcases mul_eq_zero.1 h with h | h
      · exact h
      · exact absurd h (one_div_ne_zero hc)
  have hcv : (pPoly t).eval (y / (τ ε / a)) ∈ critVals (pPoly t) := ⟨_, hd, rfl⟩
  rw [critVals_pPoly ht] at hcv
  obtain ⟨hu, hv⟩ := branchValues_mem_disk h0 h1
  rw [paperQ_form ht ha] at hy
  rcases hcv with h | h <;> rw [h] at hy
  · rw [(affA_eq_u_iff h0 0).2 rfl] at hy; linarith
  · rw [(affA_eq_v_iff h0 1).2 rfl] at hy; linarith

lemma differentiable_paperQ {t a : ℂ} (ht : t ^ 2 = -7) (ha : a ^ 7 = -bconst t) (τ : ℝ → ℂ)
    (ε : ℝ) : Differentiable ℂ (paperQ (monicP t a) τ ε) := fun z =>
  (hasDerivAt_paperQ ht ha τ ε z).differentiableAt

/-- **The closed quotient `M_ε / H` is the closed unit disk, with projection `B`.** -/
theorem closed_quotient_disk (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13)
    (H : Subgroup (deckGroup f₀)) {t : ℂ} (ht : t ^ 2 = -7) {Ev : RegFill hs f₀ → ℂ}
    (hpr : IsProperMap Ev) (hsurj : Function.Surjective Ev)
    (hfib : ∀ w w', Ev w = Ev w' ↔ ∃ σ ∈ H, regFillAct hs f₀ σ w = w')
    (hq : ∀ (ε : ℝ) w, (SteklovDiskCovers.coverPoly (pPoly t) ε).eval (Ev w) =
      affA ε (regFillProj hs f₀ w))
    {a : ℂ} (ha : a ^ 7 = -bconst t) {τ : ℝ → ℂ} (hτ : ∀ ε, τ ε ^ 7 = (lamStar - 1) * ε)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 3)
    (hconn : IsPreconnected (paperQ (monicP t a) τ ε ⁻¹' ball 0 1))
    {ψ B : ℂ → ℂ} (hc : IsNormalizedDiskCover (paperQ (monicP t a) τ ε) 7 ψ B) :
    ∃ Θ : QuotOn hs f₀ (bordered hs f₀ ε) H ≃ₜ closedBall (0 : ℂ) 1, ∃ Ψ : ℂ → ℂ,
      (∀ w : bordered hs f₀ ε, Ψ (Θ (Quotient.mk _ w)) = τ ε * Ev w / a ∧
        B (Θ (Quotient.mk _ w)) = bdf hs f₀ ε w) ∧
      InjOn Ψ (closedBall 0 1) ∧ (∀ z ∈ ball (0 : ℂ) 1, Ψ z = ψ z) ∧
      (∀ w : bordered hs f₀ ε, (w : RegFill hs f₀) ∈ borderedBdry hs f₀ ε ↔
        (Θ (Quotient.mk _ w) : ℂ) ∈ sphere (0 : ℂ) 1) ∧
      ∀ z₀ ∈ sphere (0 : ℂ) 1, ∃ δ > 0, ∃ E : ℂ → ℂ, DifferentiableOn ℂ E (ball z₀ δ) ∧
        (∀ z ∈ ball z₀ δ, deriv E z ≠ 0) ∧
        (∀ z ∈ ball z₀ δ, paperQ (monicP t a) τ ε (E z) = B z) ∧
        ∀ z ∈ ball z₀ δ ∩ closedBall 0 1, E z = Ψ z := by
  set Q := paperQ (monicP t a) τ ε
  have hτ0 := tau_ne_zero hτ h0
  have ha0 := a_ne_zero ht ha
  have hc0 : τ ε / a ≠ 0 := div_ne_zero hτ0 ha0
  have hPQ := paperQ_monicP_eq ht ha τ ε
  obtain ⟨-, A2, -, -⟩ := quotient_spaces_of_ev hs f₀ H hpr hsurj hfib hq h0 h1 (τ ε / a) hc0
  obtain ⟨Φ₀, hΦ₀⟩ := A2
  let Φ : QuotOn hs f₀ (bordered hs f₀ ε) H ≃ₜ {y : ℂ | ‖Q y‖ ≤ 1} :=
    Φ₀.trans (Homeomorph.setCongr (by ext z; simp only [mem_setOf_eq, Q, hPQ]))
  have hΦ : ∀ w : bordered hs f₀ ε, (Φ (Quotient.mk _ w) : ℂ) = τ ε * Ev w / a := fun w => by
    show (Φ₀ (Quotient.mk _ w) : ℂ) = _
    rw [hΦ₀]; ring
  -- compactness of the closed sublevel set
  have hK : IsCompact {y : ℂ | ‖Q y‖ ≤ 1} := by
    haveI : CompactSpace (bordered hs f₀ ε) :=
      isCompact_iff_compactSpace.1 (regBorderedSurface hs f₀ h0 h1).1
    haveI : CompactSpace (QuotOn hs f₀ (bordered hs f₀ ε) H) := Quotient.compactSpace
    haveI := Φ.compactSpace
    exact isCompact_iff_compactSpace.2 this
  obtain ⟨hψd, hψi, hψ0, -, -, himg0, hBl, hBQ⟩ := hc
  have h0S : (0 : ℂ) ∈ Q ⁻¹' ball 0 1 := by
    have : ψ 0 ∈ ψ '' ball (0 : ℂ) 1 := mem_image_of_mem _ (mem_ball_self one_pos)
    rw [himg0, hψ0] at this
    exact connectedComponentIn_subset _ _ this
  have himg : ψ '' ball 0 1 = {y | ‖Q y‖ < 1} := by
    rw [himg0, hconn.connectedComponentIn h0S]; ext y; simp
  obtain ⟨Ψ, eΨ, heΨ, hin, -, hQB, hloc⟩ := SteklovBordered.closed_disk_homeomorph
    (differentiable_paperQ ht ha τ ε) (paperQ_deriv_ne_zero ht ha hτ h0 h1) hK hψd hψi himg hBl
    (by norm_num) hBQ
  obtain ⟨R, R₀, c, hR₀, hR₀R, -, -, hBn, -, -, -, -⟩ := hBl.exists_radii (by norm_num)
  have hval : ∀ w : bordered hs f₀ ε, Ψ ((Φ.trans eΨ.symm) (Quotient.mk _ w)) = τ ε * Ev w / a := by
    intro w
    rw [← heΨ, Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
    exact hΦ w
  have hB : ∀ w : bordered hs f₀ ε, B ((Φ.trans eΨ.symm) (Quotient.mk _ w)) = bdf hs f₀ ε w := by
    intro w
    rw [← hQB _ ((Φ.trans eΨ.symm) (Quotient.mk _ w)).2, hval w]
    show paperQ (monicP t a) τ ε (τ ε * Ev ↑w / a) = bdf hs f₀ ε ↑w
    rw [hPQ, show τ ε * Ev ↑w / a / (τ ε / a) = Ev w by field_simp, hq]; rfl
  refine ⟨Φ.trans eΨ.symm, Ψ, fun w => ⟨hval w, hB w⟩, ?_, hin, fun w => ?_, hloc⟩
  · intro z₁ hz₁ z₂ hz₂ h
    have : eΨ ⟨z₁, hz₁⟩ = eΨ ⟨z₂, hz₂⟩ := Subtype.ext (by rw [heΨ, heΨ]; exact h)
    exact congrArg Subtype.val (eΨ.injective this)
  · set z := ((Φ.trans eΨ.symm) (Quotient.mk _ w) : ℂ)
    have hz : z ∈ closedBall (0 : ℂ) 1 := ((Φ.trans eΨ.symm) (Quotient.mk _ w)).2
    have hzR : z ∈ ball (0 : ℂ) R :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt (mem_closedBall_zero_iff.1 hz) (by linarith))
    rw [borderedBdry_eq, mem_setOf_eq, ← hB w, mem_sphere_zero_iff_norm]
    exact (hBn z hzR).2

end Degree7
