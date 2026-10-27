module

public import RequestProject.BlaschkeKernel
public import RequestProject.FanoKernel
public import RequestProject.FullMonodromy
public import RequestProject.DiskCoverExistence
public import RequestProject.HolomorphicInverse

/-!
# The actual transplantation kernel for the degree-seven disk covers

For a disk cover `B = ε + δ · p_s(κ ψ)` on `𝔻` (`ψ` injective holomorphic), the Blaschke covering
of `B` over `Xb c' {ε, ε+δ}` and the polynomial covering of `p_s` are related by the fibre map
`e ↦ κ ψ(e)` (`fmap`), which is injective and intertwines monodromy along every loop in the small
disk (`fmap_monodromy`, via `MonoTransfer.monodromy_transfer`).
-/

@[expose] public section

open Complex Metric Set Filter Topology Polynomial

noncomputable section

namespace ActualKernel

open SteklovBlaschke BCover BKernel Degree7 PolyCover

/-- The critical values `{ε, ε + δ}` of `w ↦ ε + δ p_s(w)`. -/
def Cset (ε δ : ℂ) : Set ℂ := {ε, ε + δ}

lemma Cset_finite (ε δ : ℂ) : (Cset ε δ).Finite := by
  simp [Cset]

variable {s ε δ κ : ℂ} {ψ B : ℂ → ℂ} {n : ℕ} {R R₀ c c' : ℝ}

lemma base_mem (hs : s ^ 2 = -7) (hδ : δ ≠ 0) {w : ℂ} (hw : w ∉ Cset ε δ) :
    (w - ε) / δ ∈ (critVals (pPoly s))ᶜ := by
  rw [critVals_pPoly hs]
  simp only [Cset, mem_insert_iff, mem_singleton_iff, not_or] at hw
  simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
  refine ⟨div_ne_zero (sub_ne_zero.2 hw.1) hδ, fun h => hw.2 ?_⟩
  rw [div_eq_one_iff_eq hδ] at h
  linear_combination h

section side

variable (hs : s ^ 2 = -7) (hδ : δ ≠ 0) (h : BRadii B n R R₀ c) (hcc : c' ≤ c)
  (hψi : InjOn ψ (ball 0 1))
  (hBψ : ∀ z : ℂ, ‖z‖ < 1 → B z = ε + δ * pfun s (κ * ψ z))

include h hcc in
lemma ev_lt_one (e : Etot B R₀ (Xb c' (Cset ε δ))) (he : ‖B (ev e)‖ < 1) : ‖ev e‖ < 1 :=
  ((h.2.2.2.2.1 (ev e) (mem_ball_zero_iff.2 ((ev_norm_lt h (Xb_subset hcc) e).trans
    h.2.1))).1).1 he

include hδ hBψ in
lemma pfun_eq {z : ℂ} (hz : ‖z‖ < 1) : pfun s (κ * ψ z) = (B z - ε) / δ := by
  rw [hBψ z hz]; field_simp; ring

include hs hδ h hcc hBψ in
lemma eval_mem (x : Xb c' (Cset ε δ)) (hx : ‖(x : ℂ)‖ < 1)
    (e : bproj B R₀ (Xb c' (Cset ε δ)) ⁻¹' {x}) :
    (pPoly s).eval (κ * ψ (ev e.1)) = ((x : ℂ) - ε) / δ ∧
      (pPoly s).eval (κ * ψ (ev e.1)) ∈ (critVals (pPoly s))ᶜ := by
  have hBe : B (ev e.1) = x := congrArg Subtype.val e.2
  have hlt : ‖ev e.1‖ < 1 := ev_lt_one h hcc e.1 (by rw [hBe]; exact hx)
  have heq : (pPoly s).eval (κ * ψ (ev e.1)) = ((x : ℂ) - ε) / δ := by
    rw [pPoly_eval, pfun_eq hδ hBψ hlt, hBe]
  exact ⟨heq, by rw [heq]; exact base_mem hs hδ x.2.2⟩

/-- The fibre map `e ↦ κ ψ(e)` from the Blaschke fibre to the polynomial fibre. -/
def fmap (x : Xb c' (Cset ε δ)) (hx : ‖(x : ℂ)‖ < 1) (b : Base (pPoly s))
    (hb : (b : ℂ) = ((x : ℂ) - ε) / δ) (e : bproj B R₀ (Xb c' (Cset ε δ)) ⁻¹' {x}) :
    proj (pPoly s) ⁻¹' {b} :=
  ⟨⟨κ * ψ (ev e.1), (eval_mem hs hδ h hcc hBψ x hx e).2⟩,
    Subtype.ext ((eval_mem hs hδ h hcc hBψ x hx e).1.trans hb.symm)⟩

lemma fmap_val (x : Xb c' (Cset ε δ)) (hx : ‖(x : ℂ)‖ < 1) (b : Base (pPoly s))
    (hb : (b : ℂ) = ((x : ℂ) - ε) / δ) (e : bproj B R₀ (Xb c' (Cset ε δ)) ⁻¹' {x}) :
    ((fmap hs hδ h hcc hBψ x hx b hb e : Total (pPoly s)) : ℂ) = κ * ψ (ev e.1) := rfl

include hψi in
lemma fmap_injective (hκ : κ ≠ 0) (x : Xb c' (Cset ε δ)) (hx : ‖(x : ℂ)‖ < 1)
    (b : Base (pPoly s)) (hb : (b : ℂ) = ((x : ℂ) - ε) / δ) :
    Function.Injective (fmap hs hδ h hcc hBψ x hx b hb) := by
  intro e e' hee'
  have hv := congrArg (fun f : proj (pPoly s) ⁻¹' {b} => ((f : Total (pPoly s)) : ℂ)) hee'
  simp only [fmap_val] at hv
  have hψ := mul_left_cancel₀ hκ hv
  have hBe : B (ev e.1) = x := congrArg Subtype.val e.2
  have hBe' : B (ev e'.1) = x := congrArg Subtype.val e'.2
  have h1 : ev e.1 ∈ ball (0:ℂ) 1 :=
    mem_ball_zero_iff.2 (ev_lt_one h hcc e.1 (by rw [hBe]; exact hx))
  have h2 : ev e'.1 ∈ ball (0:ℂ) 1 :=
    mem_ball_zero_iff.2 (ev_lt_one h hcc e'.1 (by rw [hBe']; exact hx))
  have := hψi h1 h2 hψ
  exact Subtype.ext (Subtype.ext (Subtype.ext this))

include hψi in
/-- **Bijectivity of the fibre map** (both fibres have seven points). -/
lemma fmap_bijective (hκ : κ ≠ 0) (hB : IsFiniteBlaschke B 7) (h7 : n = 7)
    (hc' : 1 < c') (hcrit : ∀ z : ℂ, ‖z‖ < 1 → deriv B z = 0 → B z ∈ Cset ε δ)
    (hsph : sphere (0:ℂ) 1 ⊆ Xb c' (Cset ε δ))
    (x : Xb c' (Cset ε δ)) (hx : ‖(x : ℂ)‖ < 1)
    (b : Base (pPoly s)) (hb : (b : ℂ) = ((x : ℂ) - ε) / δ) :
    Function.Bijective (fmap hs hδ h hcc hBψ x hx b hb) := by
  subst h7
  haveI := pathConnected_Xb hc' (Cset_finite ε δ)
  haveI : Finite (proj (pPoly s) ⁻¹' {b}) := by
    have := card_fibre_pPoly hs b
    exact Nat.finite_of_card_ne_zero (by rw [this]; norm_num)
  refine (fmap_injective hs hδ h hcc hψi hBψ hκ x hx b hb).bijective_of_nat_card_le ?_
  rw [card_fibre_pPoly hs b, card_fibre h (Xb_subset hcc) hB (by norm_num) (crit_Xb hcrit) hsph x]

/-- **Monodromy transfer for the fibre map**: along a loop in the small disk, the Blaschke
monodromy corresponds to the polynomial monodromy along the affine image of the loop. -/
lemma fmap_monodromy (hψd : DifferentiableOn ℂ ψ (ball 0 1)) {ρ : ℝ} (hρ1 : ρ < 1)
    (cov : IsCoveringMap (bproj B R₀ (Xb c' (Cset ε δ))))
    (x₀ : Xb c' (Cset ε δ)) (hx₀ : ‖(x₀ : ℂ)‖ < 1) (b₀ : Base (pPoly s))
    (hb₀ : (b₀ : ℂ) = ((x₀ : ℂ) - ε) / δ) (γ : Path x₀ x₀) (hγ : ∀ t, ‖(γ t : ℂ)‖ ≤ ρ)
    (β : Path b₀ b₀) (hβ : ∀ t, (β t : ℂ) = ((γ t : ℂ) - ε) / δ)
    (a : bproj B R₀ (Xb c' (Cset ε δ)) ⁻¹' {x₀}) :
    fmap hs hδ h hcc hBψ x₀ hx₀ b₀ hb₀ (cov.monodromy (Path.Homotopic.Quotient.mk γ) a) =
      (isCoveringMap (pPoly s)).monodromy (Path.Homotopic.Quotient.mk β)
        (fmap hs hδ h hcc hBψ x₀ hx₀ b₀ hb₀ a) := by
  apply Subtype.ext; apply Subtype.ext
  rw [fmap_val]
  symm
  refine MonoTransfer.monodromy_transfer cov (fun e => κ * ψ (ev e))
    (fun y => ((y : ℂ) - ε) / δ) γ β hβ {y | ‖(y : ℂ)‖ ≤ ρ} hγ ?_ ?_ a _ rfl
  · intro e' he'
    have hlt : ‖ev e'‖ < 1 := ev_lt_one h hcc e' (lt_of_le_of_lt he' hρ1)
    have hψc : ContinuousAt ψ (ev e') :=
      (hψd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hlt))).continuousAt
    exact (continuousAt_const.mul (hψc.comp continuous_ev.continuousAt))
  · intro e' he'
    have hlt : ‖ev e'‖ < 1 := ev_lt_one h hcc e' (lt_of_le_of_lt he' hρ1)
    show (pPoly s).eval (κ * ψ (ev e')) = (B (ev e') - ε) / δ
    rw [pPoly_eval, pfun_eq hδ hBψ hlt]

end side

/-- **Critical values of a disk cover** `B = ε + δ p_s(κ ψ)` in `𝔻` lie in `{ε, ε + δ}`. -/
lemma crit_of_disk (hs : s ^ 2 = -7) (hδ : δ ≠ 0) (hκ : κ ≠ 0)
    (hψd : DifferentiableOn ℂ ψ (ball 0 1)) (hψi : InjOn ψ (ball 0 1))
    (hBψ : ∀ z : ℂ, ‖z‖ < 1 → B z = ε + δ * pfun s (κ * ψ z)) :
    ∀ z : ℂ, ‖z‖ < 1 → deriv B z = 0 → B z ∈ Cset ε δ := by
  intro z hz hd
  have hzb : z ∈ ball (0:ℂ) 1 := mem_ball_zero_iff.2 hz
  have hψz : HasDerivAt ψ (deriv ψ z) z :=
    (hψd.differentiableAt (isOpen_ball.mem_nhds hzb)).hasDerivAt
  have hψ0 : deriv ψ z ≠ 0 := HolInv.deriv_ne_zero_of_injOn isOpen_ball hψd hψi hzb
  have hcomp : HasDerivAt (fun w => ε + δ * pfun s (κ * ψ w))
      (δ * (deriv (pfun s) (κ * ψ z) * (κ * deriv ψ z))) z := by
    have h1 := (hasDerivAt_pfun s (κ * ψ z))
    rw [← h1.deriv] at h1
    exact ((h1.comp z (hψz.const_mul κ)).const_mul δ).const_add ε
  have heq : B =ᶠ[𝓝 z] fun w => ε + δ * pfun s (κ * ψ w) := by
    filter_upwards [isOpen_ball.mem_nhds hzb] with w hw
    exact hBψ w (mem_ball_zero_iff.1 hw)
  rw [heq.deriv_eq, hcomp.deriv] at hd
  have hp : deriv (pfun s) (κ * ψ z) = 0 := by
    rcases mul_eq_zero.1 hd with h | h
    · exact absurd h hδ
    rcases mul_eq_zero.1 h with h | h
    · exact h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h hκ
    · exact absurd h hψ0
  rw [hBψ z hz]
  rcases pfun_critical_value_mem hs hp with h0 | h1
  · left; rw [h0]; ring
  · right; rw [h1, mul_one]; rfl

/-- The affine image `(γ - ε)/δ` of a path in the base, as a path in the base of `p_s`. -/
def basePath (hs : s ^ 2 = -7) (hδ : δ ≠ 0) {x₀ : Xb c' (Cset ε δ)} (γ : Path x₀ x₀)
    (b₀ : Base (pPoly s)) (hb₀ : (b₀ : ℂ) = ((x₀ : ℂ) - ε) / δ) : Path b₀ b₀ where
  toFun t := ⟨((γ t : ℂ) - ε) / δ, base_mem hs hδ (γ t).2.2⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact ((continuous_subtype_val.comp γ.continuous).sub continuous_const).div_const _
  source' := Subtype.ext (by simp [hb₀])
  target' := Subtype.ext (by simp [hb₀])

lemma basePath_apply (hs : s ^ 2 = -7) (hδ : δ ≠ 0) {x₀ : Xb c' (Cset ε δ)} (γ : Path x₀ x₀)
    (b₀ : Base (pPoly s)) (hb₀ : (b₀ : ℂ) = ((x₀ : ℂ) - ε) / δ) (t : unitInterval) :
    ((basePath hs hδ γ b₀ hb₀ t : Base (pPoly s)) : ℂ) = ((γ t : ℂ) - ε) / δ := rfl

section pair

variable {s ε δ κ₁ κ₂ : ℂ} {ψ₁ B₁ ψ₂ B₂ : ℂ → ℂ}

set_option maxHeartbeats 2000000 in
/-- **Equality of the weighted Steklov spectra of the two degree-seven disk covers.**  For
disk covers `B₂ = ε + δ p_s(κ₂ ψ₂)` and `B₁ = ε + δ p_{-s}(κ₁ ψ₁)` on `𝔻` (finite Blaschke products
of degree `7`, `ψᵢ` injective holomorphic on `𝔻`, `s² = -7`, `|ε| + |δ| < 1/2`), all weighted
Steklov eigenvalues agree.  The proof constructs the transplantation kernel from the Fano incidence
intertwiner by parallel transport, using the actual polynomial monodromy (`monodromy_full`). -/
theorem spectra_eq_of_disk_data (hs : s ^ 2 = -7) (hδ : δ ≠ 0) (hsmall : ‖ε‖ + ‖δ‖ < 1 / 2)
    (hκ₁ : κ₁ ≠ 0) (hκ₂ : κ₂ ≠ 0)
    (hB₁ : IsFiniteBlaschke B₁ 7) (hB₂ : IsFiniteBlaschke B₂ 7)
    (hψd₁ : DifferentiableOn ℂ ψ₁ (ball 0 1)) (hψi₁ : InjOn ψ₁ (ball 0 1))
    (hψd₂ : DifferentiableOn ℂ ψ₂ (ball 0 1)) (hψi₂ : InjOn ψ₂ (ball 0 1))
    (hB₁ψ : ∀ z : ℂ, ‖z‖ < 1 → B₁ z = ε + δ * pfun (-s) (κ₁ * ψ₁ z))
    (hB₂ψ : ∀ z : ℂ, ‖z‖ < 1 → B₂ z = ε + δ * pfun s (κ₂ * ψ₂ z)) (k : ℕ) :
    Steklov.weightedSteklovEigenvalue (fun z => ‖deriv B₁ z‖) k =
      Steklov.weightedSteklovEigenvalue (fun z => ‖deriv B₂ z‖) k := by
  have hs' : (-s) ^ 2 = -7 := neg_sq_seven hs
  have hcr₁ := crit_of_disk hs' hδ hκ₁ hψd₁ hψi₁ hB₁ψ
  have hcr₂ := crit_of_disk hs hδ hκ₂ hψd₂ hψi₂ hB₂ψ
  obtain ⟨R₁, R₀₁, c₁, h₁⟩ := exists_bRadii hB₁ (by norm_num)
  obtain ⟨R₂, R₀₂, c₂, h₂⟩ := exists_bRadii hB₂ (by norm_num)
  have hc' : 1 < min c₁ c₂ := lt_min h₁.2.2.1 h₂.2.2.1
  have hc₁ : min c₁ c₂ ≤ c₁ := min_le_left _ _
  have hc₂ : min c₁ c₂ ≤ c₂ := min_le_right _ _
  have hε : ‖ε‖ < 1 / 2 := by linarith [norm_nonneg δ]
  have hCρ : Cset ε δ ⊆ ball 0 (1 / 2) := by
    intro w hw
    rw [mem_ball_zero_iff]
    rcases hw with rfl | hw
    · exact hε
    · rw [mem_singleton_iff] at hw; subst hw
      exact (norm_add_le _ _).trans_lt hsmall
  obtain ⟨r, A, γ0, γ1, L, L', φ, hr, hr2, hA, -, -, -, -, -, hrho⟩ := monodromy_full hs
  have hcv := critVals_neg hs
  have hA01 : (A : ℂ) ≠ 0 ∧ (A : ℂ) ≠ 1 := by
    have hmem : (A : ℂ) ∉ ({0, 1} : Set ℂ) := fun h =>
      A.2 (((Set.ext_iff.1 (critVals_pPoly hs)) (A : ℂ)).2 h)
    simpa [not_or] using hmem
  have hAn : ‖(A : ℂ)‖ < 1 / 2 := by
    rw [hA, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]; exact hr2
  have hx₀n : ‖ε + δ * (A : ℂ)‖ < 1 / 2 := by
    calc ‖ε + δ * (A : ℂ)‖ ≤ ‖ε‖ + ‖δ‖ * ‖(A : ℂ)‖ := by
          rw [← norm_mul]; exact norm_add_le _ _
      _ ≤ ‖ε‖ + ‖δ‖ := by
          gcongr; nlinarith [norm_nonneg δ, norm_nonneg (A : ℂ)]
      _ < 1 / 2 := hsmall
  have hx₀X : ε + δ * (A : ℂ) ∈ Xb (min c₁ c₂) (Cset ε δ) := by
    refine ⟨mem_ball_zero_iff.2 (hx₀n.trans (by linarith)), ?_⟩
    simp only [Cset, mem_insert_iff, mem_singleton_iff, not_or]
    constructor
    · intro h; apply hA01.1
      have : δ * (A : ℂ) = 0 := by linear_combination h
      exact (mul_eq_zero.1 this).resolve_left hδ
    · intro h; apply hA01.2
      have : δ * ((A : ℂ) - 1) = 0 := by linear_combination h
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hδ)
  set x₀ : Xb (min c₁ c₂) (Cset ε δ) := ⟨ε + δ * (A : ℂ), hx₀X⟩ with hx₀def
  have hx₀1 : ‖(x₀ : ℂ)‖ < 1 := hx₀n.trans (by norm_num)
  have hx₀ρ : ‖(x₀ : ℂ)‖ ≤ 1 / 2 := hx₀n.le
  have hb₀ : (A : ℂ) = ((x₀ : ℂ) - ε) / δ := by
    show (A : ℂ) = (ε + δ * (A : ℂ) - ε) / δ
    field_simp; ring
  have hb₀' : ((CoverIneq.idBase hcv A : Base (pPoly (-s))) : ℂ) = ((x₀ : ℂ) - ε) / δ :=
    (CoverIneq.idBase_val hcv A).trans hb₀
  have hsph := sphere_subset_Xb hc' (by norm_num : (1 / 2 : ℝ) < 1) hCρ
  -- the labellings of the two fibres over `x₀`
  set Lab₂ := fun a => L (fmap hs hδ h₂ hc₂ hB₂ψ x₀ hx₀1 A hb₀ a) with hLab₂def
  set Lab₁ := fun b => L' (fmap hs' hδ h₁ hc₁ hB₁ψ x₀ hx₀1 (CoverIneq.idBase hcv A) hb₀' b)
    with hLab₁def
  have hLab₂ : Function.Bijective Lab₂ := L.bijective.comp
    (fmap_bijective hs hδ h₂ hc₂ hψi₂ hB₂ψ hκ₂ hB₂ rfl hc' hcr₂ hsph x₀ hx₀1 A hb₀)
  have hLab₁ : Function.Bijective Lab₁ := L'.bijective.comp
    (fmap_bijective hs' hδ h₁ hc₁ hψi₁ hB₁ψ hκ₁ hB₁ rfl hc' hcr₁ hsph x₀ hx₀1 _ hb₀')
  -- the monodromy of both covers along small loops
  have hmon₂ : ∀ (cov₂ : IsCoveringMap (bproj B₂ R₀₂ (Xb (min c₁ c₂) (Cset ε δ))))
      (γ : Path x₀ x₀), (∀ t, ‖(γ t : ℂ)‖ ≤ 1 / 2) → ∀ a,
      Lab₂ (cov₂.monodromy (Path.Homotopic.Quotient.mk γ) a) =
        L.permCongr (monodromyPerm (pPoly s)
          (Path.Homotopic.Quotient.mk (basePath hs hδ γ A hb₀))) (Lab₂ a) := by
    intro cov₂ γ hγ a
    simp only [hLab₂def]
    rw [fmap_monodromy hs hδ h₂ hc₂ hB₂ψ hψd₂ (by norm_num : (1 / 2 : ℝ) < 1) cov₂ x₀ hx₀1 A
      hb₀ γ hγ (basePath hs hδ γ A hb₀) (basePath_apply hs hδ γ A hb₀) a,
      Equiv.permCongr_apply, Equiv.symm_apply_apply, monodromyPerm_apply]
  have hmon₁ : ∀ (cov₁ : IsCoveringMap (bproj B₁ R₀₁ (Xb (min c₁ c₂) (Cset ε δ))))
      (γ : Path x₀ x₀), (∀ t, ‖(γ t : ℂ)‖ ≤ 1 / 2) → ∀ b,
      Lab₁ (cov₁.monodromy (Path.Homotopic.Quotient.mk γ) b) =
        L'.permCongr (monodromyPerm (pPoly (-s))
          ((Path.Homotopic.Quotient.mk (basePath hs hδ γ A hb₀)).map
            (CoverIneq.idBaseC hcv))) (Lab₁ b) := by
    intro cov₁ γ hγ b
    have hpath : (Path.Homotopic.Quotient.mk (basePath hs hδ γ A hb₀)).map
        (CoverIneq.idBaseC hcv) =
        Path.Homotopic.Quotient.mk (basePath hs' hδ γ (CoverIneq.idBase hcv A) hb₀') := by
      rw [← Path.Homotopic.Quotient.mk_map]
      congr 1
    rw [hpath]
    simp only [hLab₁def]
    rw [fmap_monodromy hs' hδ h₁ hc₁ hB₁ψ hψd₁ (by norm_num : (1 / 2 : ℝ) < 1) cov₁ x₀ hx₀1 _
      hb₀' γ hγ (basePath hs' hδ γ _ hb₀') (basePath_apply hs' hδ γ _ hb₀') b,
      Equiv.permCongr_apply, Equiv.symm_apply_apply, monodromyPerm_apply]
  have hC := Cset_finite ε δ
  have hcolT : ∀ j j' : Fin 7, ∑ i, fanoT i j * fanoT i j' =
      @ite ℝ (j = j') (Classical.propDecidable _) 1 0 := fun j j' => by
    convert fanoT_col j j'
  have hrowT : ∀ j j' : Fin 7, ∑ i, fanoT j i * fanoT j' i =
      @ite ℝ (j = j') (Classical.propDecidable _) 1 0 := fun j j' => by
    convert fanoT_row j j'
  rcases hrho with hrho | hrho
  · -- `p_s` carries the line action, `p_{-s}` the point action
    have key : ∀ (cov₂ : IsCoveringMap (bproj B₂ R₀₂ (Xb (min c₁ c₂) (Cset ε δ))))
        (cov₁ : IsCoveringMap (bproj B₁ R₀₁ (Xb (min c₁ c₂) (Cset ε δ)))) (γ : Path x₀ x₀),
        (∀ t, ‖(γ t : ℂ)‖ ≤ 1 / 2) → ∀ a b,
        fanoT (Lab₂ (cov₂.monodromy (Path.Homotopic.Quotient.mk γ) a))
          (Lab₁ (cov₁.monodromy (Path.Homotopic.Quotient.mk γ) b)) = fanoT (Lab₂ a) (Lab₁ b) := by
      intro cov₂ cov₁ γ hγ a b
      rw [hmon₂ cov₂ γ hγ a, hmon₁ cov₁ γ hγ b,
        (hrho (Path.Homotopic.Quotient.mk (basePath hs hδ γ A hb₀))).1,
        (hrho (Path.Homotopic.Quotient.mk (basePath hs hδ γ A hb₀))).2]
      exact fanoT_rho _ _ _
    apply le_antisymm
    · exact weightedSteklovEigenvalue_le hB₂ hB₁ (by norm_num) h₂ h₁ hc' hc₂ hc₁
        (by norm_num) (by norm_num) hC hCρ hcr₂ hcr₁ x₀ hx₀ρ Lab₁ Lab₂ hLab₁ hLab₂
        (fun i j => fanoT j i) hrowT (fun cov₁ cov₂ γ hγ a b => key cov₂ cov₁ γ hγ b a) k
    · exact weightedSteklovEigenvalue_le hB₁ hB₂ (by norm_num) h₁ h₂ hc' hc₁ hc₂
        (by norm_num) (by norm_num) hC hCρ hcr₁ hcr₂ x₀ hx₀ρ Lab₂ Lab₁ hLab₂ hLab₁
        fanoT hcolT key k
  · -- `p_s` carries the point action, `p_{-s}` the line action
    have key : ∀ (cov₂ : IsCoveringMap (bproj B₂ R₀₂ (Xb (min c₁ c₂) (Cset ε δ))))
        (cov₁ : IsCoveringMap (bproj B₁ R₀₁ (Xb (min c₁ c₂) (Cset ε δ)))) (γ : Path x₀ x₀),
        (∀ t, ‖(γ t : ℂ)‖ ≤ 1 / 2) → ∀ a b,
        fanoT (Lab₁ (cov₁.monodromy (Path.Homotopic.Quotient.mk γ) b))
          (Lab₂ (cov₂.monodromy (Path.Homotopic.Quotient.mk γ) a)) = fanoT (Lab₁ b) (Lab₂ a) := by
      intro cov₂ cov₁ γ hγ a b
      rw [hmon₂ cov₂ γ hγ a, hmon₁ cov₁ γ hγ b,
        (hrho (Path.Homotopic.Quotient.mk (basePath hs hδ γ A hb₀))).1,
        (hrho (Path.Homotopic.Quotient.mk (basePath hs hδ γ A hb₀))).2]
      exact fanoT_rho _ _ _
    apply le_antisymm
    · exact weightedSteklovEigenvalue_le hB₂ hB₁ (by norm_num) h₂ h₁ hc' hc₂ hc₁
        (by norm_num) (by norm_num) hC hCρ hcr₂ hcr₁ x₀ hx₀ρ Lab₁ Lab₂ hLab₁ hLab₂
        fanoT hcolT (fun cov₁ cov₂ γ hγ b a => key cov₂ cov₁ γ hγ a b) k
    · exact weightedSteklovEigenvalue_le hB₁ hB₂ (by norm_num) h₁ h₂ hc' hc₁ hc₂
        (by norm_num) (by norm_num) hC hCρ hcr₁ hcr₂ x₀ hx₀ρ Lab₂ Lab₁ hLab₂ hLab₁
        (fun i j => fanoT j i) hrowT (fun cov₂ cov₁ γ hγ a b => key cov₂ cov₁ γ hγ a b) k

end pair

end ActualKernel

end
