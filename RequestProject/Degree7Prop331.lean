module

public import RequestProject.PullbackOrbisurface
public import RequestProject.Degree7QuotientDisk
public import RequestProject.FamilyIsospectral
public import RequestProject.FamilyNoncongruence
public import RequestProject.HolomorphicInverse

/-!
# Proposition 3.3.1 for the actual quotient orbisurfaces

For the paper's family (labels `P ↦ monicP s a_P`, `L ↦ monicP (-s) a_L`, `τ(ε)⁷ = (λ_* - 1) ε`,
normalized disk covers `(ψ_j, B_j)`), and **every** base orbifold metric
`L : BaseOrbMetric ε (λ_* ε) 2 3` (cone points of orders `2`, `3` at the branch values, Euclidean
near the boundary circle):

* `isBranchedDiskMap_of_cover`: `B_j` is a branched disk map in the sense of
  `IsBranchedDiskMap` — holomorphic on a disk `V ⊋ closed 𝔻` mapped into the domain of the base
  metric, circle to circle, finitely many points over `ε`, `λ_* ε`, all inside `𝔻`, unramified off
  them (critical values `{ε, λ_* ε}`, Lemma 3.2.1, and no critical points near the circle), and at
  every critical point over `ε` (resp. `λ_* ε`) **ramified of order exactly `2` (resp. `3`)**: this
  is derived from the exact passports `{2,2,1,1,1}`, `{3,3,1}` of `p_{±s}` (`ram_of_poly`), through
  the injective `ψ_j` and the affine normalisations;
* hence the pulled-back orbisurface `X_j = pullbackOrb L hB_j` is defined: metric
  `λ_X = λ₀(B_j z)|B_j'(z)|²` off `B_j⁻¹{ε, λ_* ε}`, smooth across the ramified points, cone points
  of order `2` at the unramified points over `ε` and of order `3` at those over `λ_* ε`, boundary
  line element `|B_j'|`;
* `prop_3_3_1`: for all small `ε`, the actual open quotients `(interior M_ε)/H_j` are identified
  with `𝔻` by homeomorphisms `Θ_j` under which the projection `A_ε ∘ π̄` becomes `B_j`
  (`quotient_interior_disk`), and the two orbisurfaces `X_P`, `X_L` — the quotients with the metric
  induced from `L` through `B_j` — have **equal Riemannian orbifold Steklov spectra with
  multiplicities** (`pullback_spectra_eq`, from `family_spectra_eq` and the metric Proposition
  2.2.1).
-/

@[expose] public section

open Polynomial Set Filter Topology Metric Steklov SteklovOrb SteklovBlaschke SteklovCoalescence
  SteklovCritical PolyCover LocalMonodromy SteklovRegularCover SteklovPunctured SteklovFill
  SteklovRiemann
open scoped ContDiff

noncomputable section

namespace Degree7

/-- **Ramification from the polynomial.**  If `B = w₀ + c · P(κ ψ)` on `𝔻` with `ψ` injective
holomorphic and every root of `P` simple or of multiplicity `m`, then at a critical point `z` of
`B` over `w₀` we have `B = w₀ + (x - z)^m g` with `g(z) ≠ 0`. -/
theorem ram_of_poly {B ψ : ℂ → ℂ} {P : ℂ[X]} {c κ w₀ : ℂ} {m : ℕ} (hc : c ≠ 0) (hκ : κ ≠ 0)
    (hψd : DifferentiableOn ℂ ψ (ball 0 1)) (hψi : InjOn ψ (ball 0 1)) (hP : P ≠ 0)
    (hform : ∀ x ∈ ball (0 : ℂ) 1, B x = w₀ + c * P.eval (κ * ψ x))
    (hmult : ∀ y, P.IsRoot y → P.rootMultiplicity y = 1 ∨ P.rootMultiplicity y = m)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) (hBz : B z = w₀) (hd : deriv B z = 0) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ g z ≠ 0 ∧ ∀ᶠ x in 𝓝 z, B x = w₀ + (x - z) ^ m * g x := by
  set y₀ := κ * ψ z
  have hroot : P.IsRoot y₀ := by
    have h := hform z hz
    rw [hBz] at h
    have : c * P.eval y₀ = 0 := by linear_combination -h
    exact (mul_eq_zero.1 this).resolve_left hc
  obtain ⟨q, hq, hndvd⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP y₀
  have hq0 : q.eval y₀ ≠ 0 := fun h => hndvd (dvd_iff_isRoot.2 h)
  have hψa : AnalyticAt ℂ ψ z := hψd.analyticOnNhd isOpen_ball z hz
  have hds : AnalyticAt ℂ (dslope ψ z) z := by
    obtain ⟨S, hS⟩ := hψa
    exact ⟨_, hS.has_fpower_series_dslope_fslope⟩
  have hψ' : deriv ψ z ≠ 0 := HolInv.deriv_ne_zero_of_injOn isOpen_ball hψd hψi hz
  obtain ⟨k, hkdef⟩ : ∃ k, k = P.rootMultiplicity y₀ := ⟨_, rfl⟩
  rw [← hkdef] at hq
  set G : ℂ → ℂ := fun x => c * κ ^ k * dslope ψ z x ^ k * q.eval (κ * ψ x) with hGdef
  have hlin : AnalyticAt ℂ (fun x => κ * ψ x) z := analyticAt_const.mul hψa
  have hqa : AnalyticAt ℂ (fun x => q.eval (κ * ψ x)) z :=
    AnalyticAt.comp (g := fun y => q.eval y) (f := fun x => κ * ψ x)
      ((Polynomial.differentiable q).analyticAt (κ * ψ z)) hlin
  have hGa : AnalyticAt ℂ G z := ((analyticAt_const.mul (hds.pow k)).mul hqa)
  have hG0 : G z ≠ 0 := by
    simp only [G, dslope_same]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc (pow_ne_zero _ hκ)) (pow_ne_zero _ hψ')) hq0
  have hBG : ∀ x ∈ ball (0 : ℂ) 1, B x = w₀ + (x - z) ^ k * G x := by
    intro x hx
    rw [hform x hx, hq, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
    have h := sub_smul_dslope ψ z x
    rw [smul_eq_mul] at h
    have : κ * ψ x - y₀ = κ * ((x - z) * dslope ψ z x) := by rw [h]; ring
    rw [this, mul_pow, mul_pow, hGdef]
    ring
  have hev : ∀ᶠ x in 𝓝 z, B x = w₀ + (x - z) ^ k * G x := by
    filter_upwards [isOpen_ball.mem_nhds hz] with x hx using hBG x hx
  rcases hmult y₀ hroot with hk | hk <;> rw [← hkdef] at hk
  · exfalso
    have hd' : HasDerivAt (fun x => w₀ + (x - z) ^ k * G x) (G z) z := by
      rw [hk]
      have h1 : HasDerivAt (fun x : ℂ => x - z) 1 z := (hasDerivAt_id z).sub_const z
      have := (h1.pow 1).mul hGa.differentiableAt.hasDerivAt
      have := this.const_add w₀
      first
        | simpa using this
        | simpa [Pi.add_def, Pi.sub_def, Pi.mul_def, Pi.neg_def, Function.comp_def] using this
        | exact (this.congr_deriv (by first | rfl | simp | (simp; ring))).congr_of_eventuallyEq
            (Filter.Eventually.of_forall fun _ => by first | rfl | simp | (simp; ring))
    have : deriv B z = G z := by
      rw [Filter.EventuallyEq.deriv_eq (show B =ᶠ[𝓝 z] _ from hev)]
      exact hd'.deriv
    exact hG0 (this ▸ hd)
  · exact ⟨G, hGa, hG0, by rw [← hk]; exact hev⟩

/-- The explicit form of `B_j` on `𝔻`. -/
lemma cover_form {t a : ℂ} (ht : t ^ 2 = -7) (ha : a ^ 7 = -bconst t) {τ : ℝ → ℂ} {ε : ℝ}
    {ψ B : ℂ → ℂ} (hc : IsNormalizedDiskCover (paperQ (monicP t a) τ ε) 7 ψ B) :
    ∀ x ∈ ball (0 : ℂ) 1, B x = (ε : ℂ) + (lamStar - 1) * ε * (pPoly t).eval (a / τ ε * ψ x) := by
  intro x hx
  rw [hc.2.2.2.2.2.2.2 x hx, paperQ, monicP_eval ht ha, pPoly_eval]
  congr 3
  ring

lemma multiplicity_zero {t : ℂ} (ht : t ^ 2 = -7) (y : ℂ) (hy : (pPoly t).IsRoot y) :
    (pPoly t).rootMultiplicity y = 1 ∨ (pPoly t).rootMultiplicity y = 2 := by
  rw [pPoly_rootMultiplicity ht hy]
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

lemma pPoly_sub_one_ne_zero {t : ℂ} (ht : t ^ 2 = -7) : pPoly t - C 1 ≠ 0 := by
  intro h
  have := card_roots_sub ht 1
  rw [h, roots_zero, Multiset.card_zero] at this
  exact absurd this (by norm_num)

lemma multiplicity_one {t : ℂ} (ht : t ^ 2 = -7) (y : ℂ) (hy : (pPoly t - C 1).IsRoot y) :
    (pPoly t - C 1).rootMultiplicity y = 1 ∨ (pPoly t - C 1).rootMultiplicity y = 3 := by
  have hmem : y ∈ (pPoly t - C 1).roots.toFinset :=
    Multiset.mem_toFinset.2 ((mem_roots (pPoly_sub_one_ne_zero ht)).2 hy)
  have h := Multiset.mem_map_of_mem (fun z => (pPoly t - C 1).rootMultiplicity z) hmem
  rw [passport_one ht] at h
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h
  rcases h with h | h | h
  · exact Or.inr h
  · exact Or.inr h
  · exact Or.inl h

/-- **The paper's Blaschke products are branched disk maps** with ramification exactly `2` over
`ε` and `3` over `λ_* ε` at their critical points, for every open `U₀ ⊇ closed 𝔻`. -/
theorem isBranchedDiskMap_of_cover {t a : ℂ} (ht : t ^ 2 = -7) (ha : a ^ 7 = -bconst t)
    {τ : ℝ → ℂ} (hτ : ∀ ε, τ ε ^ 7 = (lamStar - 1) * ε) {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 3)
    {ψ B : ℂ → ℂ} (hc : IsNormalizedDiskCover (paperQ (monicP t a) τ ε) 7 ψ B)
    (hcrit : FamilyNoncongr.critSet B = {(ε : ℂ), lamStar * ε})
    {U₀ : Set ℂ} (hU₀ : IsOpen U₀) (hcb : closedBall (0 : ℂ) 1 ⊆ U₀) :
    ∃ V : Set ℂ, IsBranchedDiskMap B V (ε : ℂ) (lamStar * ε) 2 3 U₀ := by
  have hδ : (lamStar - 1) * (ε : ℂ) ≠ 0 :=
    mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast h0.ne')
  have hτ0 : τ ε ≠ 0 := by
    intro h; have := hτ ε; rw [h, zero_pow (by norm_num)] at this; exact hδ this.symm
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [zero_pow (by norm_num)] at ha; exact bconst_ne_zero ht (neg_eq_zero.1 ha.symm)
  have hκ : a / τ ε ≠ 0 := div_ne_zero ha0 hτ0
  have hform := cover_form ht ha hc
  obtain ⟨hψd, hψi, -, -, -, -, hB, -⟩ := hc
  obtain ⟨R, R₀, c, hR₀, hR₀R, -, hdiff, hnorm, hfin, -, -, hnoCrit⟩ := hB.exists_radii (by norm_num)
  obtain ⟨hu1, hv1⟩ := branchValues_mem_disk h0 h1
  set W : Set ℂ := ball 0 R ∩ B ⁻¹' U₀
  have hW : IsOpen W := hdiff.continuousOn.isOpen_inter_preimage isOpen_ball hU₀
  have hcbW : closedBall (0 : ℂ) 1 ⊆ W := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 := by simpa using hz
    have hzR : z ∈ ball (0 : ℂ) R := by rw [mem_ball_zero_iff]; linarith
    refine ⟨hzR, hcb ?_⟩
    rw [mem_closedBall_zero_iff]
    rcases hz'.lt_or_eq with h | h
    · exact ((hnorm z hzR).1.2 h).le
    · exact ((hnorm z hzR).2.2 h).le
  obtain ⟨δ, hδpos, hsub⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_cthickening_subset_open hW hcbW
  rw [cthickening_closedBall hδpos.le zero_le_one] at hsub
  set r := min R₀ (1 + δ)
  have hr1 : 1 < r := lt_min hR₀ (by linarith)
  have hVR : ball (0 : ℂ) r ⊆ ball 0 R := ball_subset_ball (by
    have := min_le_left R₀ (1 + δ); linarith)
  have hcbV : closedBall (0 : ℂ) 1 ⊆ ball 0 r := closedBall_subset_ball hr1
  have hmemD : ∀ z ∈ ball (0 : ℂ) r, (B z = ε ∨ B z = lamStar * ε) → ‖z‖ < 1 := by
    intro z hz hzb
    have hBz : ‖B z‖ < 1 := by rcases hzb with h | h <;> rw [h] <;> assumption
    exact (hnorm z (hVR hz)).1.1 hBz
  refine ⟨ball 0 r, ⟨isOpen_ball, hcbV, (hdiff.mono hVR).analyticOnNhd isOpen_ball, ?_, ?_,
    hmemD, ?_, ?_, ?_, ?_⟩⟩
  · intro z hz
    have hz' : z ∈ closedBall (0 : ℂ) (δ + 1) := by
      rw [mem_closedBall_zero_iff]
      have := mem_ball_zero_iff.1 hz
      have := min_le_right R₀ (1 + δ)
      linarith
    exact (hsub hz').2
  · intro z hz
    have hz1 : ‖z‖ = 1 := by simpa using hz
    have hzR : z ∈ ball (0 : ℂ) R := hVR (hcbV (sphere_subset_closedBall hz))
    simpa using (hnorm z hzR).2.2 hz1
  · refine ((hfin (ε : ℂ)).union (hfin (lamStar * ε))).subset ?_
    rintro z ⟨hz, hzb⟩
    rcases hzb with h | h
    · exact Or.inl ⟨hVR hz, h⟩
    · exact Or.inr ⟨hVR hz, h⟩
  · intro z hz hu hv
    by_cases hz1 : ‖z‖ < 1
    · intro hd
      have : B z ∈ FamilyNoncongr.critSet B := ⟨z, hz1, hd, rfl⟩
      rw [hcrit] at this
      rcases this with h | h
      · exact hu h
      · exact hv h
    · exact hnoCrit z (not_lt.1 hz1) (by
        have := mem_ball_zero_iff.1 hz
        have := min_le_left R₀ (1 + δ)
        linarith)
  · intro z hz hBz hd
    have hz1 : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.2 (hmemD z hz (Or.inl hBz))
    exact ram_of_poly hδ hκ hψd hψi (pPoly_ne_zero ht) hform (multiplicity_zero ht) hz1 hBz hd
  · intro z hz hBz hd
    have hz1 : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.2 (hmemD z hz (Or.inr hBz))
    refine ram_of_poly hδ hκ hψd hψi (pPoly_sub_one_ne_zero ht) (fun x hx => ?_)
      (multiplicity_one ht) hz1 hBz hd
    rw [hform x hx, eval_sub, eval_C]
    ring

variable {s : ℂ}

/-- **Proposition 3.3.1 for the actual quotient orbisurfaces.**  For `s² = -7` there are the
ordered fibre `f₀` of the common regular cover (deck group `≅ GL(3, 𝔽₂)`, order `168`) and the
quotient maps `Ev₁, Ev₂` of the completed cover `R̄`, with fibres the orbits of the point and line
stabilizers `H_P = stabSub f₀ 0`, `H_L = stabSub f₀ 7`, such that for all `a_P, a_L, τ` of the
paper's normalisation and all sufficiently small `ε > 0`, for all normalized disk covers
`(ψ_P, B_P)`, `(ψ_L, B_L)` of the paper's polynomials:
* `(interior M_ε)/H_j ≃ₜ 𝔻` via `Θ_j`, with `B_j ∘ Θ_j = A_ε ∘ π̄` (the actual quotients are the
  unit disk with projection `B_j`);
* for **every** base orbifold metric `L` (orders `2`, `3` at `ε`, `λ_* ε`, Euclidean near the
  circle), `B_P`, `B_L` are branched disk maps and the induced quotient orbisurfaces
  `pullbackOrb L hP`, `pullbackOrb L hL` (metric `λ₀(B_j)|B_j'|²`, cone points of order `2`/`3` at
  the unramified points over `ε`/`λ_* ε`, boundary line element `|B_j'|`) have the same Riemannian
  orbifold Steklov spectrum, with multiplicities. -/
theorem prop_3_3_1 (hs : s ^ 2 = -7) :
    ∃ f₀ : OrdFib (projSum hs) 13,
      Nonempty (GL3F2.G ≃* deckGroup f₀) ∧ Nat.card (deckGroup f₀) = 168 ∧
      ∃ Ev₁ Ev₂ : RegFill hs f₀ → ℂ,
        (∀ w, (pPoly s).eval (Ev₁ w) = regFillProj hs f₀ w) ∧
        (∀ w, (pPoly (-s)).eval (Ev₂ w) = regFillProj hs f₀ w) ∧
        (∀ w w', Ev₁ w = Ev₁ w' ↔ (orbSetoid hs f₀ (stabSub f₀ 0)) w w') ∧
        (∀ w w', Ev₂ w = Ev₂ w' ↔ (orbSetoid hs f₀ (stabSub f₀ 7)) w w') ∧
        ∀ (aP aL : ℂ), aP ^ 7 = -bconst s → aL ^ 7 = -bconst (-s) →
        ∀ (τ : ℝ → ℂ), (∀ ε, τ ε ^ 7 = (lamStar - 1) * ε) →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ψP BP ψL BL : ℂ → ℂ,
          IsNormalizedDiskCover (paperQ (monicP s aP) τ ε) 7 ψP BP →
          IsNormalizedDiskCover (paperQ (monicP (-s) aL) τ ε) 7 ψL BL →
          (∃ Θ : QuotOn hs f₀ (interior (bordered hs f₀ ε)) (stabSub f₀ 0) ≃ₜ ball (0 : ℂ) 1,
            ∀ w, ψP (Θ (Quotient.mk _ w)) = τ ε * Ev₁ w / aP ∧
              BP (Θ (Quotient.mk _ w)) = bdf hs f₀ ε w) ∧
          (∃ Θ : QuotOn hs f₀ (interior (bordered hs f₀ ε)) (stabSub f₀ 7) ≃ₜ ball (0 : ℂ) 1,
            ∀ w, ψL (Θ (Quotient.mk _ w)) = τ ε * Ev₂ w / aL ∧
              BL (Θ (Quotient.mk _ w)) = bdf hs f₀ ε w) ∧
          ∀ L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3,
            ∃ (VP VL : Set ℂ) (hP : IsBranchedDiskMap BP VP (ε : ℂ) (lamStar * ε) 2 3 L.U)
              (hL : IsBranchedDiskMap BL VL (ε : ℂ) (lamStar * ε) 2 3 L.U),
              (pullbackOrb L hP).metricSteklovEigenvalue =
                (pullbackOrb L hL).metricSteklovEigenvalue ∧
              (pullbackOrb L hP).steklovSpectrum = (pullbackOrb L hL).steklovSpectrum := by
  obtain ⟨f₀, hiso, hcard, Ev₁, Ev₂, e₁, e₂, fib₁, fib₂, H⟩ := quotient_interior_disk hs
  have hs' : (-s) ^ 2 = -7 := by rw [neg_sq]; exact hs
  refine ⟨f₀, hiso, hcard, Ev₁, Ev₂, e₁, e₂, fib₁, fib₂, fun aP aL haP haL τ hτ => ?_⟩
  obtain ⟨ε₁, hε₁, HP⟩ := FamilyNoncongr.family_facts hs haP hτ
  obtain ⟨ε₂, hε₂, HL⟩ := FamilyNoncongr.family_facts hs' haL hτ
  have hpos : 0 < min (min ε₁ ε₂) (1 / 10 : ℝ) := lt_min (lt_min hε₁ hε₂) (by norm_num)
  filter_upwards [H aP aL haP haL τ hτ, Ioo_mem_nhdsGT hpos] with ε hQ hεI
  intro ψP BP ψL BL hcP hcL
  obtain ⟨h0, hlt⟩ := hεI
  have hlt1 : ε < ε₁ := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_left _ _))
  have hlt2 : ε < ε₂ := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_right _ _))
  have hlt3 : ε < 1 / 10 := lt_of_lt_of_le hlt (min_le_right _ _)
  obtain ⟨hΘP, hΘL⟩ := hQ ψP BP ψL BL hcP hcL
  refine ⟨hΘP, hΘL, fun L => ?_⟩
  have critP := (HP ε h0 hlt1 ψP BP hcP).2
  have critL := (HL ε h0 hlt2 ψL BL hcL).2
  obtain ⟨VP, hP⟩ := isBranchedDiskMap_of_cover hs haP hτ h0 (by linarith) hcP critP
    L.isOpen_U L.cb
  obtain ⟨VL, hL⟩ := isBranchedDiskMap_of_cover hs' haL hτ h0 (by linarith) hcL critL
    L.isOpen_U L.cb
  have spec := FamilyIso.family_spectra_eq hs haP haL hτ h0 hlt3 hcP hcL
  exact ⟨VP, VL, hP, hL, pullback_spectra_eq hP hL spec⟩

/-- The class of base orbifold metrics of Proposition 3.3.1 (orders `2`, `3` at `ε`, `λ_* ε`,
Euclidean near the circle) is nonempty for `0 < ε < 1/3`: the universally quantified statement
`prop_3_3_1` is not vacuous. -/
theorem baseOrbMetric_nonempty {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 3) :
    Nonempty (BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3) := by
  obtain ⟨hu, hv⟩ := branchValues_mem_disk h0 h1
  refine exists_baseOrbMetric hu hv ?_ le_rfl (by norm_num)
  intro h
  have hε : (ε : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
  have : (lamStar - 1) * (ε : ℂ) = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
  exact mul_ne_zero lamStar_sub_one_ne_zero hε this

end Degree7
