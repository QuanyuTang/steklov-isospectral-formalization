module

public import RequestProject.Degree7Prop331Geom
public import RequestProject.ConeUniformizer

/-!
# The quotient orbifold metric at the cone uniformizers of the actual quotients

For one label (`H`, `Ev`, `(ψ, B)`, `c = τ ε / a`) of the actual completed covering surface
`R̄ = RegFill hs f₀`, and every base orbifold metric `L`, we make the metric identification at the
filled points (cusps) fully explicit.  Write `χ_j` for the actual cusp chart at the filled point
`j` and

  `T_j(t) = ψ⁻¹((τ ε / a) · Ev(χ_j⁻¹ t))`  (`cuspT`)

for the quotient map `R̄ → X_j ≅ 𝔻` read in that chart.  `CuspCompat` packages, for every cusp:

* the cusp lies in `interior M_ε`, `T_j` is holomorphic at `0`, and for **every** quotient
  homeomorphism `Θ : (interior M_ε)/H ≃ₜ 𝔻` with `ψ ∘ Θ = c · Ev`, `T_j(0) = Θ[cusp]` and
  `T_j` represents `Θ` near `0`;
* **cone case** (`P'(Ev(cusp)) ≠ 0`, the stabilizer is the full rotation group of order
  `m = dB`): `p = T_j(0)` is a cone point of `pullbackOrb L hB` of order `m`; there is a holomorphic
  change of uniformizer `h` with `h(0) = 0`, `h'(0) ≠ 0`, `h(ζ t) = ζ h(t)` for all `ζ^m = 1`,
  `T_j(t) = p + h(t)^m`, compatible with the actual stabilizer rotations; and for **every** smooth
  lifted factor `μ_X` of the cone condition of `pullbackOrb L hB` at `p` (as supplied by its field
  `cone_metric`), for all small `t` **including `t = 0`**,

    `regMetric L χ_j t = μ_X(h t) · |h'(t)|²`;

* **ordinary case** (`P'(Ev(cusp)) = 0`): the stabilizer is trivial, `T_j(0)` is not a cone point,
  `T_j` is a local biholomorphic coordinate (injective on a ball, `T_j' ≠ 0`) and
  `regMetric L χ_j t = λ_X(T_j t) · |T_j'(t)|²` with `λ_X` smooth and positive there, including at
  `t = 0`.

`label_geometry_cone` proves `LabelGeometry ∧ CuspCompat` for the actual objects.
-/

@[expose] public section

open Polynomial Set Filter Topology Metric PolyCover LocalMonodromy SteklovRegularCover
  SteklovPunctured SteklovFill SteklovRiemann Manifold SteklovOrb SteklovCoalescence
  SteklovCritical
open scoped ContDiff

noncomputable section

namespace Degree7

variable {s : ℂ}

/-- The quotient map read in the actual cusp chart at the filled point `j`:
`T_j(t) = ψ⁻¹(c · Ev(χ_j⁻¹ t))`. -/
def cuspT (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (Ev : RegFill hs f₀ → ℂ) (c : ℂ)
    (ψ : ℂ → ℂ) (j : BIdx (regProj f₀) cB (1 / 2)) : ℂ → ℂ :=
  fun t => Function.invFunOn ψ (ball 0 1) (c * Ev ((Fill.cuspChart (E := regEnds hs f₀) j).symm t))

/-- **Explicit metric identification at the cone uniformizers** (see the module docstring). -/
def CuspCompat (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (H : Subgroup (deckGroup f₀))
    (P : ℂ[X]) (Ev : RegFill hs f₀ → ℂ) (ε : ℝ) (c : ℂ) (ψ B : ℂ → ℂ)
    (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3) {V : Set ℂ}
    (hB : IsBranchedDiskMap B V (ε : ℂ) (lamStar * ε) 2 3 L.U) : Prop :=
  ∀ j : BIdx (regProj f₀) cB (1 / 2),
    ∃ hj : (Fill.cusp j : RegFill hs f₀) ∈ interior (bordered hs f₀ ε),
    AnalyticAt ℂ (cuspT hs f₀ Ev c ψ j) 0 ∧
    -- `T_j` represents every compatible quotient homeomorphism, `T_j(0) = Θ[cusp]`
    (∀ Θ : QuotOn hs f₀ (interior (bordered hs f₀ ε)) H ≃ₜ ball (0 : ℂ) 1,
      (∀ w, ψ (Θ (Quotient.mk _ w)) = c * Ev w) →
      (Θ (Quotient.mk _ ⟨Fill.cusp j, hj⟩) : ℂ) = cuspT hs f₀ Ev c ψ j 0 ∧
      ∀ᶠ t in 𝓝 (0 : ℂ), ∃ ht : (Fill.cuspChart (E := regEnds hs f₀) j).symm t ∈
          interior (bordered hs f₀ ε),
        (Θ (Quotient.mk _ ⟨_, ht⟩) : ℂ) = cuspT hs f₀ Ev c ψ j t) ∧
    -- cone case: full rotation stabilizer of order `m = dB`
    (P.derivative.eval (Ev (Fill.cusp j)) ≠ 0 →
      Nat.card (stabIn H (Fill.cusp j : RegFill hs f₀)) = dB j.1 ∧
      (∃ i, (pullbackOrb L hB).pt i = cuspT hs f₀ Ev c ψ j 0 ∧
        (pullbackOrb L hB).ord i = dB j.1) ∧
      ∃ ρ > 0, ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = 0 ∧ deriv h 0 ≠ 0 ∧
        (∀ ζ t : ℂ, ζ ^ dB j.1 = 1 → h (ζ * t) = ζ * h t) ∧
        (∀ t ∈ ball (0 : ℂ) ρ,
          cuspT hs f₀ Ev c ψ j t = cuspT hs f₀ Ev c ψ j 0 + h t ^ dB j.1) ∧
        (∀ σ ∈ stabIn H (Fill.cusp j : RegFill hs f₀), ∃ ζ : ℂ, ζ ^ dB j.1 = 1 ∧
          ∀ t ∈ ball (0 : ℂ) ρ,
            regFillAct hs f₀ σ ((Fill.cuspChart (E := regEnds hs f₀) j).symm t) =
              (Fill.cuspChart (E := regEnds hs f₀) j).symm (ζ * t) ∧
            cuspT hs f₀ Ev c ψ j (ζ * t) = cuspT hs f₀ Ev c ψ j t ∧ h (ζ * t) = ζ * h t) ∧
        ∀ i, (pullbackOrb L hB).pt i = cuspT hs f₀ Ev c ψ j 0 → ∀ r > 0, ∀ μ : ℂ → ℝ,
          ContinuousOn μ (ball 0 r) →
          (∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → μ w =
            chartFactor (pullbackOrb L hB).lam ((pullbackOrb L hB).pt i)
              ((pullbackOrb L hB).ord i) w) →
          ∃ δ > 0, ∀ t ∈ ball (0 : ℂ) δ, h t ∈ ball (0 : ℂ) r ∧
            regMetric L (Fill.cuspChart (E := regEnds hs f₀) j) t = μ (h t) * ‖deriv h t‖ ^ 2) ∧
    -- ordinary case: trivial stabilizer, local biholomorphic coordinate
    (P.derivative.eval (Ev (Fill.cusp j)) = 0 →
      stabIn H (Fill.cusp j : RegFill hs f₀) = ⊥ ∧
      (∀ i, (pullbackOrb L hB).pt i ≠ cuspT hs f₀ Ev c ψ j 0) ∧
      ∃ δ > 0, InjOn (cuspT hs f₀ Ev c ψ j) (ball 0 δ) ∧
        ∀ t ∈ ball (0 : ℂ) δ, AnalyticAt ℂ (cuspT hs f₀ Ev c ψ j) t ∧
          deriv (cuspT hs f₀ Ev c ψ j) t ≠ 0 ∧
          ContDiffAt ℝ ∞ (pullbackOrb L hB).lam (cuspT hs f₀ Ev c ψ j t) ∧
          0 < (pullbackOrb L hB).lam (cuspT hs f₀ Ev c ψ j t) ∧
          regMetric L (Fill.cuspChart (E := regEnds hs f₀) j) t =
            (pullbackOrb L hB).lam (cuspT hs f₀ Ev c ψ j t) *
              ‖deriv (cuspT hs f₀ Ev c ψ j) t‖ ^ 2)

/-- **The geometric package together with the explicit cone-uniformizer metric identification**,
for each label, every base orbifold metric `L` and branched-disk-map structure `hB`. -/
theorem label_geometry_cone (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13)
    (H : Subgroup (deckGroup f₀)) {t : ℂ} (ht : t ^ 2 = -7) {Ev : RegFill hs f₀ → ℂ}
    (hEv : haveI := (regFill_riemannSurface hs f₀).2.1; ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev)
    (hPEv : ∀ w, (pPoly t).eval (Ev w) = regFillProj hs f₀ w)
    (hpr : IsProperMap Ev) (hsurj : Function.Surjective Ev)
    (hfib : ∀ w w', Ev w = Ev w' ↔ ∃ σ ∈ H, regFillAct hs f₀ σ w = w')
    (hq : ∀ (ε : ℝ) w, (SteklovDiskCovers.coverPoly (pPoly t) ε).eval (Ev w) =
      affA ε (regFillProj hs f₀ w))
    {a : ℂ} (ha : a ^ 7 = -bconst t) {τ : ℝ → ℂ} (hτ : ∀ ε, τ ε ^ 7 = (lamStar - 1) * ε)
    {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1 / 3)
    (hconn : IsPreconnected (paperQ (monicP t a) τ ε ⁻¹' ball 0 1))
    {ψ B : ℂ → ℂ} (hc : IsNormalizedDiskCover (paperQ (monicP t a) τ ε) 7 ψ B)
    (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3) {V : Set ℂ}
    (hB : IsBranchedDiskMap B V (ε : ℂ) (lamStar * ε) 2 3 L.U) :
    LabelGeometry hs f₀ H (pPoly t) Ev ε (τ ε / a) ψ B L hB ∧
      CuspCompat hs f₀ H (pPoly t) Ev ε (τ ε / a) ψ B L hB := by
  have hLG := label_geometry hs f₀ H ht hEv hPEv hpr hsurj hfib hq ha hτ h0 h1 hconn hc L hB
  refine ⟨hLG, ?_⟩
  obtain ⟨Θ, -, hΘ, -, -, -, hchart, hconeiff, hord, -, -, -⟩ := hLG
  haveI := (regFill_riemannSurface hs f₀).2.1
  have hψd := hc.1
  have hψi := hc.2.1
  intro j
  set χ := Fill.cuspChart (E := regEnds hs f₀) j with hχdef
  set T := cuspT hs f₀ Ev (τ ε / a) ψ j with hTdef
  have hχ : χ ∈ atlas ℂ (RegFill hs f₀) := cuspChart_mem_atlas j
  have hr := (regEnds hs f₀).r_pos j
  have h0t : (0 : ℂ) ∈ χ.target := mem_ball_self hr
  have hj : (Fill.cusp j : RegFill hs f₀) ∈ interior (bordered hs f₀ ε) := by
    rw [(regBorderedSurface hs f₀ h0 h1).2.2.1]
    exact ((regBordered hs f₀ h0 h1).2.2.1 j).trans (collarRad_lt h0 h1)
  have hj' : χ.symm 0 ∈ interior (bordered hs f₀ ε) := by rw [cuspChart_symm_zero]; exact hj
  have hΘT : ∀ Θ' : QuotOn hs f₀ (interior (bordered hs f₀ ε)) H ≃ₜ ball (0 : ℂ) 1,
      (∀ w, ψ (Θ' (Quotient.mk _ w)) = τ ε / a * Ev w) → ∀ w,
        (Θ' (Quotient.mk _ w) : ℂ) = Function.invFunOn ψ (ball 0 1) (τ ε / a * Ev w) := by
    intro Θ' h' w
    rw [← h' w]; exact (HolInv.invFunOn_apply_self hψi (Θ' _).2).symm
  have hT0 : T 0 = Function.invFunOn ψ (ball 0 1) (τ ε / a * Ev (Fill.cusp j)) := by
    show Function.invFunOn ψ (ball 0 1) (τ ε / a * Ev (χ.symm 0)) = _
    rw [cuspChart_symm_zero]
  have hevi : ∀ᶠ t in 𝓝 (0 : ℂ), χ.symm t ∈ interior (bordered hs f₀ ε) :=
    (χ.continuousAt_symm h0t).preimage_mem_nhds (isOpen_interior.mem_nhds hj')
  have hΘ0 : (Θ (Quotient.mk _ ⟨Fill.cusp j, hj⟩) : ℂ) = T 0 := by
    rw [hT0]; exact hΘT Θ (fun w => (hΘ w).1) _
  have hTa : AnalyticAt ℂ T 0 := (hchart χ hχ 0 h0t hj').1
  -- the descended metric identity at points with trivial stabilizer
  have hmetric : ∀ t ∈ ball (0 : ℂ) ((regEnds hs f₀).r j),
      ∀ hti : χ.symm t ∈ interior (bordered hs f₀ ε),
      Nat.card (stabIn H (χ.symm t)) = 1 →
      T t ∉ coneSet B V (ε : ℂ) (lamStar * ε) ∧
      regMetric L χ t = (pullbackOrb L hB).lam (T t) * ‖deriv T t‖ ^ 2 := by
    intro t ht hti hcard
    have hnc : (Θ (Quotient.mk _ ⟨χ.symm t, hti⟩) : ℂ) ∉ coneSet B V (ε : ℂ) (lamStar * ε) :=
      fun hcon => (hconeiff ⟨_, hti⟩).1 hcon hcard
    have hΘt : (Θ (Quotient.mk _ ⟨χ.symm t, hti⟩) : ℂ) = T t :=
      hΘT Θ (fun w => (hΘ w).1) _
    refine ⟨hΘt ▸ hnc, (hchart χ hχ t ht hti).2.2.2 hnc⟩
  have hinl : ∀ t ∈ ball (0 : ℂ) ((regEnds hs f₀).r j), t ≠ 0 →
      Nat.card (stabIn H (χ.symm t)) = 1 := by
    intro t ht ht0
    obtain ⟨f, hf⟩ := cuspChart_symm_inl j ht ht0
    rw [hf, stabIn_inl, Subgroup.card_bot]
  refine ⟨hj, hTa, fun Θ' h' => ⟨by rw [hT0]; exact hΘT Θ' h' _, ?_⟩, fun hreg => ?_,
    fun hcrit => ?_⟩
  · filter_upwards [hevi] with t ht using ⟨ht, hΘT Θ' h' _⟩
  · -- cone case
    have hstab := stab_card_noncrit hEv hPEv hfib j hreg
    have hm := dB_le_three j.1
    have hcon : (Θ (Quotient.mk _ ⟨Fill.cusp j, hj⟩) : ℂ) ∈ coneSet B V (ε : ℂ) (lamStar * ε) :=
      (hconeiff ⟨_, hj⟩).2 (by rw [hstab.1]; omega)
    rw [← pullbackOrb_range_pt hB] at hcon
    obtain ⟨i₀, hi₀⟩ := hcon
    have hordi : ∀ i, (pullbackOrb L hB).pt i = T 0 → (pullbackOrb L hB).ord i = dB j.1 := by
      intro i hi
      rw [hord ⟨_, hj⟩ i (hi.trans hΘ0.symm)]; exact hstab.1
    obtain ⟨ρ₁, hρ₁, G, hGa, hG', hGc, hGeq⟩ := local_power_map hEv hPEv j hreg
    set p₀ : ℂ := (Θ (Quotient.mk _ ⟨Fill.cusp j, hj⟩) : ℂ)
    have hp₀ : p₀ ∈ ball (0 : ℂ) 1 := (Θ _).2
    have hψp₀ : ψ p₀ = τ ε / a * G (cB j.1) := by rw [hGc]; exact (hΘ _).1
    set K : ℂ → ℂ := fun z => Function.invFunOn ψ (ball 0 1) (τ ε / a * G z)
    have hinvA := analyticAt_invFunOn_disk hψd hψi hp₀
    have hKa : AnalyticAt ℂ K (cB j.1) :=
      AnalyticAt.comp_of_eq (g := Function.invFunOn ψ (ball 0 1))
        (f := fun z => τ ε / a * G z) hinvA (analyticAt_const.mul hGa) hψp₀.symm
    have hK' : deriv K (cB j.1) ≠ 0 := by
      have hinv := HolInv.hasDerivAt_invFunOn isOpen_ball hψd hψi hp₀
        (HolInv.deriv_ne_zero_of_injOn isOpen_ball hψd hψi hp₀)
      rw [hψp₀] at hinv
      have hin : HasDerivAt (fun z => τ ε / a * G z) (τ ε / a * deriv G (cB j.1)) (cB j.1) :=
        hGa.differentiableAt.hasDerivAt.const_mul _
      have hKd' := HasDerivAt.comp (h := fun z => τ ε / a * G z) (cB j.1) hinv hin
      have hKd : HasDerivAt K ((deriv ψ p₀)⁻¹ * (τ ε / a * deriv G (cB j.1))) (cB j.1) := hKd'
      rw [hKd.deriv]
      refine mul_ne_zero (inv_ne_zero (HolInv.deriv_ne_zero_of_injOn isOpen_ball hψd hψi hp₀))
        (mul_ne_zero (div_ne_zero (tau_ne_zero hτ h0) (a_ne_zero ht ha)) hG')
    have hTK : ∀ t ∈ ball (0 : ℂ) ρ₁, T t = K (cB j.1 + t ^ dB j.1) := by
      intro t ht'
      show Function.invFunOn ψ (ball 0 1) (τ ε / a * Ev (χ.symm t)) = _
      rw [hGeq t ht']
    have hKT0 : K (cB j.1) = T 0 := by
      rw [hTK 0 (mem_ball_self hρ₁), zero_pow (dB_pos j.1).ne', add_zero]
    obtain ⟨h, hha, hh0, hh', hequi, hev⟩ :=
      ConeUnif.exists_equivariant_uniformizer (dB_pos j.1) hKa hK'
    obtain ⟨ρ₂, hρ₂, hρ₂'⟩ := Metric.eventually_nhds_iff_ball.1 hev
    set ρ := min ρ₂ (min ρ₁ ((regEnds hs f₀).r j))
    have hρ : 0 < ρ := lt_min hρ₂ (lt_min hρ₁ hr)
    have hρ2 : ∀ t ∈ ball (0 : ℂ) ρ, t ∈ ball (0 : ℂ) ρ₂ :=
      fun t ht' => ball_subset_ball (min_le_left _ _) ht'
    have hρ1 : ∀ t ∈ ball (0 : ℂ) ρ, t ∈ ball (0 : ℂ) ρ₁ :=
      fun t ht' => ball_subset_ball ((min_le_right _ _).trans (min_le_left _ _)) ht'
    have hρr : ∀ t ∈ ball (0 : ℂ) ρ, t ∈ ball (0 : ℂ) ((regEnds hs f₀).r j) :=
      fun t ht' => ball_subset_ball ((min_le_right _ _).trans (min_le_right _ _)) ht'
    have hTh : ∀ t ∈ ball (0 : ℂ) ρ, T t = T 0 + h t ^ dB j.1 := by
      intro t ht'
      rw [hTK t (hρ1 t ht'), hρ₂' t (hρ2 t ht'), hKT0]
    refine ⟨hstab.1, ⟨i₀, hi₀.trans hΘ0, hordi i₀ (hi₀.trans hΘ0)⟩, ρ, hρ, h, hha, hh0, hh',
      hequi, hTh, ?_, ?_⟩
    · intro σ hσ
      obtain ⟨hσH, hσj⟩ := mem_stabIn.1 hσ
      obtain ⟨ζ, hζ, hrot⟩ := rot_formula σ j (cuspAct_eq_of_fix hσj)
      refine ⟨ζ, hζ, fun t ht' => ⟨hrot t (hρr t ht'), ?_, hequi ζ t hζ⟩⟩
      show Function.invFunOn ψ (ball 0 1) (τ ε / a * Ev (χ.symm (ζ * t))) =
        Function.invFunOn ψ (ball 0 1) (τ ε / a * Ev (χ.symm t))
      rw [← hrot t (hρr t ht'), Ev_inv hfib hσH]
    · intro i hi r' hr' μ hμc hμ
      have hoi := hordi i hi
      rw [hoi, hi] at hμ
      have hFev : ∀ᶠ t in 𝓝 (0 : ℂ), T t = T 0 + h t ^ dB j.1 := by
        filter_upwards [ball_mem_nhds (0 : ℂ) hρ] with t ht' using hTh t ht'
      have hg : ContinuousAt (regMetric L χ) 0 :=
        (regMetric_cusp h0 h1 L j).2.2.2.1.continuousAt
      have hgF : ∀ᶠ t in 𝓝[≠] (0 : ℂ),
          regMetric L χ t = (pullbackOrb L hB).lam (T t) * ‖deriv T t‖ ^ 2 := by
        filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds (0 : ℂ) hr),
          nhdsWithin_le_nhds hevi] with t ht0 htr hti
        exact (hmetric t htr hti (hinl t htr ht0)).2
      have := ConeUnif.metric_eq_at_filled_point hha hh0 hh' hFev hr' hμc hμ hg hgF
      obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff_ball.1 this
      exact ⟨δ, hδ, hδ'⟩
  · -- ordinary case
    have hbot := (stab_card_crit hEv (pPoly_degree_pos ht) hPEv hfib j hcrit).1
    have hcard : ∀ t ∈ ball (0 : ℂ) ((regEnds hs f₀).r j),
        Nat.card (stabIn H (χ.symm t)) = 1 := by
      intro t ht'
      by_cases ht0 : t = 0
      · rw [ht0, cuspChart_symm_zero, hbot, Subgroup.card_bot]
      · exact hinl t ht' ht0
    have hnotcone : ∀ i, (pullbackOrb L hB).pt i ≠ T 0 := by
      intro i hi
      have hcon : (Θ (Quotient.mk _ ⟨Fill.cusp j, hj⟩) : ℂ) ∈
          coneSet B V (ε : ℂ) (lamStar * ε) := by
        rw [hΘ0, ← hi, ← pullbackOrb_range_pt hB]; exact ⟨i, rfl⟩
      exact (hconeiff ⟨_, hj⟩).1 hcon (by rw [hbot, Subgroup.card_bot])
    have hloc : ∀ᶠ t in 𝓝 (0 : ℂ),
        T t ∉ coneSet B V (ε : ℂ) (lamStar * ε) ∧ T t ∈ V ∧
        regMetric L χ t = (pullbackOrb L hB).lam (T t) * ‖deriv T t‖ ^ 2 := by
      filter_upwards [ball_mem_nhds (0 : ℂ) hr, hevi] with t htr hti
      obtain ⟨hnc, hmt⟩ := hmetric t htr hti (hcard t htr)
      refine ⟨hnc, ?_, hmt⟩
      have hx : T t = (Θ (Quotient.mk _ ⟨χ.symm t, hti⟩) : ℂ) :=
        (hΘT Θ (fun w => (hΘ w).1) ⟨_, hti⟩).symm
      rw [hx]
      exact hB.cb (ball_subset_closedBall (Θ _).2)
    have hd0 : deriv T 0 ≠ 0 := by
      intro hd
      have hpos := (regMetric_cusp h0 h1 L j).2.2.2.2
      rw [hloc.self_of_nhds.2.2, hd, norm_zero] at hpos
      simp at hpos
    have hall : ∀ᶠ t in 𝓝 (0 : ℂ), AnalyticAt ℂ T t ∧ deriv T t ≠ 0 ∧
        (T t ∉ coneSet B V (ε : ℂ) (lamStar * ε) ∧ T t ∈ V ∧
        regMetric L χ t = (pullbackOrb L hB).lam (T t) * ‖deriv T t‖ ^ 2) :=
      hTa.eventually_analyticAt.and
        ((hTa.deriv.continuousAt.eventually_ne hd0).and hloc)
    obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.eventually_nhds_iff_ball.1 hall
    obtain ⟨ρ', hρ', hinj⟩ := HolInv.exists_ball_injOn isOpen_ball
      (fun x hx => (hδ₀' x hx).1.differentiableAt.differentiableWithinAt)
      (mem_ball_self hδ₀) hd0
    refine ⟨hbot, hnotcone, min δ₀ ρ', lt_min hδ₀ hρ',
      hinj.mono (ball_subset_ball (min_le_right _ _)), fun t ht' => ?_⟩
    obtain ⟨hA, hD, hnc, hV, hM⟩ := hδ₀' t (ball_subset_ball (min_le_left _ _) ht')
    obtain ⟨hs1, hs2⟩ := smooth_at_noncone hB hV hnc
    exact ⟨hA, hD, hs1, hs2, hM⟩

/-- **The identity with the factor supplied by `cone_metric`.**  From `CuspCompat`, at a cusp with
`P'(Ev(cusp)) ≠ 0`: the cone point `p = T_j(0)` of `pullbackOrb L hB`, the smooth positive lifted
factor `μ_X` given by the field `(pullbackOrb L hB).cone_metric` at `p`, and the equivariant
uniformizer change `h` satisfy `regMetric L χ_j t = μ_X(h t)|h'(t)|²` for all small `t`,
including `t = 0`. -/
theorem CuspCompat.cone_metric_identity {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13}
    {H : Subgroup (deckGroup f₀)} {P : ℂ[X]} {Ev : RegFill hs f₀ → ℂ} {ε : ℝ} {c : ℂ}
    {ψ B : ℂ → ℂ} {L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3} {V : Set ℂ}
    {hB : IsBranchedDiskMap B V (ε : ℂ) (lamStar * ε) 2 3 L.U}
    (hC : CuspCompat hs f₀ H P Ev ε c ψ B L hB) (j : BIdx (regProj f₀) cB (1 / 2))
    (hreg : P.derivative.eval (Ev (Fill.cusp j)) ≠ 0) :
    ∃ i, (pullbackOrb L hB).pt i = cuspT hs f₀ Ev c ψ j 0 ∧ (pullbackOrb L hB).ord i = dB j.1 ∧
      ∃ r > 0, ∃ μ : ℂ → ℝ, ContDiffOn ℝ ∞ μ (ball 0 r) ∧ (∀ w ∈ ball (0 : ℂ) r, 0 < μ w) ∧
        (∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → μ w =
          chartFactor (pullbackOrb L hB).lam ((pullbackOrb L hB).pt i)
            ((pullbackOrb L hB).ord i) w) ∧
        ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 = 0 ∧ deriv h 0 ≠ 0 ∧
          (∀ ζ t : ℂ, ζ ^ dB j.1 = 1 → h (ζ * t) = ζ * h t) ∧
          ∃ δ > 0, ∀ t ∈ ball (0 : ℂ) δ,
            cuspT hs f₀ Ev c ψ j t = cuspT hs f₀ Ev c ψ j 0 + h t ^ dB j.1 ∧
            h t ∈ ball (0 : ℂ) r ∧
            regMetric L (Fill.cuspChart (E := regEnds hs f₀) j) t = μ (h t) * ‖deriv h t‖ ^ 2 := by
  obtain ⟨-, -, -, hcone, -⟩ := hC j
  obtain ⟨-, ⟨i, hi, hoi⟩, ρ, hρ, h, hha, hh0, hh', hequi, hTh, -, hmet⟩ := hcone hreg
  obtain ⟨r, hr, μ, hμs, hμp, hμe⟩ := (pullbackOrb L hB).cone_metric i
  obtain ⟨δ, hδ, hδ'⟩ := hmet i hi r hr μ hμs.continuousOn hμe
  refine ⟨i, hi, hoi, r, hr, μ, hμs, hμp, hμe, h, hha, hh0, hh', hequi, min δ ρ,
    lt_min hδ hρ, fun t ht => ?_⟩
  have ht1 : t ∈ ball (0 : ℂ) δ := ball_subset_ball (min_le_left _ _) ht
  have ht2 : t ∈ ball (0 : ℂ) ρ := ball_subset_ball (min_le_right _ _) ht
  exact ⟨hTh t ht2, (hδ' t ht1).1, (hδ' t ht1).2⟩

end Degree7
