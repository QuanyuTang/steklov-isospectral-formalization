module

public import RequestProject.Degree7ConeMetric

/-!
# Proposition 3.3.1 for the actual quotients, with one fixed ordered fibre `f₀`

`prop_3_3_1_full` collects, **for one and the same ordered fibre `f₀`** of the common regular
cover (no unrelated existential witnesses are joined):

* the regular cover `RegCov f₀` is path connected and its branched completion `R̄ = RegFill hs f₀`
  is connected; the extended deck action on `R̄` is by holomorphic bijections, preserves `π̄`, and is
  an action (`regFillAct 1 = id`, `regFillAct (σ τ) = regFillAct τ ∘ regFillAct σ`);
* `|deck| = 168` and the explicit isomorphism `ι : GL(3, 𝔽₂) ≃* deck` (the actual combined
  monodromy representation) carrying conjugates of `HP`, `HL` onto `stabSub f₀ 0`, `stabSub f₀ 7`
  (up to the label swap);
* the holomorphic quotient maps `Ev₁`, `Ev₂` with fibres the stabilizer orbits;
* for every `0 < ε < 1/3`: `M_ε` is compact, closed, deck invariant, `interior M_ε = {‖b_ε‖ < 1}`,
  `frontier M_ε = ∂M_ε`, `closure (interior M_ε) = M_ε`, both `M_ε` and `interior M_ε` are connected,
  the boundary-chart property of `regBorderedSurface` holds, and for every base orbifold metric `L`
  the pulled-back metric `regMetric L` of `R̄` has all the properties of `prop_3_3_1_geometric`;
* for all paper normalisations, small `ε`, normalized disk covers and **every** base orbifold
  metric `L`: `LabelGeometry` **and** the explicit cone-uniformizer identification `CuspCompat`
  for both labels, and equal Steklov spectra (with multiplicities) of the two quotient
  orbisurfaces.
-/

@[expose] public section

open Polynomial Set Filter Topology Metric PolyCover LocalMonodromy SteklovRegularCover
  SteklovPunctured SteklovFill SteklovRiemann Manifold SteklovOrb SteklovCoalescence
  SteklovCritical
open scoped ContDiff

noncomputable section

namespace Degree7

variable {s : ℂ}

/-- `completed_quotient_identifications_deck`, additionally recording that the regular cover of
the chosen ordered fibre is path connected. -/
theorem completed_quotient_identifications_conn (hs : s ^ 2 = -7) :
    ∃ f₀ : OrdFib (projSum hs) 13, PathConnectedSpace (RegCov f₀) ∧
      (deckGroup f₀ = (combRho rhoL rhoP).range ∨ deckGroup f₀ = (combRho rhoP rhoL).range) ∧
      Nat.card (deckGroup f₀) = 168 ∧
      ∃ Ev₁ Ev₂ : RegFill hs f₀ → ℂ,
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev₁ ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev₂ ∧
        (∀ w, (pPoly s).eval (Ev₁ w) = regFillProj hs f₀ w) ∧
        (∀ w, (pPoly (-s)).eval (Ev₂ w) = regFillProj hs f₀ w) ∧
        (∀ w w', Ev₁ w = Ev₁ w' ↔ ∃ σ : deckGroup f₀, σ.1 0 = 0 ∧ regFillAct hs f₀ σ w = w') ∧
        (∀ w w', Ev₂ w = Ev₂ w' ↔ ∃ σ : deckGroup f₀, σ.1 7 = 7 ∧ regFillAct hs f₀ σ w = w') ∧
        Function.Surjective Ev₁ ∧ Function.Surjective Ev₂ ∧
        IsProperMap Ev₁ ∧ IsProperMap Ev₂ ∧
        (∀ (ε : ℝ) w, (SteklovDiskCovers.coverPoly (pPoly s) ε).eval (Ev₁ w) =
          affA ε (regFillProj hs f₀ w)) ∧
        (∀ (ε : ℝ) w, (SteklovDiskCovers.coverPoly (pPoly (-s)) ε).eval (Ev₂ w) =
          affA ε (regFillProj hs f₀ w)) := by
  obtain ⟨A, f₀, -, -, hpc, hdeck, -, hcard, -, -, -, -, ⟨ev₁, hc₁, hs₁, hp₁, hf₁⟩,
    ⟨ev₂, hc₂, hs₂, hp₂, hf₂⟩⟩ := common_regular_cover hs
  have hs' : (-s) ^ 2 = -7 := by rw [neg_sq]; exact hs
  obtain ⟨hk₁, hPk₁, hP'₁, hsu₁⟩ := coord_data (e := Homeomorph.refl _)
    (fun _ => rfl) hc₁ hs₁ hp₁ (critVals_pPoly hs)
  obtain ⟨hk₂, hPk₂, hP'₂, hsu₂⟩ := coord_data
    (e := baseHomeoG (critVals_neg hs)) (baseHomeoG_val _) hc₂ hs₂ hp₂ (critVals_pPoly hs')
  have hfib₁ : ∀ f f', (ev₁ f : ℂ) = ev₁ f' ↔ ∃ σ ∈ {σ : deckGroup f₀ | σ.1 0 = 0},
      regAct f₀ σ f = f' := fun f f' => Subtype.ext_iff.symm.trans (hf₁ f f')
  have hfib₂ : ∀ f f', (ev₂ f : ℂ) = ev₂ f' ↔ ∃ σ ∈ {σ : deckGroup f₀ | σ.1 7 = 7},
      regAct f₀ σ f = f' := fun f f' => Subtype.ext_iff.symm.trans (hf₂ f f')
  obtain ⟨m₁, -, e₁, q₁, su₁, pr₁, c₁⟩ :=
    quotient_ident hs f₀ (pPoly_degree_pos hs) hk₁ hPk₁ hP'₁ _ hfib₁ hsu₁
  obtain ⟨m₂, -, e₂, q₂, su₂, pr₂, c₂⟩ :=
    quotient_ident hs f₀ (pPoly_degree_pos hs') hk₂ hPk₂ hP'₂ _ hfib₂ hsu₂
  exact ⟨f₀, hpc, hdeck, hcard, _, _, m₁, m₂, e₁, e₂, q₁, q₂, su₁, su₂, pr₁, pr₂, c₁, c₂⟩

/-- Connectedness of `R̄`, `M_ε` and `interior M_ε` from connectedness of the regular cover and
surjectivity of `π̄` (the argument of `actual_bordered_surface`, for an arbitrary `f₀`). -/
theorem regFill_connected_of (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13)
    [ConnectedSpace (RegCov f₀)] (hsurj : Function.Surjective (regFillProj hs f₀)) :
    ConnectedSpace (RegFill hs f₀) ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 3 →
      IsConnected (bordered hs f₀ ε) ∧ IsConnected (interior (bordered hs f₀ ε)) := by
  have hconn : ConnectedSpace (RegFill hs f₀) := by
    have hrc : IsConnected (range (Fill.inl (E := regEnds hs f₀))) :=
      isConnected_range Fill.continuous_inl
    have := hrc.closure
    rw [Fill.dense_range_inl.closure_eq] at this
    exact connectedSpace_iff_univ.2 this
  refine ⟨hconn, fun ε h0 h1 => ?_⟩
  have hε : ε ≠ 0 := h0.ne'
  have hcov := isCoveringMapOn_bdf hs f₀ h0 h1
  have hr := collarRad_nonneg ε
  have hr1 := collarRad_lt h0 h1
  have hne : ∃ w, ‖bdf hs f₀ ε w‖ < 1 := by
    obtain ⟨w, hw⟩ := hsurj ((affHomeo hε).symm 0)
    refine ⟨w, ?_⟩
    show ‖affA ε (regFillProj hs f₀ w)‖ < 1
    rw [hw, ← affHomeo_apply hε, Homeomorph.apply_symm_apply]; simp
  obtain ⟨w₀, hw₀⟩ := hne
  have hint := (regBorderedSurface hs f₀ h0 h1).2.2.1
  refine ⟨⟨⟨w₀, hw₀.le⟩, SteklovBordered.isPreconnected_sublevel (continuous_bdf hs f₀ ε) hr
    hr1 hcov⟩, ?_⟩
  rw [hint]
  exact ⟨⟨w₀, hw₀⟩, SteklovBordered.isPreconnected_strictSublevel (continuous_bdf hs f₀ ε) hr
    hr1 hcov⟩

/-- **Proposition 3.3.1 for the actual quotients `X_j = M_ε / H_j`, with one fixed `f₀`**
(see the module docstring). -/
theorem prop_3_3_1_full (hs : s ^ 2 = -7) :
    ∃ f₀ : OrdFib (projSum hs) 13,
      PathConnectedSpace (RegCov f₀) ∧ ConnectedSpace (RegFill hs f₀) ∧
      -- the actual extended deck action on `R̄`
      (∀ σ : deckGroup f₀, ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (regFillAct hs f₀ σ) ∧
        Function.Bijective (regFillAct hs f₀ σ) ∧
        ∀ w, regFillProj hs f₀ (regFillAct hs f₀ σ w) = regFillProj hs f₀ w) ∧
      regFillAct hs f₀ 1 = id ∧
      (∀ σ τ, regFillAct hs f₀ (σ * τ) = regFillAct hs f₀ τ ∘ regFillAct hs f₀ σ) ∧
      -- the deck group and the identified stabilizers
      Nat.card (deckGroup f₀) = 168 ∧
      (∃ ι : GL3F2.G ≃* deckGroup f₀, ∃ a b : GL3F2.G,
        ((∀ g, ((ι g : deckGroup f₀) : Equiv.Perm (Fin 14)) = combRho rhoP rhoL g) ∧
          stabSub f₀ 0 = (GL3F2.HP.map (MulAut.conj a).toMonoidHom).map ι.toMonoidHom ∧
          stabSub f₀ 7 = (GL3F2.HL.map (MulAut.conj b).toMonoidHom).map ι.toMonoidHom) ∨
        ((∀ g, ((ι g : deckGroup f₀) : Equiv.Perm (Fin 14)) = combRho rhoL rhoP g) ∧
          stabSub f₀ 0 = (GL3F2.HL.map (MulAut.conj a).toMonoidHom).map ι.toMonoidHom ∧
          stabSub f₀ 7 = (GL3F2.HP.map (MulAut.conj b).toMonoidHom).map ι.toMonoidHom)) ∧
      ∃ Ev₁ Ev₂ : RegFill hs f₀ → ℂ,
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev₁ ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev₂ ∧
        (∀ w, (pPoly s).eval (Ev₁ w) = regFillProj hs f₀ w) ∧
        (∀ w, (pPoly (-s)).eval (Ev₂ w) = regFillProj hs f₀ w) ∧
        (∀ w w', Ev₁ w = Ev₁ w' ↔ (orbSetoid hs f₀ (stabSub f₀ 0)) w w') ∧
        (∀ w w', Ev₂ w = Ev₂ w' ↔ (orbSetoid hs f₀ (stabSub f₀ 7)) w w') ∧
        -- the compact connected bordered surface `M_ε` and its metric
        (∀ ε : ℝ, 0 < ε → ε < 1 / 3 →
          IsCompact (bordered hs f₀ ε) ∧ IsClosed (bordered hs f₀ ε) ∧
          interior (bordered hs f₀ ε) = {w | ‖bdf hs f₀ ε w‖ < 1} ∧
          frontier (bordered hs f₀ ε) = borderedBdry hs f₀ ε ∧
          closure (interior (bordered hs f₀ ε)) = bordered hs f₀ ε ∧
          (∀ w ∈ borderedBdry hs f₀ ε, ∃ φ : OpenPartialHomeomorph (RegFill hs f₀) ℂ,
            w ∈ φ.source ∧ EqOn φ (bdf hs f₀ ε) φ.source ∧
            φ '' (φ.source ∩ bordered hs f₀ ε) = φ.target ∩ Metric.closedBall 0 1 ∧
            φ '' (φ.source ∩ borderedBdry hs f₀ ε) = φ.target ∩ Metric.sphere 0 1 ∧
            ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω φ φ.source ∧ ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω φ.symm φ.target) ∧
          (∀ σ w, regFillAct hs f₀ σ w ∈ bordered hs f₀ ε ↔ w ∈ bordered hs f₀ ε) ∧
          IsConnected (bordered hs f₀ ε) ∧ IsConnected (interior (bordered hs f₀ ε)) ∧
          ∀ L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3,
          bordered hs f₀ ε ⊆ bdf hs f₀ ε ⁻¹' L.U ∧
          (∀ e ∈ atlas ℂ (RegFill hs f₀), ∀ z ∈ chartDom L e,
            ContDiffAt ℝ ∞ (regMetric L e) z ∧ 0 < regMetric L e z) ∧
          (∀ e ∈ atlas ℂ (RegFill hs f₀), ∀ z ∈ chartDom L e,
            bdf hs f₀ ε (e.symm z) ≠ ε → bdf hs f₀ ε (e.symm z) ≠ lamStar * ε →
            regMetric L e z = L.lam (bdf hs f₀ ε (e.symm z)) *
              ‖deriv (bdf hs f₀ ε ∘ e.symm) z‖ ^ 2) ∧
          (∀ e ∈ atlas ℂ (RegFill hs f₀), ∀ e' ∈ atlas ℂ (RegFill hs f₀), ∀ z ∈ chartDom L e,
            e.symm z ∈ e'.source →
            AnalyticAt ℂ (e' ∘ e.symm) z ∧ regMetric L e z =
              regMetric L e' ((e' ∘ e.symm) z) * ‖deriv (e' ∘ e.symm) z‖ ^ 2) ∧
          (∀ σ : deckGroup f₀, ∀ e ∈ atlas ℂ (RegFill hs f₀), ∀ e' ∈ atlas ℂ (RegFill hs f₀),
            ∀ z ∈ chartDom L e, regFillAct hs f₀ σ (e.symm z) ∈ e'.source →
            AnalyticAt ℂ (e' ∘ regFillAct hs f₀ σ ∘ e.symm) z ∧
              (e' ∘ regFillAct hs f₀ σ ∘ e.symm) z ∈ chartDom L e' ∧
              regMetric L e z = regMetric L e' ((e' ∘ regFillAct hs f₀ σ ∘ e.symm) z) *
                ‖deriv (e' ∘ regFillAct hs f₀ σ ∘ e.symm) z‖ ^ 2)) ∧
        -- the two quotient orbisurfaces, with the full geometric identification
        ∀ (aP aL : ℂ), aP ^ 7 = -bconst s → aL ^ 7 = -bconst (-s) →
        ∀ (τ : ℝ → ℂ), (∀ ε, τ ε ^ 7 = (lamStar - 1) * ε) →
        ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ ψP BP ψL BL : ℂ → ℂ,
          IsNormalizedDiskCover (paperQ (monicP s aP) τ ε) 7 ψP BP →
          IsNormalizedDiskCover (paperQ (monicP (-s) aL) τ ε) 7 ψL BL →
          ∀ L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3,
            ∃ (VP VL : Set ℂ) (hP : IsBranchedDiskMap BP VP (ε : ℂ) (lamStar * ε) 2 3 L.U)
              (hL : IsBranchedDiskMap BL VL (ε : ℂ) (lamStar * ε) 2 3 L.U),
              (LabelGeometry hs f₀ (stabSub f₀ 0) (pPoly s) Ev₁ ε (τ ε / aP) ψP BP L hP ∧
                CuspCompat hs f₀ (stabSub f₀ 0) (pPoly s) Ev₁ ε (τ ε / aP) ψP BP L hP) ∧
              (LabelGeometry hs f₀ (stabSub f₀ 7) (pPoly (-s)) Ev₂ ε (τ ε / aL) ψL BL L hL ∧
                CuspCompat hs f₀ (stabSub f₀ 7) (pPoly (-s)) Ev₂ ε (τ ε / aL) ψL BL L hL) ∧
              (pullbackOrb L hP).metricSteklovEigenvalue =
                (pullbackOrb L hL).metricSteklovEigenvalue ∧
              (pullbackOrb L hP).steklovSpectrum = (pullbackOrb L hL).steklovSpectrum := by
  obtain ⟨f₀, hpc, hd, hcard, Ev₁, Ev₂, hE₁, hE₂, e₁, e₂, fib₁, fib₂, su₁, su₂, pr₁, pr₂,
    q₁, q₂⟩ := completed_quotient_identifications_conn hs
  haveI := hpc
  have hs' : (-s) ^ 2 = -7 := by rw [neg_sq]; exact hs
  have hsurj := surjective_regFillProj hs f₀ su₁ e₁
  obtain ⟨hconn, hbconn⟩ := regFill_connected_of hs f₀ hsurj
  have hact := regFill_deckAction hs f₀
  refine ⟨f₀, hpc, hconn, fun σ => ⟨hact.1 σ, (hact.2.1 σ).2, hact.2.2.2.1 σ⟩,
    hact.2.2.2.2.2.1, hact.2.2.2.2.2.2.1, hcard,
    stabilizer_identification hd, Ev₁, Ev₂, hE₁, hE₂, e₁, e₂, fib₁, fib₂,
    fun ε h0 h1 => ?_, fun aP aL haP haL τ hτ => ?_⟩
  · obtain ⟨b1, b2, b3, b4, b5, -, b7, -, -⟩ := regBorderedSurface hs f₀ h0 h1
    refine ⟨b1, b2, b3, b4, b5, b7, (regBordered hs f₀ h0 h1).2.1, (hbconn ε h0 h1).1,
      (hbconn ε h0 h1).2, fun L => ⟨bordered_subset_metricDom L,
      fun e he z hz => regMetric_smooth h0 L he hz,
      fun e he z hz hu hv => regMetric_eq h0 L he hz hu hv,
      fun e he e' he' z hz hz' => regMetric_transition h0 L he he' hz hz',
      fun σ e he e' he' z hz hzσ => regMetric_deck h0 L σ he he' hz hzσ⟩⟩
  obtain ⟨ε₁, hε₁, HP⟩ := FamilyNoncongr.family_facts hs haP hτ
  obtain ⟨ε₂, hε₂, HL⟩ := FamilyNoncongr.family_facts hs' haL hτ
  have hpos : 0 < min (min ε₁ ε₂) (1 / 10 : ℝ) := lt_min (lt_min hε₁ hε₂) (by norm_num)
  filter_upwards [eventually_isPreconnected_paperQ hs haP hτ,
    eventually_isPreconnected_paperQ hs' haL hτ, Ioo_mem_nhdsGT hpos] with ε hcnP hcnL hεI
  intro ψP BP ψL BL hcP hcL L
  obtain ⟨h0, hlt⟩ := hεI
  have hlt1 : ε < ε₁ := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_left _ _))
  have hlt2 : ε < ε₂ := lt_of_lt_of_le hlt ((min_le_left _ _).trans (min_le_right _ _))
  have hlt3 : ε < 1 / 10 := lt_of_lt_of_le hlt (min_le_right _ _)
  have h13 : ε < 1 / 3 := by linarith
  have critP := (HP ε h0 hlt1 ψP BP hcP).2
  have critL := (HL ε h0 hlt2 ψL BL hcL).2
  obtain ⟨VP, hP⟩ := isBranchedDiskMap_of_cover hs haP hτ h0 h13 hcP critP L.isOpen_U L.cb
  obtain ⟨VL, hL⟩ := isBranchedDiskMap_of_cover hs' haL hτ h0 h13 hcL critL L.isOpen_U L.cb
  have spec := FamilyIso.family_spectra_eq hs haP haL hτ h0 hlt3 hcP hcL
  refine ⟨VP, VL, hP, hL, ?_, ?_, pullback_spectra_eq hP hL spec⟩
  · exact label_geometry_cone hs f₀ (stabSub f₀ 0) hs hE₁ e₁ pr₁ su₁ fib₁ q₁ haP hτ h0 h13 hcnP
      hcP L hP
  · exact label_geometry_cone hs f₀ (stabSub f₀ 7) hs' hE₂ e₂ pr₂ su₂ fib₂ q₂ haL hτ h0 h13 hcnL
      hcL L hL

end Degree7
