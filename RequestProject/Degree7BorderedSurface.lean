module

public import RequestProject.Degree7Quotient
public import RequestProject.BorderedTopology

/-!
# `M_ε` is a compact connected bordered Riemann surface

Let `R̄ = RegFill hs f₀` be the branched completion of the common regular cover, with branched
projection `π̄`, and `b_ε = A_ε ∘ π̄ : R̄ → ℂ` (`bdf`), so that
`M_ε = {‖b_ε‖ ≤ 1}` (`bordered`) and `∂M_ε = {‖b_ε‖ = 1}` (`borderedBdry`).  For `0 < ε < 1/3`
we prove (`regBorderedSurface`):

* `π̄` (hence `b_ε`) is an **open map** (`isOpenMap_regFillProj`: a local homeomorphism on the
  unbranched part, `t ↦ c + t^d` in the cusp charts);
* `interior M_ε = {‖b_ε‖ < 1}`, `frontier M_ε = ∂M_ε`, `closure (interior M_ε) = M_ε`, `M_ε`
  closed and compact: `∂M_ε` is the genuine topological boundary;
* **analytic boundary charts:** every point of `∂M_ε` lies in the source of an analytic chart
  `φ` of the Riemann surface `R̄` (analytic with analytic inverse, compatible with the atlas),
  equal to `b_ε` on its source, with `φ(source ∩ M_ε) = target ∩ closed unit disk` and
  `φ(source ∩ ∂M_ε) = target ∩ unit circle`;
* `b_ε : ∂M_ε → 𝕋` is a covering map (so `∂M_ε` is a disjoint union of analytic circles);
* the interior points form the open subset `{‖b_ε‖ < 1}` of the Riemann surface `R̄`.

For the actual ordered fibre of `common_regular_cover` (whose regular cover is path connected)
we moreover prove (`actual_bordered_surface`): `R̄` is connected, and `M_ε` and its interior are
**connected** (`SteklovBordered.isPreconnected_sublevel`: radial retraction obtained by lifting
the radial homotopy through the boundary collar covering).
-/

@[expose] public section

open Polynomial Set PolyCover LocalMonodromy SteklovRegularCover SteklovPunctured SteklovFill
  SteklovRiemann Topology Manifold SteklovCritical SteklovCoalescence GL3F2
open scoped ContDiff

noncomputable section

namespace Degree7

variable {s : ℂ}

/-- The boundary-defining function `b_ε = A_ε ∘ π̄` of `M_ε`. -/
def bdf (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (ε : ℝ) : RegFill hs f₀ → ℂ :=
  fun w => affA ε (regFillProj hs f₀ w)

lemma bordered_eq (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (ε : ℝ) :
    bordered hs f₀ ε = {w | ‖bdf hs f₀ ε w‖ ≤ 1} := rfl

lemma borderedBdry_eq (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (ε : ℝ) :
    borderedBdry hs f₀ ε = {w | ‖bdf hs f₀ ε w‖ = 1} := rfl

lemma continuous_regFillProj (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    Continuous (regFillProj hs f₀) :=
  (regFill_riemannSurface hs f₀).2.2.1.continuous

lemma continuous_bdf (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (ε : ℝ) :
    Continuous (bdf hs f₀ ε) := by
  unfold bdf affA
  exact continuous_const.add (continuous_const.mul (continuous_regFillProj hs f₀))

/-- `t ↦ c + t^d` (`d > 0`) is open at `0`. -/
lemma nhds_le_map_pow (c : ℂ) {d : ℕ} (hd : 0 < d) :
    𝓝 c ≤ Filter.map (fun t : ℂ => c + t ^ d) (𝓝 0) := by
  have han : AnalyticAt ℂ (fun t : ℂ => c + t ^ d) 0 :=
    analyticAt_const.add (analyticAt_id.pow d)
  have h0 : c + (0 : ℂ) ^ d = c := by simp [zero_pow hd.ne']
  rcases han.eventually_constant_or_nhds_le_map_nhds with hc | hc
  · exfalso
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hc
    have hmem : dist (((δ / 2 : ℝ)) : ℂ) 0 < δ := by
      rw [dist_zero_right, Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
    have := hball hmem
    rw [h0] at this
    have h2 : (((δ / 2 : ℝ)) : ℂ) ^ d = 0 := by
      have := congrArg (fun z => z - c) this; simpa using this
    have h3 : ((δ / 2 : ℝ) : ℂ) = 0 := pow_eq_zero_iff hd.ne' |>.1 h2
    have : δ / 2 = 0 := by exact_mod_cast h3
    linarith
  · rwa [h0] at hc

/-- **The branched projection of the completion is an open map.** -/
theorem isOpenMap_regFillProj (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    IsOpenMap (regFillProj hs f₀) := by
  obtain ⟨-, -, -, hemb, hinl, hcases, hcusp⟩ := regFill_riemannSurface hs f₀
  refine isOpenMap_iff_nhds_le.2 fun w => ?_
  rcases hcases w with ⟨f, rfl⟩ | ⟨j, rfl⟩
  · rw [← hemb.map_nhds_eq, Filter.map_map]
    have : regFillProj hs f₀ ∘ Fill.inl = coverProjC hs f₀ := funext hinl
    rw [this, hinl]
    exact (isLocalHomeomorph_coverProjC hs f₀).isOpenMap.nhds_le f
  · obtain ⟨e, -, hsrc, he0, hform⟩ := hcusp j
    have h0 : (0 : ℂ) ∈ e.target := he0 ▸ e.map_source hsrc
    have hsymm : e.symm 0 = Fill.cusp j := by rw [← he0]; exact e.left_inv hsrc
    have hn : 𝓝 (Fill.cusp j) = Filter.map e.symm (𝓝 0) := by
      rw [e.symm.map_nhds_eq h0, hsymm]
    rw [hn, Filter.map_map]
    have heq : regFillProj hs f₀ ∘ e.symm =ᶠ[𝓝 0] fun t => cB j.1 + t ^ dB j.1 :=
      Filter.eventually_of_mem (e.open_target.mem_nhds h0) fun t ht => hform t ht
    rw [Filter.map_congr heq]
    have hval : regFillProj hs f₀ (Fill.cusp j) = cB j.1 := by
      have := hform 0 h0
      rw [hsymm] at this
      simpa [zero_pow (dB_pos j.1).ne'] using this
    rw [hval]
    exact nhds_le_map_pow _ (dB_pos j.1)

lemma isOpenMap_bdf (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) {ε : ℝ} (hε : ε ≠ 0) :
    IsOpenMap (bdf hs f₀ ε) :=
  (affHomeo hε).isOpenMap.comp (isOpenMap_regFillProj hs f₀)

/-- The inverse of `A_ε`. -/
lemma affHomeo_symm_apply {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    (affHomeo hε).symm z = (z - ε) / ((lamStar - 1) * ε) := by
  have hne : (lamStar - 1) * (ε : ℂ) ≠ 0 :=
    mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast hε)
  rw [Homeomorph.symm_apply_eq, affHomeo_apply, affA, mul_div_cancel₀ _ hne]
  ring

lemma collarRad_nonneg (ε : ℝ) : 0 ≤ collarRad ε := by
  unfold collarRad
  have := le_max_left ‖(ε : ℂ)‖ ‖lamStar * ε‖
  have := norm_nonneg (ε : ℂ)
  linarith

/-- The boundary collar covering, on the completed surface. -/
lemma isCoveringMapOn_bdf (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1 / 3) : IsCoveringMapOn (bdf hs f₀ ε) {z | collarRad ε < ‖z‖} := by
  obtain ⟨-, -, -, -, -, hinl, hcov, -⟩ := regBordered hs f₀ h0 h1
  refine SteklovBordered.isCoveringMapOn_of_isOpenEmbedding Fill.isOpenEmbedding_inl
    (continuous_bdf hs f₀ ε) (isOpen_lt continuous_const continuous_norm) ?_ hcov
  rintro w hw
  obtain ⟨f, rfl⟩ := hinl w hw
  exact ⟨f, rfl⟩

/-- **`M_ε` as a compact bordered Riemann surface.** -/
theorem regBorderedSurface (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε < 1 / 3) :
    IsCompact (bordered hs f₀ ε) ∧ IsClosed (bordered hs f₀ ε) ∧
    interior (bordered hs f₀ ε) = {w | ‖bdf hs f₀ ε w‖ < 1} ∧
    frontier (bordered hs f₀ ε) = borderedBdry hs f₀ ε ∧
    closure (interior (bordered hs f₀ ε)) = bordered hs f₀ ε ∧
    IsOpenMap (regFillProj hs f₀) ∧
    (∀ w ∈ borderedBdry hs f₀ ε, ∃ φ : OpenPartialHomeomorph (RegFill hs f₀) ℂ,
      w ∈ φ.source ∧ EqOn φ (bdf hs f₀ ε) φ.source ∧
      φ '' (φ.source ∩ bordered hs f₀ ε) = φ.target ∩ Metric.closedBall 0 1 ∧
      φ '' (φ.source ∩ borderedBdry hs f₀ ε) = φ.target ∩ Metric.sphere 0 1 ∧
      ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω φ φ.source ∧ ContMDiffOn 𝓘(ℂ) 𝓘(ℂ) ω φ.symm φ.target) ∧
    IsCoveringMap ((Metric.sphere (0 : ℂ) 1).restrictPreimage (bdf hs f₀ ε)) ∧
    bdf hs f₀ ε ⁻¹' Metric.sphere 0 1 = borderedBdry hs f₀ ε := by
  have hε : ε ≠ 0 := h0.ne'
  obtain ⟨hcpt, -, -, hbdry, hr1, -, -, -⟩ := regBordered hs f₀ h0 h1
  obtain ⟨hT2, hman, hsmooth, -, -, -, -⟩ := regFill_riemannSurface hs f₀
  haveI := hman
  obtain ⟨hint, hfr, hcl, hclosed⟩ := SteklovBordered.sublevel_topology (continuous_bdf hs f₀ ε)
    (isOpenMap_bdf hs f₀ hε) (ρ := 1) one_pos
  have hsph : bdf hs f₀ ε ⁻¹' Metric.sphere 0 1 = borderedBdry hs f₀ ε := by
    ext w; simp [borderedBdry_eq]
  have hbdfS : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (bdf hs f₀ ε) := by
    have hA : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (affA ε) := by
      rw [contMDiff_iff_contDiff]
      unfold affA
      exact contDiff_const.add (contDiff_const.mul contDiff_id)
    exact hA.comp hsmooth
  refine ⟨hcpt, hclosed, hint, hfr, by rw [bordered_eq, hint, hcl], isOpenMap_regFillProj hs f₀,
    fun w hw => ?_, ?_, hsph⟩
  · -- analytic boundary chart
    obtain ⟨⟨f, rfl⟩, -⟩ := hbdry w hw
    set c := chartAt ℂ (Fill.inl (E := regEnds hs f₀) f)
    have hc : c = Fill.liftChart (chartAt ℂ f) := rfl
    have hcπ : EqOn c (regFillProj hs f₀) c.source := by
      rw [hc]
      rintro _ ⟨y, -, rfl⟩
      show chartAt ℂ f y = coverProjC hs f₀ y
      rw [chartsAre_regCov hs f₀ _ (chart_mem_atlas ℂ f)]
    set φ := c.transHomeomorph (affHomeo hε)
    have hφsrc : φ.source = c.source := c.transHomeomorph_source _
    have hφ : EqOn φ (bdf hs f₀ ε) φ.source := by
      intro x hx
      rw [hφsrc] at hx
      rw [c.transHomeomorph_apply, Function.comp_apply, hcπ hx]
      rfl
    have himg : ∀ T : Set ℂ, φ '' (φ.source ∩ bdf hs f₀ ε ⁻¹' T) = φ.target ∩ T := by
      intro T
      ext z
      constructor
      · rintro ⟨x, ⟨hx, hxT⟩, rfl⟩
        exact ⟨φ.map_source hx, by rw [hφ hx]; exact hxT⟩
      · rintro ⟨hz, hzT⟩
        refine ⟨φ.symm z, ⟨φ.map_target hz, ?_⟩, φ.right_inv hz⟩
        show bdf hs f₀ ε (φ.symm z) ∈ T
        rw [← hφ (φ.map_target hz), φ.right_inv hz]
        exact hzT
    refine ⟨φ, by rw [hφsrc]; exact mem_chart_source ℂ _, hφ, ?_, ?_, ?_, ?_⟩
    · have : bordered hs f₀ ε = bdf hs f₀ ε ⁻¹' Metric.closedBall 0 1 := by
        ext x; simp [bordered_eq]
      rw [this]; exact himg _
    · rw [← hsph]; exact himg _
    · exact hbdfS.contMDiffOn.congr fun x hx => hφ hx
    · have hsy : ⇑φ.symm = c.symm ∘ (affHomeo hε).symm := c.transHomeomorph_symm_apply _
      rw [hsy]
      have hinv : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ((affHomeo hε).symm) := by
        rw [contMDiff_iff_contDiff]
        have : ⇑(affHomeo hε).symm = fun z => (z - ε) / ((lamStar - 1) * ε) :=
          funext (affHomeo_symm_apply hε)
        rw [this]
        exact (contDiff_id.sub contDiff_const).div_const _
      refine (contMDiffOn_chart_symm (x := Fill.inl (E := regEnds hs f₀) f)).comp
        hinv.contMDiffOn ?_
      intro z hz
      have : φ.target = (affHomeo hε).symm ⁻¹' c.target := c.transHomeomorph_target _
      rw [this] at hz
      exact hz
  · have hmono := (isCoveringMapOn_bdf hs f₀ h0 h1).mono (t := Metric.sphere (0 : ℂ) 1)
      (fun z hz => by
        have : ‖z‖ = 1 := by simpa using hz
        show collarRad ε < ‖z‖
        rw [this]; exact hr1)
    exact hmono.isCoveringMap_restrictPreimage

/-- `π̄` is surjective onto `ℂ`. -/
lemma surjective_regFillProj (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13)
    {Ev : RegFill hs f₀ → ℂ} (hEv : Function.Surjective Ev)
    (hP : ∀ w, (pPoly s).eval (Ev w) = regFillProj hs f₀ w) :
    Function.Surjective (regFillProj hs f₀) := by
  intro z
  have hdeg : 0 < (pPoly s - C z).degree := by
    rw [degree_sub_C (pPoly_degree_pos hs)]; exact pPoly_degree_pos hs
  obtain ⟨x, hx⟩ := Complex.exists_root hdeg
  obtain ⟨w, rfl⟩ := hEv x
  refine ⟨w, ?_⟩
  rw [← hP]
  simpa [sub_eq_zero] using hx

/-- **The actual compact connected bordered Riemann surface `M_ε`.**  For `s² = -7` there is an
ordered fibre `f₀` (the one of `common_regular_cover`, with deck group `≅ GL(3, 𝔽₂)` of order
`168`) such that the regular cover is path connected, its branched completion `R̄` is connected,
and for every `0 < ε < 1/3` the compact bordered piece `M_ε` and its interior `{‖b_ε‖ < 1}` are
nonempty and connected; all conclusions of `regBorderedSurface` hold for it. -/
theorem actual_bordered_surface (hs : s ^ 2 = -7) :
    ∃ f₀ : OrdFib (projSum hs) 13,
      Nonempty (G ≃* deckGroup f₀) ∧ Nat.card (deckGroup f₀) = 168 ∧
      PathConnectedSpace (RegCov f₀) ∧ ConnectedSpace (RegFill hs f₀) ∧
      Function.Surjective (regFillProj hs f₀) ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / 3 →
        IsConnected (bordered hs f₀ ε) ∧ IsConnected (interior (bordered hs f₀ ε)) := by
  obtain ⟨A, f₀, -, -, hpc, -, hiso, hcard, -, -, -, -, ⟨ev₁, hc₁, hs₁, hp₁, hf₁⟩, -⟩ :=
    common_regular_cover hs
  haveI := hpc
  obtain ⟨hk₁, hPk₁, hP'₁, hsu₁⟩ := coord_data (e := Homeomorph.refl _)
    (fun _ => rfl) hc₁ hs₁ hp₁ (critVals_pPoly hs)
  have hfib₁ : ∀ f f', (ev₁ f : ℂ) = ev₁ f' ↔ ∃ σ ∈ {σ : deckGroup f₀ | σ.1 0 = 0},
      regAct f₀ σ f = f' := fun f f' => Subtype.ext_iff.symm.trans (hf₁ f f')
  obtain ⟨-, -, e₁, -, su₁, -, -⟩ :=
    quotient_ident hs f₀ (pPoly_degree_pos hs) hk₁ hPk₁ hP'₁ _ hfib₁ hsu₁
  have hsurj := surjective_regFillProj hs f₀ su₁ e₁
  have hconn : ConnectedSpace (RegFill hs f₀) := by
    have hrc : IsConnected (range (Fill.inl (E := regEnds hs f₀))) :=
      isConnected_range Fill.continuous_inl
    have := hrc.closure
    rw [Fill.dense_range_inl.closure_eq] at this
    exact connectedSpace_iff_univ.2 this
  refine ⟨f₀, hiso, hcard, hpc, hconn, hsurj, fun ε h0 h1 => ?_⟩
  have hε : ε ≠ 0 := h0.ne'
  have hcov := isCoveringMapOn_bdf hs f₀ h0 h1
  have hr := collarRad_nonneg ε
  have hr1 := collarRad_lt h0 h1
  -- a point of the interior
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

end Degree7
