module

public import RequestProject.FillMap

/-!
# Holomorphic extension of polynomial coordinates over filled punctures

Let `E` be punctured-disk ends of a Riemann surface `Y` whose charts are given by a projection
`π : Y → ℂ`, with `Φ_j^(d j) = π - c j` on the ends.  Let `P` be a polynomial of positive degree
and `k : Y → ℂ` a continuous map with `P ∘ k = π` and `P' ∘ k ≠ 0` (e.g. the `z`-coordinate of a
map from a cover to the polynomial cover `P : ℂ → ℂ`).  By Riemann's removable singularity theorem
(`k` is bounded near each puncture because `P` is proper) `k` extends to the filling:

* `Fill.extend k : Fill E → ℂ`, with value `cuspVal k j = lim_{t → 0} k(Φ_j⁻¹ t)` at `cusp j`;
* `Fill.continuous_extend`, `Fill.contMDiff_extend`: the extension is continuous and holomorphic;
* `Fill.eval_extend`: `P ∘ extend k = πFill π c`;
* `Fill.exists_common_of_cuspVal_eq`: (open mapping) if two added points have the same value, then
  points of the two ends close to them have equal values under `k`;
* `Fill.dense_range_inl`: `Y` is dense in the filling.
-/

@[expose] public section

open Set Filter Topology SteklovPunctured Manifold SteklovRiemann Polynomial
open scoped ContDiff

noncomputable section

namespace SteklovFill

/-- A continuous solution of `F ∘ k = G`, with `F` strictly differentiable with nonzero
derivative at `k t₀` and `G` differentiable, is differentiable (inverse function theorem). -/
lemma differentiableAt_of_comp_eq {F G k : ℂ → ℂ} {F' t₀ : ℂ} (hk : ContinuousAt k t₀)
    (hF : HasStrictDerivAt F F' (k t₀)) (hF' : F' ≠ 0) (hG : DifferentiableAt ℂ G t₀)
    (hcomp : ∀ᶠ t in 𝓝 t₀, F (k t) = G t) : DifferentiableAt ℂ k t₀ := by
  set ψ := hF.localInverse F F' (k t₀) hF'
  have hψ : DifferentiableAt ℂ ψ (G t₀) := by
    -- Lean 4.35 / new Mathlib: `HasStrictDerivAt` unfolds to a `HasDerivAtFilter` statement, so
    -- generalized field notation no longer finds `differentiableAt`; go through the explicit
    -- interface `HasStrictDerivAt.hasDerivAt` and `HasDerivAt.differentiableAt`.
    rw [← hcomp.self_of_nhds]
    exact HasDerivAt.differentiableAt (HasStrictDerivAt.hasDerivAt (hF.to_localInverse hF'))
  have hleft : ∀ᶠ t in 𝓝 t₀, ψ (F (k t)) = k t := hk.eventually (hF.eventually_left_inverse hF')
  have heq : (ψ ∘ G) =ᶠ[𝓝 t₀] k := by
    filter_upwards [hleft, hcomp] with t h1 h2
    simp only [Function.comp_apply, ← h2, h1]
  exact (hψ.comp t₀ hG).congr_of_eventuallyEq heq.symm

/-- Chart-formula criterion for holomorphy of a complex-valued function. -/
lemma contMDiffAt_of_formula' {M : Type*} [TopologicalSpace M] [ChartedSpace ℂ M] {f : M → ℂ}
    {x : M} (hf : ContinuousAt f x) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F (chartAt ℂ x).target)
    (hFeq : ∀ z ∈ (chartAt ℂ x).target, f ((chartAt ℂ x).symm z) = F z) :
    ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ω f x := by
  rw [contMDiffAt_iff]
  refine ⟨hf, ?_⟩
  set e := chartAt ℂ x
  have hx : e x ∈ e.target := e.map_source (mem_chart_source ℂ x)
  have hcd : ContDiffOn ℂ ω F e.target := hF.contDiffOn e.open_target
  have hcd' : ContDiffOn ℂ ω (f ∘ e.symm) e.target := hcd.congr fun z hz => hFeq z hz
  have := (hcd'.contDiffAt (e.open_target.mem_nhds hx)).contDiffWithinAt (s := range 𝓘(ℂ))
  simpa [extChartAt, OpenPartialHomeomorph.extend, Function.comp_def] using this

/-- Polynomials of positive degree are bounded below at infinity: sublevel sets are bounded. -/
lemma exists_bound_of_eval_le {P : ℂ[X]} (hP : 0 < P.degree) (M : ℝ) :
    ∃ B : ℝ, ∀ z : ℂ, ‖P.eval z‖ ≤ M → ‖z‖ ≤ B := by
  have h := P.tendsto_norm_atTop hP (l := Bornology.cobounded ℂ) (z := id)
    tendsto_norm_cobounded_atTop
  have h2 := h.eventually_gt_atTop M
  have hb : Bornology.IsBounded {x : ℂ | M < ‖P.eval (id x)‖}ᶜ := by
    rw [Bornology.isBounded_def, compl_compl]; exact h2
  obtain ⟨B, hB⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hb
  refine ⟨B, fun z hz => ?_⟩
  have : z ∈ {x | M < ‖P.eval (id x)‖}ᶜ := by simpa using hz
  simpa using hB this

variable {Y : Type*} [TopologicalSpace Y] {J : Type*} {E : Ends Y J}

namespace Fill

lemma dense_range_inl : Dense (range (inl (E := E))) := by
  rw [dense_iff_inter_open]
  intro W hW ⟨w, hw⟩
  rcases w with y | j
  · exact ⟨inl y, hw, mem_range_self _⟩
  · obtain ⟨ε, hε, hsub⟩ := (isOpen_iff.1 hW).2 j hw
    set δ := min ε (E.r j) / 2
    have hm : 0 < min ε (E.r j) := lt_min hε (E.r_pos j)
    have hδ : 0 < δ := half_pos hm
    have hδε : δ < ε := by
      have := min_le_left ε (E.r j); simp only [δ]; linarith
    have hδr : δ < E.r j := by
      have := min_le_right ε (E.r j); simp only [δ]; linarith
    have ht : ((δ : ℝ) : ℂ) ∈ pdisk (E.r j) :=
      ⟨by exact_mod_cast hδ.ne', by rw [Complex.norm_real, Real.norm_of_nonneg hδ.le]; exact hδr⟩
    set y := ((E.Φ j).symm ⟨_, ht⟩ : Y)
    have hy : y ∈ E.nbd j ε := by
      refine ⟨(E.Φ j).symm ⟨_, ht⟩, ?_, rfl⟩
      show ‖(((E.Φ j) ((E.Φ j).symm ⟨_, ht⟩) : pdisk _) : ℂ)‖ < ε
      rw [Homeomorph.apply_symm_apply]
      show ‖((δ : ℝ) : ℂ)‖ < ε
      rw [Complex.norm_real, Real.norm_of_nonneg hδ.le]; exact hδε
    exact ⟨inl y, hsub hy, mem_range_self _⟩

variable {π : Y → ℂ} (c : J → ℂ) (d : J → ℕ) (hd : ∀ j, 0 < d j)
  (hpow : ∀ j (x : E.U j), ((E.Φ j x : pdisk (E.r j)) : ℂ) ^ (d j) = π x - c j)
  {P : ℂ[X]} (hP : 0 < P.degree) {k : Y → ℂ} (hk : Continuous k)
  (hPk : ∀ y, P.eval (k y) = π y) (hP' : ∀ y, P.derivative.eval (k y) ≠ 0)

open Classical in
/-- `k` in the punctured cusp coordinate. -/
def cuspRep (k : Y → ℂ) (j : J) (t : ℂ) : ℂ :=
  if h : t ∈ pdisk (E.r j) then k ((E.Φ j).symm ⟨t, h⟩) else 0

lemma cuspRep_of_mem (k : Y → ℂ) {j : J} {t : ℂ} (h : t ∈ pdisk (E.r j)) :
    cuspRep (E := E) k j t = k ((E.Φ j).symm ⟨t, h⟩) := by
  rw [cuspRep, dif_pos h]

/-- The value at an added point: the limit of `k` along the end. -/
def cuspVal (k : Y → ℂ) (j : J) : ℂ := limUnder (𝓝[≠] (0 : ℂ)) (cuspRep (E := E) k j)

/-- The extension of `k` to the filling. -/
def extend (k : Y → ℂ) : Fill E → ℂ
  | Sum.inl y => k y
  | Sum.inr j => cuspVal (E := E) k j

@[simp] lemma extend_inl (k : Y → ℂ) (y : Y) : extend (E := E) k (inl y) = k y := rfl

@[simp] lemma extend_cusp (k : Y → ℂ) (j : J) :
    extend (E := E) k (cusp j) = cuspVal (E := E) k j := rfl

/-- The extension in the cusp coordinate. -/
def cuspExt (k : Y → ℂ) (j : J) : ℂ → ℂ :=
  Function.update (cuspRep (E := E) k j) 0 (cuspVal (E := E) k j)

lemma extend_cuspInv (k : Y → ℂ) (j : J) {t : ℂ} (ht : t ∈ Metric.ball (0 : ℂ) (E.r j)) :
    extend (E := E) k (cuspInv j t) = cuspExt (E := E) k j t := by
  by_cases h0 : t = 0
  · subst h0; rw [cuspInv_zero, cuspExt, Function.update_self]; rfl
  · have h : t ∈ pdisk (E.r j) := ⟨h0, mem_ball_zero_iff.1 ht⟩
    rw [cuspExt, Function.update_of_ne h0, cuspInv_of_mem h, extend_inl, cuspRep_of_mem k h]

include hk in
lemma continuousOn_cuspRep (j : J) : ContinuousOn (cuspRep (E := E) k j) (pdisk (E.r j)) := by
  -- Lean 4.35 / new Mathlib: `Set.restrict` is now `Set.domRestrict`; compare pointwise with
  -- `Continuous.congr` instead of rewriting the restricted function.
  rw [continuousOn_iff_continuous_domRestrict]
  refine (hk.comp (continuous_subtype_val.comp (E.Φ j).symm.continuous)).congr fun u => ?_
  exact (cuspRep_of_mem (E := E) k u.2).symm

include hpow hPk in
lemma eval_cuspRep {j : J} {t : ℂ} (h : t ∈ pdisk (E.r j)) :
    P.eval (cuspRep (E := E) k j t) = c j + t ^ (d j) := by
  rw [cuspRep_of_mem k h, hPk]
  have := hpow j ((E.Φ j).symm ⟨t, h⟩)
  rw [Homeomorph.apply_symm_apply] at this
  simp only at this
  rw [this]; ring

include hpow hk hPk hP' in
lemma differentiableOn_cuspRep (j : J) :
    DifferentiableOn ℂ (cuspRep (E := E) k j) (pdisk (E.r j)) := by
  intro t ht
  have hopen := isOpen_pdisk (E.r j)
  refine (differentiableAt_of_comp_eq (F := fun z => P.eval z) (G := fun t => c j + t ^ (d j))
    ((continuousOn_cuspRep hk j).continuousAt (hopen.mem_nhds ht))
    (P.hasStrictDerivAt _) ?_ (by fun_prop) ?_).differentiableWithinAt
  · rw [cuspRep_of_mem k ht]; exact hP' _
  · filter_upwards [hopen.mem_nhds ht] with t' ht'
    exact eval_cuspRep c d hpow hPk ht'

include hpow hPk hP in
lemma bddAbove_cuspRep (j : J) :
    BddAbove (norm ∘ cuspRep (E := E) k j '' (Metric.ball 0 (E.r j) \ {0})) := by
  obtain ⟨B, hB⟩ := exists_bound_of_eval_le hP (‖c j‖ + E.r j ^ (d j))
  refine ⟨B, ?_⟩
  rintro _ ⟨t, ⟨ht, ht0⟩, rfl⟩
  have htp : t ∈ pdisk (E.r j) := ⟨ht0, mem_ball_zero_iff.1 ht⟩
  apply hB
  rw [eval_cuspRep c d hpow hPk htp]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (mem_ball_zero_iff.1 ht).le _

include hpow hk hPk hP' hP in
/-- **Removable singularity**: the extension is holomorphic in the cusp coordinate. -/
lemma differentiableOn_cuspExt (j : J) :
    DifferentiableOn ℂ (cuspExt (E := E) k j) (Metric.ball 0 (E.r j)) := by
  have hdiff : DifferentiableOn ℂ (cuspRep (E := E) k j) (Metric.ball 0 (E.r j) \ {0}) :=
    (differentiableOn_cuspRep c d hpow hk hPk hP' j).mono fun t ⟨ht, ht0⟩ =>
      ⟨ht0, mem_ball_zero_iff.1 ht⟩
  exact Complex.differentiableOn_update_limUnder_of_bddAbove
    (Metric.ball_mem_nhds 0 (E.r_pos j)) hdiff (bddAbove_cuspRep c d hpow hP hPk j)

include hpow hk hPk hP' hP in
lemma continuousAt_extend (w : Fill E) : ContinuousAt (extend (E := E) k) w := by
  rcases w with y | j
  · exact (isOpenEmbedding_inl.continuousAt_iff (g := extend (E := E) k)).1 hk.continuousAt
  · have hsrc : (cuspChart (E := E) j).source ∈ 𝓝 (cusp j) :=
      (cuspChart j).open_source.mem_nhds (Or.inr rfl)
    have heq : (cuspExt (E := E) k j ∘ cuspChart j) =ᶠ[𝓝 (cusp j)] extend (E := E) k := by
      filter_upwards [hsrc] with w hw
      rw [Function.comp_apply, ← extend_cuspInv k j ((cuspChart j).map_source hw)]
      congr 1
      exact (cuspChart j).left_inv hw
    have h0 : cuspChart (E := E) j (cusp j) = 0 := rfl
    have hc : ContinuousAt (cuspExt (E := E) k j) (cuspChart (E := E) j (cusp j)) := by
      rw [h0]
      exact ((differentiableOn_cuspExt c d hpow hP hk hPk hP' j).differentiableAt
        (Metric.ball_mem_nhds 0 (E.r_pos j))).continuousAt
    exact (hc.comp ((cuspChart j).continuousAt (Or.inr rfl))).congr heq

include hpow hk hPk hP' hP in
theorem continuous_extend : Continuous (extend (E := E) k) :=
  continuous_iff_continuousAt.2 (continuousAt_extend c d hpow hP hk hPk hP')

include hpow hk hPk hP' hP hd in
/-- `P ∘ extend k = πFill π c`. -/
theorem eval_extend (w : Fill E) : P.eval (extend (E := E) k w) = πFill π c w := by
  rcases w with y | j
  · exact hPk y
  · show P.eval (cuspVal k j) = c j
    have hcont : ContinuousAt (cuspExt (E := E) k j) 0 :=
      ((differentiableOn_cuspExt c d hpow hP hk hPk hP' j).differentiableAt
        (Metric.ball_mem_nhds 0 (E.r_pos j))).continuousAt
    have h1 : Tendsto (fun t => P.eval (cuspExt (E := E) k j t)) (𝓝[≠] 0)
        (𝓝 (P.eval (cuspVal (E := E) k j))) := by
      have := (P.continuous.continuousAt.comp hcont).tendsto.mono_left
        (nhdsWithin_le_nhds (s := {0}ᶜ))
      first
        | simpa [cuspExt] using this
        | simpa [cuspExt, Function.comp_def] using this
    have h2 : Tendsto (fun t : ℂ => c j + t ^ (d j)) (𝓝[≠] 0) (𝓝 (c j)) := by
      have : Tendsto (fun t : ℂ => c j + t ^ (d j)) (𝓝 0) (𝓝 (c j + 0 ^ (d j))) :=
        (continuous_const.add (continuous_pow _)).tendsto 0
      rw [zero_pow (hd j).ne', add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h3 : (fun t => P.eval (cuspExt (E := E) k j t)) =ᶠ[𝓝[≠] 0]
        fun t : ℂ => c j + t ^ (d j) := by
      filter_upwards [inter_mem_nhdsWithin {0}ᶜ (Metric.ball_mem_nhds 0 (E.r_pos j)),
        self_mem_nhdsWithin] with t ht ht0
      have htp : t ∈ pdisk (E.r j) := ⟨ht0, mem_ball_zero_iff.1 ht.2⟩
      rw [cuspExt, Function.update_of_ne ht0]
      exact eval_cuspRep c d hpow hPk htp
    exact tendsto_nhds_unique (h1.congr' h3) h2

variable [ChartedSpace ℂ Y] (hπ : ChartsAre Y π)

include hπ hpow hk hPk hP' hP in
/-- **The extension is holomorphic** on the filled Riemann surface. -/
theorem contMDiff_extend : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (extend (E := E) k) := by
  intro w
  have hcont := continuousAt_extend c d hpow hP hk hPk hP' w
  rcases w with y | j
  · refine contMDiffAt_of_formula' hcont (F := k ∘ (chartAt ℂ y).symm) ?_ fun z _ => rfl
    intro z hz
    set e := chartAt ℂ y
    have hopen := e.open_target
    refine (differentiableAt_of_comp_eq (F := fun z => P.eval z) (G := id)
      (hk.continuousAt.comp (e.continuousAt_symm hz)) (P.hasStrictDerivAt _) (hP' _)
      differentiableAt_id ?_).differentiableWithinAt
    filter_upwards [hopen.mem_nhds hz] with z' hz'
    simp only [Function.comp_apply, id]
    rw [hPk, ← hπ e (chart_mem_atlas ℂ y)]
    exact e.right_inv hz'
  · exact contMDiffAt_of_formula' hcont (differentiableOn_cuspExt c d hpow hP hk hPk hP' j)
      fun t ht => extend_cuspInv k j ht

omit [ChartedSpace ℂ Y] in
include hpow hk hPk hP' hP hd in
/-- In the cusp coordinate the extension is a nonconstant analytic function, hence an open map
at `0`. -/
lemma nhds_le_map_cuspExt (j : J) :
    𝓝 (cuspVal (E := E) k j) ≤ Filter.map (cuspExt (E := E) k j) (𝓝 0) := by
  have han : AnalyticAt ℂ (cuspExt (E := E) k j) 0 :=
    (differentiableOn_cuspExt c d hpow hP hk hPk hP' j).analyticAt
      (Metric.ball_mem_nhds 0 (E.r_pos j))
  have h0 : cuspExt (E := E) k j 0 = cuspVal (E := E) k j := by simp [cuspExt]
  rcases han.eventually_constant_or_nhds_le_map_nhds with hc | hc
  · exfalso
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hc
    set a : ℝ := min δ (E.r j) / 2
    have hm : 0 < min δ (E.r j) := lt_min hδ (E.r_pos j)
    have ha : 0 < a := half_pos hm
    have haδ : a < δ := by have := min_le_left δ (E.r j); simp only [a]; linarith
    have har : a < E.r j := by have := min_le_right δ (E.r j); simp only [a]; linarith
    have hmem : ∀ b : ℝ, 0 < b → b ≤ a →
        P.eval (cuspExt (E := E) k j b) = c j + (b : ℂ) ^ (d j) := by
      intro b hb hba
      have hbp : ((b : ℝ) : ℂ) ∈ pdisk (E.r j) := ⟨by exact_mod_cast hb.ne', by
        rw [Complex.norm_real, Real.norm_of_nonneg hb.le]; linarith⟩
      rw [cuspExt, Function.update_of_ne (by exact_mod_cast hb.ne')]
      exact eval_cuspRep c d hpow hPk hbp
    have hval : ∀ b : ℝ, 0 < b → b ≤ a → cuspExt (E := E) k j b = cuspExt (E := E) k j 0 := by
      intro b hb hba
      apply hball
      rw [dist_zero_right, Complex.norm_real, Real.norm_of_nonneg hb.le]; linarith
    have e1 := hmem a ha le_rfl
    have e2 := hmem (a / 2) (half_pos ha) (by linarith)
    rw [hval a ha le_rfl] at e1
    rw [hval (a / 2) (half_pos ha) (by linarith), e1] at e2
    have e3 : ((a : ℝ) : ℂ) ^ (d j) = ((a / 2 : ℝ) : ℂ) ^ (d j) := add_left_cancel e2
    have e4 : a ^ (d j) = (a / 2) ^ (d j) := by exact_mod_cast e3
    have := (pow_left_inj₀ ha.le (half_pos ha).le (hd j).ne').1 e4
    linarith
  · rwa [h0] at hc

omit [ChartedSpace ℂ Y] in
include hpow hk hPk hP' hP hd in
/-- **Equal values at added points come from equal values nearby** (open mapping). -/
theorem exists_common_of_cuspVal_eq {j j' : J}
    (h : cuspVal (E := E) k j = cuspVal (E := E) k j') :
    ∃ y ∈ E.U j, ∃ y' ∈ E.U j', k y = k y' := by
  have hV : cuspExt (E := E) k j '' Metric.ball 0 (E.r j) ∈ 𝓝 (cuspVal (E := E) k j) :=
    nhds_le_map_cuspExt c d hd hpow hP hk hPk hP' j
      (image_mem_map (Metric.ball_mem_nhds 0 (E.r_pos j)))
  have hV' : cuspExt (E := E) k j' '' Metric.ball 0 (E.r j') ∈ 𝓝 (cuspVal (E := E) k j) := by
    rw [h]
    exact nhds_le_map_cuspExt c d hd hpow hP hk hPk hP' j'
      (image_mem_map (Metric.ball_mem_nhds 0 (E.r_pos j')))
  obtain ⟨z, ⟨hz, hz'⟩, hzL⟩ := (Filter.Eventually.and
    (mem_nhdsWithin_of_mem_nhds (t := {cuspVal (E := E) k j}ᶜ) (inter_mem hV hV'))
    (self_mem_nhdsWithin (s := {cuspVal (E := E) k j}ᶜ))).exists
  obtain ⟨t, ht, rfl⟩ := hz
  obtain ⟨t', ht', htt'⟩ := hz'
  have ht0 : t ≠ 0 := by
    rintro rfl; exact hzL (by simp [cuspExt])
  have ht'0 : t' ≠ 0 := by
    rintro rfl; apply hzL; rw [← htt']; simp [cuspExt, h]
  have htp : t ∈ pdisk (E.r j) := ⟨ht0, mem_ball_zero_iff.1 ht⟩
  have htp' : t' ∈ pdisk (E.r j') := ⟨ht'0, mem_ball_zero_iff.1 ht'⟩
  refine ⟨_, ((E.Φ j).symm ⟨t, htp⟩).2, _, ((E.Φ j').symm ⟨t', htp'⟩).2, ?_⟩
  rw [← cuspRep_of_mem k htp, ← cuspRep_of_mem k htp']
  rw [cuspExt, Function.update_of_ne ht'0] at htt'
  rw [cuspExt, Function.update_of_ne ht0] at htt'
  exact htt'.symm

end Fill

end SteklovFill
