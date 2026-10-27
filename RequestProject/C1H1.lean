module

public import RequestProject.DiskH1
public import RequestProject.DomainH1
public import RequestProject.C1Mollify
public import RequestProject.GeneralConformalPullback

/-!
# `C¹` functions belong to `H¹`, and their traces are their boundary values

`H¹(𝔻)` (`SteklovH1.H1`) and `H¹(Ω)` (`SteklovH1.BddDomain.H1`) are defined as closures of
graphs `(u, ∇u)` of globally smooth `u`.  Here we show, using the mollification result
`SteklovC1.exists_smooth_C1_approx`, that the graph of every globally `C¹` function `w` lies in
these closures (`embedC1_mem_H1`, `BddDomain.embedC1_mem_H1`), and that the trace of that element
is the restriction of `w` to the boundary (`trace_embedC1_ae`, `BddDomain.trace_embedC1_ae`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal ContDiff Real NNReal

noncomputable section

namespace SteklovH1

/-! ### Smooth approximation of real `C¹` functions on a compact set -/

/-- A real `C¹` function is, on a compact set `K`, uniformly `ε`-close together with its derivative
to a globally smooth function. -/
theorem exists_smooth_approx_on {w : ℂ → ℝ} (hw : ContDiff ℝ 1 w) {K : Set ℂ} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ℂ → ℝ, ContDiff ℝ ∞ v ∧
      ∀ x ∈ K, ‖v x - w x‖ ≤ ε ∧ ‖fderiv ℝ v x - fderiv ℝ w x‖ ≤ ε := by
  obtain ⟨χ, hχ, ⟨W, hW, hKW, hχ1⟩, -, hcs⟩ :=
    SteklovC1.exists_cutoff_compact hK isOpen_univ (subset_univ K)
  set Φ : ℂ → ℂ := fun z => ((χ z * w z : ℝ) : ℂ) with hΦdef
  have hΦ : ContDiff ℝ 1 Φ :=
    Complex.ofRealCLM.contDiff.comp ((hχ.of_le (by simp)).mul hw)
  have hΦc : HasCompactSupport Φ :=
    (hcs.mul_right (f' := w)).comp_left Complex.ofReal_zero
  obtain ⟨Ψ, hΨ, h0, h1⟩ := SteklovC1.exists_smooth_C1_approx hΦ hΦc hε
  refine ⟨fun z => Complex.reCLM (Ψ z), Complex.reCLM.contDiff.comp hΨ, fun x hx => ?_⟩
  have hev : (fun z => Complex.reCLM (Φ z)) =ᶠ[𝓝 x] w := by
    filter_upwards [hW.mem_nhds (hKW hx)] with y hy
    simp [Φ, hχ1 y hy]
  have hwx : Complex.reCLM (Φ x) = w x := hev.eq_of_nhds
  have hdv : fderiv ℝ (fun z => Complex.reCLM (Ψ z)) x = Complex.reCLM.comp (fderiv ℝ Ψ x) :=
    (Complex.reCLM.hasFDerivAt.comp x
      ((hΨ.differentiable (by simp)) x).hasFDerivAt).fderiv
  have hdw : fderiv ℝ w x = Complex.reCLM.comp (fderiv ℝ Φ x) := by
    rw [← hev.fderiv_eq]
    exact (Complex.reCLM.hasFDerivAt.comp x
      ((hΦ.differentiable one_ne_zero) x).hasFDerivAt).fderiv
  constructor
  · rw [← hwx, ← map_sub]
    exact (Complex.abs_re_le_norm _).trans (h0 x)
  · rw [hdv, hdw, ← ContinuousLinearMap.comp_sub]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [Complex.reCLM_norm, one_mul]
    exact h1 x

/-! ### `L²` estimates -/

lemma norm_toLp_sub_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {E : Type*} [NormedAddCommGroup E] {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) {δ : ℝ} (hδ : 0 ≤ δ)
    (h : ∀ᵐ x ∂μ, ‖f x - g x‖ ≤ δ) :
    ‖hf.toLp f - hg.toLp g‖ ≤ (measureUnivNNReal μ : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹ * δ := by
  rw [← MemLp.toLp_sub]
  refine Lp.norm_le_of_ae_bound hδ ?_
  filter_upwards [MemLp.coeFn_toLp (hf.sub hg), h] with x h1 h2
  rw [h1]; exact h2

lemma norm_prod_le {X Y : Type*} [SeminormedAddCommGroup X] [SeminormedAddCommGroup Y]
    (x : WithLp 2 (X × Y)) : ‖x‖ ≤ ‖x.fst‖ + ‖x.snd‖ := by
  have h := WithLp.prod_norm_sq_eq_of_L2 x
  have := norm_nonneg x
  have := norm_nonneg x.fst
  have := norm_nonneg x.snd
  nlinarith

lemma norm_grad_sub (w v : ℂ → ℝ) (x : ℂ) :
    ‖grad w x - grad v x‖ = ‖fderiv ℝ w x - fderiv ℝ v x‖ := by
  unfold grad
  rw [← map_sub, LinearIsometryEquiv.norm_map]

/-- The `L²` closeness of graphs over a bounded measurable set `S`. -/
theorem exists_smooth_graph_approx {S : Set ℂ} (hS : MeasurableSet S)
    (hSb : Bornology.IsBounded S) {w : ℂ → ℝ} (hw : ContDiff ℝ 1 w) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ℂ → ℝ, ContDiff ℝ ∞ v ∧ (∀ x ∈ closure S, ‖v x - w x‖ ≤ ε) ∧
      (∀ (h₁ : MemLp w 2 (volume.restrict S)) (h₂ : MemLp v 2 (volume.restrict S)),
        ‖h₁.toLp w - h₂.toLp v‖ ≤ ε) ∧
      (∀ (h₁ : MemLp (grad w) 2 (volume.restrict S)) (h₂ : MemLp (grad v) 2 (volume.restrict S)),
        ‖h₁.toLp (grad w) - h₂.toLp (grad v)‖ ≤ ε) := by
  haveI : IsFiniteMeasure (volume.restrict S) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter]
    exact hSb.measure_lt_top
  set K0 : ℝ := (measureUnivNNReal (volume.restrict S) : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹
  have hK0 : 0 ≤ K0 := by positivity
  set δ : ℝ := min ε (ε / (K0 + 1)) with hδdef
  have hδ : 0 < δ := lt_min hε (by positivity)
  have hδK : K0 * δ ≤ ε := by
    calc K0 * δ ≤ (K0 + 1) * (ε / (K0 + 1)) :=
          mul_le_mul (by linarith) (min_le_right _ _) hδ.le (by positivity)
      _ = ε := by field_simp
  obtain ⟨v, hv, hvK⟩ := exists_smooth_approx_on hw hSb.isCompact_closure hδ
  refine ⟨v, hv, fun x hx => (hvK x hx).1.trans (min_le_left _ _), fun h₁ h₂ => ?_,
    fun h₁ h₂ => ?_⟩
  · refine (norm_toLp_sub_le h₁ h₂ hδ.le ?_).trans hδK
    rw [ae_restrict_iff' hS]
    exact Eventually.of_forall fun x hx => by
      rw [norm_sub_rev]; exact (hvK x (subset_closure hx)).1
  · refine (norm_toLp_sub_le h₁ h₂ hδ.le ?_).trans hδK
    rw [ae_restrict_iff' hS]
    exact Eventually.of_forall fun x hx => by
      rw [norm_grad_sub, norm_sub_rev]; exact (hvK x (subset_closure hx)).2

/-! ### The disk -/

/-- The graph `(w, ∇w)` of a `C¹` function in `L²(𝔻) ⊕₂ L²(𝔻; ℝ²)`. -/
def embedC1 (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) : Amb :=
  WithLp.toLp 2 ((memLp_disk hw.continuous).toLp w, (memLp_disk (continuous_grad hw)).toLp (grad w))

@[simp] lemma embedC1_fst (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) :
    (embedC1 w hw).fst = (memLp_disk hw.continuous).toLp w := rfl
@[simp] lemma embedC1_snd (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) :
    (embedC1 w hw).snd = (memLp_disk (continuous_grad hw)).toLp (grad w) := rfl

lemma embedC1_smooth (u : smoothFns) :
    embedC1 u (contDiff_one_of_mem u.2) = embed u := rfl

/-- For every `ε > 0` there is a smooth `v` with `‖(w,∇w) - (v,∇v)‖ ≤ ε` in `L²(𝔻)`, and
`|v - w| ≤ ε` on `𝔻̄`. -/
theorem exists_embed_close (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : smoothFns, ‖embedC1 w hw - embed v‖ ≤ ε ∧
      ∀ x ∈ closedBall (0 : ℂ) 1, ‖(v : ℂ → ℝ) x - w x‖ ≤ ε := by
  obtain ⟨v, hv, hK, h1, h2⟩ := exists_smooth_graph_approx measurableSet_ball isBounded_ball hw
    (half_pos hε)
  refine ⟨⟨v, hv⟩, ?_, fun x hx => ?_⟩
  · refine (norm_prod_le _).trans ?_
    have a := h1 (memLp_disk hw.continuous) (memLp_disk hv.continuous)
    have b := h2 (memLp_disk (continuous_grad hw))
      (memLp_disk (continuous_grad (contDiff_one_of_mem hv)))
    change ‖_ - toL2 ⟨v, hv⟩‖ + ‖_ - gradL2 ⟨v, hv⟩‖ ≤ ε
    exact (add_le_add a b).trans (le_of_eq (add_halves ε))
  · exact (hK x (by rwa [closure_ball 0 one_ne_zero])).trans (half_le_self hε.le)

/-- **`C¹` functions lie in `H¹(𝔻)`.** -/
theorem embedC1_mem_H1 (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) : embedC1 w hw ∈ H1 := by
  show embedC1 w hw ∈ closure (LinearMap.range embed : Set Amb)
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, hv, -⟩ := exists_embed_close w hw (half_pos hε)
  exact ⟨embed v, ⟨v, rfl⟩, by rw [dist_eq_norm]; linarith⟩

/-- `C¹` functions as elements of `H¹(𝔻)`. -/
def embedC1H (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) : H1 := ⟨embedC1 w hw, embedC1_mem_H1 w hw⟩

lemma memLp_bdryC1 {w : ℂ → ℝ} (hw : Continuous w) :
    MemLp (fun t : ℝ => w (Complex.exp (t * Complex.I))) 2 μT :=
  memLp_circle (by fun_prop)

/-- **The trace of a `C¹` function is its boundary restriction**: `T(w) = w(e^{it})`. -/
theorem trace_embedC1 (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) :
    trace (embedC1H w hw) = (memLp_bdryC1 hw.continuous).toLp _ := by
  haveI : IsFiniteMeasure μT := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  set K1 : ℝ := (measureUnivNNReal μT : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹
  refine eq_of_forall_dist_le fun ε hε => ?_
  set δ : ℝ := ε / (4 + K1 + 1) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨v, hv, hvK⟩ := exists_embed_close w hw hδ
  have e1 : ‖trace (embedC1H w hw) - trace (embedH v)‖ ≤ 2 * δ := by
    rw [← map_sub]
    refine (norm_trace_le _).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Submodule.coe_norm, Submodule.coe_sub]
    exact hv
  have e2 : ‖trace (embedH v) - (memLp_bdryC1 hw.continuous).toLp _‖ ≤ K1 * δ := by
    rw [trace_embed]
    change ‖(memLp_bdry v).toLp _ - _‖ ≤ _
    refine norm_toLp_sub_le (memLp_bdry v) _ hδ.le (Eventually.of_forall fun t => ?_)
    exact hvK _ (sphere_subset_closedBall (ConformalPullback.exp_mem_sphere t))
  rw [dist_eq_norm, ← sub_add_sub_cancel _ (trace (embedH v))]
  refine (norm_add_le _ _).trans ((add_le_add e1 e2).trans ?_)
  have hK1 : 0 ≤ K1 := by positivity
  calc 2 * δ + K1 * δ ≤ (4 + K1 + 1) * δ := by nlinarith
    _ = ε := by rw [hδdef]; field_simp

theorem trace_embedC1_ae (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) :
    (trace (embedC1H w hw) : ℝ → ℝ) =ᵐ[μT] fun t => w (Complex.exp (t * Complex.I)) := by
  rw [trace_embedC1]; exact MemLp.coeFn_toLp _

/-! ### Bounded domains -/

namespace BddDomain

variable (D : BddDomain)

/-- The graph `(w, ∇w)` of a `C¹` function in `L²(Ω) ⊕₂ L²(Ω; ℝ²)`. -/
def embedC1 (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) : D.Amb :=
  WithLp.toLp 2 ((D.memLp_dom hw.continuous).toLp w,
    (D.memLp_dom (continuous_grad hw)).toLp (grad w))

@[simp] lemma embedC1_fst (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) :
    (D.embedC1 w hw).fst = (D.memLp_dom hw.continuous).toLp w := rfl
@[simp] lemma embedC1_snd (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) :
    (D.embedC1 w hw).snd = (D.memLp_dom (continuous_grad hw)).toLp (grad w) := rfl

theorem exists_embed_close (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : smoothFns, ‖D.embedC1 w hw - D.embed v‖ ≤ ε ∧
      ∀ x ∈ closure D.carrier, ‖(v : ℂ → ℝ) x - w x‖ ≤ ε := by
  obtain ⟨v, hv, hK, h1, h2⟩ := exists_smooth_graph_approx D.isOpen.measurableSet D.isBounded hw
    (half_pos hε)
  refine ⟨⟨v, hv⟩, ?_, fun x hx => (hK x hx).trans (half_le_self hε.le)⟩
  refine (norm_prod_le _).trans ?_
  have a := h1 (D.memLp_dom hw.continuous) (D.memLp_dom hv.continuous)
  have b := h2 (D.memLp_dom (continuous_grad hw))
    (D.memLp_dom (continuous_grad (contDiff_one_of_mem hv)))
  change ‖_ - D.toL2 ⟨v, hv⟩‖ + ‖_ - D.gradL2 ⟨v, hv⟩‖ ≤ ε
  exact (add_le_add a b).trans (le_of_eq (add_halves ε))

/-- **`C¹` functions lie in `H¹(Ω)`.** -/
theorem embedC1_mem_H1 (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) : D.embedC1 w hw ∈ D.H1 := by
  show D.embedC1 w hw ∈ closure (LinearMap.range D.embed : Set D.Amb)
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨v, hv, -⟩ := D.exists_embed_close w hw (half_pos hε)
  exact ⟨D.embed v, ⟨v, rfl⟩, by rw [dist_eq_norm]; linarith⟩

/-- `C¹` functions as elements of `H¹(Ω)`. -/
def embedC1H (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) : D.H1 := ⟨D.embedC1 w hw, D.embedC1_mem_H1 w hw⟩

/-- **The trace of a `C¹` function on `Ω` is its restriction to `∂Ω`** (given a trace
inequality). -/
theorem trace_embedC1 {C : ℝ} (hC : D.HasTraceIneq C) (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) :
    D.trace (D.embedC1H w hw) = (D.memLp_bdry hw.continuous).toLp w := by
  set K1 : ℝ := (measureUnivNNReal D.ν : ℝ) ^ ((2 : ℝ≥0∞).toReal)⁻¹
  refine eq_of_forall_dist_le fun ε hε => ?_
  set δ : ℝ := ε / (Real.sqrt C + K1 + 1) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨v, hv, hvK⟩ := D.exists_embed_close w hw hδ
  have e1 : ‖D.trace (D.embedC1H w hw) - D.trace (D.embedH v)‖ ≤ Real.sqrt C * δ := by
    rw [← map_sub]
    refine (D.norm_trace_le hC _).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    rw [Submodule.coe_norm, Submodule.coe_sub]
    exact hv
  have e2 : ‖D.trace (D.embedH v) - (D.memLp_bdry hw.continuous).toLp w‖ ≤ K1 * δ := by
    rw [D.trace_embed hC]
    refine norm_toLp_sub_le (D.memLp_bdry (continuous_of_mem v.2)) _ hδ.le ?_
    rw [ae_restrict_iff' isClosed_frontier.measurableSet]
    exact Eventually.of_forall fun x hx => hvK x (frontier_subset_closure hx)
  rw [dist_eq_norm, ← sub_add_sub_cancel _ (D.trace (D.embedH v))]
  refine (norm_add_le _ _).trans ((add_le_add e1 e2).trans ?_)
  have hK1 : 0 ≤ K1 := by positivity
  have hsC := Real.sqrt_nonneg C
  calc Real.sqrt C * δ + K1 * δ ≤ (Real.sqrt C + K1 + 1) * δ := by nlinarith
    _ = ε := by rw [hδdef]; field_simp

theorem trace_embedC1_ae {C : ℝ} (hC : D.HasTraceIneq C) (w : ℂ → ℝ) (hw : ContDiff ℝ 1 w) :
    (D.trace (D.embedC1H w hw) : ℂ → ℝ) =ᵐ[D.ν] w := by
  rw [D.trace_embedC1 hC]; exact MemLp.coeFn_toLp _

end BddDomain

end SteklovH1
