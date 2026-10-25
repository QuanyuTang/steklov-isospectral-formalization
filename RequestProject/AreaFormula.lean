module

public import RequestProject.ConformalPullback

/-!
# Area formula with multiplicity for holomorphic maps

For `B` holomorphic on an open set `U`, a measurable `E ⊆ U` whose critical points form a
countable set, and a measurable `F ≥ 0`,
`∫_E |B'(z)|² F(z) dA(z) = ∫_ℂ ∑_{z ∈ E, B(z) = w} F(z) dA(w)`
(`lintegral_deriv_sq_mul_eq_fibreSum`).  This is the change of variables for non-injective maps
(each value counted with multiplicity): it is the measure-theoretic input for comparing Dirichlet
energies on the two sides of a branched cover in the transplantation argument.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace SteklovArea

/-- The fibre sum `∑_{z ∈ E, B z = w} F z`. -/
def fibreSum (B : ℂ → ℂ) (E : Set ℂ) (F : ℂ → ℝ≥0∞) (w : ℂ) : ℝ≥0∞ :=
  ∑' z : {z // z ∈ E ∧ B z = w}, F z

/-- A countable cover of the non-critical part of `E` by open sets on which `B` is injective. -/
theorem exists_injective_cover {U : Set ℂ} (hU : IsOpen U) {B : ℂ → ℂ}
    (hB : DifferentiableOn ℂ B U) {E' : Set ℂ} (hE'U : E' ⊆ U)
    (hE' : ∀ z ∈ E', deriv B z ≠ 0) :
    ∃ V : ℕ → Set ℂ, (∀ n, IsOpen (V n)) ∧ (∀ n, V n ⊆ U) ∧ (∀ n, InjOn B (V n)) ∧
      E' ⊆ ⋃ n, V n := by
  have hloc : ∀ z : E', ∃ r > 0, Metric.ball (z : ℂ) r ⊆ U ∧
      InjOn B (Metric.ball (z : ℂ) r) := by
    intro z
    obtain ⟨r₁, hr₁, hinj⟩ := HolInv.exists_ball_injOn hU hB (hE'U z.2) (hE' z z.2)
    obtain ⟨r₂, hr₂, hsub⟩ := Metric.isOpen_iff.1 hU z (hE'U z.2)
    refine ⟨min r₁ r₂, lt_min hr₁ hr₂, (Metric.ball_subset_ball (min_le_right _ _)).trans hsub,
      hinj.mono (Metric.ball_subset_ball (min_le_left _ _))⟩
  choose r hr hrU hrinj using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : E' => Metric.ball (z : ℂ) (r z)) (fun _ => Metric.isOpen_ball)
  rcases T.eq_empty_or_nonempty with hT | hT
  · refine ⟨fun _ => ∅, fun _ => isOpen_empty, fun _ => empty_subset _, fun _ => injOn_empty _,
      ?_⟩
    intro z hz
    have : z ∈ ⋃ i : E', Metric.ball (i : ℂ) (r i) :=
      mem_iUnion.2 ⟨⟨z, hz⟩, Metric.mem_ball_self (hr _)⟩
    rw [← hTU, hT] at this
    simp at this
  · obtain ⟨e, he⟩ := hTc.exists_eq_range hT
    refine ⟨fun n => Metric.ball ((e n : E') : ℂ) (r (e n)), fun _ => Metric.isOpen_ball,
      fun n => hrU _, fun n => hrinj _, ?_⟩
    intro z hz
    have : z ∈ ⋃ i : E', Metric.ball (i : ℂ) (r i) :=
      mem_iUnion.2 ⟨⟨z, hz⟩, Metric.mem_ball_self (hr _)⟩
    rw [← hTU, he] at this
    simp only [mem_iUnion, mem_range, exists_prop] at this
    obtain ⟨i, ⟨n, rfl⟩, hi⟩ := this
    exact mem_iUnion.2 ⟨n, hi⟩

/-- **Area formula with multiplicity.** -/
theorem lintegral_deriv_sq_mul_eq_fibreSum {U : Set ℂ} (hU : IsOpen U) {B : ℂ → ℂ}
    (hB : DifferentiableOn ℂ B U) {E : Set ℂ} (hE : MeasurableSet E) (hEU : E ⊆ U)
    (hcrit : {z ∈ E | deriv B z = 0}.Countable) (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z in E, ‖deriv B z‖ₑ ^ 2 * F z = ∫⁻ w, fibreSum B E F w := by
  classical
  set C := {z ∈ E | deriv B z = 0} with hC
  set E' := E \ C with hE'
  have hCm : MeasurableSet C := hcrit.measurableSet
  have hE'm : MeasurableSet E' := hE.diff hCm
  have hC0 : volume C = 0 := hcrit.measure_zero _
  have hE'E : E' ⊆ E := diff_subset
  have hE'd : ∀ z ∈ E', deriv B z ≠ 0 := fun z hz h => hz.2 ⟨hz.1, h⟩
  obtain ⟨V, hVo, hVU, hVinj, hcov⟩ := exists_injective_cover hU hB (hE'E.trans hEU) hE'd
  set P : ℕ → Set ℂ := disjointed (fun n => V n ∩ E') with hP
  have hPm : ∀ n, MeasurableSet (P n) := MeasurableSet.disjointed fun n =>
    (hVo n).measurableSet.inter hE'm
  have hPd : Pairwise (Function.onFun Disjoint P) := disjoint_disjointed _
  have hPV : ∀ n, P n ⊆ V n ∩ E' := fun n => disjointed_subset _ n
  have hPU : ⋃ n, P n = E' := by
    rw [hP, iUnion_disjointed, ← iUnion_inter, inter_eq_right.2 hcov]
  -- remove the (null) critical set
  have h1 : ∫⁻ z in E, ‖deriv B z‖ₑ ^ 2 * F z = ∫⁻ z in E', ‖deriv B z‖ₑ ^ 2 * F z := by
    refine setLIntegral_congr ?_
    exact (diff_null_ae_eq_self hC0).symm
  -- split into pieces on which `B` is injective
  have h2 : ∫⁻ z in E', ‖deriv B z‖ₑ ^ 2 * F z =
      ∑' n, ∫⁻ z in P n, ‖deriv B z‖ₑ ^ 2 * F z := by
    rw [← hPU, lintegral_iUnion hPm hPd]
  -- measurable local inverses
  set ψ : ℕ → ℂ → ℂ := fun n => (B '' V n).piecewise (Function.invFunOn B (V n)) (fun _ => 0)
    with hψ
  have hψm : ∀ n, Measurable (ψ n) := by
    intro n
    refine ContinuousOn.measurable_piecewise ?_ continuousOn_const
      ((HolInv.isOpen_image (hB.mono (hVU n)) (hVinj n) subset_rfl (hVo n)).measurableSet)
    rintro _ ⟨z, hz, rfl⟩
    exact (HolInv.continuousAt_invFunOn (hVo n) (hB.mono (hVU n)) (hVinj n)
      hz).continuousWithinAt
  have hψB : ∀ n, ∀ z ∈ V n, ψ n (B z) = z := fun n z hz => by
    simp only [hψ, piecewise_eq_of_mem _ _ _ (mem_image_of_mem B hz)]
    exact HolInv.invFunOn_apply_self (hVinj n) hz
  have hBd : ∀ z ∈ U, HasFDerivAt B (ConformalPullback.mulR (deriv B z)) z := fun z hz =>
    ((hB.differentiableAt (hU.mem_nhds hz)).hasDerivAt.hasFDerivAt).restrictScalars ℝ
  -- change of variables on each piece (Jacobian `|B'|²`)
  have h3 : ∀ n, ∫⁻ z in P n, ‖deriv B z‖ₑ ^ 2 * F z = ∫⁻ w in B '' P n, F (ψ n w) := by
    intro n
    rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (hPm n)
      (fun x hx => (hBd x (hVU n (hPV n hx).1)).hasFDerivWithinAt)
      ((hVinj n).mono fun x hx => (hPV n hx).1)]
    refine setLIntegral_congr_fun (hPm n) fun x hx => ?_
    rw [hψB n x (hPV n hx).1, ConformalPullback.det_mulR, abs_of_nonneg (by positivity),
      ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have himm : ∀ n, MeasurableSet (B '' P n) := fun n =>
    (hPm n).image_of_continuousOn_injOn
      ((hB.mono (hVU n)).continuousOn.mono fun x hx => (hPV n hx).1)
      ((hVinj n).mono fun x hx => (hPV n hx).1)
  have h4 : ∑' n, ∫⁻ w in B '' P n, F (ψ n w) =
      ∫⁻ w, ∑' n, (B '' P n).indicator (fun w => F (ψ n w)) w := by
    rw [lintegral_tsum (f := fun n => (B '' P n).indicator (fun w => F (ψ n w)))
      fun n => ((hF.comp (hψm n)).indicator (himm n)).aemeasurable]
    exact tsum_congr fun n => (lintegral_indicator (himm n) _).symm
  -- identification with the fibre sums off the (null) set of critical values
  have hnull : ∀ᵐ w, w ∉ B '' C := by
    have : volume (B '' C) = 0 := (hcrit.image B).measure_zero _
    exact measure_eq_zero_iff_ae_notMem.1 this
  have h5 : ∀ w ∉ B '' C, ∑' n, (B '' P n).indicator (fun w => F (ψ n w)) w =
      fibreSum B E F w := by
    intro w hw
    have hind : ∀ n, (B '' P n).indicator (fun w => F (ψ n w)) w =
        ({n | w ∈ B '' P n} : Set ℕ).indicator (fun n => F (ψ n w)) n := by
      intro n
      by_cases h : w ∈ B '' P n
      · rw [indicator_of_mem h, indicator_of_mem (show n ∈ {n | w ∈ B '' P n} from h)]
      · rw [indicator_of_notMem h, indicator_of_notMem (show n ∉ {n | w ∈ B '' P n} from h)]
    rw [tsum_congr hind, ← tsum_subtype]
    have hmem : ∀ n : {n | w ∈ B '' P n}, ψ n w ∈ P n ∧ B (ψ n w) = w := by
      rintro ⟨n, x, hx, hxw⟩
      simp only
      rw [← hxw, hψB n x (hPV n hx).1]
      exact ⟨hx, rfl⟩
    let e : {n | w ∈ B '' P n} → {z // z ∈ E ∧ B z = w} := fun n =>
      ⟨ψ n w, hE'E (hPV n (hmem n).1).2, (hmem n).2⟩
    have he : Function.Bijective e := by
      constructor
      · intro n m hnm
        have h' : ψ n w = ψ m w := congrArg Subtype.val hnm
        by_contra hne
        have hne' : (n : ℕ) ≠ m := fun h => hne (Subtype.ext h)
        exact Set.disjoint_left.1 (hPd hne') (hmem n).1 (h' ▸ (hmem m).1)
      · rintro ⟨z, hzE, hzw⟩
        have hzE' : z ∈ E' := ⟨hzE, fun hzC => hw ⟨z, hzC, hzw⟩⟩
        rw [← hPU] at hzE'
        obtain ⟨n, hn⟩ := mem_iUnion.1 hzE'
        have hn' : n ∈ {n | w ∈ B '' P n} := ⟨z, hn, hzw⟩
        refine ⟨⟨n, hn'⟩, Subtype.ext ?_⟩
        show ψ n w = z
        rw [← hzw, hψB n z (hPV n hn).1]
    unfold fibreSum
    exact (Equiv.ofBijective e he).tsum_eq (fun z => F z)
  rw [h1, h2, tsum_congr h3, h4]
  exact lintegral_congr_ae (hnull.mono h5)

end SteklovArea
