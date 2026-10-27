module

public import RequestProject.PuncturedDiskCover

/-!
# Classification of connected finite covers of a punctured disk: the power maps

Let `p : C → D*_r` be a covering map of the punctured disk `D*_r = {0 < |z| < r}` by a
path-connected space `C`, with finite fibres.  We prove that there are `e ≥ 1` and a
homeomorphism `Φ : C ≃ₜ D*_{r^{1/e}}` with `(Φ c)^e = p c` for all `c`
(`exists_powerCover_homeomorph`); moreover `e` is the cardinality of every fibre.

The proof uses the half-plane lift `L : {Re w < log r} → C` of `exp` constructed in
`PuncturedDiskCover.lean`: `L` is surjective, its period group is `eℤ`, and `Φ (L w) = exp (w/e)`.
-/

@[expose] public section

open Set Topology Complex Filter

noncomputable section

namespace SteklovPunctured

variable {r : ℝ} [Fact (0 < r)] {C : Type*} [TopologicalSpace C] {p : C → pdisk r}

lemma isLocalHomeomorph_expP (r : ℝ) : IsLocalHomeomorph (expP r) :=
  (isCoveringMap_expP r).isLocalHomeomorph

lemma expP_surjective (r : ℝ) : Function.Surjective (expP r) := by
  rintro ⟨z, hz⟩
  refine ⟨⟨log z, ?_⟩, Subtype.ext ?_⟩
  · show exp (log z) ∈ pdisk r
    rw [exp_log hz.1]; exact hz
  · show exp (log z) = z
    exact exp_log hz.1

omit [Fact (0 < r)] in
/-- The lift is a local homeomorphism. -/
lemma isLocalHomeomorph_lift (hp : IsCoveringMap p) (L : C(Hp r, C)) (hL : p ∘ L = expP r) :
    IsLocalHomeomorph L :=
  IsLocalHomeomorph.of_comp (hL ▸ isLocalHomeomorph_expP r) hp.isLocalHomeomorph L.continuous

/-- The lift is surjective when `C` is path-connected. -/
theorem lift_surjective [PathConnectedSpace C] (hp : IsCoveringMap p) (L : C(Hp r, C))
    (hL : p ∘ L = expP r) : Function.Surjective L := by
  have hw : (Real.log r - 1 : ℂ) ∈ exp ⁻¹' pdisk r := by
    rw [exp_preimage_pdisk (Fact.out)]; simp
  let w₀ : Hp r := ⟨_, hw⟩
  intro c
  obtain ⟨γ⟩ := PathConnectedSpace.joined (L w₀) c
  -- lift `p ∘ γ` through `exp`
  obtain ⟨δ, hδ, hδ0⟩ := (isCoveringMap_expP r).exists_path_lifts
    ⟨p ∘ γ, hp.continuous.comp γ.continuous⟩ w₀
    (by simp only [ContinuousMap.coe_mk, Function.comp_apply, Path.source]
        exact congrFun hL w₀)
  have heq : (L ∘ δ : unitInterval → C) = γ := by
    have := hp.eq_of_comp_eq (g₁ := L ∘ δ) (g₂ := γ) (L.continuous.comp δ.continuous)
      γ.continuous ?_ 0 (by simp [hδ0])
    · exact this
    · funext t
      have h1 := congrFun hδ t
      simp only [ContinuousMap.coe_mk, Function.comp_apply] at h1 ⊢
      rw [← h1]; exact congrFun hL (δ t)
  exact ⟨δ 1, by simpa using congrFun heq 1⟩

/-- Two points of the half-plane with the same image under `L` differ by a period. -/
lemma exists_period_of_eq (hp : IsCoveringMap p) (L : C(Hp r, C)) (hL : p ∘ L = expP r)
    {w w' : Hp r} (h : L w' = L w) : ∃ n ∈ periods L, w' = shift n w := by
  have h1 : exp (w' : ℂ) = exp (w : ℂ) := by
    have h2 := congrFun hL w
    have h3 := congrFun hL w'
    simp only [Function.comp_apply] at h2 h3
    have : expP r w' = expP r w := by rw [← h2, ← h3, h]
    exact congrArg Subtype.val this
  obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 h1
  have hw' : w' = shift n w := Subtype.ext hn
  refine ⟨n, fun v => ?_, hw'⟩
  exact shift_eq_of_eq hp L hL n (w₀ := w) (by rw [← hw', h]) v

omit [Fact (0 < r)] in
/-- The period group of `L` is `eℤ` for some natural `e`. -/
lemma exists_periods_eq (L : C(Hp r, C)) :
    ∃ e : ℕ, periods L = AddSubgroup.zmultiples (e : ℤ) := by
  obtain ⟨a, ha⟩ := Int.subgroup_cyclic (periods L)
  refine ⟨a.natAbs, ?_⟩
  rw [Int.zmultiples_natAbs, ha, AddSubgroup.zmultiples_eq_closure]

omit [Fact (0 < r)] in
/-- The map `n ↦ L (w + 2πin)` from `ℤ` onto the fibre through `L w`. -/
lemma fibre_eq_range (L : C(Hp r, C)) (hL : p ∘ L = expP r)
    (hsurj : Function.Surjective L) (w : Hp r) :
    p ⁻¹' {p (L w)} = range (fun n : ℤ => L (shift n w)) := by
  ext c
  simp only [mem_preimage, mem_singleton_iff, mem_range]
  constructor
  · intro hc
    obtain ⟨v, rfl⟩ := hsurj c
    have h1 : exp (v : ℂ) = exp (w : ℂ) := by
      have h2 := congrFun hL w
      have h3 := congrFun hL v
      simp only [Function.comp_apply] at h2 h3
      have : expP r v = expP r w := by rw [← h2, ← h3, hc]
      exact congrArg Subtype.val this
    obtain ⟨n, hn⟩ := exp_eq_exp_iff_exists_int.1 h1
    exact ⟨n, by rw [show v = shift n w from Subtype.ext hn]⟩
  · rintro ⟨n, rfl⟩
    have h1 := congrFun hL (shift n w)
    have h2 := congrFun hL w
    simp only [Function.comp_apply] at h1 h2
    rw [h1, h2, expP_shift]

/-- With finite fibres the period is positive, and every fibre has exactly `e` points. -/
theorem card_fibre_eq (hp : IsCoveringMap p) (L : C(Hp r, C)) (hL : p ∘ L = expP r)
    (hsurj : Function.Surjective L) {e : ℕ} (he : periods L = AddSubgroup.zmultiples (e : ℤ))
    (c : C) : Nat.card (p ⁻¹' {p c}) = e := by
  obtain ⟨w, rfl⟩ := hsurj c
  rw [fibre_eq_range L hL hsurj w]
  -- the fibre is the image of `ℤ ⧸ eℤ`
  have key : ∀ m n : ℤ, L (shift m w) = L (shift n w) ↔ (m : ZMod e) = n := by
    intro m n
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    constructor
    · intro h
      have : n - m ∈ periods L := by
        intro v
        have := shift_eq_of_eq hp L hL (n - m) (w₀ := shift m w)
          (by rw [← shift_add, sub_add_cancel, h]) v
        exact this
      rw [he, Int.mem_zmultiples_iff] at this
      exact this
    · intro h
      have hm : n - m ∈ periods L := by rw [he, Int.mem_zmultiples_iff]; exact h
      rw [show n = (n - m) + m by ring, shift_add, hm]
  let F : ZMod e → range (fun n : ℤ => L (shift n w)) := fun k =>
    ⟨L (shift ((k.cast : ℤ)) w), ⟨_, rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro a b hab
      have := (key _ _).1 (congrArg Subtype.val hab)
      simpa using this
    · rintro ⟨_, ⟨n, rfl⟩⟩
      refine ⟨(n : ZMod e), Subtype.ext ((key _ _).2 ?_)⟩
      simp
  rw [← Nat.card_eq_of_bijective F hF, Nat.card_zmod]

/-- If some fibre is finite then the period `e` is positive. -/
theorem period_pos (hp : IsCoveringMap p) (L : C(Hp r, C)) (hL : p ∘ L = expP r)
    (hsurj : Function.Surjective L) {e : ℕ} (he : periods L = AddSubgroup.zmultiples (e : ℤ))
    (c : C) (hfin : (p ⁻¹' {p c}).Finite) : 0 < e := by
  rcases Nat.eq_zero_or_pos e with h0 | h
  · exfalso
    obtain ⟨w, rfl⟩ := hsurj c
    rw [fibre_eq_range L hL hsurj w] at hfin
    have hinj : Function.Injective (fun n : ℤ => L (shift n w)) := by
      intro m n hmn
      have : n - m ∈ periods L := by
        intro v
        exact shift_eq_of_eq hp L hL (n - m) (w₀ := shift m w)
          (by rw [← shift_add, sub_add_cancel]; exact hmn.symm) v
      rw [he, h0, Nat.cast_zero, AddSubgroup.zmultiples_zero_eq_bot,
        AddSubgroup.mem_bot] at this
      omega
    exact infinite_range_of_injective hinj hfin
  · exact h

lemma re_lt_log (w : Hp r) : (w : ℂ).re < Real.log r := by
  have h : (w : ℂ) ∈ {w : ℂ | w.re < Real.log r} := exp_preimage_pdisk (Fact.out : 0 < r) ▸ w.2
  exact h

/-- The radius `r^{1/e}` of the model punctured disk. -/
def rootRad (r : ℝ) (e : ℕ) : ℝ := Real.exp (Real.log r / e)

lemma exp_div_mem {e : ℕ} (he : 0 < e) (w : Hp r) :
    exp ((w : ℂ) / e) ∈ pdisk (rootRad r e) := by
  refine ⟨exp_ne_zero _, ?_⟩
  rw [Complex.norm_exp, rootRad, Real.exp_lt_exp]
  have hw : (w : ℂ).re < Real.log r := by
    exact re_lt_log w
  have : ((w : ℂ) / e).re = (w : ℂ).re / e := by
    simp [Complex.div_re, Complex.normSq_natCast]
    field_simp
  rw [this]
  exact div_lt_div_of_pos_right hw (by exact_mod_cast he)

/-- `w ↦ exp (w / e)` as a map from the half-plane to the model punctured disk. -/
def rootExp (r : ℝ) [Fact (0 < r)] {e : ℕ} (he : 0 < e) (w : Hp r) : pdisk (rootRad r e) :=
  ⟨exp ((w : ℂ) / e), exp_div_mem he w⟩

lemma continuous_rootExp {e : ℕ} (he : 0 < e) : Continuous (rootExp r he) :=
  (continuous_exp.comp (continuous_subtype_val.div_const _)).subtype_mk _

lemma isOpenMap_rootExp {e : ℕ} (he : 0 < e) : IsOpenMap (rootExp r he) := by
  intro U hU
  have hHp : IsOpen (exp ⁻¹' pdisk r) := (isOpen_pdisk r).preimage continuous_exp
  obtain ⟨V, hV, rfl⟩ := hU
  have hne : (e : ℂ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast he.ne')
  have hO : IsOpen ((fun w : ℂ => exp (w / e)) '' (V ∩ exp ⁻¹' pdisk r)) := by
    have := (isOpenMap_exp.comp (Homeomorph.mulRight₀ _ hne).isOpenMap) _ (hV.inter hHp)
    simpa [div_eq_mul_inv] using this
  refine ⟨_, hO, ?_⟩
  ext z
  simp only [mem_preimage, mem_image, rootExp]
  constructor
  · rintro ⟨w, ⟨hwV, hw⟩, hz⟩
    exact ⟨⟨w, hw⟩, hwV, Subtype.ext hz⟩
  · rintro ⟨w, hwV, rfl⟩
    exact ⟨w, ⟨hwV, w.2⟩, rfl⟩


lemma rootRad_pos (r : ℝ) (e : ℕ) : 0 < rootRad r e := Real.exp_pos _

lemma rootRad_pow {e : ℕ} (he : 0 < e) : rootRad r e ^ e = r := by
  rw [rootRad, ← Real.exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast he.ne'),
    Real.exp_log Fact.out]

section Model

variable (hp : IsCoveringMap p) (L : C(Hp r, C)) (hL : p ∘ L = expP r)
  {e : ℕ} (he0 : 0 < e) (he : periods L = AddSubgroup.zmultiples (e : ℤ))
include hp hL he

lemma rootExp_eq_iff {w w' : Hp r} : rootExp r he0 w = rootExp r he0 w' ↔ L w = L w' := by
  have hne : (e : ℂ) ≠ 0 := by exact_mod_cast he0.ne'
  constructor
  · intro h
    have h1 : exp ((w : ℂ) / e) = exp ((w' : ℂ) / e) := congrArg Subtype.val h
    obtain ⟨k, hk⟩ := exp_eq_exp_iff_exists_int.1 h1
    have hmem : (e : ℤ) * k ∈ periods L := by
      rw [he]; exact Int.mem_zmultiples_iff.2 (dvd_mul_right _ _)
    have hw : w = shift ((e : ℤ) * k) w' := by
      apply Subtype.ext
      simp only [shift]
      field_simp at hk
      push_cast
      linear_combination hk
    rw [hw, hmem]
  · intro h
    obtain ⟨n, hn, hw⟩ := exists_period_of_eq hp L hL h
    rw [he, Int.mem_zmultiples_iff] at hn
    obtain ⟨k, rfl⟩ := hn
    apply Subtype.ext
    simp only [rootExp, hw, shift]
    rw [show ((w' : ℂ) + ((e * k : ℤ) : ℂ) * (2 * Real.pi * I)) / e
        = (w' : ℂ) / e + (k : ℂ) * (2 * Real.pi * I) by push_cast; field_simp,
      exp_add, exp_int_mul_two_pi_mul_I, mul_one]

variable [PathConnectedSpace C]

/-- The power chart `Φ : C → D*_{r^{1/e}}`, characterized by `Φ (L w) = exp (w / e)`. -/
def powerChart : C → pdisk (rootRad r e) :=
  fun c => rootExp r he0 (Function.surjInv (lift_surjective hp L hL) c)

omit he in
lemma powerChart_lift (w : Hp r) (he : periods L = AddSubgroup.zmultiples (e : ℤ)) :
    powerChart hp L hL he0 (L w) = rootExp r he0 w :=
  (rootExp_eq_iff hp L hL he0 he).2 (Function.surjInv_eq (lift_surjective hp L hL) (L w))

lemma powerChart_comp : powerChart hp L hL he0 ∘ L = rootExp r he0 :=
  funext fun w => powerChart_lift hp L hL he0 w he

lemma continuous_powerChart : Continuous (powerChart hp L hL he0) := by
  have hq : IsQuotientMap L := (isLocalHomeomorph_lift hp L hL).isOpenMap.isQuotientMap
    L.continuous (lift_surjective hp L hL)
  rw [hq.continuous_iff, powerChart_comp hp L hL he0 he]
  exact continuous_rootExp he0

lemma powerChart_bijective : Function.Bijective (powerChart hp L hL he0) := by
  have hsurj := lift_surjective hp L hL
  constructor
  · intro c c' h
    obtain ⟨w, rfl⟩ := hsurj c
    obtain ⟨w', rfl⟩ := hsurj c'
    rw [powerChart_lift hp L hL he0 w he, powerChart_lift hp L hL he0 w' he] at h
    exact (rootExp_eq_iff hp L hL he0 he).1 h
  · rintro ⟨z, hz0, hzr⟩
    have hre : ((e : ℂ) * log z).re < Real.log r := by
      have h1 : ((e : ℂ) * log z).re = e * Real.log ‖z‖ := by
        simp [Complex.log_re]
      rw [h1]
      have h2 : Real.log ‖z‖ < Real.log r / e := by
        have := Real.log_lt_log (norm_pos_iff.2 hz0) hzr
        rwa [rootRad, Real.log_exp] at this
      have hepos : (0 : ℝ) < e := by exact_mod_cast he0
      calc (e : ℝ) * Real.log ‖z‖ < e * (Real.log r / e) := mul_lt_mul_of_pos_left h2 hepos
        _ = Real.log r := by field_simp
    have hw : (e : ℂ) * log z ∈ exp ⁻¹' pdisk r := by
      rw [exp_preimage_pdisk Fact.out]; exact hre
    refine ⟨L ⟨_, hw⟩, ?_⟩
    rw [powerChart_lift hp L hL he0 _ he]
    apply Subtype.ext
    simp only [rootExp]
    rw [mul_div_cancel_left₀ _ (by exact_mod_cast he0.ne'), exp_log hz0]

lemma isOpenMap_powerChart : IsOpenMap (powerChart hp L hL he0) := by
  intro U hU
  have : powerChart hp L hL he0 '' U = rootExp r he0 '' (L ⁻¹' U) := by
    rw [← powerChart_comp hp L hL he0 he, image_comp,
      image_preimage_eq _ (lift_surjective hp L hL)]
  rw [this]
  exact isOpenMap_rootExp he0 _ (hU.preimage L.continuous)

/-- The power chart as a homeomorphism `C ≃ₜ D*_{r^{1/e}}`. -/
def powerHomeo : C ≃ₜ pdisk (rootRad r e) :=
  (Equiv.ofBijective _ (powerChart_bijective hp L hL he0 he)).toHomeomorphOfContinuousOpen
    (continuous_powerChart hp L hL he0 he) (isOpenMap_powerChart hp L hL he0 he)

lemma powerHomeo_apply (c : C) : powerHomeo hp L hL he0 he c = powerChart hp L hL he0 c := rfl

/-- The power chart conjugates `p` to `t ↦ t^e`. -/
lemma powerChart_pow (c : C) : ((powerChart hp L hL he0 c : ℂ)) ^ e = p c := by
  obtain ⟨w, rfl⟩ := lift_surjective hp L hL c
  rw [powerChart_lift hp L hL he0 w he]
  have h1 := congrFun hL w
  simp only [Function.comp_apply] at h1
  rw [h1]
  simp only [rootExp, expP, restrictPreimage_coe]
  rw [← exp_nat_mul, mul_div_cancel₀ _ (by exact_mod_cast he0.ne')]

end Model

/-- A covering of the punctured disk by a nonempty space is surjective. -/
theorem covering_surjective [Nonempty C] (hp : IsCoveringMap p) : Function.Surjective p := by
  obtain ⟨c₀⟩ := (inferInstance : Nonempty C)
  obtain ⟨w₀, hw₀⟩ := expP_surjective r (p c₀)
  obtain ⟨L, -, hL⟩ := exists_lift hp w₀ c₀ hw₀.symm
  intro x
  obtain ⟨w, rfl⟩ := expP_surjective r x
  exact ⟨L w, congrFun hL w⟩

/-- **Local power-cover classification.**  A path-connected covering space with finite fibres of
the punctured disk `{0 < |z| < r}` is isomorphic, over the punctured disk, to the power map
`t ↦ t^e` on `{0 < |t| < r^{1/e}}`, where `e ≥ 1` is the number of sheets. -/
theorem exists_powerCover_homeomorph [PathConnectedSpace C] (hp : IsCoveringMap p)
    (hfin : ∀ x, (p ⁻¹' {x}).Finite) :
    ∃ e : ℕ, 0 < e ∧ (∀ x, Nat.card (p ⁻¹' {x}) = e) ∧
      ∃ Φ : C ≃ₜ pdisk (rootRad r e), ∀ c, ((Φ c : ℂ)) ^ e = p c := by
  obtain ⟨c₀⟩ := (inferInstance : Nonempty C)
  obtain ⟨w₀, hw₀⟩ := expP_surjective r (p c₀)
  obtain ⟨L, -, hL⟩ := exists_lift hp w₀ c₀ hw₀.symm
  have hsurj := lift_surjective hp L hL
  obtain ⟨e, he⟩ := exists_periods_eq L
  have he0 : 0 < e := period_pos hp L hL hsurj he c₀ (hfin _)
  refine ⟨e, he0, fun x => ?_, powerHomeo hp L hL he0 he, powerChart_pow hp L hL he0 he⟩
  obtain ⟨w, rfl⟩ := expP_surjective r x
  have h1 := congrFun hL w
  simp only [Function.comp_apply] at h1
  rw [← h1]
  exact card_fibre_eq hp L hL hsurj he (L w)

end SteklovPunctured
