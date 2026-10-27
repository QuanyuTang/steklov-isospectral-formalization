module

public import RequestProject.BlaschkePerimeter

/-!
# Boundary fibre formula for finite Blaschke products

For a finite Blaschke product `B` of degree `n ≥ 1` and a measurable `F : ℂ → [0,∞]`,
`∫₀^{2π} F(e^{it}) |B'(e^{it})| dt = ∫₀^{2π} ∑_{z ∈ 𝕋, B z = e^{is}} F(z) ds`.

This is the boundary half of the transplantation computation (the interior half is the area
formula `SteklovArea.lintegral_deriv_sq_mul_eq_fibreSum`): the boundary measure `|B'| dt` on
`𝕋` pushes forward under `B` to the fibre-sum of arc length.  The proof lifts the boundary
values: `B(e^{it}) = e^{iφ(t)}` with `φ' = |B'(e^{it})| > 0` and `φ(t + 2π) = φ(t) + 2πn`.
-/

@[expose] public section

open Complex Metric Set MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace SteklovBlaschke

/-- The fibre sum `∑_{z ∈ 𝕋, B z = w} F(z)` over the unit circle. -/
def circFibreSum (B : ℂ → ℂ) (F : ℂ → ℝ≥0∞) (w : ℂ) : ℝ≥0∞ :=
  ∑' z : {z : ℂ // ‖z‖ = 1 ∧ B z = w}, F z

section lift

variable {B : ℂ → ℂ} {q : ℝ → ℝ} {n : ℕ}

/-- The lift `φ(t) = c + ∫₀ᵗ q`. -/
def liftFun (c : ℝ) (q : ℝ → ℝ) (t : ℝ) : ℝ := c + ∫ τ in (0:ℝ)..t, q τ

lemma hasDerivAt_liftFun (c : ℝ) (hq : Continuous q) (t : ℝ) :
    HasDerivAt (liftFun c q) (q t) t := by
  unfold liftFun
  exact (hq.integral_hasStrictDerivAt 0 t).hasDerivAt.const_add c

lemma liftFun_add_period (c : ℝ) (hq : Continuous q) (hper : ∀ t, q (t + 2 * Real.pi) = q t)
    (hint : ∫ t in (0:ℝ)..(2 * Real.pi), q t = 2 * Real.pi * n) (t : ℝ) :
    liftFun c q (t + 2 * Real.pi) = liftFun c q t + 2 * Real.pi * n := by
  unfold liftFun
  have h1 := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hq.intervalIntegrable 0 t) (hq.intervalIntegrable t (t + 2 * Real.pi))
  have h2 : ∫ τ in t..t + 2 * Real.pi, q τ = ∫ τ in (0:ℝ)..0 + 2 * Real.pi, q τ :=
    Function.Periodic.intervalIntegral_add_eq (f := q) hper t 0
  rw [← h1, h2, zero_add, hint]
  ring

lemma liftFun_strictMono (c : ℝ) (hq : Continuous q) (hpos : ∀ t, 0 < q t) :
    StrictMono (liftFun c q) :=
  strictMono_of_hasDerivAt_pos (fun t => hasDerivAt_liftFun c hq t) hpos

lemma liftFun_add_mul_period (c : ℝ) (hq : Continuous q) (hper : ∀ t, q (t + 2 * Real.pi) = q t)
    (hint : ∫ t in (0:ℝ)..(2 * Real.pi), q t = 2 * Real.pi * n) (t : ℝ) (m : ℕ) :
    liftFun c q (t + 2 * Real.pi * m) = liftFun c q t + 2 * Real.pi * n * m := by
  induction m with
  | zero => simp
  | succ m ih =>
    have := liftFun_add_period (n := n) c hq hper hint (t + 2 * Real.pi * m)
    push_cast
    rw [show t + 2 * Real.pi * (m + 1) = t + 2 * Real.pi * m + 2 * Real.pi by ring, this, ih]
    ring

lemma liftFun_surjective (c : ℝ) (hq : Continuous q) (hpos : ∀ t, 0 < q t)
    (hper : ∀ t, q (t + 2 * Real.pi) = q t)
    (hint : ∫ t in (0:ℝ)..(2 * Real.pi), q t = 2 * Real.pi * n) (hn : 0 < n) :
    Function.Surjective (liftFun c q) := by
  have hmono := (liftFun_strictMono c hq hpos).monotone
  have hcont : Continuous (liftFun c q) :=
    continuous_iff_continuousAt.2 fun t => (hasDerivAt_liftFun c hq t).continuousAt
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpi := Real.pi_pos
  refine hcont.surjective ?_ ?_
  · refine hmono.tendsto_atTop_atTop fun b => ?_
    obtain ⟨m, hm⟩ := exists_nat_ge ((b - liftFun c q 0) / (2 * Real.pi))
    refine ⟨0 + 2 * Real.pi * m, ?_⟩
    rw [liftFun_add_mul_period (n := n) c hq hper hint]
    rw [div_le_iff₀ (by positivity)] at hm
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [mul_nonneg (mul_nonneg this hpi.le) (sub_nonneg.2 hnR)]
  · refine hmono.tendsto_atBot_atBot fun b => ?_
    obtain ⟨m, hm⟩ := exists_nat_ge ((liftFun c q 0 - b) / (2 * Real.pi))
    refine ⟨0 - 2 * Real.pi * m, ?_⟩
    have := liftFun_add_mul_period (n := n) c hq hper hint (0 - 2 * Real.pi * m) m
    rw [sub_add_cancel] at this
    rw [div_le_iff₀ (by positivity)] at hm
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith [mul_nonneg (mul_nonneg this hpi.le) (sub_nonneg.2 hnR)]

end lift

lemma exists_lift {B : ℂ → ℂ} {q : ℝ → ℝ} (hq : Continuous q)
    (hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => B (exp (s * I))) (I * B (exp (t * I)) * q t) t)
    (hnorm : ∀ t : ℝ, ‖B (exp (t * I))‖ = 1) :
    ∃ c : ℝ, ∀ t : ℝ, B (exp (t * I)) = exp (liftFun c q t * I) := by
  obtain ⟨c, hc⟩ := circle_surj (hnorm 0)
  have h2 : ∀ t : ℝ, HasDerivAt (fun s : ℝ => exp ((liftFun c q s : ℂ) * I))
      (I * exp ((liftFun c q t : ℂ) * I) * q t) t := by
    intro t
    have := (((hasDerivAt_liftFun c hq t).ofReal_comp).mul_const I).cexp
    convert this using 1
    ring
  obtain ⟨η, -, hη⟩ := const_of_same_arg hderiv h2 hnorm (fun t => norm_exp_ofReal_mul_I _)
  have h0 := hη 0
  have hl0 : liftFun c q 0 = c := by simp [liftFun]
  rw [hl0, hc] at h0
  have hB0 : B (exp ((0:ℝ) * I)) ≠ 0 := by
    intro h; have := hnorm 0; rw [h, norm_zero] at this; exact zero_ne_one this
  have hη1 : η = 1 := by
    have := mul_right_cancel₀ hB0 (h0.symm.trans (one_mul _).symm)
    exact this
  refine ⟨c, fun t => ?_⟩
  rw [hη t, hη1, one_mul]

/-- Splitting `Ioc a (a + T n)` into `n` translates of `Ioc a (a + T)`. -/
lemma lintegral_Ioc_mul_eq_sum (g : ℝ → ℝ≥0∞) (hg : Measurable g) {T : ℝ} (hT : 0 < T)
    (a : ℝ) (n : ℕ) :
    ∫⁻ y in Ioc a (a + T * n), g y =
      ∫⁻ y in Ioc a (a + T), ∑ k ∈ Finset.range n, g (y + T * k) := by
  have hm : ∀ k : ℕ, Measurable fun y => g (y + T * k) := fun k => hg.comp (measurable_add_const _)
  rw [lintegral_finset_sum _ (fun k _ => hm k)]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ← ih]
    have hsplit : Ioc a (a + T * (n + 1 : ℕ)) = Ioc a (a + T * n) ∪ Ioc (a + T * n) (a + T * (n + 1 : ℕ)) := by
      refine (Ioc_union_Ioc_eq_Ioc ?_ ?_).symm
      · have : (0:ℝ) ≤ n := Nat.cast_nonneg n
        nlinarith
      · push_cast; nlinarith
    rw [hsplit, lintegral_union measurableSet_Ioc (Ioc_disjoint_Ioc_of_le le_rfl)]
    congr 1
    have hmp : MeasurePreserving (fun y : ℝ => y + T * n) volume volume :=
      measurePreserving_add_right volume (T * n)
    rw [← hmp.setLIntegral_comp_preimage measurableSet_Ioc hg]
    congr 2
    ext y
    simp only [mem_preimage, mem_Ioc]
    push_cast
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- Integrals of a `T`-periodic function over any period interval agree. -/
lemma lintegral_Ioc_periodic (g : ℝ → ℝ≥0∞) {T : ℝ} (hT : 0 < T)
    (hper : ∀ y, g (y + T) = g y) (a b : ℝ) :
    ∫⁻ y in Ioc a (a + T), g y = ∫⁻ y in Ioc b (b + T), g y := by
  have hper' : ∀ (m : ℤ) (y : ℝ), g (y + m * T) = g y := by
    intro m y
    have hP : Function.Periodic g T := hper
    simpa [zsmul_eq_mul] using hP.zsmul m y
  refine (isAddFundamentalDomain_Ioc hT a).setLIntegral_eq (isAddFundamentalDomain_Ioc hT b) g ?_
  rintro ⟨_, m, rfl⟩ y
  simp only [AddSubgroup.vadd_def, vadd_eq_add]
  rw [add_comm, zsmul_eq_mul]
  exact hper' m y

lemma exp_mul_I_eq_exp_mul_I_iff (a b : ℝ) :
    exp (a * I) = exp (b * I) ↔ ∃ m : ℤ, a = b + 2 * Real.pi * m := by
  rw [Complex.exp_eq_exp_iff_exists_int]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have := congrArg Complex.im hm
    simpa [mul_comm, mul_left_comm, mul_assoc] using this
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    rw [hm]; push_cast; ring

lemma eq_of_exp_eq_window {a b c : ℝ} (ha : c ≤ a ∧ a < c + 2 * Real.pi)
    (hb : c ≤ b ∧ b < c + 2 * Real.pi) (h : exp (a * I) = exp (b * I)) : a = b := by
  obtain ⟨m, hm⟩ := (exp_mul_I_eq_exp_mul_I_iff a b).1 h
  have hpi := Real.pi_pos
  have h1 : (m:ℝ) < 1 := by
    by_contra h'; push_neg at h'; nlinarith
  have h2 : (-1:ℝ) < m := by
    by_contra h'; push_neg at h'; nlinarith
  have : m = 0 := by
    have h1' : m < 1 := by exact_mod_cast h1
    have h2' : -1 < m := by exact_mod_cast h2
    omega
  subst this; simpa using hm

/-- The circle fibre of `B` over `e^{iy}` is `{e^{iψ(y + 2πk)} : 0 ≤ k < n}`, where `ψ` is the
inverse of the lift. -/
lemma circFibreSum_eq_sum {B : ℂ → ℂ} {φ : ℝ → ℝ} {n : ℕ} (hφ : StrictMono φ)
    (hsurj : Function.Surjective φ) (hper : ∀ t, φ (t + 2 * Real.pi) = φ t + 2 * Real.pi * n)
    (hlift : ∀ t : ℝ, B (exp (t * I)) = exp (φ t * I)) (F : ℂ → ℝ≥0∞) (y : ℝ) :
    circFibreSum B F (exp (y * I)) =
      ∑ k ∈ Finset.range n,
        F (exp (((hφ.orderIsoOfSurjective φ hsurj).symm (y + 2 * Real.pi * k) : ℝ) * I)) := by
  classical
  set e := hφ.orderIsoOfSurjective φ hsurj with he
  have hφψ : ∀ s, φ (e.symm s) = s := fun s => e.apply_symm_apply s
  have hψφ : ∀ t, e.symm (φ t) = t := fun t => by
    apply hφ.injective; rw [hφψ]
  have hψmono : StrictMono e.symm := e.symm.strictMono
  have hpi := Real.pi_pos
  set t0 := e.symm y with ht0
  have hψper : e.symm (y + 2 * Real.pi * n) = t0 + 2 * Real.pi := by
    apply hφ.injective
    rw [hφψ, hper, hφψ]
  set f : ℕ → ℂ := fun k => exp ((e.symm (y + 2 * Real.pi * k) : ℝ) * I) with hf
  have hwin : ∀ k < n, t0 ≤ e.symm (y + 2 * Real.pi * k) ∧
      e.symm (y + 2 * Real.pi * k) < t0 + 2 * Real.pi := by
    intro k hk
    have hk' : (k:ℝ) < n := by exact_mod_cast hk
    refine ⟨hψmono.monotone ?_, ?_⟩
    · have : (0:ℝ) ≤ k := Nat.cast_nonneg k
      nlinarith
    · rw [← hψper]; apply hψmono; nlinarith
  have hinj : Set.InjOn f (Finset.range n) := by
    intro j hj k hk hjk
    have hj' := Finset.mem_range.1 hj
    have hk' := Finset.mem_range.1 hk
    have := eq_of_exp_eq_window (hwin j hj') (hwin k hk') hjk
    have := congrArg φ this
    rw [hφψ, hφψ] at this
    have : (j:ℝ) = k := by nlinarith
    exact_mod_cast this
  have hset : {z : ℂ | ‖z‖ = 1 ∧ B z = exp (y * I)} = ↑((Finset.range n).image f) := by
    ext z
    simp only [mem_setOf_eq, Finset.coe_image, Finset.coe_range, mem_image, mem_Iio]
    constructor
    · rintro ⟨hz, hBz⟩
      obtain ⟨t, rfl⟩ := circle_surj hz
      set t' := toIcoMod Real.two_pi_pos t0 t with ht'
      have ht'mem := toIcoMod_mem_Ico Real.two_pi_pos t0 t
      have hexp : exp (t' * I) = exp (t * I) := by
        rw [exp_mul_I_eq_exp_mul_I_iff]
        refine ⟨-toIcoDiv Real.two_pi_pos t0 t, ?_⟩
        rw [ht', toIcoMod]
        push_cast
        rw [zsmul_eq_mul]
        ring
      rw [← hexp, hlift] at hBz
      obtain ⟨m, hm⟩ := (exp_mul_I_eq_exp_mul_I_iff _ _).1 hBz
      have hlo : y ≤ φ t' := by rw [← hφψ y]; exact hφ.monotone ht'mem.1
      have hhi : φ t' < y + 2 * Real.pi * n := by
        rw [← hφψ (y + 2 * Real.pi * n), hψper]; exact hφ ht'mem.2
      have hm0 : (0:ℝ) ≤ m := by nlinarith
      have hmn : (m:ℝ) < n := by nlinarith
      have hm0' : 0 ≤ m := by exact_mod_cast hm0
      refine ⟨m.toNat, ?_, ?_⟩
      · have : m < n := by exact_mod_cast hmn
        omega
      · rw [hf, ← hexp]
        simp only
        have : ((m.toNat : ℕ) : ℝ) = m := by
          have := Int.toNat_of_nonneg hm0'
          exact_mod_cast this
        rw [this, ← hm, hψφ]
    · rintro ⟨k, hk, rfl⟩
      refine ⟨norm_exp_ofReal_mul_I _, ?_⟩
      rw [hf]; simp only
      rw [hlift, hφψ, exp_mul_I_eq_exp_mul_I_iff]
      exact ⟨k, by push_cast; ring⟩
  unfold circFibreSum
  change ∑' z : ({z : ℂ | ‖z‖ = 1 ∧ B z = exp (y * I)} : Set ℂ), F z = _
  rw [hset, Finset.tsum_subtype' ((Finset.range n).image f) F, Finset.sum_image hinj]

/-- **Abstract circle fibre formula.** -/
theorem lintegral_circle_eq_circFibreSum_of_lift {B : ℂ → ℂ} {q : ℝ → ℝ} {n : ℕ} (hn : 0 < n)
    (hq : Continuous q) (hpos : ∀ t, 0 < q t) (hper : ∀ t, q (t + 2 * Real.pi) = q t)
    (hint : ∫ t in (0:ℝ)..(2 * Real.pi), q t = 2 * Real.pi * n)
    (hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => B (exp (s * I))) (I * B (exp (t * I)) * q t) t)
    (hnorm : ∀ t : ℝ, ‖B (exp (t * I))‖ = 1) (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ t in Ioc 0 (2 * Real.pi), F (exp (t * I)) * ENNReal.ofReal (q t) =
      ∫⁻ s in Ioc 0 (2 * Real.pi), circFibreSum B F (exp (s * I)) := by
  obtain ⟨c, hlift⟩ := exists_lift hq hderiv hnorm
  set φ := liftFun c q with hφdef
  have hmono : StrictMono φ := liftFun_strictMono c hq hpos
  have hsurj : Function.Surjective φ := liftFun_surjective c hq hpos hper hint hn
  have hperφ : ∀ t, φ (t + 2 * Real.pi) = φ t + 2 * Real.pi * n :=
    liftFun_add_period c hq hper hint
  set e := hmono.orderIsoOfSurjective φ hsurj with he
  have hψφ : ∀ t, e.symm (φ t) = t := fun t => e.symm_apply_apply t
  set g : ℝ → ℝ≥0∞ := fun s => F (exp ((e.symm s : ℝ) * I)) with hg
  have hgm : Measurable g :=
    hF.comp (by have := e.symm.continuous; fun_prop : Continuous fun s => exp ((e.symm s : ℝ) * I)).measurable
  have hpi := Real.pi_pos
  -- change of variables
  have h1 : ∫⁻ t in Ioc 0 (2 * Real.pi), F (exp (t * I)) * ENNReal.ofReal (q t) =
      ∫⁻ x in φ '' Ioc 0 (2 * Real.pi), g x := by
    rw [lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioc
      (fun x _ => (hasDerivAt_liftFun c hq x).hasDerivWithinAt) hmono.injective.injOn g]
    refine setLIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    have := hψφ t
    rw [hφdef] at this
    simp only [hg, abs_of_pos (hpos t), this, mul_comm]
  have h2 : φ '' Ioc 0 (2 * Real.pi) = Ioc (φ 0) (φ 0 + 2 * Real.pi * n) := by
    have := e.image_Ioc 0 (2 * Real.pi)
    have h2π : φ (2 * Real.pi) = φ 0 + 2 * Real.pi * n := by
      simpa using hperφ 0
    simpa [he, h2π] using this
  have hfib : ∀ y, ∑ k ∈ Finset.range n, g (y + 2 * Real.pi * k) =
      circFibreSum B F (exp (y * I)) := fun y =>
    (circFibreSum_eq_sum hmono hsurj hperφ hlift F y).symm
  rw [h1, h2, lintegral_Ioc_mul_eq_sum g hgm (by positivity) (φ 0) n]
  simp_rw [hfib]
  have hperfib : ∀ y : ℝ, circFibreSum B F (exp (((y + 2 * Real.pi : ℝ) : ℂ) * I)) =
      circFibreSum B F (exp ((y : ℂ) * I)) := by
    intro y
    congr 1
    rw [exp_mul_I_eq_exp_mul_I_iff]
    exact ⟨1, by push_cast; ring⟩
  have := lintegral_Ioc_periodic (fun y : ℝ => circFibreSum B F (exp (y * I)))
    (by positivity) hperfib (φ 0) 0
  simpa using this

/-- Boundary data of a finite Blaschke product of positive degree: the density
`q(t) = |B'(e^{it})| > 0` is continuous, `2π`-periodic, has integral `2πn`, and
`d/dt B(e^{it}) = i B(e^{it}) q(t)` with `|B(e^{it})| = 1`. -/
lemma blaschke_circle_data {B : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n) (hn : 0 < n) :
    ∃ q : ℝ → ℝ, Continuous q ∧ (∀ t, 0 < q t) ∧ (∀ t, q (t + 2 * Real.pi) = q t) ∧
      (∫ t in (0:ℝ)..(2 * Real.pi), q t = 2 * Real.pi * n) ∧
      (∀ t : ℝ, HasDerivAt (fun s : ℝ => B (exp (s * I))) (I * B (exp (t * I)) * q t) t) ∧
      (∀ t : ℝ, ‖B (exp (t * I))‖ = 1) ∧ (∀ t : ℝ, ‖deriv B (exp (t * I))‖ = q t) := by
  obtain ⟨η, a, hη, ha, rfl⟩ := hB
  set Q : ℂ → ℝ := fun z => ∑ l, bdens (a l) z with hQ
  have hBA : BdryArg (fun z => η * ∏ l, bfac (a l) z) Q := by
    intro z hz
    obtain ⟨h1, h2, h3⟩ := bdryArg_prod Finset.univ a ha z hz
    refine ⟨by simp only at h1 ⊢; rw [norm_mul, hη, one_mul]; exact h1, h2, ?_⟩
    have := h3.const_mul η
    convert this using 1
    simp only
    ring
  have hq : Continuous fun t : ℝ => Q (exp (t * I)) :=
    continuous_finset_sum _ fun l _ => continuous_bdens_circle (ha l)
  have hpos : ∀ t : ℝ, 0 < Q (exp (t * I)) := by
    intro t
    haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    refine Finset.sum_pos (fun l _ => ?_) Finset.univ_nonempty
    have hal : normSq (a l) < 1 := by
      rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg (a l), ha l]
    have hza : exp (t * I) - a l ≠ 0 := by
      intro h; rw [sub_eq_zero] at h
      have := norm_exp_ofReal_mul_I t; rw [h] at this; have := ha l; linarith
    exact div_pos (by linarith) (normSq_pos.2 hza)
  have hper : ∀ t : ℝ, Q (exp (((t + 2 * Real.pi : ℝ) : ℂ) * I)) = Q (exp (t * I)) := by
    intro t
    congr 1
    rw [exp_mul_I_eq_exp_mul_I_iff]
    exact ⟨1, by push_cast; ring⟩
  have hint : ∫ t in (0:ℝ)..(2 * Real.pi), Q (exp (t * I)) = 2 * Real.pi * n := by
    simp only [hQ]
    rw [intervalIntegral.integral_finset_sum (fun l _ =>
      (continuous_bdens_circle (ha l)).intervalIntegrable _ _)]
    simp_rw [integral_bdens (ha _)]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hnormd : ∀ t : ℝ, ‖deriv (fun z => η * ∏ l, bfac (a l) z) (exp (t * I))‖ =
      Q (exp (t * I)) := by
    intro t
    have hz : ‖exp (t * I)‖ = 1 := norm_exp_ofReal_mul_I t
    obtain ⟨h1, h2, h3⟩ := hBA _ hz
    rw [h3.deriv, norm_div, norm_mul, h1, hz, norm_real, Real.norm_eq_abs, abs_of_nonneg h2]
    ring
  exact ⟨fun t => Q (exp (t * I)), hq, hpos, hper, hint, fun t => hasDerivAt_circle hBA t,
    fun t => (hBA _ (norm_exp_ofReal_mul_I t)).1, hnormd⟩

/-- The circle fibres of a finite Blaschke product of positive degree are finite. -/
lemma circFibre_finite {B : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n) (hn : 0 < n) (w : ℂ) :
    {z : ℂ | ‖z‖ = 1 ∧ B z = w}.Finite := by
  obtain ⟨q, hq, hpos, hper, hint, hderiv, hnorm, -⟩ := blaschke_circle_data hB hn
  by_cases hw : ‖w‖ = 1
  · obtain ⟨y, rfl⟩ := circle_surj hw
    obtain ⟨c, hlift⟩ := exists_lift hq hderiv hnorm
    have hsum := circFibreSum_eq_sum (liftFun_strictMono c hq hpos)
      (liftFun_surjective c hq hpos hper hint hn) (liftFun_add_period c hq hper hint) hlift
      (fun _ => 1) y
    unfold circFibreSum at hsum
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
    by_contra hinf
    have : Infinite {z : ℂ // ‖z‖ = 1 ∧ B z = exp (y * I)} := Set.infinite_coe_iff.2 hinf
    rw [ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero] at hsum
    exact ENNReal.natCast_ne_top n hsum.symm
  · refine Set.Finite.subset (Set.finite_empty) fun z ⟨hz, hBz⟩ => ?_
    obtain ⟨t, rfl⟩ := circle_surj hz
    exact hw (hBz ▸ hnorm t)

/-- **Circle fibre formula for finite Blaschke products.**  For a finite Blaschke product `B`
of degree `n ≥ 1` and measurable `F ≥ 0`,
`∫₀^{2π} F(e^{it}) |B'(e^{it})| dt = ∫₀^{2π} ∑_{z ∈ 𝕋, B z = e^{is}} F(z) ds`. -/
theorem lintegral_circle_norm_deriv_eq_circFibreSum {B : ℂ → ℂ} {n : ℕ}
    (hB : IsFiniteBlaschke B n) (hn : 0 < n) (F : ℂ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ t in Ioc 0 (2 * Real.pi), F (exp (t * I)) * ENNReal.ofReal ‖deriv B (exp (t * I))‖ =
      ∫⁻ s in Ioc 0 (2 * Real.pi), circFibreSum B F (exp (s * I)) := by
  obtain ⟨q, hq, hpos, hper, hint, hderiv, hnorm, hnormd⟩ := blaschke_circle_data hB hn
  simp_rw [hnormd]
  exact lintegral_circle_eq_circFibreSum_of_lift hn hq hpos hper hint hderiv hnorm F hF

end SteklovBlaschke

end
