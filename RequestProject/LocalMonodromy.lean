module

public import RequestProject.PolynomialCover

/-!
# Local monodromy of a polynomial covering around a small circle

Let `P` be a complex polynomial and `w₀ ∈ ℂ`.  We show that, near any root `a` of `P - w₀` of
multiplicity `k`, `P(z) = w₀ + h(z)^k` with `h` a local biholomorphism, `h(a) = 0`
(`exists_local_root`, `exists_local_chart`).  Consequently the lift of the small circle
`t ↦ w₀ + r e^{2π i t}` starting at the point `h⁻¹(u₀)` (`u₀^k = r`) ends at
`h⁻¹(u₀ e^{2π i / k})` (`monodromy_chart`).
-/

@[expose] public section

open Polynomial Set Filter Topology Metric Complex
open scoped Real

noncomputable section

namespace LocalMonodromy

/-- **Local normal form.** If `a` is a root of `P - w₀` of multiplicity `k`, then near `a`,
`P(z) = w₀ + h(z)^k` for some `h` holomorphic near `a` with `h(a) = 0`, `h'(a) ≠ 0`. -/
theorem exists_local_root {P : ℂ[X]} {w0 a : ℂ} (hP : P - C w0 ≠ 0)
    (hroot : (P - C w0).IsRoot a) :
    ∃ h : ℂ → ℂ, ∃ ε > 0,
      (∀ z ∈ ball a ε, P.eval z = w0 + h z ^ ((P - C w0).rootMultiplicity a)) ∧
      h a = 0 ∧ DifferentiableOn ℂ h (ball a ε) ∧ deriv h a ≠ 0 := by
  set k := (P - C w0).rootMultiplicity a with hk
  have hk0 : 0 < k := (rootMultiplicity_pos hP).2 hroot
  set g := (P - C w0) /ₘ (X - C a) ^ k
  have hga : g.eval a ≠ 0 := eval_divByMonic_pow_rootMultiplicity_ne_zero a hP
  have hfac : ∀ z, P.eval z = w0 + (z - a) ^ k * g.eval z := by
    intro z
    have := congrArg (eval z) (pow_mul_divByMonic_rootMultiplicity_eq (P - C w0) a)
    simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C] at this
    rw [← hk] at this
    linear_combination -this
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (g.eval a) hk0
  have hc0 : c ≠ 0 := by rintro rfl; rw [zero_pow hk0.ne'] at hc; exact hga hc.symm
  set u : ℂ → ℂ := fun z => g.eval z / g.eval a
  have hu_cont : ContinuousAt u a := (g.continuous.continuousAt).div_const _
  have hua : u a = 1 := div_self hga
  obtain ⟨ε, hε, hεu⟩ := Metric.continuousAt_iff.1 hu_cont 1 one_pos
  have hslit : ∀ z ∈ ball a ε, u z ∈ slitPlane := by
    intro z hz
    have := hεu (mem_ball.1 hz)
    rw [hua, dist_eq_norm] at this
    simpa using mem_slitPlane_of_norm_lt_one this
  have hu0 : ∀ z ∈ ball a ε, u z ≠ 0 := fun z hz => slitPlane_ne_zero (hslit z hz)
  set F : ℂ → ℂ := fun z => c * exp (log (u z) / k)
  refine ⟨fun z => (z - a) * F z, ε, hε, fun z hz => ?_, by simp, ?_, ?_⟩
  · rw [hfac z, mul_pow]
    congr 1
    have : F z ^ k = g.eval z := by
      simp only [F, mul_pow, ← Complex.exp_nat_mul, hc]
      rw [mul_div_cancel₀ _ (by exact_mod_cast hk0.ne'), exp_log (hu0 z hz)]
      simp only [u]; field_simp
    rw [this]
  · have hFd : ∀ z ∈ ball a ε, DifferentiableAt ℂ F z := by
      intro z hz
      have h1 : DifferentiableAt ℂ u z := (g.differentiable z).div_const _
      exact (((differentiableAt_log (hslit z hz)).comp z h1).div_const _).cexp.const_mul c
    intro z hz
    exact ((differentiableAt_id.sub_const a).mul (hFd z hz)).differentiableWithinAt
  · have hFd : DifferentiableAt ℂ F a := by
      have h1 : DifferentiableAt ℂ u a := (g.differentiable a).div_const _
      exact (((differentiableAt_log (hslit a (mem_ball_self hε))).comp a h1).div_const _).cexp.const_mul c
    have hd : HasDerivAt (fun z => (z - a) * F z) (1 * F a + (a - a) * deriv F a) a :=
      ((hasDerivAt_id a).sub_const a).mul hFd.hasDerivAt
    rw [hd.deriv, sub_self, zero_mul, add_zero, one_mul]
    simp [F, hua, hc0]

/-- A local chart at a root `a` of `P - w₀` of multiplicity `k`: on the open set `V ∋ a`,
`P = w₀ + h^k` and `h : V → B(0,δ)` is a homeomorphism with inverse `g`. -/
structure Chart (P : ℂ[X]) (w0 a : ℂ) (k : ℕ) where
  h : ℂ → ℂ
  g : ℂ → ℂ
  δ : ℝ
  V : Set ℂ
  δ_pos : 0 < δ
  V_open : IsOpen V
  a_mem : a ∈ V
  h_maps : ∀ z ∈ V, h z ∈ ball (0 : ℂ) δ
  g_maps : ∀ u ∈ ball (0 : ℂ) δ, g u ∈ V
  g_h : ∀ z ∈ V, g (h z) = z
  h_g : ∀ u ∈ ball (0 : ℂ) δ, h (g u) = u
  g_cont : ContinuousOn g (ball 0 δ)
  normal : ∀ z ∈ V, P.eval z = w0 + h z ^ k

/-- **Existence of local charts**, inside any prescribed ball around the root. -/
theorem exists_chart {P : ℂ[X]} {w0 a : ℂ} (hP : P - C w0 ≠ 0) (hroot : (P - C w0).IsRoot a)
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Ch : Chart P w0 a ((P - C w0).rootMultiplicity a), Ch.V ⊆ ball a ρ := by
  obtain ⟨h, ε, hε, hnorm, ha, hdiff, hder⟩ := exists_local_root hP hroot
  have han : AnalyticAt ℂ h a := hdiff.analyticAt (ball_mem_nhds a hε)
  have hs := han.hasStrictDerivAt
  let φ := (hs.hasStrictFDerivAt_equiv hder).toOpenPartialHomeomorph h
  have hφ : (φ : ℂ → ℂ) = h := HasStrictFDerivAt.toOpenPartialHomeomorph_coe _
  have haφ : a ∈ φ.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  set S := φ.source ∩ ball a (min ε ρ)
  have hSo : IsOpen S := φ.open_source.inter isOpen_ball
  have hSs : S ⊆ φ.source := inter_subset_left
  have himo : IsOpen (φ '' S) := φ.isOpen_image_of_subset_source hSo hSs
  have h0 : (0 : ℂ) ∈ φ '' S :=
    ⟨a, ⟨haφ, mem_ball_self (lt_min hε hρ)⟩, by rw [hφ, ha]⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 himo 0 h0
  have hbt : ball (0 : ℂ) δ ⊆ φ.target := fun u hu => by
    obtain ⟨z, hz, rfl⟩ := hball hu
    exact φ.map_source (hSs hz)
  refine ⟨⟨h, φ.symm, δ, S ∩ h ⁻¹' ball 0 δ, hδ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show IsOpen (S ∩ h ⁻¹' ball 0 δ)
    rw [← hφ]; exact (φ.continuousOn.mono hSs).isOpen_inter_preimage hSo isOpen_ball
  · exact ⟨⟨haφ, mem_ball_self (lt_min hε hρ)⟩, by simp [ha, hδ]⟩
  · intro z hz; exact hz.2
  · intro u hu
    obtain ⟨z, hz, rfl⟩ := hball hu
    have : φ.symm (φ z) = z := φ.left_inv (hSs hz)
    refine ⟨by rw [this]; exact hz, ?_⟩
    rw [mem_preimage, this, ← hφ]; exact hu
  · intro z hz
    rw [← hφ]; exact φ.left_inv (hSs hz.1)
  · intro u hu
    rw [← hφ]; exact φ.right_inv (hbt hu)
  · exact φ.continuousOn_symm.mono hbt
  · intro z hz
    exact hnorm z (ball_subset_ball (min_le_left _ _) hz.1.2)
  · intro z hz
    exact ball_subset_ball (min_le_right _ _) hz.1.2

/-- The circle `t ↦ w₀ + r e^{2π i t}`. -/
def circ (w0 : ℂ) (r : ℝ) (t : ℝ) : ℂ := w0 + r * exp (2 * π * I * t)

theorem circ_zero (w0 : ℂ) (r : ℝ) : circ w0 r 0 = w0 + r := by simp [circ]

theorem circ_one (w0 : ℂ) (r : ℝ) : circ w0 r 1 = circ w0 r 0 := by
  simp [circ]

theorem continuous_circ (w0 : ℂ) (r : ℝ) : Continuous (circ w0 r) := by
  unfold circ; fun_prop

open PolyCover

variable {P : ℂ[X]}

/-- The base point `w₀ + r` of the covering, assuming the circle avoids the critical values. -/
def basePt (w0 : ℂ) (r : ℝ) (hcirc : ∀ t, circ w0 r t ∉ critVals P) : Base P :=
  ⟨circ w0 r 0, hcirc 0⟩

/-- The loop `t ↦ w₀ + r e^{2π i t}` in `ℂ \ critVals P`, based at `w₀ + r`. -/
def circleLoop (w0 : ℂ) (r : ℝ) (hcirc : ∀ t, circ w0 r t ∉ critVals P) :
    Path (basePt w0 r hcirc) (basePt w0 r hcirc) where
  toFun t := ⟨circ w0 r t, hcirc t⟩
  continuous_toFun := ((continuous_circ w0 r).comp continuous_subtype_val).subtype_mk _
  source' := rfl
  target' := Subtype.ext (circ_one w0 r)

theorem Chart.eval_g {w0 a : ℂ} {k : ℕ} (Ch : Chart P w0 a k) {v : ℂ} (hv : v ∈ ball (0 : ℂ) Ch.δ) :
    P.eval (Ch.g v) = w0 + v ^ k := by
  rw [Ch.normal _ (Ch.g_maps v hv), Ch.h_g v hv]

theorem norm_lt_of_pow_eq {k : ℕ} {δ r : ℝ} (hδ : 0 < δ) (hr : 0 ≤ r) (hrδ : r < δ ^ k)
    {u : ℂ} (hu : u ^ k = r) : ‖u‖ < δ := by
  have h : ‖u‖ ^ k = r := by
    rw [← norm_pow, hu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
  exact lt_of_pow_lt_pow_left₀ k hδ.le (h ▸ hrδ)

/-- **Monodromy along a small circle, inside a chart.**  If `e = g(u₀)` with `u₀^k = r`, then the
monodromy of the circle `t ↦ w₀ + r e^{2π i t}` sends `e` to `g(u₀ e^{2π i/k})`. -/
theorem monodromy_chart {w0 a : ℂ} {k : ℕ} (Ch : Chart P w0 a k) (hk : 0 < k) {r : ℝ}
    (hr : 0 < r) (hrδ : r < Ch.δ ^ k) (hcirc : ∀ t, circ w0 r t ∉ critVals P) {u0 : ℂ} (hu0 : u0 ^ k = r)
    (e : proj P ⁻¹' {basePt w0 r hcirc}) (he : e.1.1 = Ch.g u0) :
    (monodromyPerm P (Path.Homotopic.Quotient.mk (circleLoop w0 r hcirc)) e).1.1 =
      Ch.g (u0 * exp (2 * π * I / k)) := by
  have hu0n : ‖u0‖ < Ch.δ := norm_lt_of_pow_eq Ch.δ_pos hr.le hrδ hu0
  let v : ℝ → ℂ := fun t => u0 * exp (2 * π * I * t / k)
  have hvn : ∀ t, v t ∈ ball (0 : ℂ) Ch.δ := fun t => by
    rw [mem_ball_zero_iff]
    simp only [v, norm_mul]
    rw [show 2 * π * I * t / k = ((2 * π * t / k : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, mul_one]
    exact hu0n
  have hvk : ∀ t, v t ^ k = r * exp (2 * π * I * t) := fun t => by
    have hkc : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [v, mul_pow, ← Complex.exp_nat_mul, hu0]
    congr 2
    field_simp
  have hev : ∀ t, P.eval (Ch.g (v t)) = circ w0 r t := fun t => by
    rw [Ch.eval_g (hvn t), hvk, circ]
  have hvc : Continuous v := by unfold v; fun_prop
  have hc : Continuous (fun t : unitInterval => Ch.g (v t)) :=
    Ch.g_cont.comp_continuous (hvc.comp continuous_subtype_val) (fun t => hvn t)
  have hmem : ∀ t : unitInterval, Ch.g (v t) ∈ P.eval ⁻¹' (critVals P)ᶜ := fun t => by
    simp only [mem_preimage, hev]; exact hcirc t
  let Γ : C(unitInterval, Total P) := ⟨fun t => ⟨Ch.g (v t), hmem t⟩, hc.subtype_mk hmem⟩
  have hl : (isCoveringMap P).liftPath ((circleLoop w0 r hcirc : Path _ _) : C(unitInterval, Base P))
      e.1 ((circleLoop w0 r hcirc).source.trans e.2.symm) = Γ := by
    refine (((isCoveringMap P).eq_liftPath_iff' _).2 ⟨?_, ?_⟩).symm
    · funext t
      exact Subtype.ext (hev t)
    · apply Subtype.ext
      show Ch.g (v 0) = e.1.1
      rw [he]; simp [v]
  show ((isCoveringMap P).liftPath _ e.1 _ 1).1 = _
  rw [hl]
  show Ch.g (v 1) = _
  simp [v]

theorem exists_pos_le_finset {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 < f i) :
    ∃ m > 0, ∀ i ∈ s, m ≤ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert a s ha ih =>
    obtain ⟨m, hm, hms⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    refine ⟨min m (f a), lt_min hm (hf a (Finset.mem_insert_self a s)), fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hms i hi)

theorem finRotate_val {n : ℕ} (hn : 0 < n) (j : Fin n) : (finRotate n j : ℕ) = (j + 1) % n := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  simp only [zero_add] at *
  rw [coe_finRotate]
  split_ifs with h
  · subst h; simp
  · have : (j : ℕ) < m := by
      have := j.2
      have h' : (j : ℕ) ≠ m := fun h2 => h (Fin.ext (by simpa using h2))
      omega
    rw [Nat.mod_eq_of_lt (by omega)]

theorem pow_mod_eq {ζ : ℂ} {k : ℕ} (hζ : ζ ^ k = 1) (n : ℕ) : ζ ^ (n % k) = ζ ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n k, pow_add, pow_mul, hζ, one_pow, mul_one]

/-- The standard model of a permutation with prescribed cycle lengths: on `Σ i, Fin (k i)`,
rotate each block `Fin (k i)` cyclically. -/
def blockRotation {ι : Type*} (k : ι → ℕ) : Equiv.Perm (Σ i, Fin (k i)) :=
  Equiv.sigmaCongrRight fun i => finRotate (k i)

/-- **Local monodromy theorem.**  Let `P` be a nonconstant polynomial and `w₀ ∈ ℂ`.  For all
sufficiently small `r > 0`, the circle `t ↦ w₀ + r e^{2π i t}` avoids the critical values of `P`,
and there is a bijection between the fibre of `P` over `w₀ + r` and `Σ a, Fin (k_a)` (`a` ranging
over the distinct roots of `P - w₀`, `k_a` = multiplicity) which conjugates the monodromy of this
circle to the standard block rotation.  In particular the monodromy permutation has exactly one
cycle of length `k_a` for each root `a` of `P - w₀`. -/
theorem local_monodromy {P : ℂ[X]} (hP : 0 < P.degree) (w0 : ℂ) :
    ∃ r0 > 0, ∀ r : ℝ, 0 < r → r < r0 → ∃ hcirc : ∀ t, circ w0 r t ∉ critVals P,
      ∃ E : (Σ a : (P - C w0).roots.toFinset, Fin ((P - C w0).rootMultiplicity (a : ℂ))) ≃
          proj P ⁻¹' {basePt w0 r hcirc},
        ∀ x, monodromyPerm P (Path.Homotopic.Quotient.mk (circleLoop w0 r hcirc)) (E x) =
          E (blockRotation _ x) := by
  classical
  set Q := P - C w0 with hQdef
  have hQ : Q ≠ 0 := by
    intro h
    have : P = C w0 := sub_eq_zero.1 h
    rw [this] at hP; exact absurd hP (not_lt.2 degree_C_le)
  set R := Q.roots.toFinset
  set k : R → ℕ := fun a => Q.rootMultiplicity (a : ℂ)
  have hroot : ∀ a : R, Q.IsRoot a := fun a => by
    have := a.2; rw [Multiset.mem_toFinset, mem_roots hQ] at this; exact this
  have hk : ∀ a : R, 0 < k a := fun a => (rootMultiplicity_pos hQ).2 (hroot a)
  -- separation radius
  obtain ⟨ρ, hρ, hsep⟩ := exists_pos_le_finset ((R ×ˢ R).filter fun p => p.1 ≠ p.2)
    (fun p => dist p.1 p.2 / 2) (fun p hp => by
      simp only [Finset.mem_filter] at hp; exact half_pos (dist_pos.2 hp.2))
  choose Ch hChV using fun a : R => exists_chart hQ (hroot a) hρ
  obtain ⟨m1, hm1, hm1le⟩ := exists_pos_le_finset (Finset.univ : Finset R)
    (fun a => (Ch a).δ ^ k a) (fun a _ => pow_pos (Ch a).δ_pos _)
  obtain ⟨m2, hm2, hm2le⟩ := exists_pos_le_finset
    ((critVals_finite hP).toFinset.filter (· ≠ w0)) (fun c => dist w0 c)
    (fun c hc => by simp only [Finset.mem_filter] at hc; exact dist_pos.2 (Ne.symm hc.2))
  refine ⟨min m1 m2, lt_min hm1 hm2, fun r hr hr0 => ?_⟩
  have hdist : ∀ t, dist w0 (circ w0 r t) = r := fun t => by
    rw [dist_comm, dist_eq_norm, circ, add_sub_cancel_left, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr,
      show 2 * π * I * t = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, mul_one]
  have hcirc : ∀ t, circ w0 r t ∉ critVals P := by
    intro t hc
    by_cases h : circ w0 r t = w0
    · have := hdist t; rw [h, dist_self] at this; linarith
    · have := hm2le (circ w0 r t) (by
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset]; exact ⟨hc, h⟩)
      have := hdist t
      linarith [min_le_right m1 m2]
  refine ⟨hcirc, ?_⟩
  have hu : ∀ a : R, ∃ u : ℂ, u ^ k a = r := fun a => IsAlgClosed.exists_pow_nat_eq _ (hk a)
  choose u hu using hu
  set ζ : R → ℂ := fun a => exp (2 * π * I / k a)
  have hζ : ∀ a, IsPrimitiveRoot (ζ a) (k a) := fun a => isPrimitiveRoot_exp _ (hk a).ne'
  have hrδ : ∀ a, r < (Ch a).δ ^ k a := fun a =>
    lt_of_lt_of_le hr0 ((min_le_left _ _).trans (hm1le a (Finset.mem_univ a)))
  have hpow : ∀ a (j : ℕ), (u a * ζ a ^ j) ^ k a = r := fun a j => by
    rw [mul_pow, ← pow_mul, mul_comm j, pow_mul, (hζ a).pow_eq_one, one_pow, mul_one, hu]
  have hball : ∀ a (j : ℕ), u a * ζ a ^ j ∈ ball (0 : ℂ) (Ch a).δ := fun a j => by
    rw [mem_ball_zero_iff]
    exact norm_lt_of_pow_eq (Ch a).δ_pos hr.le (hrδ a) (hpow a j)
  have hval : ∀ a (j : ℕ), P.eval ((Ch a).g (u a * ζ a ^ j)) = circ w0 r 0 := fun a j => by
    rw [(Ch a).eval_g (hball a j), hpow, circ_zero]
  have hmem : ∀ a (j : ℕ), (Ch a).g (u a * ζ a ^ j) ∈ P.eval ⁻¹' (critVals P)ᶜ := fun a j => by
    simp only [mem_preimage, hval]; exact hcirc 0
  let F : (Σ a : R, Fin (k a)) → proj P ⁻¹' {basePt w0 r hcirc} := fun x =>
    ⟨⟨(Ch x.1).g (u x.1 * ζ x.1 ^ (x.2 : ℕ)), hmem _ _⟩, Subtype.ext (hval _ _)⟩
  have hFv : ∀ x, (F x).1.1 = (Ch x.1).g (u x.1 * ζ x.1 ^ (x.2 : ℕ)) := fun x => rfl
  have hu0 : ∀ a, u a ≠ 0 := fun a h => by
    have := hu a; rw [h, zero_pow (hk a).ne'] at this; exact hr.ne' (by exact_mod_cast this.symm)
  have hinj : Function.Injective F := by
    rintro ⟨a, i⟩ ⟨b, j⟩ h
    have h' := congrArg (fun e => e.1.1) h
    simp only [hFv] at h'
    by_cases hab : a = b
    · subst hab
      have := congrArg (Ch a).h h'
      rw [(Ch a).h_g _ (hball a i), (Ch a).h_g _ (hball a j)] at this
      have hij := (hζ a).pow_inj i.2 j.2 (mul_left_cancel₀ (hu0 a) this)
      rw [Fin.val_inj] at hij
      subst hij; rfl
    · exfalso
      have h1 := hChV a ((Ch a).g_maps _ (hball a i))
      have h2 := hChV b ((Ch b).g_maps _ (hball b j))
      rw [h'] at h1
      have hne : (a : ℂ) ≠ b := fun h => hab (Subtype.ext h)
      have := hsep (a, b) (by simp [hne, a.2, b.2])
      have := dist_triangle_right (a : ℂ) b ((Ch b).g (u b * ζ b ^ (j : ℕ)))
      rw [mem_ball, dist_comm] at h1 h2
      simp only at *
      linarith
  have hcardE : Nat.card (Σ a : R, Fin (k a)) = P.natDegree := by
    rw [Nat.card_sigma]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    rw [Finset.sum_coe_sort R (fun a : ℂ => Q.rootMultiplicity a)]
    have := Multiset.toFinset_sum_count_eq Q.roots
    simp only [count_roots] at this
    rw [this, IsAlgClosed.card_roots_eq_natDegree, hQdef, natDegree_sub_C]
  have hcardF := card_fibre hP (basePt w0 r hcirc)
  haveI : Finite (proj P ⁻¹' {basePt w0 r hcirc}) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcardF]
    exact (natDegree_pos_iff_degree_pos.2 hP).ne'
  have hbij : Function.Bijective F :=
    hinj.bijective_of_nat_card_le (by rw [hcardF, hcardE])
  refine ⟨Equiv.ofBijective F hbij, ?_⟩
  rintro ⟨a, j⟩
  apply Subtype.ext; apply Subtype.ext
  change (monodromyPerm P _ (F ⟨a, j⟩)).1.1 = (F (blockRotation k ⟨a, j⟩)).1.1
  rw [monodromy_chart (Ch a) (hk a) hr (hrδ a) hcirc (hpow a j) (F ⟨a, j⟩) rfl]
  show _ = (Ch a).g (u a * ζ a ^ ((finRotate (k a) j : Fin (k a)) : ℕ))
  rw [finRotate_val (hk a), pow_mod_eq (hζ a).pow_eq_one, pow_succ, mul_assoc]

end LocalMonodromy
