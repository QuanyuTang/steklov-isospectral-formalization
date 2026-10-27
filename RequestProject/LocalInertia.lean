module

public import RequestProject.PowerCover
public import RequestProject.LocalMonodromy
public import RequestProject.RegularCover

/-!
# Local power models of a covering of a plane domain near a puncture

Let `q : Y → S` be a covering map, `S ⊆ ℂ`, and let the punctured disk
`{0 < |z - c| < ρ}` be contained in `S`.  For `y₀ ∈ Y` over `c + r'` (`0 < r' < ρ`) let
`C` be the path component of `y₀` in `q⁻¹{0 < |z - c| < ρ}`.  If the monodromy of the circle
`t ↦ c + r' e^{2π i t}` returns `y₀` to itself after exactly the multiples of `d` turns, then `C`
is homeomorphic to the punctured disk `{0 < |t| < ρ^{1/d}}` with `q = c + t^d`
(`local_power_model`).  This is the local model `t ↦ t^d` of a branched cover over the puncture
`c`, derived from the monodromy (no assumption on the local structure).
-/

@[expose] public section

open Set Topology Complex Filter LocalMonodromy

noncomputable section

namespace SteklovPunctured

variable {S : Set ℂ} {Y : Type*} [TopologicalSpace Y] {q : Y → S}

/-- The part of `S` lying over the punctured disk `{0 < |z - c| < ρ}`. -/
def nbhdSet (S : Set ℂ) (c : ℂ) (ρ : ℝ) : Set S := {z | (z : ℂ) - c ∈ pdisk ρ}

/-- Translation `z ↦ z - c` from `nbhdSet S c ρ` to the punctured disk. -/
def transFun (S : Set ℂ) (c : ℂ) (ρ : ℝ) (z : nbhdSet S c ρ) : pdisk ρ :=
  ⟨((z : S) : ℂ) - c, z.2⟩

/-- Its inverse `u ↦ u + c`. -/
def transInv {S : Set ℂ} {c : ℂ} {ρ : ℝ} (hS : ∀ u ∈ pdisk ρ, u + c ∈ S) (u : pdisk ρ) :
    nbhdSet S c ρ :=
  ⟨⟨(u : ℂ) + c, hS u u.2⟩, by
    show (u : ℂ) + c - c ∈ pdisk ρ
    rw [add_sub_cancel_right]; exact u.2⟩

/-- Translation `z ↦ z - c` from `nbhdSet S c ρ` onto the punctured disk. -/
def transHomeo {S : Set ℂ} {c : ℂ} {ρ : ℝ} (hS : ∀ u ∈ pdisk ρ, u + c ∈ S) :
    nbhdSet S c ρ ≃ₜ pdisk ρ where
  toFun := transFun S c ρ
  invFun := transInv hS
  left_inv z := Subtype.ext (Subtype.ext (by simp [transFun, transInv]))
  right_inv u := Subtype.ext (by simp [transFun, transInv])
  continuous_toFun := ((continuous_subtype_val.comp continuous_subtype_val).sub
    continuous_const).subtype_mk _
  continuous_invFun := ((continuous_subtype_val.add continuous_const).subtype_mk _).subtype_mk _

/-- The covering over the punctured disk obtained by restricting `q` and translating. -/
def locProj (q : Y → S) {c : ℂ} {ρ : ℝ} (hS : ∀ u ∈ pdisk ρ, u + c ∈ S) :
    q ⁻¹' nbhdSet S c ρ → pdisk ρ :=
  transHomeo hS ∘ (nbhdSet S c ρ).restrictPreimage q

omit [TopologicalSpace Y] in
lemma locProj_val {c : ℂ} {ρ : ℝ} (hS : ∀ u ∈ pdisk ρ, u + c ∈ S) (y : q ⁻¹' nbhdSet S c ρ) :
    (locProj q hS y : ℂ) = (q y : ℂ) - c := rfl

lemma isCoveringMap_locProj (hq : IsCoveringMap q) {c : ℂ} {ρ : ℝ}
    (hS : ∀ u ∈ pdisk ρ, u + c ∈ S) : IsCoveringMap (locProj q hS) :=
  (hq.restrictPreimage _).homeomorph_comp _

instance instLocPathPdisk (ρ : ℝ) : LocallyPathConnectedSpace (pdisk ρ) :=
  (isOpen_pdisk ρ).locPathConnectedSpace

/-- The path component of `y₀` over the punctured disk. -/
abbrev LocComp {c : ℂ} {ρ : ℝ} (q : Y → S) (y₀ : q ⁻¹' nbhdSet S c ρ) : Set (q ⁻¹' nbhdSet S c ρ) :=
  pathComponent y₀

/-- The projection of the local component to the punctured disk. -/
def compProj {c : ℂ} {ρ : ℝ} (hS : ∀ u ∈ pdisk ρ, u + c ∈ S) (y₀ : q ⁻¹' nbhdSet S c ρ) :
    LocComp q y₀ → pdisk ρ := fun y => locProj q hS y

lemma isCoveringMap_compProj (hq : IsCoveringMap q) {c : ℂ} {ρ : ℝ}
    (hS : ∀ u ∈ pdisk ρ, u + c ∈ S) (y₀ : q ⁻¹' nbhdSet S c ρ) :
    IsCoveringMap (compProj hS y₀) :=
  SteklovRegularCover.isCoveringMap_restrict_pathComponent (isCoveringMap_locProj hq hS) y₀

instance instPathConnLocComp {c : ℂ} {ρ : ℝ} (y₀ : q ⁻¹' nbhdSet S c ρ) :
    PathConnectedSpace (LocComp q y₀) :=
  isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_pathComponent)

/-- The inclusion of the local component into `Y`. -/
def incl {c : ℂ} {ρ : ℝ} (y₀ : q ⁻¹' nbhdSet S c ρ) : LocComp q y₀ → Y := fun y => y.1.1

lemma continuous_incl {c : ℂ} {ρ : ℝ} (y₀ : q ⁻¹' nbhdSet S c ρ) :
    Continuous (incl (q := q) y₀) :=
  continuous_subtype_val.comp continuous_subtype_val

lemma incl_injective {c : ℂ} {ρ : ℝ} (y₀ : q ⁻¹' nbhdSet S c ρ) :
    Function.Injective (incl (q := q) y₀) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

lemma q_incl {c : ℂ} {ρ : ℝ} (hS : ∀ u ∈ pdisk ρ, u + c ∈ S) (y₀ : q ⁻¹' nbhdSet S c ρ)
    (y : LocComp q y₀) : (q (incl y₀ y) : ℂ) = c + compProj hS y₀ y := by
  show (q y.1.1 : ℂ) = c + (((q y.1.1 : S) : ℂ) - c); ring

lemma mem_Hp_iff {ρ : ℝ} [Fact (0 < ρ)] {w : ℂ} : w ∈ exp ⁻¹' pdisk ρ ↔ w.re < Real.log ρ := by
  rw [exp_preimage_pdisk Fact.out]; rfl

/-- Vertical translation by `2π i s` in the half-plane. -/
def vshift {ρ : ℝ} [Fact (0 < ρ)] (s : ℝ) (v : Hp ρ) : Hp ρ :=
  ⟨(v : ℂ) + s * (2 * Real.pi * I), by
    rw [mem_Hp_iff]; have := mem_Hp_iff.1 v.2; simpa using this⟩

lemma continuous_vshift {ρ : ℝ} [Fact (0 < ρ)] (v : Hp ρ) : Continuous fun s : ℝ => vshift s v :=
  (continuous_const.add ((Complex.continuous_ofReal).mul continuous_const)).subtype_mk _

lemma vshift_zero {ρ : ℝ} [Fact (0 < ρ)] (v : Hp ρ) : vshift 0 v = v := by
  apply Subtype.ext; simp [vshift]

lemma vshift_int {ρ : ℝ} [Fact (0 < ρ)] (n : ℤ) (v : Hp ρ) : vshift n v = shift n v := by
  apply Subtype.ext; simp [vshift, shift]

section Monodromy

variable {c : ℂ} {ρ : ℝ} [Fact (0 < ρ)] (hq : IsCoveringMap q) (hS : ∀ u ∈ pdisk ρ, u + c ∈ S)
  {r' : ℝ} {b : S} (γ : Path b b) (hγ : ∀ t, (γ t : ℂ) = circ c r' t)
  (y₀ : q ⁻¹' nbhdSet S c ρ)
  (L : C(Hp ρ, LocComp q y₀)) (hL : compProj hS y₀ ∘ L = expP ρ)
include hγ hL

/-- One turn of the half-plane lift is the monodromy of the circle. -/
lemma incl_shift_one (v : Hp ρ) (hv : exp (v : ℂ) = r') (hb : q (incl y₀ (L v)) = b) :
    incl y₀ (L (shift 1 v)) = (hq.monodromy (Path.Homotopic.Quotient.mk γ) ⟨_, hb⟩).1 := by
  let Γ : C(unitInterval, Y) := ⟨fun t => incl y₀ (L (vshift t v)),
    (continuous_incl y₀).comp (L.continuous.comp
      ((continuous_vshift v).comp continuous_subtype_val))⟩
  have hΓ : Γ = hq.liftPath (γ : C(unitInterval, S)) (incl y₀ (L v)) (γ.source.trans hb.symm) := by
    rw [IsCoveringMap.eq_liftPath_iff']
    constructor
    · funext t
      apply Subtype.ext
      simp only [Function.comp_apply, Γ, ContinuousMap.coe_mk, ContinuousMap.coe_coe]
      rw [q_incl hS, hγ, show compProj hS y₀ (L (vshift t v)) = expP ρ (vshift t v) from
        congrFun hL _]
      simp only [expP, restrictPreimage_coe, vshift, circ, exp_add, hv]
      ring_nf
    · simp [Γ, vshift_zero]
  show _ = hq.liftPath (γ : C(unitInterval, S)) (incl y₀ (L v)) _ 1
  rw [← hΓ]
  simp [Γ, ← vshift_int]

omit hγ [Fact (0 < ρ)] in
lemma q_incl_L (v : Hp ρ) : (q (incl y₀ (L v)) : ℂ) = c + exp (v : ℂ) := by
  rw [q_incl hS, show compProj hS y₀ (L v) = expP ρ v from congrFun hL v]; rfl

omit [Fact (0 < ρ)] in
lemma q_incl_L_eq (v : Hp ρ) (hv : exp (v : ℂ) = r') : q (incl y₀ (L v)) = b := by
  apply Subtype.ext
  rw [q_incl_L hS y₀ L hL, hv, ← γ.source, hγ]; simp [circ]

/-- `k` turns of the half-plane lift are the `k`-th iterate of the circle monodromy. -/
lemma incl_shift_nat (v₀ : Hp ρ) (hv : exp (v₀ : ℂ) = r') (k : ℕ) :
    (⟨incl y₀ (L (shift k v₀)), q_incl_L_eq hS γ hγ y₀ L hL _
        (by rw [← vshift_int, show ((vshift (k : ℤ) v₀ : Hp ρ) : ℂ) = v₀ + (k : ℤ) * (2 * Real.pi * I)
          from rfl, exp_add, exp_int_mul_two_pi_mul_I, mul_one, hv])⟩ : q ⁻¹' {b}) =
      (hq.monodromy (Path.Homotopic.Quotient.mk γ))^[k]
        ⟨incl y₀ (L v₀), q_incl_L_eq hS γ hγ y₀ L hL v₀ hv⟩ := by
  induction k with
  | zero => apply Subtype.ext; simp [shift_zero]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ← ih]
    apply Subtype.ext
    have hk : exp ((shift (k : ℤ) v₀ : Hp ρ) : ℂ) = r' := by
      rw [← vshift_int, show ((vshift (k : ℤ) v₀ : Hp ρ) : ℂ) = v₀ + (k : ℤ) * (2 * Real.pi * I)
        from rfl, exp_add, exp_int_mul_two_pi_mul_I, mul_one, hv]
    have := incl_shift_one hq hS γ hγ y₀ L hL (shift (k : ℤ) v₀) hk
      (q_incl_L_eq hS γ hγ y₀ L hL _ hk)
    rw [← shift_add] at this
    simp only [Nat.cast_succ, add_comm (k : ℤ) 1]
    exact this

/-- **The period group of the half-plane lift is `dℤ`** when the circle monodromy returns the
base point after exactly the multiples of `d` turns. -/
theorem periods_eq_of_monodromy (v₀ : Hp ρ) (hv : exp (v₀ : ℂ) = r') {d : ℕ}
    (hd : ∀ k : ℕ, (hq.monodromy (Path.Homotopic.Quotient.mk γ))^[k]
        ⟨incl y₀ (L v₀), q_incl_L_eq hS γ hγ y₀ L hL v₀ hv⟩ =
          ⟨incl y₀ (L v₀), q_incl_L_eq hS γ hγ y₀ L hL v₀ hv⟩ ↔ d ∣ k) :
    periods L = AddSubgroup.zmultiples (d : ℤ) := by
  have hcov := isCoveringMap_compProj hq hS y₀
  have key : ∀ n : ℤ, n ∈ periods L ↔ L (shift n v₀) = L v₀ := fun n =>
    ⟨fun h => h v₀, fun h w => shift_eq_of_eq hcov L hL n h w⟩
  have hnat : ∀ k : ℕ, (k : ℤ) ∈ periods L ↔ d ∣ k := by
    intro k
    rw [key, ← hd k, ← incl_shift_nat hq hS γ hγ y₀ L hL v₀ hv k]
    constructor
    · intro h; apply Subtype.ext; simp only [h]
    · intro h; exact incl_injective y₀ (congrArg Subtype.val h :)
  ext n
  rw [Int.mem_zmultiples_iff]
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · rw [hnat, Int.natCast_dvd_natCast]
  · rw [AddSubgroup.neg_mem_iff, hnat, dvd_neg, Int.natCast_dvd_natCast]

end Monodromy

/-- **Local power model from the monodromy.**  Let `q : Y → S` be a covering, `S ⊆ ℂ`, with
`{0 < |z - c| < ρ} ⊆ S`, let `y₀ ∈ Y` lie over `c + r'` (`0 < r' < ρ`), and suppose the monodromy of
the circle `γ : t ↦ c + r' e^{2π i t}` returns `y₀` exactly after the multiples of `d ≥ 1` turns.
Then the path component `C` of `y₀` in `q⁻¹{0 < |z - c| < ρ}` is homeomorphic to
`{0 < |t| < ρ^{1/d}}` by a map `Φ` with `q = c + Φ^d` on `C`, and `C` meets every fibre over the
punctured disk in exactly `d` points. -/
theorem local_power_model {c : ℂ} {ρ : ℝ} [Fact (0 < ρ)] (hq : IsCoveringMap q)
    (hS : ∀ u ∈ pdisk ρ, u + c ∈ S) {r' : ℝ} (hr' : 0 < r') (hr'ρ : r' < ρ) {b : S}
    (γ : Path b b) (hγ : ∀ t, (γ t : ℂ) = circ c r' t)
    (y₀ : q ⁻¹' nbhdSet S c ρ) (hy₀ : q y₀ = b) {d : ℕ} (hd0 : 0 < d)
    (hd : ∀ k : ℕ, (hq.monodromy (Path.Homotopic.Quotient.mk γ))^[k] ⟨y₀, hy₀⟩ = ⟨y₀, hy₀⟩ ↔
      d ∣ k) :
    ∃ Φ : LocComp q y₀ ≃ₜ pdisk (rootRad ρ d),
      (∀ x, ((Φ x : ℂ)) ^ d = (q (incl y₀ x) : ℂ) - c) ∧
      ∀ u : pdisk ρ, Nat.card (compProj hS y₀ ⁻¹' {u}) = d := by
  have hv : ((Real.log r' : ℝ) : ℂ) ∈ exp ⁻¹' pdisk ρ := by
    rw [mem_Hp_iff]; simpa using Real.log_lt_log hr' hr'ρ
  let v₀ : Hp ρ := ⟨_, hv⟩
  have hv₀ : exp (v₀ : ℂ) = r' := by
    show exp ((Real.log r' : ℝ) : ℂ) = r'
    rw [← Complex.ofReal_exp, Real.exp_log hr']
  have hc₀ : compProj hS y₀ ⟨y₀, mem_pathComponent_self y₀⟩ = expP ρ v₀ := by
    apply Subtype.ext
    show ((q y₀ : S) : ℂ) - c = exp (v₀ : ℂ)
    rw [hy₀, hv₀, ← γ.source, hγ]; simp [circ]
  obtain ⟨L, hL0, hL⟩ := exists_lift (isCoveringMap_compProj hq hS y₀) v₀ _ hc₀
  have hper := periods_eq_of_monodromy hq hS γ hγ y₀ L hL v₀ hv₀ (d := d) (by
    have h1 : (⟨incl y₀ (L v₀), q_incl_L_eq hS γ hγ y₀ L hL v₀ hv₀⟩ : q ⁻¹' {b}) =
        ⟨y₀, hy₀⟩ := by
      apply Subtype.ext; show incl y₀ (L v₀) = y₀.1; rw [hL0]; rfl
    rw [h1]; exact hd)
  have hcov := isCoveringMap_compProj hq hS y₀
  refine ⟨powerHomeo hcov L hL hd0 hper, fun x => ?_, fun u => ?_⟩
  · rw [powerHomeo_apply, powerChart_pow hcov L hL hd0 hper x]
    rw [q_incl hS]; ring
  · obtain ⟨w, rfl⟩ := expP_surjective ρ u
    have h1 := congrFun hL w
    simp only [Function.comp_apply] at h1
    rw [← h1]
    exact card_fibre_eq hcov L hL (lift_surjective hcov L hL) hper (L w)

end SteklovPunctured

namespace SteklovPunctured

variable {S : Set ℂ} {Y : Type*} [TopologicalSpace Y] {q : Y → S}

/-- **Local power model at every point over the punctured disk.**  If the circle monodromy returns
every point of the fibre over `c + r'` exactly after the multiples of `d` turns, then the path
component of *every* point of `q⁻¹{0 < |z - c| < ρ}` is a `d`-sheeted power cover
`t ↦ c + t^d` of the punctured disk. -/
theorem local_power_model_all {c : ℂ} {ρ : ℝ} [Fact (0 < ρ)] (hq : IsCoveringMap q)
    (hS : ∀ u ∈ pdisk ρ, u + c ∈ S) {r' : ℝ} (hr' : 0 < r') (hr'ρ : r' < ρ) {b : S}
    (γ : Path b b) (hγ : ∀ t, (γ t : ℂ) = circ c r' t) {d : ℕ} (hd0 : 0 < d)
    (hd : ∀ (e : q ⁻¹' {b}) (k : ℕ),
      (hq.monodromy (Path.Homotopic.Quotient.mk γ))^[k] e = e ↔ d ∣ k)
    (y : q ⁻¹' nbhdSet S c ρ) :
    ∃ Φ : LocComp q y ≃ₜ pdisk (rootRad ρ d),
      (∀ x, ((Φ x : ℂ)) ^ d = (q (incl y x) : ℂ) - c) ∧
      ∀ u : pdisk ρ, Nat.card (compProj hS y ⁻¹' {u}) = d := by
  have hb : (b : ℂ) = c + r' := by rw [← γ.source, hγ]; simp [circ]
  have hub : (b : ℂ) - c ∈ pdisk ρ := by
    refine ⟨by rw [hb]; simp [hr'.ne'], ?_⟩
    rw [hb, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr']
    exact hr'ρ
  haveI : Nonempty (LocComp q y) := ⟨⟨y, mem_pathComponent_self y⟩⟩
  obtain ⟨x₀, hx₀⟩ := covering_surjective (isCoveringMap_compProj hq hS y) ⟨_, hub⟩
  set y₀ := x₀.1
  have hy₀ : q y₀ = b := by
    apply Subtype.ext
    have := congrArg Subtype.val hx₀
    change ((q y₀ : S) : ℂ) - c = (b : ℂ) - c at this
    exact sub_left_injective this
  have heq : pathComponent y₀ = pathComponent y := pathComponent_congr x₀.2
  obtain ⟨Φ₀, hΦ₀, hcard⟩ := local_power_model hq hS hr' hr'ρ γ hγ y₀ hy₀ hd0 (hd _)
  refine ⟨(Homeomorph.setCongr heq.symm).trans Φ₀, fun x => hΦ₀ _, fun u => ?_⟩
  rw [← hcard u]
  exact Nat.card_congr (Equiv.subtypeEquiv (Set.equivOfEq heq.symm) (fun x => Iff.rfl))

end SteklovPunctured
