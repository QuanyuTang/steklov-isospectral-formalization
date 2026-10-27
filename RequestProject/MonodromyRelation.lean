module

public import RequestProject.LocalMonodromy

/-!
# The product relation between the loops around `0`, `1` and `∞`

Let `P` be a polynomial whose critical values lie in `{0, 1}`.  In `X = ℂ \ critVals P` we show
that, based at the point `-r` (`0 < r < 1/2`), the loop around `0`, followed by the (conjugated)
loop around `1`, is homotopic to the (conjugated) big circle of radius `R > 1`
(`loop_relation`).  The proof only uses that any two paths with the same end points inside one
of the star-shaped regions `H₊ = {Im z > 0} ∪ (ℝ \ {0,1})`, `H₋ = {Im z < 0} ∪ (ℝ \ {0,1})` are
homotopic (`homotopic_of_starConvex`).
-/

@[expose] public section

open Polynomial Set Filter Topology Metric Complex PolyCover
open scoped Real

noncomputable section

namespace MonodromyRelation

variable {P : ℂ[X]}

/-- Two paths in `ℂ \ critVals P` with the same end points, both inside a star-shaped region
avoiding the critical values, are homotopic. -/
theorem homotopic_of_starConvex {S : Set ℂ} {c : ℂ} (hS : StarConvex ℝ c S)
    (hSX : S ⊆ (critVals P)ᶜ) {x y : Base P} (γ γ' : Path x y) (hγ : ∀ t, (γ t : ℂ) ∈ S)
    (hγ' : ∀ t, (γ' t : ℂ) ∈ S) : γ.Homotopic γ' := by
  haveI : ContractibleSpace S := hS.contractibleSpace ⟨_, hγ 0⟩
  let x' : S := ⟨x, by simpa using hγ 0⟩
  let y' : S := ⟨y, by simpa using hγ 1⟩
  let lift : (p : Path x y) → (∀ t, (p t : ℂ) ∈ S) → Path x' y' := fun p hp =>
    { toFun := fun t => ⟨p t, hp t⟩
      continuous_toFun := (continuous_subtype_val.comp p.continuous).subtype_mk _
      source' := Subtype.ext (by simp [x'])
      target' := Subtype.ext (by simp [y']) }
  let ι : C(S, Base P) := ⟨fun z => ⟨z.1, hSX z.2⟩, (continuous_subtype_val).subtype_mk _⟩
  have hmap : ∀ (p : Path x y) (hp : ∀ t, (p t : ℂ) ∈ S), (lift p hp).map ι.continuous = p := by
    intro p hp; ext t; rfl
  have := (SimplyConnectedSpace.paths_homotopic (lift γ hγ) (lift γ' hγ')).map ι
  rwa [hmap, hmap] at this

/-- The upper region `H₊ = {Im z > 0} ∪ (ℝ \ {0, 1})`. -/
def Hup : Set ℂ := {z | 0 < z.im ∨ (z.im = 0 ∧ z ≠ 0 ∧ z ≠ 1)}

/-- The lower region `H₋ = {Im z < 0} ∪ (ℝ \ {0, 1})`. -/
def Hdown : Set ℂ := {z | z.im < 0 ∨ (z.im = 0 ∧ z ≠ 0 ∧ z ≠ 1)}

theorem starConvex_Hup : StarConvex ℝ I Hup := by
  intro z hz a b ha hb hab
  simp only [Hup, mem_setOf_eq] at hz ⊢
  rcases eq_or_lt_of_le hb with rfl | hb'
  · left; simp only [zero_smul, add_zero] at *
    rw [show a = 1 by linarith]; simp
  · rcases eq_or_lt_of_le ha with rfl | ha'
    · rw [show b = 1 by linarith]; simpa using hz
    · left
      have : (a • I + b • z).im = a + b * z.im := by simp
      rw [this]
      rcases hz with h | h
      · positivity
      · rw [h.1]; linarith

theorem starConvex_Hdown : StarConvex ℝ (-I) Hdown := by
  intro z hz a b ha hb hab
  simp only [Hdown, mem_setOf_eq] at hz ⊢
  rcases eq_or_lt_of_le hb with rfl | hb'
  · left; simp only [zero_smul, add_zero] at *
    rw [show a = 1 by linarith]; simp
  · rcases eq_or_lt_of_le ha with rfl | ha'
    · rw [show b = 1 by linarith]; simpa using hz
    · left
      have : (a • (-I) + b • z).im = -a + b * z.im := by simp
      rw [this]
      rcases hz with h | h
      · nlinarith
      · rw [h.1]; linarith

variable (hcrit : critVals P ⊆ {0, 1})
include hcrit

theorem notMem_critVals {z : ℂ} (h0 : z ≠ 0) (h1 : z ≠ 1) : z ∉ critVals P := fun h => by
  rcases hcrit h with h | h
  · exact h0 h
  · exact h1 h

theorem Hup_subset : Hup ⊆ (critVals P)ᶜ := by
  intro z hz
  apply notMem_critVals hcrit
  · rintro rfl; simp [Hup] at hz
  · rintro rfl; simp [Hup] at hz

theorem Hdown_subset : Hdown ⊆ (critVals P)ᶜ := by
  intro z hz
  apply notMem_critVals hcrit
  · rintro rfl; simp [Hdown] at hz
  · rintro rfl; simp [Hdown] at hz

omit hcrit in
/-- A path in `ℂ \ critVals P` given by a continuous complex curve on `[0,1]`. -/
def cpath {x y : Base P} (f : ℝ → ℂ) (hf : Continuous f)
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, f t ∉ critVals P) (h0 : f 0 = x) (h1 : f 1 = y) : Path x y where
  toFun t := ⟨f t, hm t t.2⟩
  continuous_toFun := (hf.comp continuous_subtype_val).subtype_mk _
  source' := Subtype.ext h0
  target' := Subtype.ext h1

omit hcrit in
@[simp] theorem cpath_apply {x y : Base P} (f : ℝ → ℂ) (hf : Continuous f)
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, f t ∉ critVals P) (h0 : f 0 = x) (h1 : f 1 = y)
    (t : unitInterval) : (cpath f hf hm h0 h1 t : ℂ) = f t := rfl

/-- Upper semicircle `t ↦ w₀ + r e^{π i t}` from `w₀ + r` to `w₀ - r`. -/
def upper (w0 : ℂ) (r : ℝ) (t : ℝ) : ℂ := w0 + r * exp (π * I * t)

/-- Lower semicircle `t ↦ w₀ + r e^{π i (1 + t)}` from `w₀ - r` to `w₀ + r`. -/
def lower (w0 : ℂ) (r : ℝ) (t : ℝ) : ℂ := w0 + r * exp (π * I * (1 + t))

/-- Straight segment from `a` to `b`. -/
def seg (a b : ℂ) (t : ℝ) : ℂ := a + t * (b - a)

omit hcrit in
theorem continuous_upper (w0 : ℂ) (r : ℝ) : Continuous (upper w0 r) := by
  unfold upper; fun_prop
omit hcrit in
theorem continuous_lower (w0 : ℂ) (r : ℝ) : Continuous (lower w0 r) := by
  unfold lower; fun_prop
omit hcrit in
theorem continuous_seg (a b : ℂ) : Continuous (seg a b) := by
  unfold seg; fun_prop

omit hcrit in
theorem upper_im (w0 : ℝ) (r t : ℝ) : (upper w0 r t).im = r * Real.sin (π * t) := by
  rw [upper, show π * I * t = ((π * t : ℝ) : ℂ) * I by push_cast; ring]
  simp only [add_im, ofReal_im, mul_im, ofReal_re, exp_ofReal_mul_I_im, exp_ofReal_mul_I_re]
  ring

omit hcrit in
theorem lower_im (w0 : ℝ) (r t : ℝ) : (lower w0 r t).im = - (r * Real.sin (π * t)) := by
  rw [lower, show π * I * (1 + t) = ((π * t + π : ℝ) : ℂ) * I by push_cast; ring]
  simp only [add_im, ofReal_im, mul_im, ofReal_re, exp_ofReal_mul_I_im, exp_ofReal_mul_I_re,
    Real.sin_add_pi]
  ring

omit hcrit in
theorem upper_zero (w0 : ℂ) (r : ℝ) : upper w0 r 0 = w0 + r := by simp [upper]
omit hcrit in
theorem upper_one (w0 : ℂ) (r : ℝ) : upper w0 r 1 = w0 - r := by
  simp [upper, exp_pi_mul_I]; ring
omit hcrit in
theorem lower_zero (w0 : ℂ) (r : ℝ) : lower w0 r 0 = w0 - r := by
  simp [lower, exp_pi_mul_I]; ring
omit hcrit in
theorem lower_one (w0 : ℂ) (r : ℝ) : lower w0 r 1 = w0 + r := by
  simp [lower, show π * I * (1 + 1) = 2 * π * I by ring, exp_two_pi_mul_I]
omit hcrit in
theorem seg_zero (a b : ℂ) : seg a b 0 = a := by simp [seg]
omit hcrit in
theorem seg_one (a b : ℂ) : seg a b 1 = b := by simp [seg]

omit hcrit in
theorem sin_pi_pos {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (h0 : t ≠ 0) (h1 : t ≠ 1) :
    0 < Real.sin (π * t) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos Real.pi_pos (lt_of_le_of_ne ht.1 (Ne.symm h0))
  · have : t < 1 := lt_of_le_of_ne ht.2 h1
    nlinarith [Real.pi_pos]

omit hcrit in
/-- The upper semicircle lies in `H₊` provided its end points avoid `0` and `1`. -/
theorem upper_mem_Hup {w0 : ℝ} {r : ℝ} (hr : 0 < r) (hA0 : (w0 : ℂ) + r ≠ 0)
    (hA1 : (w0 : ℂ) + r ≠ 1) (hB0 : (w0 : ℂ) - r ≠ 0) (hB1 : (w0 : ℂ) - r ≠ 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, upper w0 r t ∈ Hup := by
  intro t ht
  by_cases h0 : t = 0
  · subst h0; right; refine ⟨?_, ?_, ?_⟩ <;> simp_all [upper_zero]
  by_cases h1 : t = 1
  · subst h1; right; refine ⟨?_, ?_, ?_⟩ <;> simp_all [upper_one]
  left; rw [upper_im]; exact mul_pos hr (sin_pi_pos ht h0 h1)

omit hcrit in
theorem lower_mem_Hdown {w0 : ℝ} {r : ℝ} (hr : 0 < r) (hA0 : (w0 : ℂ) + r ≠ 0)
    (hA1 : (w0 : ℂ) + r ≠ 1) (hB0 : (w0 : ℂ) - r ≠ 0) (hB1 : (w0 : ℂ) - r ≠ 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, lower w0 r t ∈ Hdown := by
  intro t ht
  by_cases h0 : t = 0
  · subst h0; right; refine ⟨?_, ?_, ?_⟩ <;> simp_all [lower_zero]
  by_cases h1 : t = 1
  · subst h1; right; refine ⟨?_, ?_, ?_⟩ <;> simp_all [lower_one]
  left; rw [lower_im]; have := mul_pos hr (sin_pi_pos ht h0 h1); linarith

omit hcrit in
/-- A real segment avoiding `0` and `1` lies in both regions. -/
theorem seg_mem {a b : ℝ} (hab : ∀ t ∈ Icc (0 : ℝ) 1, a + t * (b - a) ≠ 0 ∧ a + t * (b - a) ≠ 1) :
    ∀ t ∈ Icc (0 : ℝ) 1, seg a b t ∈ Hup ∩ Hdown := by
  intro t ht
  have hv : seg a b t = ((a + t * (b - a) : ℝ) : ℂ) := by simp [seg]
  obtain ⟨h0, h1⟩ := hab t ht
  have h0' : seg a b t ≠ 0 := by rw [hv]; exact_mod_cast h0
  have h1' : seg a b t ≠ 1 := by rw [hv]; exact_mod_cast h1
  have him : (seg a b t).im = 0 := by rw [hv]; simp
  exact ⟨Or.inr ⟨him, h0', h1'⟩, Or.inr ⟨him, h0', h1'⟩⟩

omit hcrit in
theorem mem_trans {S : Set ℂ} {x y z : Base P} {γ : Path x y} {γ' : Path y z}
    (h1 : ∀ t, (γ t : ℂ) ∈ S) (h2 : ∀ t, (γ' t : ℂ) ∈ S) : ∀ t, ((γ.trans γ') t : ℂ) ∈ S := by
  intro t; rw [Path.trans_apply]; split_ifs
  · exact h1 _
  · exact h2 _

omit hcrit in
theorem mem_symm {S : Set ℂ} {x y : Base P} {γ : Path x y} (h : ∀ t, (γ t : ℂ) ∈ S) :
    ∀ t, (γ.symm t : ℂ) ∈ S := fun t => by rw [Path.symm_apply]; exact h _

omit hcrit in
theorem mem_cpath {S : Set ℂ} {x y : Base P} {f : ℝ → ℂ} {hf : Continuous f}
    {hm : ∀ t ∈ Icc (0 : ℝ) 1, f t ∉ critVals P} {h0 : f 0 = x} {h1 : f 1 = y}
    (h : ∀ t ∈ Icc (0 : ℝ) 1, f t ∈ S) : ∀ t, (cpath f hf hm h0 h1 t : ℂ) ∈ S :=
  fun t => h t t.2

omit hcrit in
theorem quot_cancel {x y z : Base P} (γ : Path.Homotopic.Quotient x y)
    (δ : Path.Homotopic.Quotient x z) : γ.trans (γ.symm.trans δ) = δ := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.trans_symm,
    Path.Homotopic.Quotient.refl_trans]

omit hcrit in
theorem quot_cancel' {x y z : Base P} (γ : Path.Homotopic.Quotient x y)
    (δ : Path.Homotopic.Quotient y z) : γ.symm.trans (γ.trans δ) = δ := by
  rw [← Path.Homotopic.Quotient.trans_assoc, Path.Homotopic.Quotient.symm_trans,
    Path.Homotopic.Quotient.refl_trans]

omit hcrit in
theorem quot_symm_trans {x y z : Base P} (γ : Path.Homotopic.Quotient x y)
    (δ : Path.Homotopic.Quotient y z) : (γ.trans δ).symm = δ.symm.trans γ.symm := by
  induction γ using Path.Homotopic.Quotient.ind with | mk γ =>
  induction δ using Path.Homotopic.Quotient.ind with | mk δ =>
  rw [← Path.Homotopic.Quotient.mk_trans, ← Path.Homotopic.Quotient.mk_symm,
    ← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_symm,
    ← Path.Homotopic.Quotient.mk_trans, Path.trans_symm]

omit hcrit in
theorem quot_symm_symm {x y : Base P} (γ : Path.Homotopic.Quotient x y) : γ.symm.symm = γ := by
  induction γ using Path.Homotopic.Quotient.ind with | mk γ =>
  rw [← Path.Homotopic.Quotient.mk_symm, ← Path.Homotopic.Quotient.mk_symm, Path.symm_symm]

section Relation

variable {r R : ℝ}

open LocalMonodromy

omit hcrit in
theorem hm_upper0 (hr : 0 < r) (hr2 : r < 1 / 2) : ∀ t ∈ Icc (0 : ℝ) 1, upper 0 r t ∈ Hup := by
  have := upper_mem_Hup (w0 := 0) hr (by push_cast; simp; exact hr.ne')
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; simp; exact hr.ne')
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
  simpa using this

omit hcrit in
theorem hm_lower0 (hr : 0 < r) (hr2 : r < 1 / 2) : ∀ t ∈ Icc (0 : ℝ) 1, lower 0 r t ∈ Hdown := by
  have := lower_mem_Hdown (w0 := 0) hr (by push_cast; simp; exact hr.ne')
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; simp; exact hr.ne')
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
  simpa using this

omit hcrit in
theorem hm_upper1 (hr : 0 < r) (hr2 : r < 1 / 2) : ∀ t ∈ Icc (0 : ℝ) 1, upper 1 r t ∈ Hup := by
  have := upper_mem_Hup (w0 := 1) hr
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
  simpa using this

omit hcrit in
theorem hm_lower1 (hr : 0 < r) (hr2 : r < 1 / 2) : ∀ t ∈ Icc (0 : ℝ) 1, lower 1 r t ∈ Hdown := by
  have := lower_mem_Hdown (w0 := 1) hr
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
  simpa using this

omit hcrit in
theorem hm_upperR (hR : 1 < R) : ∀ t ∈ Icc (0 : ℝ) 1, upper 0 R t ∈ Hup := by
  have := upper_mem_Hup (w0 := 0) (by linarith : (0 : ℝ) < R)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
  simpa using this

omit hcrit in
theorem hm_lowerR (hR : 1 < R) : ∀ t ∈ Icc (0 : ℝ) 1, lower 0 R t ∈ Hdown := by
  have := lower_mem_Hdown (w0 := 0) (by linarith : (0 : ℝ) < R)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
    (by push_cast; intro h; have := congrArg re h; simp at this; linarith)
  simpa using this

omit hcrit in
theorem hm_segBC (hr : 0 < r) (hr2 : r < 1 / 2) : ∀ t ∈ Icc (0 : ℝ) 1, seg r (1 - r) t ∈ Hup ∩ Hdown := by
  have := seg_mem (a := r) (b := 1 - r) (fun t ht => by
    constructor <;> nlinarith [ht.1, ht.2])
  simpa using this

omit hcrit in
theorem hm_segAF (hr : 0 < r) (hr2 : r < 1 / 2) (hR : 1 < R) : ∀ t ∈ Icc (0 : ℝ) 1, seg (-r) (-R) t ∈ Hup ∩ Hdown := by
  have := seg_mem (a := -r) (b := -R) (fun t ht => by
    have h1 : 0 ≤ t * (R - r) := mul_nonneg ht.1 (by linarith)
    constructor <;> nlinarith [ht.1, ht.2])
  simpa using this

omit hcrit in
theorem hm_segED (hr : 0 < r) (hR : 1 < R) : ∀ t ∈ Icc (0 : ℝ) 1, seg R (1 + r) t ∈ Hup ∩ Hdown := by
  have := seg_mem (a := R) (b := 1 + r) (fun t ht => by
    have h1 : (1 - t) * 1 ≤ (1 - t) * R := mul_le_mul_of_nonneg_left hR.le (by linarith [ht.2])
    have h2 : t * 1 ≤ t * (1 + r) := mul_le_mul_of_nonneg_left (by linarith) ht.1
    constructor <;> nlinarith [ht.1, ht.2])
  simpa using this

/-- The conjugate `w⁻¹ · γ · w` of a loop `γ` at `x` by a path `w` from `x` to `a`. -/
def conjLoop {x a : Base P} (w : Path x a) (γ : Path x x) : Path.Homotopic.Quotient a a :=
  (Path.Homotopic.Quotient.mk w).symm.trans
    ((Path.Homotopic.Quotient.mk γ).trans (Path.Homotopic.Quotient.mk w))

omit hcrit in
/-- **The standard generators at `-r`**, described geometrically: `γ₀` is the class of the lower
half circle `L₀` (from `-r` to `r`) followed by the upper half circle `U₀` (from `r` back to `-r`)
of radius `r` about `0`; `γ₁` goes from `-r` along `U₀⁻¹` to `r`, along the segment `[r, 1-r]`,
once counterclockwise around the circle of radius `r` about `1` (from `1 - r`: lower half `L₁`,
then upper half `U₁`), and back.  All pieces are given by explicit parametrizations. -/
def IsStdLoops (r : ℝ) {A : Base P} (γ0 γ1 : Path.Homotopic.Quotient A A) : Prop :=
  ∃ (B C D : Base P) (U0 : Path B A) (L0 : Path A B) (U1 : Path D C) (L1 : Path C D)
    (sBC : Path B C),
    (∀ t : unitInterval, (U0 t : ℂ) = upper 0 r t) ∧ (∀ t : unitInterval, (L0 t : ℂ) = lower 0 r t) ∧
    (∀ t : unitInterval, (U1 t : ℂ) = upper 1 r t) ∧ (∀ t : unitInterval, (L1 t : ℂ) = lower 1 r t) ∧
    (∀ t : unitInterval, (sBC t : ℂ) = seg r (1 - r) t) ∧
    γ0 = (Path.Homotopic.Quotient.mk L0).trans (Path.Homotopic.Quotient.mk U0) ∧
    γ1 = (Path.Homotopic.Quotient.mk U0).symm.trans ((Path.Homotopic.Quotient.mk sBC).trans
      ((Path.Homotopic.Quotient.mk L1).trans ((Path.Homotopic.Quotient.mk U1).trans
        ((Path.Homotopic.Quotient.mk sBC).symm.trans (Path.Homotopic.Quotient.mk U0)))))

omit hcrit in
theorem circle_eq_trans {w0 : ℂ} {ρ : ℝ} (hc : ∀ t, circ w0 ρ t ∉ critVals P) {a : Base P}
    (U : Path (basePt w0 ρ hc) a) (L : Path a (basePt w0 ρ hc))
    (hU : ∀ t : unitInterval, (U t : ℂ) = upper w0 ρ t)
    (hL : ∀ t : unitInterval, (L t : ℂ) = lower w0 ρ t) :
    circleLoop w0 ρ hc = U.trans L := by
  ext t
  rw [Path.trans_apply]
  split_ifs with h
  · rw [hU]; simp only [circleLoop, Path.coe_mk_mk, circ, upper]
    congr 2; push_cast; ring_nf
  · rw [hL]; simp only [circleLoop, Path.coe_mk_mk, circ, lower]
    congr 2; push_cast; ring_nf

/-- **The product relation.**  Based at `-r`, the loop around `0` (the small circle of radius `r`
about `0`, conjugated by a path `w₀`) followed by the loop around `1` (the circle of radius `r`
about `1`, conjugated by `w₁`) is homotopic to the circle of radius `R` about `0` (conjugated by
`w_R`). -/
theorem loop_relation (hr : 0 < r) (hr2 : r < 1 / 2) (hR : 1 < R)
    (hc0 : ∀ t, circ 0 r t ∉ critVals P) (hc1 : ∀ t, circ 1 r t ∉ critVals P)
    (hcR : ∀ t, circ 0 R t ∉ critVals P) :
    ∃ (A : Base P) (w0 : Path (basePt 0 r hc0) A) (w1 : Path (basePt 1 r hc1) A)
      (wR : Path (basePt 0 R hcR) A), (A : ℂ) = -r ∧
      (conjLoop w0 (circleLoop 0 r hc0)).trans (conjLoop w1 (circleLoop 1 r hc1)) =
        conjLoop wR (circleLoop 0 R hcR) ∧
      IsStdLoops r (conjLoop w0 (circleLoop 0 r hc0)) (conjLoop w1 (circleLoop 1 r hc1)) := by
  have hup := Hup_subset hcrit
  have hdown := Hdown_subset hcrit
  have hnot : ∀ {z : ℂ}, z ∈ Hup → z ∉ critVals P := fun h => hup h
  have hnot' : ∀ {z : ℂ}, z ∈ Hdown → z ∉ critVals P := fun h => hdown h
  let A : Base P := ⟨-r, notMem_critVals hcrit (by simp [hr.ne']) (by
    intro h; have := congrArg re h; simp at this; linarith)⟩
  let C1 : Base P := ⟨1 - r, notMem_critVals hcrit (by
    intro h; have := congrArg re h; simp at this; linarith) (by
    intro h; have := congrArg re h; simp at this; linarith)⟩
  let F : Base P := ⟨-R, notMem_critVals hcrit (by
    intro h; have := congrArg re h; simp at this; linarith) (by
    intro h; have := congrArg re h; simp at this; linarith)⟩
  have e0 : (basePt 0 r hc0 : ℂ) = r := by simp [basePt, circ_zero]
  have e1 : (basePt 1 r hc1 : ℂ) = 1 + r := by simp [basePt, circ_zero]
  have eR : (basePt 0 R hcR : ℂ) = R := by simp [basePt, circ_zero]
  let U0 : Path (basePt 0 r hc0) A := cpath (upper 0 r) (continuous_upper _ _)
    (fun t ht => hnot (hm_upper0 hr hr2 t ht)) (by rw [e0, upper_zero]; simp)
    (by rw [upper_one]; simp [A])
  let L0 : Path A (basePt 0 r hc0) := cpath (lower 0 r) (continuous_lower _ _)
    (fun t ht => hnot' (hm_lower0 hr hr2 t ht)) (by rw [lower_zero]; simp [A])
    (by rw [e0, lower_one]; simp)
  let U1 : Path (basePt 1 r hc1) C1 := cpath (upper 1 r) (continuous_upper _ _)
    (fun t ht => hnot (hm_upper1 hr hr2 t ht)) (by rw [e1, upper_zero])
    (by rw [upper_one])
  let L1 : Path C1 (basePt 1 r hc1) := cpath (lower 1 r) (continuous_lower _ _)
    (fun t ht => hnot' (hm_lower1 hr hr2 t ht)) (by rw [lower_zero])
    (by rw [e1, lower_one])
  let UR : Path (basePt 0 R hcR) F := cpath (upper 0 R) (continuous_upper _ _)
    (fun t ht => hnot (hm_upperR hR t ht)) (by rw [eR, upper_zero]; simp)
    (by rw [upper_one]; simp [F])
  let LR : Path F (basePt 0 R hcR) := cpath (lower 0 R) (continuous_lower _ _)
    (fun t ht => hnot' (hm_lowerR hR t ht)) (by rw [lower_zero]; simp [F])
    (by rw [eR, lower_one]; simp)
  let sBC : Path (basePt 0 r hc0) C1 := cpath (seg r (1 - r)) (continuous_seg _ _)
    (fun t ht => hnot (hm_segBC hr hr2 t ht).1) (by rw [e0, seg_zero]) (by rw [seg_one])
  let sAF : Path A F := cpath (seg (-r) (-R)) (continuous_seg _ _)
    (fun t ht => hnot (hm_segAF hr hr2 hR t ht).1) (by rw [seg_zero]) (by rw [seg_one])
  let sED : Path (basePt 0 R hcR) (basePt 1 r hc1) := cpath (seg R (1 + r)) (continuous_seg _ _)
    (fun t ht => hnot (hm_segED hr hR t ht).1) (by rw [eR, seg_zero]) (by rw [e1, seg_one])
  have hc0eq : circleLoop 0 r hc0 = U0.trans L0 :=
    circle_eq_trans hc0 U0 L0 (fun t => rfl) (fun t => rfl)
  have hc1eq : circleLoop 1 r hc1 = U1.trans L1 :=
    circle_eq_trans hc1 U1 L1 (fun t => rfl) (fun t => rfl)
  have hcReq : circleLoop 0 R hcR = UR.trans LR :=
    circle_eq_trans hcR UR LR (fun t => rfl) (fun t => rfl)
  -- the two region homotopies
  have R1 : Path.Homotopic.Quotient.mk ((L0.trans sBC).trans L1) =
      Path.Homotopic.Quotient.mk ((sAF.trans LR).trans sED) := by
    apply Path.Homotopic.Quotient.eq.2
    refine homotopic_of_starConvex starConvex_Hdown hdown _ _ ?_ ?_
    · exact mem_trans (mem_trans (mem_cpath (hm_lower0 hr hr2))
        (mem_cpath fun t ht => (hm_segBC hr hr2 t ht).2)) (mem_cpath (hm_lower1 hr hr2))
    · exact mem_trans (mem_trans (mem_cpath fun t ht => (hm_segAF hr hr2 hR t ht).2)
        (mem_cpath (hm_lowerR hR))) (mem_cpath fun t ht => (hm_segED hr hR t ht).2)
  have R2 : Path.Homotopic.Quotient.mk ((U1.trans sBC.symm).trans U0) =
      Path.Homotopic.Quotient.mk ((sED.symm.trans UR).trans sAF.symm) := by
    apply Path.Homotopic.Quotient.eq.2
    refine homotopic_of_starConvex starConvex_Hup hup _ _ ?_ ?_
    · exact mem_trans (mem_trans (mem_cpath (hm_upper1 hr hr2))
        (mem_symm (mem_cpath fun t ht => (hm_segBC hr hr2 t ht).1))) (mem_cpath (hm_upper0 hr hr2))
    · exact mem_trans (mem_trans (mem_symm (mem_cpath fun t ht => (hm_segED hr hR t ht).1))
        (mem_cpath (hm_upperR hR))) (mem_symm (mem_cpath fun t ht => (hm_segAF hr hr2 hR t ht).1))
  refine ⟨A, U0, U1.trans (U0.symm.trans sBC).symm, UR.trans sAF.symm, rfl, ?_, ?_⟩
  swap
  · refine ⟨_, _, _, U0, L0, U1, L1, sBC, fun t => rfl, fun t => rfl, fun t => rfl, fun t => rfl,
      fun t => rfl, ?_, ?_⟩
    · rw [hc0eq]
      simp only [conjLoop, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.trans_assoc,
        quot_cancel']
    · rw [hc1eq]
      simp only [conjLoop, Path.trans_symm, Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
        Path.Homotopic.Quotient.mk_symm, Path.Homotopic.Quotient.trans_assoc, quot_symm_trans,
        quot_symm_symm, quot_cancel']
  rw [hc0eq, hc1eq, hcReq]
  simp only [conjLoop, Path.trans_symm, Path.symm_symm, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm] at R1 R2 ⊢
  generalize Path.Homotopic.Quotient.mk U0 = u0 at *
  generalize Path.Homotopic.Quotient.mk L0 = l0 at *
  generalize Path.Homotopic.Quotient.mk U1 = u1 at *
  generalize Path.Homotopic.Quotient.mk L1 = l1 at *
  generalize Path.Homotopic.Quotient.mk UR = uR at *
  generalize Path.Homotopic.Quotient.mk LR = lR at *
  generalize Path.Homotopic.Quotient.mk sBC = b at *
  generalize Path.Homotopic.Quotient.mk sAF = a at *
  generalize Path.Homotopic.Quotient.mk sED = e at *
  simp only [Path.Homotopic.Quotient.trans_assoc] at R1 R2
  have R1' : ∀ {z : Base P} (Y : Path.Homotopic.Quotient (basePt 1 r hc1) z),
      l0.trans (b.trans (l1.trans Y)) = a.trans (lR.trans (e.trans Y)) := fun Y => by
    simpa only [Path.Homotopic.Quotient.trans_assoc] using congrArg (fun q => q.trans Y) R1
  simp only [quot_symm_trans, quot_symm_symm, Path.Homotopic.Quotient.trans_assoc, quot_cancel,
    quot_cancel']
  rw [R2, R1', quot_cancel]

end Relation

end MonodromyRelation
