module

public import Mathlib

/-!
# Connected finite covers of a punctured disk

Let `p : C → D*` be a covering map of the punctured disk `D* = {0 < |z| < r}` by a path-connected
space `C`.  Via the universal cover `exp : {Re w < log r} → D*` we obtain a lift
`L : {Re w < log r} → C` with `p ∘ L = exp` (`exists_lift`); the set of periods
`{n ∈ ℤ | L(w + 2πin) = L(w) ∀ w}` is a subgroup of `ℤ` (`periods`), and agreement of a shifted
lift at one point forces agreement everywhere (`shift_eq_of_eq`).  This is only preliminary
topological groundwork for the local models `t ↦ t^e` of a branched cover over a branch value;
the completion itself is not yet formalized.
-/

@[expose] public section

open Set Topology Complex Filter

noncomputable section

namespace SteklovPunctured

/-- The punctured disk `{0 < |z| < r}`. -/
def pdisk (r : ℝ) : Set ℂ := {z | z ≠ 0 ∧ ‖z‖ < r}

lemma isOpen_pdisk (r : ℝ) : IsOpen (pdisk r) :=
  (isOpen_ne.inter (isOpen_lt continuous_norm continuous_const))

lemma exp_preimage_pdisk {r : ℝ} (hr : 0 < r) :
    exp ⁻¹' pdisk r = {w : ℂ | w.re < Real.log r} := by
  ext w
  simp only [pdisk, mem_preimage, mem_setOf_eq, Complex.norm_exp, exp_ne_zero, ne_eq,
    not_false_eq_true, true_and]
  rw [← Real.exp_lt_exp (x := w.re), Real.exp_log hr]

/-- The universal cover of the punctured disk: a half-plane. -/
abbrev Hp (r : ℝ) : Type := ↥(exp ⁻¹' pdisk r)

/-- The exponential map `Hp r → pdisk r`. -/
def expP (r : ℝ) : Hp r → pdisk r := (pdisk r).restrictPreimage exp

lemma isCoveringMap_expP (r : ℝ) : IsCoveringMap (expP r) :=
  (isCoveringMapOn_exp.mono fun _ hz => hz.1).isCoveringMap_restrictPreimage

lemma convex_Hp {r : ℝ} (hr : 0 < r) : Convex ℝ (exp ⁻¹' pdisk r) := by
  rw [exp_preimage_pdisk hr]
  exact convex_halfSpace_lt (f := fun w : ℂ => w.re) ⟨fun _ _ => by simp, fun _ _ => by simp⟩ _

lemma nonempty_Hp {r : ℝ} (hr : 0 < r) : (exp ⁻¹' pdisk r).Nonempty := by
  rw [exp_preimage_pdisk hr]
  exact ⟨(Real.log r - 1 : ℝ), by simp⟩

instance instContractibleHp {r : ℝ} [Fact (0 < r)] : ContractibleSpace (Hp r) :=
  (convex_Hp Fact.out).contractibleSpace (nonempty_Hp Fact.out)

instance instLocPathHp {r : ℝ} : LocallyPathConnectedSpace (Hp r) :=
  ((isOpen_pdisk r).preimage continuous_exp).locPathConnectedSpace

instance instPathConnHp {r : ℝ} [Fact (0 < r)] : PathConnectedSpace (Hp r) :=
  isPathConnected_iff_pathConnectedSpace.1 ((convex_Hp Fact.out).isPathConnected
    (nonempty_Hp Fact.out))

/-- Translation by `2πin` preserves the half-plane. -/
def shift {r : ℝ} (n : ℤ) (w : Hp r) : Hp r :=
  ⟨w + n * (2 * Real.pi * I), by
    show exp (w + n * (2 * Real.pi * I)) ∈ pdisk r
    rw [exp_add, exp_int_mul_two_pi_mul_I, mul_one]; exact w.2⟩

lemma continuous_shift {r : ℝ} (n : ℤ) : Continuous (shift (r := r) n) :=
  (continuous_subtype_val.add continuous_const).subtype_mk _

lemma expP_shift {r : ℝ} (n : ℤ) (w : Hp r) : expP r (shift n w) = expP r w := by
  apply Subtype.ext
  show exp (w + n * (2 * Real.pi * I)) = exp w
  rw [exp_add, exp_int_mul_two_pi_mul_I, mul_one]

lemma shift_add {r : ℝ} (m n : ℤ) (w : Hp r) : shift (m + n) w = shift m (shift n w) := by
  apply Subtype.ext
  simp only [shift]; push_cast; ring

lemma shift_zero {r : ℝ} (w : Hp r) : shift 0 w = w := by
  apply Subtype.ext; simp [shift]

variable {r : ℝ} [Fact (0 < r)] {C : Type*} [TopologicalSpace C] {p : C → pdisk r}

/-- A lift of the universal cover through `p`. -/
theorem exists_lift (hp : IsCoveringMap p) (w₀ : Hp r) (c₀ : C) (hc₀ : p c₀ = expP r w₀) :
    ∃ L : C(Hp r, C), L w₀ = c₀ ∧ p ∘ L = expP r := by
  obtain ⟨L, ⟨h1, h2⟩, -⟩ := hp.existsUnique_continuousMap_lifts
    ⟨expP r, (isCoveringMap_expP r).continuous⟩ w₀ c₀ hc₀
  exact ⟨L, h1, h2⟩

/-- Two shifts of a lift agree everywhere as soon as they agree at one point. -/
theorem shift_eq_of_eq (hp : IsCoveringMap p) (L : C(Hp r, C)) (hL : p ∘ L = expP r)
    (n : ℤ) {w₀ : Hp r} (h : L (shift n w₀) = L w₀) (w : Hp r) : L (shift n w) = L w := by
  have := hp.eq_of_comp_eq (g₁ := L ∘ shift n) (g₂ := L)
    (L.continuous.comp (continuous_shift n)) L.continuous
    (by funext x; have h1 := congrFun hL (shift n x); have h2 := congrFun hL x
        simp only [Function.comp_apply] at h1 h2 ⊢; rw [h1, h2, expP_shift]) w₀ h
  exact congrFun this w

/-- **The periods of a lift form a subgroup of `ℤ`.** -/
def periods (L : C(Hp r, C)) : AddSubgroup ℤ where
  carrier := {n | ∀ w, L (shift n w) = L w}
  zero_mem' w := by rw [shift_zero]
  add_mem' {m n} hm hn w := by rw [shift_add, hm, hn]
  neg_mem' {n} hn w := by
    have := hn (shift (-n) w)
    rw [← shift_add, add_neg_cancel, shift_zero] at this
    exact this.symm

lemma mem_periods {L : C(Hp r, C)} {n : ℤ} : n ∈ periods L ↔ ∀ w, L (shift n w) = L w := Iff.rfl

end SteklovPunctured
