module

public import Mathlib

/-!
# Topology of sublevel sets of a map which is a covering near infinity

Let `g : X → ℂ` be continuous and suppose `g` is a covering map over the annulus
`{z | r < ‖z‖}`.  For every `ρ > r` we construct a continuous **radial retraction**
`X → {x | ‖g x‖ ≤ ρ}` (`exists_radial_retraction`), by lifting the radial homotopy
`z ↦ z ((1 - t) + t ρ / ‖z‖)` through the covering.  Consequently, if `X` is (pre)connected so is
every sublevel set `{‖g‖ ≤ ρ}` (`isPreconnected_sublevel`), and also the open sublevel set
`{‖g‖ < ρ}` (`isPreconnected_strictSublevel`), a directed union of closed ones.

We also record the transfer of the covering property along an open embedding whose range
contains the relevant preimage (`isCoveringMapOn_of_isOpenEmbedding`), and the description of the
interior, closure and frontier of a sublevel set of an open map.
-/

@[expose] public section

open Set Topology unitInterval

noncomputable section

namespace SteklovBordered

variable {X : Type*} [TopologicalSpace X]

/-- Transfer of a covering property along an open embedding `i : Y → X`, when every point of
`X` over `s` is in the range of `i`. -/
theorem isCoveringMapOn_of_isOpenEmbedding {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    {i : Y → X} (hi : IsOpenEmbedding i) {g : X → Z} (hg : Continuous g) {s : Set Z}
    (hs : IsOpen s) (hrange : g ⁻¹' s ⊆ range i) (h : IsCoveringMapOn (g ∘ i) s) :
    IsCoveringMapOn g s := by
  set t : Set X := g ⁻¹' s
  have hcont : Continuous (t.restrictPreimage i) := hi.continuous.restrictPreimage
  have hopen : IsOpenMap (t.restrictPreimage i) := hi.isOpenMap.restrictPreimage t
  have hbij : Function.Bijective (t.restrictPreimage i) :=
    ⟨Set.restrictPreimage_injective _ hi.injective, by
      rintro ⟨x, hx⟩
      obtain ⟨y, rfl⟩ := hrange hx
      exact ⟨⟨y, hx⟩, rfl⟩⟩
  let Φ : i ⁻¹' t ≃ₜ t :=
    (Equiv.ofBijective _ hbij).toHomeomorphOfContinuousOpen hcont hopen
  have hcov : IsCoveringMap (s.restrictPreimage (g ∘ i)) := h.isCoveringMap_restrictPreimage
  have hcov' : IsCoveringMap (s.restrictPreimage g) := by
    have := hcov.comp_homeomorph Φ.symm
    convert this using 1
    funext x
    obtain ⟨y, rfl⟩ := Φ.surjective x
    simp only [Function.comp_apply]
    exact congrArg (s.restrictPreimage (g ∘ i)) (Φ.symm_apply_apply y).symm
  exact IsCoveringMapOn.of_isCoveringMap_restrictPreimage _ hs (hs.preimage hg) hcov'

/-- The radial homotopy, as a function. -/
def radial (ρ : ℝ) (t : ℝ) (z : ℂ) : ℂ := z * (((1 - t) + t * ρ / ‖z‖ : ℝ) : ℂ)

lemma norm_radial {ρ t : ℝ} {z : ℂ} (hρ : 0 < ρ) (hz : ρ ≤ ‖z‖) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖radial ρ t z‖ = (1 - t) * ‖z‖ + t * ρ := by
  have hz0 : 0 < ‖z‖ := lt_of_lt_of_le hρ hz
  have hnn : 0 ≤ (1 - t) + t * ρ / ‖z‖ := by
    have : 0 ≤ t * ρ / ‖z‖ := div_nonneg (mul_nonneg ht0 hρ.le) hz0.le
    linarith
  rw [radial, norm_mul, Complex.norm_real, Real.norm_of_nonneg hnn]
  field_simp

lemma radial_zero (ρ : ℝ) (z : ℂ) : radial ρ 0 z = z := by simp [radial]

lemma radial_of_norm_eq {ρ t : ℝ} {z : ℂ} (hz : ‖z‖ = ρ) (hρ : 0 < ρ) : radial ρ t z = z := by
  rw [radial, hz, mul_div_assoc, div_self hρ.ne']; simp

/-- **Radial retraction onto a sublevel set.**  If `g` is a covering over `{r < ‖z‖}` and
`0 ≤ r < ρ`, there is a continuous `R : X → X`, the identity on `{‖g‖ ≤ ρ}`, with values in
`{‖g‖ ≤ ρ}`. -/
theorem exists_radial_retraction {g : X → ℂ} (hg : Continuous g) {r ρ : ℝ} (hr : 0 ≤ r)
    (hrρ : r < ρ) (hcov : IsCoveringMapOn g {z | r < ‖z‖}) :
    ∃ R : X → X, Continuous R ∧ (∀ x, ‖g x‖ ≤ ρ → R x = x) ∧ ∀ x, ‖g (R x)‖ ≤ ρ := by
  have hρ : 0 < ρ := lt_of_le_of_lt hr hrρ
  set S : Set ℂ := {z | r < ‖z‖}
  set p := S.restrictPreimage g
  have cov : IsCoveringMap p := hcov.isCoveringMap_restrictPreimage
  set A : Set (g ⁻¹' S) := {a | ρ ≤ ‖g a‖}
  -- the radial homotopy on `A`
  have hmem : ∀ (t : I) (a : A), radial ρ t (g a.1.1) ∈ S := by
    intro t a
    show r < ‖radial ρ t (g a.1.1)‖
    rw [norm_radial hρ a.2 t.2.1 t.2.2]
    have h1 : ρ ≤ (1 - (t : ℝ)) * ‖g a.1.1‖ + t * ρ := by
      have := mul_le_mul_of_nonneg_left (show ρ ≤ ‖g a.1.1‖ from a.2)
        (show 0 ≤ 1 - (t : ℝ) by linarith [t.2.2])
      nlinarith
    linarith
  have hgA : Continuous fun a : A => g a.1.1 :=
    hg.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hradc : Continuous fun ta : I × A => radial ρ ta.1 (g ta.2.1.1) := by
    unfold radial
    have hn : ∀ ta : I × A, ‖g ta.2.1.1‖ ≠ 0 := fun ta =>
      (lt_of_lt_of_le hρ ta.2.2).ne'
    refine (hgA.comp continuous_snd).mul (Complex.continuous_ofReal.comp ?_)
    refine ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      (((continuous_subtype_val.comp continuous_fst).mul continuous_const).div
        (continuous_norm.comp (hgA.comp continuous_snd)) hn))
  let H : C(I × A, S) := ⟨fun ta => ⟨radial ρ ta.1 (g ta.2.1.1), hmem ta.1 ta.2⟩,
    hradc.subtype_mk _⟩
  let f : C(A, g ⁻¹' S) := ⟨Subtype.val, continuous_subtype_val⟩
  have H0 : ∀ a, H (0, a) = p (f a) := by
    intro a
    apply Subtype.ext
    show radial ρ ((0 : I) : ℝ) (g a.1.1) = g a.1.1
    simp [radial]
  set L := cov.liftHomotopy H f H0
  have hL : ∀ ta, g (L ta).1 = radial ρ ta.1 (g ta.2.1.1) := fun ta =>
    congrArg Subtype.val (congrFun (cov.liftHomotopy_lifts H f H0) ta)
  -- the lift is constant over points of norm `ρ`
  have hconst : ∀ a : A, ‖g a.1.1‖ = ρ → (L (1, a)).1 = a.1.1 := by
    intro a ha
    have key := (cov.eq_liftPath_iff' (γ := H.comp ((ContinuousMap.id I).prodMk
      (ContinuousMap.const I a))) (e := f a) (γ_0 := H0 a)
      (Γ := ContinuousMap.const I (f a))).2 ⟨?_, rfl⟩
    · have : L (1, a) = cov.liftPath _ (f a) (H0 a) 1 := rfl
      rw [this, ← key]; rfl
    · funext t
      apply Subtype.ext
      show g a.1.1 = radial ρ t (g a.1.1)
      rw [radial_of_norm_eq ha hρ]
  -- the retraction
  have hSx : ∀ x : X, ρ ≤ ‖g x‖ → x ∈ g ⁻¹' S := fun x hx =>
    show r < ‖g x‖ from lt_of_lt_of_le hrρ hx
  let g' : X → X := fun x =>
    if h : ρ ≤ ‖g x‖ then (L (1, ⟨⟨x, hSx x h⟩, h⟩)).1 else x
  refine ⟨fun x => if ‖g x‖ ≤ ρ then x else g' x, ?_, fun x hx => if_pos hx, fun x => ?_⟩
  · refine continuous_if_le (continuous_norm.comp hg) continuous_const continuousOn_id ?_ ?_
    · rw [continuousOn_iff_continuous_restrict]
      have hc : Continuous fun x : {x | ρ ≤ ‖g x‖} =>
          (L (1, ⟨⟨x.1, hSx x.1 x.2⟩, x.2⟩)).1 := by
        refine continuous_subtype_val.comp (L.continuous.comp ?_)
        refine continuous_const.prodMk ?_
        exact ((continuous_subtype_val.subtype_mk _).subtype_mk _)
      refine hc.congr ?_
      intro x
      have hx2 : ρ ≤ ‖g x.1‖ := x.2
      show _ = g' x.1
      simp only [g', dif_pos hx2]
    · intro x hx
      show x = g' x
      have h' : ρ ≤ ‖g x‖ := hx.ge
      simp only [g', dif_pos h']
      exact (hconst ⟨⟨x, hSx x h'⟩, h'⟩ hx).symm
  · by_cases hx : ‖g x‖ ≤ ρ
    · simp only [if_pos hx]; exact hx
    · simp only [if_neg hx]
      have h' : ρ ≤ ‖g x‖ := (not_le.1 hx).le
      simp only [g', dif_pos h']
      rw [hL]
      rw [norm_radial hρ h' (by simp) (by simp)]
      simp

/-- Sublevel sets of a map which is a covering near infinity are preconnected. -/
theorem isPreconnected_sublevel [PreconnectedSpace X] {g : X → ℂ} (hg : Continuous g) {r ρ : ℝ}
    (hr : 0 ≤ r) (hrρ : r < ρ) (hcov : IsCoveringMapOn g {z | r < ‖z‖}) :
    IsPreconnected {x | ‖g x‖ ≤ ρ} := by
  obtain ⟨R, hR, hid, hle⟩ := exists_radial_retraction hg hr hrρ hcov
  have : {x | ‖g x‖ ≤ ρ} = range R := by
    ext x
    exact ⟨fun hx => ⟨x, hid x hx⟩, by rintro ⟨y, rfl⟩; exact hle y⟩
  rw [this]
  exact isPreconnected_range hR

/-- Open sublevel sets of a map which is a covering near infinity are preconnected. -/
theorem isPreconnected_strictSublevel [PreconnectedSpace X] {g : X → ℂ} (hg : Continuous g)
    {r ρ : ℝ} (hr : 0 ≤ r) (hrρ : r < ρ) (hcov : IsCoveringMapOn g {z | r < ‖z‖}) :
    IsPreconnected {x | ‖g x‖ < ρ} := by
  have hU : {x | ‖g x‖ < ρ} = ⋃ n : ℕ, {x | ‖g x‖ ≤ ρ - (ρ - r) / (n + 2)} := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_gt ((ρ - r) / (ρ - ‖g x‖))
      refine ⟨n, ?_⟩
      have hpos : 0 < ρ - ‖g x‖ := by linarith
      have hn2 : (ρ - r) / (ρ - ‖g x‖) < (n : ℝ) + 2 := by linarith
      have : (ρ - r) / ((n : ℝ) + 2) < ρ - ‖g x‖ := by
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hpos] at hn2
        linarith
      linarith
    · rintro ⟨n, hn⟩
      have : 0 < (ρ - r) / ((n : ℝ) + 2) := div_pos (by linarith) (by positivity)
      linarith
  have hmono : Monotone (fun n : ℕ => {x | ‖g x‖ ≤ ρ - (ρ - r) / (n + 2)}) := by
    intro m n hmn x hx
    have hx' : ‖g x‖ ≤ ρ - (ρ - r) / ((m : ℝ) + 2) := hx
    show ‖g x‖ ≤ ρ - (ρ - r) / ((n : ℝ) + 2)
    have : (ρ - r) / ((n : ℝ) + 2) ≤ (ρ - r) / ((m : ℝ) + 2) := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      have : (m : ℝ) ≤ n := by exact_mod_cast hmn
      linarith
    linarith
  rw [hU, ← sUnion_range]
  refine IsPreconnected.sUnion_directed ?_ ?_
  · first
    | exact directedOn_range.2 hmono.directed_le
    | exact directedOn_range.1 hmono.directed_le
  · rintro _ ⟨n, rfl⟩
    refine isPreconnected_sublevel hg hr ?_ hcov
    have : (ρ - r) / ((n : ℝ) + 2) < ρ - r := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

/-- Interior, frontier and closure of sublevel sets of continuous open maps to `ℂ`. -/
theorem sublevel_topology {g : X → ℂ} (hg : Continuous g) (ho : IsOpenMap g) {ρ : ℝ}
    (hρ : 0 < ρ) :
    interior {x | ‖g x‖ ≤ ρ} = {x | ‖g x‖ < ρ} ∧
    frontier {x | ‖g x‖ ≤ ρ} = {x | ‖g x‖ = ρ} ∧
    closure {x | ‖g x‖ < ρ} = {x | ‖g x‖ ≤ ρ} ∧
    IsClosed {x | ‖g x‖ ≤ ρ} := by
  have e1 : {x | ‖g x‖ ≤ ρ} = g ⁻¹' Metric.closedBall 0 ρ := by ext x; simp
  have e2 : {x | ‖g x‖ < ρ} = g ⁻¹' Metric.ball 0 ρ := by ext x; simp
  have e3 : {x | ‖g x‖ = ρ} = g ⁻¹' Metric.sphere 0 ρ := by ext x; simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e1, e2, ← ho.preimage_interior_eq_interior_preimage hg, interior_closedBall _ hρ.ne']
  · rw [e1, e3, ← ho.preimage_frontier_eq_frontier_preimage hg, frontier_closedBall _ hρ.ne']
  · rw [e1, e2, ← ho.preimage_closure_eq_closure_preimage hg, closure_ball _ hρ.ne']
  · rw [e1]; exact Metric.isClosed_closedBall.preimage hg

end SteklovBordered
