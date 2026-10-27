module

public import RequestProject.LocalInertia
public import RequestProject.RegCovMonodromy
public import RequestProject.PolyLocalPeriod
public import RequestProject.Degree7CommonCover
public import RequestProject.Degree7Monodromy

/-!
# Local inertia of the actual common regular cover: orders `2` over `0` and `3` over `1`

For `s² = -7` and any ordered complete fibre `f₀` of `p_s ⊔ p_{-s}` over `ℂ \ {0,1}` (in
particular the one of `Degree7.common_regular_cover`), consider the regular cover
`R = RegCov f₀ → ℂ \ {0,1}`.  We prove from the passports of `p_{±s}` (no assumption):

* `regCov_return_zero` / `regCov_return_one`: for every small circle about `0` (resp. `1`) every
  point of `R` over its base point returns to itself after exactly the multiples of `2`
  (resp. `3`) turns;
* `regCov_local_model_zero` / `regCov_local_model_one`: every path component of the part of `R`
  over the punctured disk `{0 < |z| < 1/2}` (resp. `{0 < |z - 1| < 1/2}`) is homeomorphic to a
  punctured disk by a map `Φ` with `z = Φ²` (resp. `z = 1 + Φ³`), with `2` (resp. `3`) sheets.

These are the local inertia orders `2` and `3` and the local power-cover models of the actual
`GL(3,𝔽₂)` cover over its two finite branch values.
-/

@[expose] public section

open Polynomial Set PolyCover LocalMonodromy SteklovRegularCover SteklovPunctured

noncomputable section

namespace Degree7

variable {s : ℂ}

/-- Divisibility by all values of a multiset-valued passport. -/
theorem dvd_all_iff_of_map {T : Finset ℂ} {f : ℂ → ℕ} {M : Multiset ℕ} (h : T.val.map f = M)
    {d : ℕ} (hd : d ∈ M) (hdiv : ∀ m ∈ M, m ∣ d) (k : ℕ) :
    (∀ a ∈ T, f a ∣ k) ↔ d ∣ k := by
  constructor
  · intro H
    rw [← h] at hd
    obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hd
    exact H a ha
  · intro H a ha
    have : f a ∈ M := by rw [← h]; exact Multiset.mem_map_of_mem f ha
    exact (hdiv _ this).trans H

theorem passport_dvd_zero (hs : s ^ 2 = -7) (k : ℕ) :
    (∀ a ∈ (pPoly s - C 0).roots.toFinset, (pPoly s - C 0).rootMultiplicity a ∣ k) ↔ 2 ∣ k := by
  rw [show pPoly s - C 0 = pPoly s by simp]
  exact dvd_all_iff_of_map (passport_zero hs) (by decide) (by decide) k

theorem passport_dvd_one (hs : s ^ 2 = -7) (k : ℕ) :
    (∀ a ∈ (pPoly s - C 1).roots.toFinset, (pPoly s - C 1).rootMultiplicity a ∣ k) ↔ 3 ∣ k :=
  dvd_all_iff_of_map (passport_one hs) (by decide) (by decide) k

/-! ### Iterated monodromy of a disjoint union and of a transported cover -/

section Generic

variable {X E₁ E₂ : Type*} [TopologicalSpace X] [TopologicalSpace E₁] [TopologicalSpace E₂]
  {p₁ : E₁ → X} {p₂ : E₂ → X} (h₁ : IsCoveringMap p₁) (h₂ : IsCoveringMap p₂)

theorem monodromy_sumElim_inl_iterate {x : X} (γ : Path.Homotopic.Quotient x x)
    (e : p₁ ⁻¹' {x}) (k : ℕ) :
    (((isCoveringMap_sumElim h₁ h₂).monodromy γ)^[k] ⟨Sum.inl e.1, e.2⟩ : E₁ ⊕ E₂) =
      Sum.inl ((h₁.monodromy γ)^[k] e).1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have : ((isCoveringMap_sumElim h₁ h₂).monodromy γ)^[k] ⟨Sum.inl e.1, e.2⟩ =
        ⟨Sum.inl ((h₁.monodromy γ)^[k] e).1, ((h₁.monodromy γ)^[k] e).2⟩ := Subtype.ext ih
    rw [this, monodromy_sumElim_inl h₁ h₂]

theorem monodromy_sumElim_inr_iterate {x : X} (γ : Path.Homotopic.Quotient x x)
    (e : p₂ ⁻¹' {x}) (k : ℕ) :
    (((isCoveringMap_sumElim h₁ h₂).monodromy γ)^[k] ⟨Sum.inr e.1, e.2⟩ : E₁ ⊕ E₂) =
      Sum.inr ((h₂.monodromy γ)^[k] e).1 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have : ((isCoveringMap_sumElim h₁ h₂).monodromy γ)^[k] ⟨Sum.inr e.1, e.2⟩ =
        ⟨Sum.inr ((h₂.monodromy γ)^[k] e).1, ((h₂.monodromy γ)^[k] e).2⟩ := Subtype.ext ih
    rw [this, monodromy_sumElim_inr h₁ h₂]

/-- The iterated monodromy of a disjoint union fixes the fibre iff it does on both summands. -/
theorem sumElim_iterate_fix_iff {x : X} (γ : Path.Homotopic.Quotient x x) (k : ℕ) :
    (∀ e, ((isCoveringMap_sumElim h₁ h₂).monodromy γ)^[k] e = e) ↔
      (∀ e, (h₁.monodromy γ)^[k] e = e) ∧ (∀ e, (h₂.monodromy γ)^[k] e = e) := by
  constructor
  · intro H
    refine ⟨fun e => Subtype.ext ?_, fun e => Subtype.ext ?_⟩
    · have := congrArg Subtype.val (H ⟨Sum.inl e.1, e.2⟩)
      rw [monodromy_sumElim_inl_iterate h₁ h₂] at this
      exact Sum.inl_injective this
    · have := congrArg Subtype.val (H ⟨Sum.inr e.1, e.2⟩)
      rw [monodromy_sumElim_inr_iterate h₁ h₂] at this
      exact Sum.inr_injective this
  · rintro ⟨H1, H2⟩ ⟨e, he⟩
    apply Subtype.ext
    cases e with
    | inl e =>
      rw [monodromy_sumElim_inl_iterate h₁ h₂ γ ⟨e, he⟩, H1]
    | inr e =>
      rw [monodromy_sumElim_inr_iterate h₁ h₂ γ ⟨e, he⟩, H2]

end Generic

section Transport

variable {X Y E : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace E]
  {q : E → Y} (hq : IsCoveringMap q) (g : Y ≃ₜ X)

theorem homeomorph_comp_iterate_fix_iff {A : X} (γ : Path.Homotopic.Quotient A A) (k : ℕ) :
    (∀ b, ((hq.homeomorph_comp g).monodromy γ)^[k] b = b) ↔
      ∀ e, (hq.monodromy (γ.map ⟨g.symm, g.symm.continuous⟩))^[k] e = e := by
  have hit : ∀ b, fibreEquivH g A (((hq.homeomorph_comp g).monodromy γ)^[k] b) =
      (hq.monodromy (γ.map ⟨g.symm, g.symm.continuous⟩))^[k] (fibreEquivH g A b) := by
    intro b
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih,
        monodromy_homeomorph_comp]
  constructor
  · intro H e
    obtain ⟨b, rfl⟩ := (fibreEquivH g A).surjective e
    rw [← hit, H]
  · intro H b
    apply (fibreEquivH g A).injective
    rw [hit, H]

end Transport

/-! ### The circle monodromy of `p_s ⊔ p_{-s}` -/

lemma hcirc_neg (hs : s ^ 2 = -7) {w0 : ℂ} {r : ℝ} (hcirc : ∀ t, circ w0 r t ∉ critVals (pPoly s)) :
    ∀ t, circ w0 r t ∉ critVals (pPoly (-s)) := by
  rw [← critVals_neg hs]; exact hcirc

lemma circleLoop_map_neg (hs : s ^ 2 = -7) {w0 : ℂ} {r : ℝ}
    (hcirc : ∀ t, circ w0 r t ∉ critVals (pPoly s)) :
    (Path.Homotopic.Quotient.mk (circleLoop w0 r hcirc)).map
        ⟨(baseHomeoG (critVals_neg hs)).symm, (baseHomeoG (critVals_neg hs)).symm.continuous⟩ =
      Path.Homotopic.Quotient.mk (circleLoop (P := pPoly (-s)) w0 r (hcirc_neg hs hcirc)) := by
  rfl

/-- Iterated circle monodromy of the sum cover about a point `w₀`, in terms of the two passports. -/
theorem projSum_iterate_fix_iff (hs : s ^ 2 = -7) {w0 : ℂ} {r : ℝ}
    (hcirc : ∀ t, circ w0 r t ∉ critVals (pPoly s)) (k : ℕ) :
    (∀ e, ((isCoveringMap_projSum hs).monodromy
        (Path.Homotopic.Quotient.mk (circleLoop w0 r hcirc)))^[k] e = e) ↔
      (∀ e, ((isCoveringMap (pPoly s)).monodromy
        (Path.Homotopic.Quotient.mk (circleLoop w0 r hcirc)))^[k] e = e) ∧
      (∀ e, ((isCoveringMap (pPoly (-s))).monodromy
        (Path.Homotopic.Quotient.mk (circleLoop w0 r (hcirc_neg hs hcirc))))^[k] e = e) := by
  have := sumElim_iterate_fix_iff (isCoveringMap (pPoly s)) (isCoveringMap_proj₂ hs)
    (Path.Homotopic.Quotient.mk (circleLoop w0 r hcirc)) k
  have h2 := homeomorph_comp_iterate_fix_iff (isCoveringMap (pPoly (-s)))
    (baseHomeoG (critVals_neg hs)) (Path.Homotopic.Quotient.mk (circleLoop w0 r hcirc)) k
  rw [circleLoop_map_neg hs hcirc] at h2
  exact this.trans (and_congr Iff.rfl h2)

/-- **Return orders of the regular cover about a branch value**, from the passports. -/
theorem regCov_return (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (w0 : ℂ) {d : ℕ}
    (hdiv : ∀ k : ℕ, (∀ a ∈ (pPoly s - C w0).roots.toFinset,
        (pPoly s - C w0).rootMultiplicity a ∣ k) ↔ d ∣ k)
    (hdiv' : ∀ k : ℕ, (∀ a ∈ (pPoly (-s) - C w0).roots.toFinset,
        (pPoly (-s) - C w0).rootMultiplicity a ∣ k) ↔ d ∣ k) :
    ∃ r0 > 0, ∀ r : ℝ, 0 < r → r < r0 → ∃ hcirc : ∀ t, circ w0 r t ∉ critVals (pPoly s),
      ∀ (f : regProj f₀ ⁻¹' {basePt w0 r hcirc}) (k : ℕ),
        (haveI := locPathConnectedSpace_base hs
         ((isCoveringMap_regProj (isCoveringMap_projSum hs) f₀).monodromy
          (Path.Homotopic.Quotient.mk (circleLoop w0 r hcirc)))^[k] f = f) ↔ d ∣ k := by
  have hs' : (-s) ^ 2 = -7 := by rw [neg_sq]; exact hs
  obtain ⟨r1, hr1, H1⟩ := local_monodromy_iterate (pPoly_degree_pos hs) w0
  obtain ⟨r2, hr2, H2⟩ := local_monodromy_iterate (pPoly_degree_pos hs') w0
  refine ⟨min r1 r2, lt_min hr1 hr2, fun r hr hrr => ?_⟩
  obtain ⟨hc1, K1⟩ := H1 r hr (lt_of_lt_of_le hrr (min_le_left _ _))
  obtain ⟨hc2, K2⟩ := H2 r hr (lt_of_lt_of_le hrr (min_le_right _ _))
  refine ⟨hc1, fun f k => ?_⟩
  haveI := locPathConnectedSpace_base hs
  rw [regMonodromy_iterate_eq_self_iff (isCoveringMap_projSum hs) f₀ (card_fibre_projSum hs),
    projSum_iterate_fix_iff hs hc1 k, K1, hdiv]
  have : (∀ e, ((isCoveringMap (pPoly (-s))).monodromy
      (Path.Homotopic.Quotient.mk (circleLoop w0 r (hcirc_neg hs hc1))))^[k] e = e) ↔ d ∣ k := by
    rw [← hdiv' k, ← K2 k]
  rw [this, and_self]

/-- **Local inertia order `2` over `0`.** -/
theorem regCov_return_zero (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    ∃ r0 > 0, ∀ r : ℝ, 0 < r → r < r0 → ∃ hcirc : ∀ t, circ 0 r t ∉ critVals (pPoly s),
      ∀ (f : regProj f₀ ⁻¹' {basePt 0 r hcirc}) (k : ℕ),
        (haveI := locPathConnectedSpace_base hs
         ((isCoveringMap_regProj (isCoveringMap_projSum hs) f₀).monodromy
          (Path.Homotopic.Quotient.mk (circleLoop 0 r hcirc)))^[k] f = f) ↔ 2 ∣ k :=
  regCov_return hs f₀ 0 (passport_dvd_zero hs) (passport_dvd_zero (by rw [neg_sq]; exact hs))

/-- **Local inertia order `3` over `1`.** -/
theorem regCov_return_one (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    ∃ r0 > 0, ∀ r : ℝ, 0 < r → r < r0 → ∃ hcirc : ∀ t, circ 1 r t ∉ critVals (pPoly s),
      ∀ (f : regProj f₀ ⁻¹' {basePt 1 r hcirc}) (k : ℕ),
        (haveI := locPathConnectedSpace_base hs
         ((isCoveringMap_regProj (isCoveringMap_projSum hs) f₀).monodromy
          (Path.Homotopic.Quotient.mk (circleLoop 1 r hcirc)))^[k] f = f) ↔ 3 ∣ k :=
  regCov_return hs f₀ 1 (passport_dvd_one hs) (passport_dvd_one (by rw [neg_sq]; exact hs))

/-- **Local power-cover model of the actual regular cover over `w₀ ∈ {0, 1}`** (generic form):
given the return orders `d` for all small circles about `w₀`, every path component of the part of
`R` over `{0 < |z - w₀| < 1/2}` is homeomorphic to `{0 < |t| < (1/2)^{1/d}}` by `Φ` with
`z = w₀ + Φ^d`, and is `d`-sheeted. -/
theorem regCov_local_model (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) {w0 : ℂ}
    (hw0 : w0 = 0 ∨ w0 = 1) {d : ℕ} (hd0 : 0 < d)
    (hret : ∃ r0 > 0, ∀ r : ℝ, 0 < r → r < r0 → ∃ hcirc : ∀ t, circ w0 r t ∉ critVals (pPoly s),
      ∀ (f : regProj f₀ ⁻¹' {basePt w0 r hcirc}) (k : ℕ),
        (haveI := locPathConnectedSpace_base hs
         ((isCoveringMap_regProj (isCoveringMap_projSum hs) f₀).monodromy
          (Path.Homotopic.Quotient.mk (circleLoop w0 r hcirc)))^[k] f = f) ↔ d ∣ k) :
    ∃ hS : ∀ u ∈ pdisk (1 / 2), u + w0 ∈ (critVals (pPoly s))ᶜ,
      ∀ y : regProj f₀ ⁻¹' nbhdSet _ w0 (1 / 2),
        ∃ Φ : LocComp (regProj f₀) y ≃ₜ pdisk (rootRad (1 / 2) d),
          (∀ x : LocComp (regProj f₀) y,
            ((Φ x : ℂ)) ^ d = ((regProj f₀ x.1.1 : Base (pPoly s)) : ℂ) - w0) ∧
          ∀ u : pdisk (1 / 2), Nat.card (compProj hS y ⁻¹' {u}) = d := by
  haveI : Fact ((0 : ℝ) < 1 / 2) := ⟨by norm_num⟩
  haveI := locPathConnectedSpace_base hs
  have hS : ∀ u ∈ pdisk (1 / 2), u + w0 ∈ (critVals (pPoly s))ᶜ := by
    rintro u ⟨hu0, hu⟩
    rw [critVals_pPoly hs]
    simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
    rcases hw0 with rfl | rfl
    · refine ⟨by simpa using hu0, fun h => ?_⟩
      rw [add_zero] at h; rw [h] at hu; norm_num at hu
    · refine ⟨fun h => ?_, fun h => hu0 (by linear_combination h)⟩
      have : u = -1 := by linear_combination h
      rw [this] at hu; norm_num at hu
  refine ⟨hS, fun y => ?_⟩
  obtain ⟨r0, hr0, H⟩ := hret
  set r' := min (r0 / 2) (1 / 4) with hr'
  have hr'0 : 0 < r' := lt_min (half_pos hr0) (by norm_num)
  obtain ⟨hcirc, hd⟩ := H r' hr'0 (lt_of_le_of_lt (min_le_left _ _) (half_lt_self hr0))
  exact local_power_model_all (isCoveringMap_regProj (isCoveringMap_projSum hs) f₀) hS hr'0
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num)) (circleLoop w0 r' hcirc) (fun t => rfl)
    hd0 (fun e k => hd e k) y

/-- **The actual regular cover is locally `t ↦ t²` over `0`.** -/
theorem regCov_local_model_zero (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    ∃ hS : ∀ u ∈ pdisk (1 / 2), u + 0 ∈ (critVals (pPoly s))ᶜ,
      ∀ y : regProj f₀ ⁻¹' nbhdSet _ 0 (1 / 2),
        ∃ Φ : LocComp (regProj f₀) y ≃ₜ pdisk (rootRad (1 / 2) 2),
          (∀ x : LocComp (regProj f₀) y,
            ((Φ x : ℂ)) ^ 2 = ((regProj f₀ x.1.1 : Base (pPoly s)) : ℂ) - 0) ∧
          ∀ u : pdisk (1 / 2), Nat.card (compProj hS y ⁻¹' {u}) = 2 :=
  regCov_local_model hs f₀ (Or.inl rfl) (by norm_num) (regCov_return_zero hs f₀)

/-- **The actual regular cover is locally `t ↦ 1 + t³` over `1`.** -/
theorem regCov_local_model_one (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) :
    ∃ hS : ∀ u ∈ pdisk (1 / 2), u + 1 ∈ (critVals (pPoly s))ᶜ,
      ∀ y : regProj f₀ ⁻¹' nbhdSet _ 1 (1 / 2),
        ∃ Φ : LocComp (regProj f₀) y ≃ₜ pdisk (rootRad (1 / 2) 3),
          (∀ x : LocComp (regProj f₀) y,
            ((Φ x : ℂ)) ^ 3 = ((regProj f₀ x.1.1 : Base (pPoly s)) : ℂ) - 1) ∧
          ∀ u : pdisk (1 / 2), Nat.card (compProj hS y ⁻¹' {u}) = 3 :=
  regCov_local_model hs f₀ (Or.inr rfl) (by norm_num) (regCov_return_one hs f₀)

end Degree7
