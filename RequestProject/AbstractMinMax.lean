module

public import Mathlib
public import RequestProject.DiskH1
public import RequestProject.MinMaxApprox

/-!
# Min–max over a completion versus min–max over smooth test functions (abstract form)

Let `j` map the globally smooth functions linearly and densely into a normed space `X`, and let
`A, B` be continuous linear maps on `X` such that for smooth `u` the energy and the boundary mass
are `E u = ‖A (j u)‖²` and `M u = ‖B (j u)‖²`. Then for every `k` the min–max value of `E / M`
over `(k+1)`-dimensional admissible spaces of smooth functions equals the min–max value of
`‖A x‖² / ‖B x‖²` over `(k+1)`-dimensional subspaces of `X` on which `B` is injective
(`SteklovH1.minMax_eq_closureMinMax`).
-/

@[expose] public section

open Filter Topology Set
open scoped ENNReal

noncomputable section

namespace SteklovH1

variable {X YA YB : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup YA] [NormedSpace ℝ YA] [NormedAddCommGroup YB] [NormedSpace ℝ YB]

/-- Min–max of `‖A x‖² / ‖B x‖²` over `(k+1)`-dimensional subspaces on which `B` is injective. -/
def closureMinMax (A : X →L[ℝ] YA) (B : X →L[ℝ] YB) (k : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule ℝ X) (_ : Module.finrank ℝ V = k + 1 ∧ ∀ x ∈ V, x ≠ 0 → ‖B x‖ₑ ^ 2 ≠ 0),
    ⨆ (x : X) (_ : x ∈ V) (_ : x ≠ 0), ‖A x‖ₑ ^ 2 / ‖B x‖ₑ ^ 2

lemma enorm_sq_ofReal' {F : Type*} [NormedAddCommGroup F] (y : F) :
    ‖y‖ₑ ^ 2 = ENNReal.ofReal (‖y‖ ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem closureMinMax_le_minMax (A : X →L[ℝ] YA) (B : X →L[ℝ] YB) (j : smoothFns →ₗ[ℝ] X)
    {E M : (ℂ → ℝ) → ℝ≥0∞} (hE : ∀ u : smoothFns, E u = ‖A (j u)‖ₑ ^ 2)
    (hM : ∀ u : smoothFns, M u = ‖B (j u)‖ₑ ^ 2) (k : ℕ) :
    closureMinMax A B k ≤ Steklov.minMax E M k := by
  unfold Steklov.minMax
  refine le_iInf₂ (fun V hV => ?_)
  have hVs : V ≤ smoothFns := fun u hu => hV.1 u hu
  let f : V →ₗ[ℝ] X := j ∘ₗ Submodule.inclusion hVs
  have hf : ∀ v : V, f v = j ⟨v, hVs v.2⟩ := fun v => rfl
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    by_contra hne
    have hv0 : (v : ℂ → ℝ) ≠ 0 := fun h => hne (Subtype.ext h)
    apply hV.2.2 v v.2 hv0
    have := hM ⟨v, hVs v.2⟩
    rw [← hf, hv, map_zero] at this
    simpa using this
  let W : Submodule ℝ X := LinearMap.range f
  have hW : Module.finrank ℝ W = k + 1 ∧ ∀ x ∈ W, x ≠ 0 → ‖B x‖ₑ ^ 2 ≠ 0 := by
    refine ⟨?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hinj, hV.2.1]
    · rintro _ ⟨v, rfl⟩ hx
      have hv0 : (v : ℂ → ℝ) ≠ 0 := by
        intro h
        apply hx
        have : v = 0 := Subtype.ext h
        rw [this, map_zero]
      rw [hf, ← hM]
      exact hV.2.2 v v.2 hv0
  unfold closureMinMax
  refine iInf₂_le_of_le W hW ?_
  refine iSup₂_le (fun x hx => iSup_le (fun hx0 => ?_))
  obtain ⟨v, rfl⟩ := hx
  have hv0 : (v : ℂ → ℝ) ≠ 0 := by
    intro h
    apply hx0
    have : v = 0 := Subtype.ext h
    rw [this, map_zero]
  rw [hf, ← hM, ← hE]
  exact le_iSup₂_of_le (v : ℂ → ℝ) v.2 (le_iSup_of_le hv0 le_rfl)

theorem minMax_le_closureMinMax (A : X →L[ℝ] YA) (B : X →L[ℝ] YB) (j : smoothFns →ₗ[ℝ] X)
    (hj : DenseRange j) {E M : (ℂ → ℝ) → ℝ≥0∞} (hE : ∀ u : smoothFns, E u = ‖A (j u)‖ₑ ^ 2)
    (hM : ∀ u : smoothFns, M u = ‖B (j u)‖ₑ ^ 2) (k : ℕ) :
    Steklov.minMax E M k ≤ closureMinMax A B k := by
  unfold closureMinMax
  refine le_iInf₂ (fun W hW => ?_)
  set R := ⨆ (x : X) (_ : x ∈ W) (_ : x ≠ 0), ‖A x‖ₑ ^ 2 / ‖B x‖ₑ ^ 2 with hR
  refine le_of_forall_gt_imp_ge_of_dense (fun r hr => ?_)
  by_cases hrtop : r = ⊤
  · rw [hrtop]; exact le_top
  have hRtop : R ≠ ⊤ := ne_top_of_lt hr
  set Mr := R.toReal
  have hMr : Mr < r.toReal := by
    rw [ENNReal.toReal_lt_toReal hRtop hrtop]; exact hr
  have hBne : ∀ x ∈ W, x ≠ 0 → B x ≠ 0 := by
    intro x hx hx0 h
    apply hW.2 x hx hx0
    rw [h]; simp
  have hMW : ∀ x ∈ W, ‖A x‖ ^ 2 ≤ Mr * ‖B x‖ ^ 2 := by
    intro x hx
    by_cases hx0 : x = 0
    · simp [hx0]
    have hq : ‖A x‖ₑ ^ 2 / ‖B x‖ₑ ^ 2 ≤ R :=
      le_iSup₂_of_le x hx (le_iSup_of_le hx0 le_rfl)
    have hBpos : 0 < ‖B x‖ ^ 2 := by
      have := hBne x hx hx0; positivity
    rw [enorm_sq_ofReal', enorm_sq_ofReal',
      ENNReal.div_le_iff (ENNReal.ofReal_pos.2 hBpos).ne' ENNReal.ofReal_ne_top,
      ← ENNReal.ofReal_toReal hRtop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg] at hq
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hq
  obtain ⟨s, hs⟩ := exists_family_ratio_lt A B j hj W hW.1 hBne hMW hMr
  set V : Submodule ℝ (ℂ → ℝ) := Submodule.span ℝ (Set.range fun i => (s i : ℂ → ℝ)) with hV
  have hcomb : ∀ c : Fin (k + 1) → ℝ,
      (∑ i, c i • (s i : ℂ → ℝ)) = ((∑ i, c i • s i : smoothFns) : ℂ → ℝ) := by
    intro c; rw [Submodule.coe_sum]; simp only [Submodule.coe_smul]
  have hmemV : ∀ u ∈ V, ∃ c : Fin (k + 1) → ℝ, u = ∑ i, c i • (s i : ℂ → ℝ) := by
    intro u hu
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hu
    exact ⟨c, hc.symm⟩
  have hpos : ∀ c : Fin (k + 1) → ℝ, c ≠ 0 →
      M (∑ i, c i • (s i : ℂ → ℝ)) ≠ 0 ∧
      E (∑ i, c i • (s i : ℂ → ℝ)) / M (∑ i, c i • (s i : ℂ → ℝ)) ≤ r := by
    intro c hc
    have h := hs c hc
    rw [hcomb, hM, hE, enorm_sq_ofReal', enorm_sq_ofReal']
    have hBpos : 0 < ‖B (j (∑ i, c i • s i))‖ ^ 2 := by
      rcases (sq_nonneg ‖B (j (∑ i, c i • s i))‖).lt_or_eq with h' | h'
      · exact h'
      · rw [← h', mul_zero] at h
        exact absurd h (not_lt.2 (sq_nonneg _))
    refine ⟨(ENNReal.ofReal_pos.2 hBpos).ne', ?_⟩
    rw [ENNReal.div_le_iff (ENNReal.ofReal_pos.2 hBpos).ne' ENNReal.ofReal_ne_top,
      ← ENNReal.ofReal_toReal hrtop, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_le_ofReal h.le
  have hM0 : M 0 = 0 := by
    have := hM 0
    simp only [map_zero, enorm_zero] at this
    rw [show ((0 : smoothFns) : ℂ → ℝ) = 0 from rfl] at this
    rw [this]; simp
  have hli : LinearIndependent ℝ (fun i => (s i : ℂ → ℝ)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push_neg at hne
    have hc0 : c ≠ 0 := fun h => by
      obtain ⟨i, hi⟩ := hne; exact hi (by rw [h]; rfl)
    apply (hpos c hc0).1
    rw [hc, hM0]
  have hVadm : Steklov.AdmissibleSpace M k V := by
    refine ⟨?_, ?_, ?_⟩
    · intro u hu
      have : V ≤ smoothFns := by
        rw [hV, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (s i).2
      exact this hu
    · rw [hV, finrank_span_eq_card hli, Fintype.card_fin]
    · intro u hu hu0
      obtain ⟨c, rfl⟩ := hmemV u hu
      have hc0 : c ≠ 0 := by
        rintro rfl; apply hu0; simp
      exact (hpos c hc0).1
  unfold Steklov.minMax
  refine iInf₂_le_of_le V hVadm ?_
  refine iSup₂_le (fun u hu => iSup_le (fun hu0 => ?_))
  obtain ⟨c, rfl⟩ := hmemV u hu
  have hc0 : c ≠ 0 := by
    rintro rfl; apply hu0; simp
  exact (hpos c hc0).2

/-- **Abstract `H¹`/smooth min–max equality.** -/
theorem minMax_eq_closureMinMax (A : X →L[ℝ] YA) (B : X →L[ℝ] YB) (j : smoothFns →ₗ[ℝ] X)
    (hj : DenseRange j) {E M : (ℂ → ℝ) → ℝ≥0∞} (hE : ∀ u : smoothFns, E u = ‖A (j u)‖ₑ ^ 2)
    (hM : ∀ u : smoothFns, M u = ‖B (j u)‖ₑ ^ 2) (k : ℕ) :
    Steklov.minMax E M k = closureMinMax A B k :=
  le_antisymm (minMax_le_closureMinMax A B j hj hE hM k) (closureMinMax_le_minMax A B j hE hM k)

end SteklovH1
