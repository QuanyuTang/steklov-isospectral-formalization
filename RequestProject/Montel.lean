module

public import Mathlib

/-!
# Montel's theorem (cluster-point form)

A sequence of holomorphic functions on an open set `U ⊆ ℂ`, uniformly bounded by `1` on `U`, has
a locally uniformly convergent "subnet": there is a nontrivial filter `l ≤ atTop` on `ℕ` and a
function `g` with `f_k → g` locally uniformly on `U` along `l`.

Proof: Cauchy estimates give equicontinuity on compact subsets of `U`; the Arzelà–Ascoli theorem
(`ArzelaAscoli.isCompact_closure_of_isClosedEmbedding`) in the space of functions with the
topology of uniform convergence on compact subsets of `U` gives a compact closure, hence a
cluster point of the sequence.
-/

@[expose] public section

open Set Filter Topology Metric

noncomputable section

namespace SteklovRiemann

/-- Cauchy estimate + mean value: a holomorphic function bounded by `1` on `U ⊇ B̄(x, 2δ)` is
`1/δ`-Lipschitz on `B(x, δ)`. -/
lemma lipschitz_of_bounded {U : Set ℂ} {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U)
    (hb : ∀ z ∈ U, ‖f z‖ ≤ 1) {x : ℂ} {δ : ℝ} (hδ : 0 < δ) (hsub : closedBall x (2 * δ) ⊆ U)
    {y : ℂ} (hy : y ∈ ball x δ) : ‖f y - f x‖ ≤ (1 / δ) * ‖y - x‖ := by
  have hderiv : ∀ z ∈ ball x δ, ‖deriv f z‖ ≤ 1 / δ := by
    intro z hz
    have hsub' : closedBall z δ ⊆ U := by
      refine (closedBall_subset_closedBall' ?_).trans hsub
      have := mem_ball.1 hz; linarith
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ ?_ ?_
    · exact hf.diffContOnCl_ball hsub'
    · intro w hw; exact hb w (hsub' (sphere_subset_closedBall hw))
  have hdiff : ∀ z ∈ ball x δ, DifferentiableAt ℂ f z := by
    intro z hz
    have : z ∈ closedBall x (2 * δ) := by
      have := mem_ball.1 hz; rw [mem_closedBall]; linarith
    refine hf.differentiableAt ?_
    have hzU : ball x (2 * δ) ∈ 𝓝 z := isOpen_ball.mem_nhds (by
      have := mem_ball.1 hz; rw [mem_ball]; linarith)
    exact Filter.mem_of_superset hzU (ball_subset_closedBall.trans hsub)
  exact (convex_ball x δ).norm_image_sub_le_of_norm_deriv_le hdiff hderiv
    (mem_ball_self hδ) hy

/-- Equicontinuity at points of `U` of a family of holomorphic functions bounded by `1` on `U`. -/
lemma equicontinuousAt_of_bounded {ι : Type*} {U : Set ℂ} (hU : IsOpen U) {f : ι → ℂ → ℂ}
    (hf : ∀ i, DifferentiableOn ℂ (f i) U) (hb : ∀ i, ∀ z ∈ U, ‖f i z‖ ≤ 1) {x : ℂ}
    (hx : x ∈ U) : EquicontinuousAt f x := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.1 hU x hx
  set δ := r / 4 with hδdef
  have hδ : 0 < δ := by positivity
  have hsub : closedBall x (2 * δ) ⊆ U :=
    (closedBall_subset_ball (by rw [hδdef]; linarith)).trans hrU
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hmem : ball x (min δ (ε * δ / 2)) ∈ 𝓝 x := ball_mem_nhds x (by positivity)
  filter_upwards [hmem] with y hy i
  have hy1 : y ∈ ball x δ := ball_subset_ball (min_le_left _ _) hy
  have h := lipschitz_of_bounded (hf i) (hb i) hδ hsub hy1
  rw [dist_eq_norm, norm_sub_rev]
  have hyx : ‖y - x‖ < ε * δ / 2 := by
    have := mem_ball.1 hy; rw [dist_eq_norm] at this
    exact this.trans_le (min_le_right _ _)
  calc ‖f i y - f i x‖ ≤ (1 / δ) * ‖y - x‖ := h
    _ ≤ (1 / δ) * (ε * δ / 2) := by gcongr
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- **Montel's theorem** (cluster-point form). -/
theorem montel {U : Set ℂ} (hU : IsOpen U) (f : ℕ → ℂ → ℂ)
    (hf : ∀ k, DifferentiableOn ℂ (f k) U) (hb : ∀ k, ∀ z ∈ U, ‖f k z‖ ≤ 1) :
    ∃ (l : Filter ℕ) (g : ℂ → ℂ), l.NeBot ∧ l ≤ atTop ∧ TendstoLocallyUniformlyOn f g l U := by
  set 𝔖 : Set (Set ℂ) := {K | IsCompact K ∧ K ⊆ U} with h𝔖
  have h𝔖c : ∀ K ∈ 𝔖, IsCompact K := fun K hK => hK.1
  set F : UniformOnFun ℂ ℂ 𝔖 → ℂ → ℂ := fun φ => UniformOnFun.toFun 𝔖 φ with hF
  have hclemb : IsClosedEmbedding (UniformOnFun.ofFun 𝔖 ∘ F) := by
    have : UniformOnFun.ofFun 𝔖 ∘ F = id := by
      funext φ; rfl
    rw [this]; exact IsClosedEmbedding.id
  set u : ℕ → UniformOnFun ℂ ℂ 𝔖 := fun k => UniformOnFun.ofFun 𝔖 (f k) with hu
  set s : Set (UniformOnFun ℂ ℂ 𝔖) := range u with hs
  have heq : ∀ K ∈ 𝔖, EquicontinuousOn (F ∘ ((↑) : s → UniformOnFun ℂ ℂ 𝔖)) K := by
    intro K hK x hx
    have : EquicontinuousAt (fun k : ℕ => f k) x :=
      equicontinuousAt_of_bounded hU hf hb (hK.2 hx)
    have h2 : EquicontinuousAt (F ∘ ((↑) : s → UniformOnFun ℂ ℂ 𝔖)) x := by
      rw [Metric.equicontinuousAt_iff_right] at this ⊢
      intro ε hε
      filter_upwards [this ε hε] with y hy
      rintro ⟨_, k, rfl⟩
      exact hy k
    exact h2.equicontinuousWithinAt K
  have hpt : ∀ K ∈ 𝔖, ∀ x ∈ K, ∃ Q, IsCompact Q ∧ ∀ i ∈ s, F i x ∈ Q := by
    intro K hK x hx
    refine ⟨closedBall 0 1, isCompact_closedBall 0 1, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact mem_closedBall_zero_iff.2 (hb k x (hK.2 hx))
  have hcpt := ArzelaAscoli.isCompact_closure_of_isClosedEmbedding h𝔖c hclemb heq hpt
  obtain ⟨φ, -, hφ⟩ := hcpt.exists_mapClusterPt (f := atTop) (u := u)
    (by
      rw [Filter.le_principal_iff, Filter.mem_map]
      exact Filter.Eventually.of_forall fun k => subset_closure ⟨k, rfl⟩)
  obtain ⟨𝒰, h𝒰le, h𝒰⟩ := mapClusterPt_iff_ultrafilter.1 hφ
  refine ⟨𝒰, F φ, inferInstance, h𝒰le, ?_⟩
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  exact UniformOnFun.tendsto_iff_tendstoUniformlyOn.1 h𝒰 K ⟨hK, hKU⟩

end SteklovRiemann
