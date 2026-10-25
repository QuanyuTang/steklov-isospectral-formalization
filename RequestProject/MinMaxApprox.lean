module

public import Mathlib

/-!
# Approximation of finite-dimensional test spaces in a Rayleigh quotient

Abstract lemma used for the `H¹`-versus-smooth min–max comparison. Let `A, B` be continuous
linear maps on a normed space `X`, and let `j : S → X` be a linear map with dense range. If `W`
is an `n`-dimensional subspace on which `B` is injective and `‖Ax‖² ≤ M ‖Bx‖²`, then for every
`M' > M` there are `s₁, …, sₙ ∈ S` with `‖A(j(∑ cᵢ sᵢ))‖² < M' ‖B(j(∑ cᵢ sᵢ))‖²` for **every**
nonzero coefficient vector `c`. In particular `B ∘ j` is injective on the span of the `sᵢ`.

The proof is uniform on the unit sphere of coefficients (compactness, tube lemma) and uses
homogeneity; pointwise approximation of individual functions would not suffice.
-/

@[expose] public section

open Filter Topology Set

noncomputable section

namespace SteklovH1

variable {X YA YB S : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup YA] [NormedSpace ℝ YA] [NormedAddCommGroup YB] [NormedSpace ℝ YB]
  [AddCommGroup S] [Module ℝ S]

theorem exists_family_ratio_lt (A : X →L[ℝ] YA) (B : X →L[ℝ] YB) (j : S →ₗ[ℝ] X)
    (hj : DenseRange j) (W : Submodule ℝ X) {n : ℕ} (hW : Module.finrank ℝ W = n)
    (hB : ∀ x ∈ W, x ≠ 0 → B x ≠ 0) {M M' : ℝ}
    (hM : ∀ x ∈ W, ‖A x‖ ^ 2 ≤ M * ‖B x‖ ^ 2) (hMM' : M < M') :
    ∃ s : Fin n → S, ∀ c : Fin n → ℝ, c ≠ 0 →
      ‖A (j (∑ i, c i • s i))‖ ^ 2 < M' * ‖B (j (∑ i, c i • s i))‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨fun i => i.elim0, fun c hc => absurd (Subsingleton.elim c 0) hc⟩
  haveI : FiniteDimensional ℝ W := Module.finite_of_finrank_pos (hW ▸ hn)
  let bW := Module.finBasisOfFinrankEq ℝ W hW
  let b : Fin n → X := fun i => (bW i : X)
  let Φ : (Fin n → X) → (Fin n → ℝ) → X := fun v c => ∑ i, c i • v i
  let P : (Fin n → X) → (Fin n → ℝ) → Prop :=
    fun v c => ‖A (Φ v c)‖ ^ 2 < M' * ‖B (Φ v c)‖ ^ 2
  have hΦc : Continuous fun p : (Fin n → X) × (Fin n → ℝ) => Φ p.1 p.2 := by
    simp only [Φ]
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact ((continuous_apply i).comp continuous_snd).smul ((continuous_apply i).comp continuous_fst)
  have hopen : IsOpen {p : (Fin n → X) × (Fin n → ℝ) | P p.1 p.2} := by
    refine isOpen_lt ?_ ?_
    · exact ((A.continuous.comp hΦc).norm).pow 2
    · exact continuous_const.mul (((B.continuous.comp hΦc).norm).pow 2)
  have hK : IsCompact (Metric.sphere (0 : Fin n → ℝ) 1) := isCompact_sphere 0 1
  have hbase : ∀ c ∈ Metric.sphere (0 : Fin n → ℝ) 1, P b c := by
    intro c hc
    have hc0 : c ≠ 0 := by
      intro h; rw [h, mem_sphere_zero_iff_norm, norm_zero] at hc; exact zero_ne_one hc
    have hmem : Φ b c = ((∑ i, c i • bW i : W) : X) := by
      simp [Φ, b]
    have hne : (∑ i, c i • bW i : W) ≠ 0 := by
      intro h
      have := Fintype.linearIndependent_iff.1 bW.linearIndependent c h
      exact hc0 (funext this)
    have hx : Φ b c ∈ W := by rw [hmem]; exact Submodule.coe_mem _
    have hx0 : Φ b c ≠ 0 := by
      rw [hmem]; exact fun h => hne (Subtype.ext h)
    have hBpos : 0 < ‖B (Φ b c)‖ ^ 2 := by
      have := hB _ hx hx0
      positivity
    calc ‖A (Φ b c)‖ ^ 2 ≤ M * ‖B (Φ b c)‖ ^ 2 := hM _ hx
      _ < M' * ‖B (Φ b c)‖ ^ 2 := mul_lt_mul_of_pos_right hMM' hBpos
  have hev : ∀ᶠ v in 𝓝 b, ∀ c ∈ Metric.sphere (0 : Fin n → ℝ) 1, P v c := by
    refine hK.eventually_forall_of_forall_eventually (fun c hc => ?_)
    exact hopen.mem_nhds (hbase c hc)
  have hd : DenseRange (fun (s : Fin n → S) (i : Fin n) => j (s i)) :=
    DenseRange.piMap (fun _ => hj)
  obtain ⟨U, hUsub, hUo, hbU⟩ := mem_nhds_iff.1 hev
  obtain ⟨s, hs⟩ := hd.exists_mem_open hUo ⟨b, hbU⟩
  refine ⟨s, fun c hc => ?_⟩
  have hPs := hUsub hs
  have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
  set c' : Fin n → ℝ := ‖c‖⁻¹ • c with hc'
  have hc'mem : c' ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
    rw [mem_sphere_zero_iff_norm, hc', norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ hcn.ne']
  have key := hPs c' hc'mem
  have hsum : j (∑ i, c i • s i) = ‖c‖ • Φ (fun i => j (s i)) c' := by
    simp only [Φ, map_sum, map_smul, Finset.smul_sum, hc', Pi.smul_apply, smul_eq_mul,
      ← smul_smul, smul_inv_smul₀ hcn.ne']
  rw [hsum, map_smul, map_smul, norm_smul, norm_smul, mul_pow, mul_pow, Real.norm_eq_abs,
    abs_of_pos hcn]
  have hc2 : 0 < ‖c‖ ^ 2 := by positivity
  nlinarith [mul_lt_mul_of_pos_left key hc2]

end SteklovH1
