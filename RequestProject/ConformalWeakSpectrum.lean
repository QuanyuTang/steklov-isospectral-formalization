module

public import RequestProject.DiskSpectral
public import RequestProject.ConformalPullback

/-!
# The Steklov spectrum of a conformal image as a weak (PDE) spectrum

For `Ω = F(𝔻)` with `F` holomorphic near `𝔻̄`, injective on `𝔻̄` and `F' ≠ 0` on `𝕋`
(the hypotheses of `Prop_2_1_1` as formalized), the smooth-test Steklov spectrum of `Ω` is the
weak `H¹(𝔻)` spectrum of the pulled-back problem `Δu = 0`, `∂_ν u = σ |F'| u`
(`SteklovH1.conformal_weak_spectrum`): every term is a weak eigenvalue, every weak eigenvalue
occurs, and the multiplicity of each eigenvalue in the sequence equals the dimension of its
weak eigenspace.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

noncomputable section

namespace SteklovH1

theorem conformal_weak_spectrum {F : ℂ → ℂ}
    (hF : ∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ F U)
    (hinj : InjOn F (closedBall 0 1)) (hder : ∀ z ∈ sphere (0 : ℂ) 1, deriv F z ≠ 0) :
    ∃ (e : ℕ → H1) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = 0 ∧ Tendsto σ atTop atTop ∧
      (∀ k, e k ≠ 0 ∧ IsWeakSteklovEigen (fun z => ‖deriv F z‖) (σ k) (e k)) ∧
      (∀ τ, (∃ x : H1, x ≠ 0 ∧ IsWeakSteklovEigen (fun z => ‖deriv F z‖) τ x) ↔
        ∃ k, σ k = τ) ∧
      (∀ τ, ∃ S : Submodule ℝ H1,
        (∀ x, x ∈ S ↔ IsWeakSteklovEigen (fun z => ‖deriv F z‖) τ x) ∧
        Module.finrank ℝ S = Set.ncard {k | σ k = τ}) ∧
      (∀ k, Steklov.steklovSpectrum (F '' ball 0 1) k = ENNReal.ofReal (σ k)) := by
  obtain ⟨U, hU, hcb, hFd⟩ := hF
  set ρ : ℂ → ℝ := fun z => ‖deriv F z‖
  have hρ : ContinuousOn ρ (sphere 0 1) := by
    have hc : ContinuousOn (deriv F) U := (hFd.analyticOnNhd hU).deriv.continuousOn
    exact (hc.mono (sphere_subset_closedBall.trans hcb)).norm
  have hpos : ∀ z ∈ sphere (0:ℂ) 1, 0 < ρ z := fun z hz => norm_pos_iff.2 (hder z hz)
  obtain ⟨e, σ, hmono, h0, htend, heig, hiff, -, hdim, hmm⟩ :=
    weighted_disk_spectral_theorem hρ hpos
  refine ⟨e, σ, hmono, h0, htend, heig, hiff, fun τ => ⟨weakEigenspace hρ τ,
    fun x => mem_weakEigenspace hρ hpos, hdim τ⟩, fun k => ?_⟩
  rw [ConformalPullback.prop_2_1_1 F ⟨U, hU, hcb, hFd⟩ hinj hder]
  exact hmm k

/-- `Ω` is the conformal image `G(𝔻)` (`G` holomorphic near `𝔻̄`, injective on `𝔻̄`, `G' ≠ 0` on
`𝕋`) and its Steklov spectrum is the weak `H¹(𝔻)` spectrum of `Δu = 0`, `∂_ν u = σ |G'| u`,
with multiplicities. -/
def HasWeakSteklovSpectrum (Ω : Set ℂ) : Prop :=
  ∃ G : ℂ → ℂ, (∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ G U) ∧
    InjOn G (closedBall 0 1) ∧ (∀ z ∈ sphere (0 : ℂ) 1, deriv G z ≠ 0) ∧ G '' ball 0 1 = Ω ∧
    ∃ (e : ℕ → H1) (σ : ℕ → ℝ), Monotone σ ∧ σ 0 = 0 ∧ Tendsto σ atTop atTop ∧
      (∀ k, e k ≠ 0 ∧ IsWeakSteklovEigen (fun z => ‖deriv G z‖) (σ k) (e k)) ∧
      (∀ τ, (∃ x : H1, x ≠ 0 ∧ IsWeakSteklovEigen (fun z => ‖deriv G z‖) τ x) ↔
        ∃ k, σ k = τ) ∧
      (∀ τ, ∃ S : Submodule ℝ H1,
        (∀ x, x ∈ S ↔ IsWeakSteklovEigen (fun z => ‖deriv G z‖) τ x) ∧
        Module.finrank ℝ S = Set.ncard {k | σ k = τ}) ∧
      (∀ k, Steklov.steklovSpectrum Ω k = ENNReal.ofReal (σ k))

theorem hasWeakSteklovSpectrum_image {G : ℂ → ℂ}
    (hG : ∃ U : Set ℂ, IsOpen U ∧ closedBall 0 1 ⊆ U ∧ DifferentiableOn ℂ G U)
    (hinj : InjOn G (closedBall 0 1)) (hder : ∀ z ∈ sphere (0 : ℂ) 1, deriv G z ≠ 0) :
    HasWeakSteklovSpectrum (G '' ball 0 1) :=
  ⟨G, hG, hinj, hder, rfl, conformal_weak_spectrum hG hinj hder⟩

/-- Isospectral domains with weak spectra have the same weak eigenvalue sequences, hence the same
weak eigenvalues with the same multiplicities. -/
theorem weak_sigma_eq {σ₁ σ₂ : ℕ → ℝ} (h₁ : Monotone σ₁) (h₁0 : σ₁ 0 = 0)
    (h₂ : Monotone σ₂) (h₂0 : σ₂ 0 = 0)
    (h : ∀ k, ENNReal.ofReal (σ₁ k) = ENNReal.ofReal (σ₂ k)) : σ₁ = σ₂ := by
  funext k
  have a1 : 0 ≤ σ₁ k := h₁0 ▸ h₁ (Nat.zero_le k)
  have a2 : 0 ≤ σ₂ k := h₂0 ▸ h₂ (Nat.zero_le k)
  exact (ENNReal.ofReal_eq_ofReal_iff a1 a2).1 (h k)

end SteklovH1
