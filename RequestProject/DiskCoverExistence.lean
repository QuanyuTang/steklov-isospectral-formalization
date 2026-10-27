module

public import Mathlib
public import RequestProject.NearDiskDomain
public import RequestProject.StarPrimitive
public import RequestProject.RiemannMap
public import RequestProject.BlaschkeFactorization
public import RequestProject.Coalescence
public import RequestProject.CoalescenceRealization

/-!
# Existence of the normalized disk-cover data (the input of Proposition 3.4.1)

`exists_normalizedDiskCover`: if `Q(z) = zⁿ + ∑_{k<n} q_k z^k`, `n ≥ 1`, `|q_k| ≤ s`,
`3 n s 16ⁿ < 1`, then there are `ψ, B` with `IsNormalizedDiskCover Q n ψ B`:
`ψ` is a genuine normalized conformal map of `𝔻` onto the component of `Q⁻¹(𝔻)` containing `0`
and `B = Q ∘ ψ` on `𝔻` is a finite Blaschke product of degree `n` (in the sense of
`SteklovBlaschke.IsFiniteBlaschke`).

Construction (no input assumed):
* `V = Q⁻¹(𝔻)` is open, bounded, star-shaped about `0` and equals the component containing `0`
  (`nearDisk_preimage`);
* zero-free holomorphic functions on `V` have square roots (`exists_sqrt_of_starConvex`);
* the Riemann mapping theorem (`riemann_mapping`, Koebe's proof via Montel and Hurwitz) gives
  `φ : V → 𝔻`, and `ψ = φ⁻¹`;
* `Q ∘ ψ = ∏_l (ψ - ψ(a_l))`, `a_l = φ(r_l)` for the roots `r_l` of `Q` (with multiplicity), is
  proper (`|Q ∘ ψ(w)| → 1` as `|w| → 1`: the sets `{|Q| ≤ δ}` are compact in `V`), hence
  `= η ∏ bfac a_l` (`eq_blaschke_of_proper`).

`exists_paper_diskCover` specializes to the paper's `Q_ε(z) = ε + (λ_*-1) ε P(z/τ_ε)`, and
`prop_3_4_1_unconditional`, `coalescence_realization_unconditional` remove the cover hypothesis
from Proposition 3.4.1 and its link to Proposition 2.3.1.
-/

@[expose] public section

open Set Filter Topology Metric Complex SteklovBlaschke SteklovRiemann PlaneDomain Steklov

noncomputable section

namespace SteklovCoalescence

variable {n : ℕ} {q : Fin n → ℂ} {s : ℝ}

/-- **Properness of `Q ∘ ψ`**: `|Q(ψ(w))| → 1` as `|w| → 1`. -/
theorem proper_comp_inv {Q φ : ℂ → ℂ} (hQ : Continuous Q) {V : Set ℂ}
    (hV : V = Q ⁻¹' ball 0 1) (hVb : Bornology.IsBounded V)
    (hφc : ContinuousOn φ V) (hφs : φ '' V = ball 0 1) {δ : ℝ} (hδ : δ < 1) :
    ∃ ρ < 1, ∀ w : ℂ, ρ < ‖w‖ → ‖w‖ < 1 → δ ≤ ‖Q (Function.invFunOn φ V w)‖ := by
  set K := Q ⁻¹' closedBall 0 δ with hK
  have hKV : K ⊆ V := by
    intro z hz; rw [hV, mem_preimage, mem_ball_zero_iff]
    exact lt_of_le_of_lt (mem_closedBall_zero_iff.1 hz) hδ
  have hKc : IsCompact K :=
    isCompact_of_isClosed_isBounded (isClosed_closedBall.preimage hQ) (hVb.subset hKV)
  have hφK : IsCompact (φ '' K) := hKc.image_of_continuousOn (hφc.mono hKV)
  obtain ⟨ρ, hρ, hsub⟩ := exists_lt_subset_ball hφK.isClosed
    (by rw [← hφs]; exact image_mono hKV)
  refine ⟨ρ, hρ, fun w hw1 hw2 => ?_⟩
  have hwV : w ∈ φ '' V := by rw [hφs]; exact mem_ball_zero_iff.2 hw2
  by_contra hlt
  push_neg at hlt
  have hmem : Function.invFunOn φ V w ∈ K := by
    rw [hK, mem_preimage, mem_closedBall_zero_iff]; exact hlt.le
  have := hsub ⟨_, hmem, Function.invFunOn_eq hwV⟩
  rw [mem_ball_zero_iff] at this
  linarith

/-- **Existence of the normalized disk cover** for nearly monomial polynomials. -/
theorem exists_normalizedDiskCover (hn : 1 ≤ n) (hq : ∀ k, ‖q k‖ ≤ s) (hs0 : 0 ≤ s)
    (hs : 3 * n * s * 16 ^ n < 1) :
    ∃ ψ B : ℂ → ℂ, IsNormalizedDiskCover (polyQ n q) n ψ B := by
  obtain ⟨hVo, hVs, h0, hVb, hVcc⟩ := nearDisk_preimage hq hs0 hs hn
  set Q := polyQ n q with hQdef
  set V := Q ⁻¹' ball 0 1 with hV
  have hVbd : Bornology.IsBounded V := isBounded_ball.subset hVb
  have hsq : HasSqrtProperty V := fun f hf hf0 => exists_sqrt_of_starConvex hVo hVs h0 hf hf0
  obtain ⟨φ, hφd, hφi, hφs, hφ0, hφre, hφim⟩ := riemann_mapping hVo
    (hVs.isPathConnected h0).isConnected.isPreconnected hVbd h0 hsq
  set ψ := Function.invFunOn φ V with hψ
  have hψmem : ∀ w ∈ ball (0 : ℂ) 1, ψ w ∈ V := fun w hw =>
    Function.invFunOn_mem (by rw [← hφs] at hw; exact hw)
  have hφψ : ∀ w ∈ ball (0 : ℂ) 1, φ (ψ w) = w := fun w hw =>
    Function.invFunOn_eq (by rw [← hφs] at hw; exact hw)
  have hψφ : ∀ z ∈ V, ψ (φ z) = z := fun z hz => HolInv.invFunOn_apply_self hφi hz
  have hφder : ∀ z ∈ V, deriv φ z ≠ 0 := fun z hz =>
    HolInv.deriv_ne_zero_of_injOn hVo hφd hφi hz
  have hψd : DifferentiableOn ℂ ψ (ball 0 1) := by
    intro w hw
    have h := HolInv.hasDerivAt_invFunOn hVo hφd hφi (hψmem w hw) (hφder _ (hψmem w hw))
    rw [hφψ w hw] at h
    exact h.differentiableAt.differentiableWithinAt
  have hψi : InjOn ψ (ball 0 1) := by
    intro w hw w' hw' h
    rw [← hφψ w hw, ← hφψ w' hw', h]
  have hψ0 : ψ 0 = 0 := by rw [← hφ0, hψφ 0 h0, hφ0]
  have hψder : deriv ψ 0 = (deriv φ 0)⁻¹ := by
    have h := HolInv.hasDerivAt_invFunOn hVo hφd hφi h0 (hφder 0 h0)
    rw [hφ0] at h
    exact h.deriv
  have hφder0 : deriv φ 0 = ((deriv φ 0).re : ℂ) := by
    apply Complex.ext <;> simp [hφim]
  have hψim : ψ '' ball 0 1 = V := by
    ext z; constructor
    · rintro ⟨w, hw, rfl⟩; exact hψmem w hw
    · intro hz
      refine ⟨φ z, ?_, hψφ z hz⟩
      rw [← hφs]; exact mem_image_of_mem φ hz
  -- roots and their images
  obtain ⟨r, hr⟩ := polyQ_eq_prod n q
  have hrV : ∀ l, r l ∈ V := by
    intro l
    rw [hV, mem_preimage, mem_ball_zero_iff, hQdef, hr]
    rw [Finset.prod_eq_zero (Finset.mem_univ l) (sub_self _), norm_zero]
    exact one_pos
  set a : Fin n → ℂ := fun l => φ (r l) with ha
  have haball : ∀ l, a l ∈ ball (0 : ℂ) 1 := fun l => by
    rw [← hφs]; exact mem_image_of_mem φ (hrV l)
  have hψa : ∀ l, ψ (a l) = r l := fun l => hψφ _ (hrV l)
  have hQψ : ∀ w, Q (ψ w) = ∏ l, (ψ w - ψ (a l)) := by
    intro w; rw [hQdef, hr]; simp only [hψa]
  obtain ⟨η, hη, hηeq⟩ := eq_blaschke_of_proper hψd hψi (fun l => mem_ball_zero_iff.1 (haball l))
    (fun w hw => by rw [← hQψ]; exact mem_ball_zero_iff.1 (hψmem w hw))
    (fun δ hδ => by
      obtain ⟨ρ, hρ, h⟩ := proper_comp_inv (polyQ_continuous n q) hV hVbd hφd.continuousOn
        hφs hδ
      exact ⟨ρ, hρ, fun w h1 h2 => by rw [← hQψ]; exact h w h1 h2⟩)
  refine ⟨ψ, fun z => η * ∏ l, bfac (a l) z, hψd, hψi, hψ0, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hψder, hφder0, ← Complex.ofReal_inv, Complex.ofReal_re]
    exact inv_pos.2 hφre
  · rw [hψder, hφder0, ← Complex.ofReal_inv, Complex.ofReal_im]
  · rw [hψim, hVcc]
  · exact ⟨η, a, hη, fun l => mem_ball_zero_iff.1 (haball l), rfl⟩
  · intro z hz
    rw [hQψ, hηeq z hz]

open SteklovCritical in
/-- **Existence of the cover data for the paper's polynomials.** For every monic `P` of degree
`n ≥ 1` and every `τ` with `τ_ε^n = (λ_* - 1) ε`, there are `ε₀ > 0` and families `ψ_ε, B_ε` such
that `IsNormalizedDiskCover Q_ε n ψ_ε B_ε` holds for all `0 < ε < ε₀`, where
`Q_ε(z) = ε + (λ_* - 1) ε P(z/τ_ε)`. -/
theorem exists_paper_diskCover {P : Polynomial ℂ} (hP : P.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : P.natDegree = n) {τ : ℝ → ℂ} (hτ : ∀ ε, τ ε ^ n = (lamStar - 1) * ε) :
    ∃ ε₀ > (0 : ℝ), ∃ ψ B : ℝ → ℂ → ℂ, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      IsNormalizedDiskCover (paperQ P τ ε) n (ψ ε) (B ε) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set s : ℝ := 1 / (4 * n * 16 ^ n) with hs_def
  have hs0 : 0 < s := by positivity
  have hs : 3 * n * s * 16 ^ n < 1 := by
    rw [hs_def]
    have : (0 : ℝ) < 4 * n * 16 ^ n := by positivity
    field_simp
    nlinarith
  have hgood : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ ψ B : ℂ → ℂ,
      IsNormalizedDiskCover (paperQ P τ ε) n ψ B := by
    filter_upwards [eventually_coeff_small (paperCoeff_tendsto (P := P) hτ) hs0,
      self_mem_nhdsWithin] with ε hε hpos
    rw [paperQ_eq_polyQ hP hn hdeg (ne_of_gt hpos) (hτ ε)]
    exact exists_normalizedDiskCover hn hε hs0.le hs
  obtain ⟨ε₀, hε₀, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hgood
  have hch : ∀ ε : ℝ, ∃ ψ B : ℂ → ℂ, 0 < ε → ε < ε₀ →
      IsNormalizedDiskCover (paperQ P τ ε) n ψ B := by
    intro ε
    by_cases h : 0 < ε ∧ ε < ε₀
    · obtain ⟨ψ, B, hψB⟩ := hsub ⟨h.1, h.2⟩
      exact ⟨ψ, B, fun _ _ => hψB⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose ψ B hψB using hch
  exact ⟨ε₀, hε₀, ψ, B, hψB⟩

open SteklovCritical in
/-- The same, in filter form. -/
theorem exists_paper_diskCover_eventually {P : Polynomial ℂ} (hP : P.Monic) {n : ℕ}
    (hn : 1 ≤ n) (hdeg : P.natDegree = n) {τ : ℝ → ℂ}
    (hτ : ∀ ε, τ ε ^ n = (lamStar - 1) * ε) :
    ∃ ψ B : ℝ → ℂ → ℂ,
      ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsNormalizedDiskCover (paperQ P τ ε) n (ψ ε) (B ε) := by
  obtain ⟨ε₀, hε₀, ψ, B, h⟩ := exists_paper_diskCover hP hn hdeg hτ
  exact ⟨ψ, B, Filter.mem_of_superset (Ioo_mem_nhdsGT hε₀) fun ε hε => h ε hε.1 hε.2⟩

open SteklovCritical in
/-- **Proposition 3.4.1 without the cover hypothesis.** For monic `P` of degree `n ≥ 1` and
`τ_ε^n = (λ_* - 1) ε`, normalized cover data `ψ_ε, B_ε` exist for all small `ε > 0`, and for any
such data all conclusions of Proposition 3.4.1 hold. -/
theorem prop_3_4_1_unconditional {P : Polynomial ℂ} (hP : P.Monic) {n : ℕ} (hn : 1 ≤ n)
    (hdeg : P.natDegree = n) {τ : ℝ → ℂ} (hτ : ∀ ε, τ ε ^ n = (lamStar - 1) * ε) :
    ∃ ψ B : ℝ → ℂ → ℂ,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsNormalizedDiskCover (paperQ P τ ε) n (ψ ε) (B ε)) ∧
      CoalescenceConclusions (𝓝[>] (0 : ℝ)) n ψ B := by
  obtain ⟨ψ, B, h⟩ := exists_paper_diskCover_eventually hP hn hdeg hτ
  exact ⟨ψ, B, h, prop_3_4_1 hP hn hdeg hτ h⟩

open SteklovCritical in
/-- **Proposition 3.4.1 → Proposition 2.3.1 without the cover hypothesis.** -/
theorem coalescence_realization_unconditional {P : Polynomial ℂ} (hP : P.Monic) {n : ℕ}
    (hn : 1 ≤ n) (hdeg : P.natDegree = n) {τ : ℝ → ℂ}
    (hτ : ∀ ε, τ ε ^ n = (lamStar - 1) * ε) :
    ∃ ψ B : ℝ → ℂ → ℂ,
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), IsNormalizedDiskCover (paperQ P τ ε) n (ψ ε) (B ε)) ∧
      ∃ F : ℝ → ℂ → ℂ,
        (∀ᶠ ε in 𝓝[>] (0 : ℝ),
          IsNormalizedRealizing (F ε) (fun z => ‖deriv (B ε) z‖) ∧
          IsDomain (F ε '' ball 0 1) ∧ Bornology.IsBounded (F ε '' ball 0 1) ∧
          SimplyConnectedSpace (F ε '' ball 0 1) ∧
          IsRealAnalyticJordanBoundary (F ε '' ball 0 1) ∧
          steklovSpectrum (F ε '' ball 0 1) =
            weightedSteklovSpectrum (fun z => ‖deriv (B ε) z‖) ∧
          boundaryLength ((fun z : ℂ => ((n : ℝ)⁻¹) • z) '' (F ε '' ball 0 1)) =
            ENNReal.ofReal (2 * Real.pi)) ∧
        ∀ k : ℕ, ∀ η > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ closedBall (0 : ℂ) 1,
          ‖iteratedFDeriv ℝ k (fun w => F ε w - (n : ℂ) * w) z‖ < η := by
  obtain ⟨ψ, B, h⟩ := exists_paper_diskCover_eventually hP hn hdeg hτ
  exact ⟨ψ, B, h, coalescence_realization hP hn hdeg hτ h⟩

end SteklovCoalescence
