module

public import RequestProject.MainTheoremH1
public import RequestProject.ConformalWeakSpectrum

/-!
# Theorem 1.1.2 with the weak (PDE) Steklov spectrum

`MainTheoremWeak` is `MainTheoremH1` (hence `MainTheorem`, all five conclusions) together with:
for every domain `Ω_{i,ε}` of the family, `SteklovH1.HasWeakSteklovSpectrum (Ω_{i,ε})`, i.e.
`Ω_{i,ε} = G(𝔻)` for a map `G` holomorphic near `𝔻̄`, injective on `𝔻̄` with `G' ≠ 0` on `𝕋`, and
the Steklov spectrum of `Ω_{i,ε}` is exactly the weak `H¹(𝔻)` spectrum of the pulled-back problem
`∫_𝔻 ⟨∇u, ∇v⟩ = σ ∫_𝕋 |G'| Tu Tv` — every eigenvalue occurs, and the multiplicity of each value in
the sequence equals the dimension of its weak eigenspace.

Combined with (ii) and `SteklovH1.weak_sigma_eq`, the two domains `Ω_{P,ε}`, `Ω_{L,ε}` have the
same weak eigenvalue sequences (`SteklovCoalescence.weak_isospectral`).

The assembly is the same as for `MainTheoremH1` (copied, with the extra conjunct).
-/

@[expose] public section

open Complex Metric Set Filter Topology SteklovBlaschke Steklov PlaneDomain

noncomputable section

/-- **Theorem 1.1.2 with the weak `H¹` Steklov spectrum of every domain.** -/
def MainTheoremWeak : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ Ω : Label → ℝ → Set ℂ,
    -- (i)
    (∀ i ε, 0 < ε → ε < ε₀ →
      IsDomain (Ω i ε) ∧ Bornology.IsBounded (Ω i ε) ∧ SimplyConnectedSpace (Ω i ε) ∧
      IsStrictlyConvexDomain (Ω i ε) ∧ IsRealAnalyticJordanBoundary (Ω i ε)) ∧
    -- (ii)
    (∀ ε, 0 < ε → ε < ε₀ → steklovSpectrum (Ω Label.P ε) = steklovSpectrum (Ω Label.L ε)) ∧
    -- (iii)
    (∀ i j ε ε', 0 < ε → ε < ε₀ → 0 < ε' → ε' < ε₀ → (i, ε) ≠ (j, ε') →
      ¬ Congruent (Ω i ε) (Ω j ε')) ∧
    (∀ i ε, 0 < ε → ε < ε₀ → ¬ HasOrientationReversingSymmetry (Ω i ε)) ∧
    -- (iv)
    (∀ i ε, 0 < ε → ε < ε₀ → boundaryLength (Ω i ε) = ENNReal.ofReal (2 * Real.pi)) ∧
    -- (ii-H¹): equal `H¹` variational Steklov spectra, with multiplicities
    (∀ ε, 0 < ε → ε < ε₀ →
      SteklovH1.h1SteklovSpectrum (Ω Label.P ε) = SteklovH1.h1SteklovSpectrum (Ω Label.L ε)) ∧
    -- identification of the two spectra for every domain of the family
    (∀ i ε, 0 < ε → ε < ε₀ → steklovSpectrum (Ω i ε) = SteklovH1.h1SteklovSpectrum (Ω i ε)) ∧
    -- weak `H¹(𝔻)` (PDE) spectrum of every domain, with multiplicities
    (∀ i ε, 0 < ε → ε < ε₀ → SteklovH1.HasWeakSteklovSpectrum (Ω i ε)) ∧
    -- (v)
    (∃ F : Label → ℝ → ℂ → ℂ,
      (∀ i ε, 0 < ε → ε < ε₀ → IsNormalizedConformalMap (F i ε) (Ω i ε)) ∧
      ∀ i, TendstoIdInCInfty (F i))

theorem mainTheoremH1_of_mainTheoremWeak (h : MainTheoremWeak) : MainTheoremH1 := by
  obtain ⟨ε₀, hε₀, Ω, h1, h2, h3, h3', h4, h5, h6, -, h7⟩ := h
  exact ⟨ε₀, hε₀, Ω, h1, h2, h3, h3', h4, h5, h6, h7⟩

namespace SteklovCoalescence

open SteklovCritical

theorem mainTheoremWeak_of_cover_data {n : ℕ} (hn : 1 ≤ n) (P : Label → Polynomial ℂ)
    (hP : ∀ i, (P i).Monic) (hdeg : ∀ i, (P i).natDegree = n) (τ : Label → ℝ → ℂ)
    (hτ : ∀ i ε, τ i ε ^ n = (lamStar - 1) * ε) (ψ B : Label → ℝ → ℂ → ℂ)
    (hcov : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      IsNormalizedDiskCover (paperQ (P i) (τ i) ε) n (ψ i ε) (B i ε))
    (hspec : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      weightedSteklovSpectrum (fun z => ‖deriv (B Label.P ε) z‖) =
        weightedSteklovSpectrum (fun z => ‖deriv (B Label.L ε) z‖))
    (hiii : ∀ F : Label → ℝ → ℂ → ℂ, (∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        IsNormalizedRealizing (F i ε) (fun z => ‖deriv (B i ε) z‖)) →
      ∃ ε₁ > (0 : ℝ), ∀ i j ε ε', 0 < ε → ε < ε₁ → 0 < ε' → ε' < ε₁ →
        ((i, ε) ≠ (j, ε') → ¬ Congruent ((fun w => (((n : ℝ)⁻¹ : ℝ) : ℂ) * F i ε w) '' ball 0 1)
          ((fun w => (((n : ℝ)⁻¹ : ℝ) : ℂ) * F j ε' w) '' ball 0 1)) ∧
        ¬ HasOrientationReversingSymmetry
          ((fun w => (((n : ℝ)⁻¹ : ℝ) : ℂ) * F i ε w) '' ball 0 1)) :
    MainTheoremWeak := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hc : (0 : ℝ) < (n : ℝ)⁻¹ := inv_pos.2 hn0
  choose F hFgood hFconv using fun i => coalescence_realization (hP i) hn (hdeg i) (hτ i) (hcov i)
  set c : ℂ := (((n : ℝ)⁻¹ : ℝ) : ℂ) with hc_def
  set G : Label → ℝ → ℂ → ℂ := fun i ε w => c * F i ε w with hG
  set Ω : Label → ℝ → Set ℂ := fun i ε => G i ε '' ball 0 1 with hΩ
  -- positivity of the weights on the circle
  have hpos : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ z ∈ sphere (0 : ℂ) 1, 0 < ‖deriv (B i ε) z‖ := by
    intro i
    filter_upwards [hcov i] with ε h z hz
    obtain ⟨t, rfl⟩ := circle_surj (by simpa using hz)
    exact (blaschke_weight_posAnalytic hn h.2.2.2.2.2.2.1).2 t
  -- convergence of the rescaled maps
  have hGconv : ∀ i, TendstoIdInCInfty (G i) := by
    intro i
    refine rescale_tendsto hc ((hFgood i).mono fun ε h => h.1.1) ?_
    intro k η hη
    have := hFconv i k η hη
    first
      | simpa [inv_inv] using this
      | simpa [inv_inv, Function.comp_def] using this
  -- strict convexity
  have hconvex : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsStrictlyConvexDomain (Ω i ε) := by
    intro i
    refine SteklovConvexity.eventually_strictConvex_of_C2 (c := 1) one_pos ?_ ?_
    · filter_upwards [hFgood i] with ε h
      obtain ⟨U, hU, hcb, hd⟩ := h.1.1
      exact ⟨U, hU, hcb, hd.const_mul _⟩
    · intro k η hη
      simpa using hGconv i k η hη
  -- everything holds eventually
  have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i : Label,
      IsNormalizedConformalMap (G i ε) (Ω i ε) ∧ IsDomain (Ω i ε) ∧
      Bornology.IsBounded (Ω i ε) ∧ SimplyConnectedSpace (Ω i ε) ∧
      IsStrictlyConvexDomain (Ω i ε) ∧ IsRealAnalyticJordanBoundary (Ω i ε) ∧
      boundaryLength (Ω i ε) = ENNReal.ofReal (2 * Real.pi) := by
    have hlab : ∀ i : Label, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        IsNormalizedConformalMap (G i ε) (Ω i ε) ∧ IsDomain (Ω i ε) ∧
        Bornology.IsBounded (Ω i ε) ∧ SimplyConnectedSpace (Ω i ε) ∧
        IsStrictlyConvexDomain (Ω i ε) ∧ IsRealAnalyticJordanBoundary (Ω i ε) ∧
        boundaryLength (Ω i ε) = ENNReal.ofReal (2 * Real.pi) := by
      intro i
      filter_upwards [hFgood i, hpos i, hconvex i] with ε h hp hcv
      obtain ⟨r1, r2, r3, r4, r5⟩ := rescale_props hc h.1 hp
      refine ⟨r1, r2, r3, r4, hcv, r5, ?_⟩
      have hlen := h.2.2.2.2.2.2
      simp only [hΩ, hG, rescale_image]
      convert hlen using 3
    filter_upwards [hlab Label.P, hlab Label.L] with ε hP' hL' i
    cases i
    · exact hP'
    · exact hL'
  have hiso : ∀ᶠ ε in 𝓝[>] (0 : ℝ), steklovSpectrum (Ω Label.P ε) = steklovSpectrum (Ω Label.L ε) := by
    filter_upwards [hFgood Label.P, hFgood Label.L, hpos Label.P, hpos Label.L, hspec]
      with ε hP' hL' hpP hpL hs
    simp only [hΩ, hG, rescale_image]
    exact Prop231Reduction.isospectral_of_weighted hP'.1.1 hL'.1.1 hP'.1.2.1 hL'.1.2.1
      (fun z hz => ⟨hP'.1.2.2.2.2.2 z hz, hpP z hz⟩) (fun z hz => ⟨hL'.1.2.2.2.2.2 z hz, hpL z hz⟩)
      hs hc
  have hc' : c ≠ 0 := by
    rw [hc_def]; exact Complex.ofReal_ne_zero.2 hc.ne'
  have hbridge : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i,
      steklovSpectrum (Ω i ε) = SteklovH1.h1SteklovSpectrum (Ω i ε) := by
    have hlab : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        steklovSpectrum (Ω i ε) = SteklovH1.h1SteklovSpectrum (Ω i ε) := by
      intro i
      filter_upwards [hFgood i, hpos i] with ε h hp
      obtain ⟨U, hU, hcb, hd⟩ := h.1.1
      refine SteklovH1.steklovSpectrum_image_eq_h1 hU hcb (hd.const_mul c) ?_ ?_
      · intro x hx y hy hxy
        exact h.1.2.1 hx hy (mul_left_cancel₀ hc' hxy)
      · intro z hz
        have hdz : DifferentiableAt ℂ (F i ε) z :=
          hd.differentiableAt (hU.mem_nhds (hcb (sphere_subset_closedBall hz)))
        rw [deriv_const_mul c hdz]
        refine mul_ne_zero hc' ?_
        intro h0
        have hρ : ‖deriv (F i ε) z‖ = ‖deriv (B i ε) z‖ := h.1.2.2.2.2.2 z hz
        have hpz := hp z hz
        rw [← hρ, h0, norm_zero] at hpz
        exact lt_irrefl 0 hpz
    filter_upwards [hlab Label.P, hlab Label.L] with ε hP hL i
    cases i
    · exact hP
    · exact hL
  have hweak : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, SteklovH1.HasWeakSteklovSpectrum (Ω i ε) := by
    have hlab : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), SteklovH1.HasWeakSteklovSpectrum (Ω i ε) := by
      intro i
      filter_upwards [hFgood i, hpos i] with ε h hp
      obtain ⟨U, hU, hcb, hd⟩ := h.1.1
      refine SteklovH1.hasWeakSteklovSpectrum_image ⟨U, hU, hcb, hd.const_mul c⟩ ?_ ?_
      · intro x hx y hy hxy
        exact h.1.2.1 hx hy (mul_left_cancel₀ hc' hxy)
      · intro z hz
        have hdz : DifferentiableAt ℂ (F i ε) z :=
          hd.differentiableAt (hU.mem_nhds (hcb (sphere_subset_closedBall hz)))
        rw [deriv_const_mul c hdz]
        refine mul_ne_zero hc' ?_
        intro h0
        have hρ : ‖deriv (F i ε) z‖ = ‖deriv (B i ε) z‖ := h.1.2.2.2.2.2 z hz
        have hpz := hp z hz
        rw [← hρ, h0, norm_zero] at hpz
        exact lt_irrefl 0 hpz
    filter_upwards [hlab Label.P, hlab Label.L] with ε hP hL i
    cases i
    · exact hP
    · exact hL
  obtain ⟨ε₀, hε₀, hsub⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset).1 (hall.and (hiso.and (hbridge.and hweak)))
  obtain ⟨ε₁, hε₁, h3⟩ := hiii F (fun i => (hFgood i).mono fun ε h => h.1)
  have hsub' : ∀ ε, 0 < ε → ε < min ε₀ ε₁ → _ := fun ε h0 h1 =>
    hsub ⟨h0, lt_of_lt_of_le h1 (min_le_left _ _)⟩
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, Ω, fun i ε h0 h1 => ?_, fun ε h0 h1 => (hsub' ε h0 h1).2.1,
    fun i j ε ε' h0 h1 h0' h1' hne => (h3 i j ε ε' h0 (lt_of_lt_of_le h1 (min_le_right _ _)) h0'
      (lt_of_lt_of_le h1' (min_le_right _ _))).1 hne,
    fun i ε h0 h1 => (h3 i i ε ε h0 (lt_of_lt_of_le h1 (min_le_right _ _)) h0
      (lt_of_lt_of_le h1 (min_le_right _ _))).2,
    fun i ε h0 h1 => ((hsub' ε h0 h1).1 i).2.2.2.2.2.2,
    fun ε h0 h1 => (((hsub' ε h0 h1).2.2.1 Label.P).symm.trans ((hsub' ε h0 h1).2.1)).trans
      ((hsub' ε h0 h1).2.2.1 Label.L),
    fun i ε h0 h1 => (hsub' ε h0 h1).2.2.1 i, fun i ε h0 h1 => (hsub' ε h0 h1).2.2.2 i, G,
    fun i ε h0 h1 => ((hsub' ε h0 h1).1 i).1, hGconv⟩
  obtain ⟨-, a1, a2, a3, a4, a5, -⟩ := (hsub' ε h0 h1).1 i
  exact ⟨a1, a2, a3, a4, a5⟩


open SteklovCritical Degree7 DiskAut CongrRigid FamilyNoncongr

theorem mainTheoremWeak_proved : MainTheoremWeak := by
  set s : ℂ := I * Real.sqrt 7
  have hs : s ^ 2 = -7 := i_sqrt7_sq.1
  have hs' : (-s) ^ 2 = -7 := neg_sq_seven hs
  obtain ⟨aP, haP0, haP, hmP, hdP, -, -⟩ := exists_monic_normalization hs
  obtain ⟨aM, haM0, haM, hmM, hdM, -, -⟩ := exists_monic_normalization hs'
  choose τ hτ using fun ε : ℝ =>
    IsAlgClosed.exists_pow_nat_eq ((lamStar - 1) * (ε : ℂ)) (by norm_num : 0 < 7)
  have hτ0 : ∀ ε : ℝ, 0 < ε → τ ε ≠ 0 := by
    intro ε hε h
    have h1 := hτ ε
    rw [h, zero_pow (by norm_num)] at h1
    exact mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast hε.ne') h1.symm
  let P : Label → Polynomial ℂ := fun i => match i with
    | Label.P => monicP s aP
    | Label.L => monicP (-s) aM
  have hPm : ∀ i, (P i).Monic := fun i => by cases i <;> assumption
  have hPd : ∀ i, (P i).natDegree = 7 := fun i => by cases i <;> assumption
  choose ψ B hcov using fun i =>
    exists_paper_diskCover_eventually (hPm i) (by norm_num : 1 ≤ 7) (hPd i) hτ
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 / 10 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
  refine mainTheoremWeak_of_cover_data (n := 7) (by norm_num) P hPm hPd (fun _ => τ) (fun _ => hτ)
    ψ B hcov ?_ ?_
  · filter_upwards [hcov Label.P, hcov Label.L, self_mem_nhdsWithin, hsmall]
      with ε h1 h2 hε0 hε1
    exact FamilyIso.family_spectra_eq hs haP haM hτ hε0 hε1 h1 h2
  · intro F hF
    obtain ⟨ε₁P, hε₁P, factsP⟩ := family_facts hs haP hτ
    obtain ⟨ε₁L, hε₁L, factsL⟩ := family_facts hs' haM hτ
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (∀ i, IsNormalizedRealizing (F i ε)
        (fun z => ‖deriv (B i ε) z‖) ∧
        IsNormalizedDiskCover (paperQ (P i) τ ε) 7 (ψ i ε) (B i ε)) ∧ ε < ε₁P ∧ ε < ε₁L := by
      have hi : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), IsNormalizedRealizing (F i ε)
          (fun z => ‖deriv (B i ε) z‖) ∧
          IsNormalizedDiskCover (paperQ (P i) τ ε) 7 (ψ i ε) (B i ε) :=
        fun i => (hF i).and (hcov i)
      filter_upwards [hi Label.P, hi Label.L, nhdsWithin_le_nhds (gt_mem_nhds hε₁P),
        nhdsWithin_le_nhds (gt_mem_nhds hε₁L)] with ε h1 h2 h3 h4
      exact ⟨fun i => by cases i <;> assumption, h3, h4⟩
    obtain ⟨ε₁, hε₁, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
    have hcv : ∀ i ε, 0 < ε → ε < ε₁ → critSet (B i ε) = {(ε : ℂ), lamStar * ε} := by
      intro i ε h0 h1
      obtain ⟨hall, hP', hL'⟩ := hsub ⟨h0, h1⟩
      cases i
      · exact (factsP ε h0 hP' _ _ (hall Label.P).2).2
      · exact (factsL ε h0 hL' _ _ (hall Label.L).2).2
    have c7 : ((7 : ℕ) : ℝ)⁻¹ ≠ 0 := by norm_num
    refine ⟨ε₁, hε₁, fun i j ε ε' h0 h1 h0' h1' => ⟨fun hne => ?_, ?_⟩⟩
    · obtain ⟨hall, hP', hL'⟩ := hsub ⟨h0, h1⟩
      obtain ⟨hall', -, -⟩ := hsub ⟨h0', h1'⟩
      refine not_congruent_of_critSet (hall i).2.2.2.2.2.2.2.1 (hall' j).2.2.2.2.2.2.2.1
        (hall i).1 (hall' j).1 c7 h0 h0' (hcv i ε h0 h1) (hcv j ε' h0' h1') ?_
      rintro rfl φ hφ hrel
      have hij : i ≠ j := fun h => hne (by rw [h])
      set δ : ℂ := (lamStar - 1) * ε
      have hδ : δ ≠ 0 := mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast h0.ne')
      have hcP := (hall Label.P).2
      have hcL := (hall Label.L).2
      have fP := cover_form hs haP hcP
      have fL := cover_form hs' haM hcL
      have hκP : aP / τ ε ≠ 0 := div_ne_zero haP0 (hτ0 ε h0)
      have hκL : aM / τ ε ≠ 0 := div_ne_zero haM0 (hτ0 ε h0)
      cases i <;> cases j
      · exact hij rfl
      · refine no_disk_equiv hs hκP hκL hcP.1 hcP.2.1 hcL.1 hcL.2.1 hφ
          (factsP ε h0 hP' _ _ hcP).1 (fun z hz => ?_)
        have := hrel z hz.le
        rw [fP z hz, fL _ (diskAut_maps hφ hz)] at this
        exact mul_left_cancel₀ hδ (add_left_cancel this)
      · refine no_disk_equiv hs' hκL hκP hcL.1 hcL.2.1 hcP.1 hcP.2.1 hφ
          (factsL ε h0 hL' _ _ hcL).1 (fun z hz => ?_)
        have := hrel z hz.le
        rw [fL z hz, fP _ (diskAut_maps hφ hz)] at this
        rw [neg_neg]
        exact mul_left_cancel₀ hδ (add_left_cancel this)
      · exact hij rfl
    · obtain ⟨hall, -, -⟩ := hsub ⟨h0, h1⟩
      exact not_reversing_of_critSet (hall i).2.2.2.2.2.2.2.1 (hall i).1 c7 h0 (hcv i ε h0 h1)

/-- Two Steklov-isospectral domains whose spectra are realized as weak `H¹` spectra have the same
weak eigenvalue sequences (hence the same weak eigenvalues with the same multiplicities, since
each multiplicity is the number of repetitions in the sequence). -/
theorem weak_isospectral {Ω₁ Ω₂ : Set ℂ} (h : steklovSpectrum Ω₁ = steklovSpectrum Ω₂)
    {σ₁ σ₂ : ℕ → ℝ} (h₁ : Monotone σ₁) (h₁0 : σ₁ 0 = 0) (h₂ : Monotone σ₂) (h₂0 : σ₂ 0 = 0)
    (hs₁ : ∀ k, steklovSpectrum Ω₁ k = ENNReal.ofReal (σ₁ k))
    (hs₂ : ∀ k, steklovSpectrum Ω₂ k = ENNReal.ofReal (σ₂ k)) : σ₁ = σ₂ :=
  SteklovH1.weak_sigma_eq h₁ h₁0 h₂ h₂0 (fun k => by rw [← hs₁, ← hs₂, h])

end SteklovCoalescence

end
