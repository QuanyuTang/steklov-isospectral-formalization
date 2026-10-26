module

public import RequestProject.BranchPointRemoval

/-!
# Min–max transfer with test functions singular at interior branch points

`minMax_le_of_singular_transfer`: if a linear map `T` sends smooth test functions to functions
that are continuous on the plane and smooth off a fixed finite subset `S` of the open unit disk,
preserving the Dirichlet energy on `𝔻` and the weighted boundary mass, then the weighted
Steklov eigenvalues `σ_k(𝔻, ρ)` (smooth-test-function min–max) are bounded by the min–max values
of the source problem.  This removes the smoothness requirement on transplanted functions at
branch points (the role of Proposition 2.2.1 in the paper), using the zero capacity of points
(`BranchPointRemoval.lean`).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace SteklovBranch

open Steklov

/-- The unit circle parametrization. -/
def circ (t : ℝ) : ℂ := Complex.exp (t * Complex.I)

theorem continuous_circ : Continuous circ := by
  unfold circ; fun_prop

theorem norm_circ (t : ℝ) : ‖circ t‖ = 1 := Complex.norm_exp_ofReal_mul_I t

/-- The weighted arc-length measure on the parameter interval. -/
def circMeasure (ρ : ℂ → ℝ) : Measure ℝ :=
  (volume.restrict (Ioc 0 (2 * π))).withDensity (fun t => ENNReal.ofReal (ρ (circ t)))

theorem weightedBoundaryMass_congr' (ρ : ℂ → ℝ) {g h : ℂ → ℝ}
    (hgh : ∀ z, ‖z‖ = 1 → g z = h z) :
    weightedBoundaryMass ρ g = weightedBoundaryMass ρ h := by
  unfold weightedBoundaryMass
  refine lintegral_congr fun t => ?_
  rw [hgh _ (Complex.norm_exp_ofReal_mul_I t)]

theorem weightedBoundaryMass_eq_eLpNorm (hρ : Continuous fun t : ℝ => ρ (circ t)) (g : ℂ → ℝ)
    (hg : Continuous fun t => g (circ t)) :
    weightedBoundaryMass ρ g = eLpNorm (fun t => g (circ t)) 2 (circMeasure ρ) ^ 2 := by
  rw [eLpNorm_two_sq _ _ hg.aestronglyMeasurable, circMeasure,
    lintegral_withDensity_eq_lintegral_mul]
  · unfold weightedBoundaryMass
    refine lintegral_congr fun t => ?_
    simp only [Pi.mul_apply, circ]
    ring
  · exact ENNReal.measurable_ofReal.comp hρ.measurable
  · exact (hg.enorm.measurable).pow_const 2

theorem weightedBoundaryMass_ne_top (hρ : Continuous fun t : ℝ => ρ (circ t)) {g : ℂ → ℝ}
    (hg : Continuous fun t => g (circ t)) :
    weightedBoundaryMass ρ g ≠ ⊤ := by
  have hc : Continuous fun t : ℝ => ‖g (circ t)‖ ^ 2 * ρ (circ t) :=
    (hg.norm.pow 2).mul hρ
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 2 * π)).exists_bound_of_continuousOn
    hc.continuousOn
  unfold weightedBoundaryMass
  refine ne_top_of_le_ne_top (b := ∫⁻ t in Ioc 0 (2 * π), ENNReal.ofReal C) ?_ ?_
  · simp [lintegral_const, ENNReal.mul_eq_top]
  · refine setLIntegral_mono measurable_const fun t ht => ?_
    have := hC t (Ioc_subset_Icc_self ht)
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    exact (le_abs_self _).trans (by simpa [circ] using this)

/-- A positive definite `ℝ≥0∞`-valued seminorm on `ℝⁿ` dominates the `ℓ¹` norm. -/
theorem exists_sum_le_of_seminorm {n : ℕ} (N : (Fin n → ℝ) → ℝ≥0∞) (htop : ∀ c, N c ≠ ⊤)
    (hadd : ∀ c c', N (c + c') ≤ N c + N c') (hsmul : ∀ (a : ℝ) c, N (a • c) = ‖a‖ₑ * N c)
    (hpos : ∀ c, c ≠ 0 → N c ≠ 0) : ∃ K : ℝ≥0, ∀ c, ∑ i, ‖c i‖ₑ ≤ K * N c := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨0, fun c => by simp⟩
  set p : (Fin n → ℝ) → ℝ := fun c => (N c).toReal with hp
  have hN0 : N 0 = 0 := by simpa using hsmul 0 0
  have padd : ∀ c c', p (c + c') ≤ p c + p c' := fun c c' => by
    simp only [hp]; rw [← ENNReal.toReal_add (htop c) (htop c')]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨htop c, htop c'⟩) (hadd c c')
  have psmul : ∀ (a : ℝ) c, p (a • c) = |a| * p c := fun a c => by
    simp only [hp, hsmul, ENNReal.toReal_mul, toReal_enorm, Real.norm_eq_abs]
  have hsum : ∀ (s : Finset (Fin n)) (d : Fin n → Fin n → ℝ),
      p (∑ i ∈ s, d i) ≤ ∑ i ∈ s, p (d i) := by
    intro s d
    induction s using Finset.induction_on with
    | empty => simp [hp, hN0]
    | insert a s has ih =>
      rw [Finset.sum_insert has, Finset.sum_insert has]
      exact (padd _ _).trans (by linarith)
  set C := ∑ i, p (Pi.single i 1) with hC
  have pbound : ∀ d, p d ≤ C * ‖d‖ := by
    intro d
    have hd : d = ∑ i, d i • (Pi.single i 1 : Fin n → ℝ) := by
      ext j; simp [Finset.sum_apply, Pi.single_apply]
    calc p d = p (∑ i, d i • (Pi.single i 1 : Fin n → ℝ)) := by rw [← hd]
      _ ≤ ∑ i, p (d i • (Pi.single i 1 : Fin n → ℝ)) := hsum _ _
      _ = ∑ i, |d i| * p (Pi.single i 1) := by simp_rw [psmul]
      _ ≤ ∑ i, ‖d‖ * p (Pi.single i 1) := by
          gcongr with i
          exact norm_le_pi_norm d i
      _ = C * ‖d‖ := by rw [← Finset.mul_sum]; ring
  have pcont : Continuous p := by
    have hlip : ∀ c c', |p c - p c'| ≤ C * dist c c' := by
      intro c c'
      rw [dist_eq_norm, abs_le]
      have h1 := padd c' (c - c'); have h2 := padd c (c' - c)
      simp only [add_sub_cancel] at h1 h2
      have h3 : p (c' - c) = p (c - c') := by
        rw [← neg_sub, ← neg_one_smul ℝ (c - c'), psmul]; simp
      have h4 := pbound (c - c')
      constructor <;> linarith
    have hC0 : 0 ≤ C := Finset.sum_nonneg fun i _ => ENNReal.toReal_nonneg
    refine LipschitzWith.continuous (K := C.toNNReal)
      (LipschitzWith.of_dist_le_mul fun c c' => ?_)
    rw [Real.dist_eq, Real.coe_toNNReal _ hC0]; exact hlip c c'
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨c0, hc0, hmin⟩ := (isCompact_sphere (0 : Fin n → ℝ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) pcont.continuousOn
  have hc0ne : c0 ≠ 0 := by
    rintro rfl; simp at hc0
  set m := p c0
  have hm : 0 < m := ENNReal.toReal_pos (hpos c0 hc0ne) (htop c0)
  have hlow : ∀ c, m * ‖c‖ ≤ p c := by
    intro c
    by_cases hc : c = 0
    · simp [hc, hp, hN0]
    have hcn : 0 < ‖c‖ := norm_pos_iff.2 hc
    have hu : ‖c‖⁻¹ • c ∈ Metric.sphere (0 : Fin n → ℝ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hcn.ne']
    have := hmin hu
    simp only [Set.mem_setOf_eq] at this
    rw [psmul, abs_inv, abs_norm] at this
    rw [mul_comm]
    calc ‖c‖ * m ≤ ‖c‖ * (‖c‖⁻¹ * p c) := by gcongr
      _ = p c := by field_simp
  refine ⟨(n / m : ℝ).toNNReal, fun c => ?_⟩
  have h1 : ∑ i, ‖c i‖ₑ = ENNReal.ofReal (∑ i, |c i|) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)]
    simp [← ofReal_norm_eq_enorm]
  have h2 : ∑ i, |c i| ≤ n * ‖c‖ := by
    calc ∑ i, |c i| ≤ ∑ _i : Fin n, ‖c‖ := Finset.sum_le_sum fun i _ => norm_le_pi_norm c i
      _ = n * ‖c‖ := by simp
  rw [h1, ← ENNReal.ofReal_toReal (htop c), ENNReal.ofReal, ENNReal.ofReal, ← ENNReal.coe_mul,
    ENNReal.coe_le_coe, ← Real.toNNReal_mul (by positivity)]
  apply Real.toNNReal_le_toNNReal
  calc ∑ i, |c i| ≤ n * ‖c‖ := h2
    _ ≤ n / m * p c := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hm]
        nlinarith [hlow c, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]

theorem corr_comb_eq (S : Finset ℂ) (r : ℝ) {n : ℕ} (f : Fin n → ℂ → ℝ) (c : Fin n → ℝ) :
    corr S r (∑ i, c i • f i) = (∑ i, c i • f i) + ∑ i, c i • (corr S r (f i) - f i) := by
  have h : corrL S r (∑ i, c i • f i) = ∑ i, c i • corrL S r (f i) := by
    simp [map_sum, map_smul]
  change corrL S r (∑ i, c i • f i) = _
  rw [h]
  simp only [smul_sub, Finset.sum_sub_distrib]
  change _ = _ + (∑ i, c i • corr S r (f i) - _)
  abel

set_option maxHeartbeats 1000000 in
/-- Energy of the corrected linear combination. -/
theorem eLpNorm_fderiv_corr_comb_le {S : Finset ℂ} {r : ℝ} (hr : GoodRadius S r) {n : ℕ}
    (f : Fin n → ℂ → ℝ) (hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (↑S)ᶜ) (c : Fin n → ℝ)
    (μ : Measure ℂ) (hμ : μ ≪ volume) :
    eLpNorm (fderiv ℝ (corr S r (∑ i, c i • f i))) 2 μ ≤
      eLpNorm (fderiv ℝ (∑ i, c i • f i)) 2 μ +
        ∑ i, ‖c i‖ₑ * eLpNorm (fderiv ℝ (corr S r (f i) - f i)) 2 μ := by
  have hopen : IsOpen ((↑S : Set ℂ)ᶜ) := S.finite_toSet.isClosed.isOpen_compl
  have hnull : ∀ᵐ z ∂μ, z ∉ S := by
    apply hμ.ae_le
    have : volume (↑S : Set ℂ) = 0 := S.finite_toSet.measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 this] with z hz using hz
  have hdf : ∀ i, ∀ z ∉ S, DifferentiableAt ℝ (f i) z := fun i z hz =>
    ((hfs i).contDiffAt (hopen.mem_nhds hz)).differentiableAt (by simp)
  have hdh : ∀ i, ∀ z ∉ S, DifferentiableAt ℝ (corr S r (f i) - f i) z := fun i z hz =>
    ((corr_contDiff hr (hfs i)).differentiable (by simp) z).sub (hdf i z hz)
  have hae : ∀ᵐ z ∂μ, fderiv ℝ (corr S r (∑ i, c i • f i)) z =
      fderiv ℝ (∑ i, c i • f i) z + ∑ i, c i • fderiv ℝ (corr S r (f i) - f i) z := by
    filter_upwards [hnull] with z hz
    rw [corr_comb_eq]
    have e1 : (∑ i, c i • f i) = fun y => ∑ i, c i • f i y := by
      funext y; simp only [Finset.sum_apply, Pi.smul_apply]
    have e2 : (∑ i, c i • (corr S r (f i) - f i)) =
        fun y => ∑ i, c i • (corr S r (f i) - f i) y := by
      funext y; simp only [Finset.sum_apply, Pi.smul_apply]
    have h1 : HasFDerivAt (∑ i, c i • f i) (∑ i, c i • fderiv ℝ (f i) z) z := by
      rw [e1]
      exact HasFDerivAt.fun_sum (u := Finset.univ)
        fun i _ => ((hdf i z hz).hasFDerivAt.const_smul (c i))
    have h2 : HasFDerivAt (∑ i, c i • (corr S r (f i) - f i))
        (∑ i, c i • fderiv ℝ (corr S r (f i) - f i) z) z := by
      rw [e2]
      exact HasFDerivAt.fun_sum (u := Finset.univ)
        fun i _ => ((hdh i z hz).hasFDerivAt.const_smul (c i))
    rw [(h1.add h2).fderiv, h1.fderiv]
  have hcongr := eLpNorm_congr_ae (p := 2) hae
  rw [hcongr]
  have hsplit : (fun z => fderiv ℝ (∑ i, c i • f i) z +
        ∑ i, c i • fderiv ℝ (corr S r (f i) - f i) z) =
      fderiv ℝ (∑ i, c i • f i) + fun z => ∑ i, c i • fderiv ℝ (corr S r (f i) - f i) z := by
    funext z; simp only [Pi.add_apply]
  rw [hsplit]
  refine (eLpNorm_add_le (μ := μ) (p := (2 : ℝ≥0∞)) (by norm_num)).trans ?_
  refine add_le_add le_rfl ?_
  have : (fun z => ∑ i, c i • fderiv ℝ (corr S r (f i) - f i) z) =
      ∑ i, c i • fderiv ℝ (corr S r (f i) - f i) := by
    funext z; simp only [Finset.sum_apply, Pi.smul_apply]
  rw [this]
  refine (eLpNorm_sum_le (μ := μ) (p := (2 : ℝ≥0∞)) (by norm_num)).trans ?_
  exact Finset.sum_le_sum fun i _ => (eLpNorm_const_smul (c := c i)
    (f := fderiv ℝ (corr S r (f i) - f i)) (p := 2) (μ := μ)).le

theorem ennreal_div_sq (a b : ℝ≥0∞) : (a / b) ^ 2 = a ^ 2 / b ^ 2 := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_pow, ENNReal.inv_pow]

theorem rayleigh_bound {a n e Λ d : ℝ≥0∞} (hn0 : n ≠ 0) (hnt : n ≠ ⊤) (ha : a ^ 2 / n ^ 2 ≤ Λ)
    (hd : d ≤ a + e * n) : d ^ 2 / n ^ 2 ≤ (Λ ^ (1/2 : ℝ) + e) ^ 2 := by
  have hsq : (Λ ^ (1/2 : ℝ)) ^ 2 = Λ := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have h1 : a / n ≤ Λ ^ (1/2 : ℝ) := by
    apply ennreal_le_of_sq_le
    rw [hsq, ennreal_div_sq]; exact ha
  have h2 : d / n ≤ a / n + e := by
    calc d / n ≤ (a + e * n) / n := by gcongr
      _ = a / n + e := by rw [ENNReal.add_div, ENNReal.mul_div_cancel_right hn0 hnt]
  rw [← ennreal_div_sq]
  gcongr
  exact h2.trans (add_le_add h1 le_rfl)

theorem tendsto_rayleigh_bound (Λ : ℝ≥0∞) :
    Tendsto (fun e : ℝ≥0∞ => (Λ ^ (1/2 : ℝ) + e) ^ 2) (𝓝 0) (𝓝 Λ) := by
  have hsq : (Λ ^ (1/2 : ℝ)) ^ 2 = Λ := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have hc : Continuous (fun e : ℝ≥0∞ => (Λ ^ (1/2 : ℝ) + e) ^ 2) :=
    (ENNReal.continuous_pow 2).comp (continuous_const.add continuous_id)
  have := hc.tendsto 0
  rw [add_zero, hsq] at this
  exact this

/-- **Min–max transfer with test functions singular at interior branch points.**
Let `T` be a linear map of functions on the plane such that, for every `C^∞` test function `u`,
`T u` is bounded on the open unit disk and `C^∞` off a fixed finite set `S` of points of the
open unit disk, has Dirichlet energy on `𝔻` equal to `E₁ u`, and has weighted boundary mass
`∫_𝕋 ρ |T u|²` equal to `B₁ u`.  Then `σ_k(𝔻, ρ) ≤ minMax E₁ B₁ k` for every `k`.

The functions `T u` are *not* admissible test functions in `σ_k(𝔻, ρ)` (they need not be smooth
at the points of `S`); they are corrected near `S` by logarithmic cut-offs, at an arbitrarily
small cost in energy and no change on the boundary. -/
theorem minMax_le_of_singular_transfer {E₁ B₁ : (ℂ → ℝ) → ℝ≥0∞} {ρ : ℂ → ℝ}
    (hρ : Continuous fun t : ℝ => ρ (circ t)) (S : Finset ℂ) (hS : ∀ s ∈ S, ‖s‖ < 1)
    (T : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ))
    (hT : ∀ u, ContDiff ℝ ∞ u → (∃ M, ∀ z ∈ Metric.ball (0:ℂ) 1, |T u z| ≤ M) ∧
      ContDiffOn ℝ ∞ (T u) (↑S)ᶜ ∧
      dirichletEnergy (Metric.ball 0 1) (T u) = E₁ u ∧ weightedBoundaryMass ρ (T u) = B₁ u)
    (hE : ∀ u, ContDiff ℝ ∞ u → E₁ u ≠ ⊤) (k : ℕ) :
    weightedSteklovEigenvalue ρ k ≤ minMax E₁ B₁ k := by
  unfold weightedSteklovEigenvalue minMax
  refine le_iInf₂ fun V hV => ?_
  obtain ⟨hsm, hdim, hpos⟩ := hV
  set Λ := ⨆ (u : ℂ → ℝ) (_ : u ∈ V) (_ : u ≠ 0), E₁ u / B₁ u with hΛ
  set μB := volume.restrict (Metric.ball (0:ℂ) 1) with hμB
  haveI : Module.Finite ℝ V := Module.finite_of_finrank_pos (by rw [hdim]; exact Nat.succ_pos k)
  let b := Module.finBasisOfFinrankEq ℝ V hdim
  set f : Fin (k+1) → ℂ → ℝ := fun i => T (b i) with hf
  have hfb : ∀ i, ∃ M, ∀ z ∈ Metric.ball (0:ℂ) 1, |f i z| ≤ M := fun i =>
    (hT _ (hsm _ (b i).2)).1
  have hfs : ∀ i, ContDiffOn ℝ ∞ (f i) (↑S)ᶜ := fun i => (hT _ (hsm _ (b i).2)).2.1
  set U : (Fin (k+1) → ℝ) → (ℂ → ℝ) := fun c => ∑ i, c i • (b i : ℂ → ℝ) with hU
  have hUmem : ∀ c, U c ∈ V := fun c =>
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (b i).2
  have hTU : ∀ c, T (U c) = ∑ i, c i • f i := fun c => by simp [hU, hf, map_sum, map_smul]
  have hUcoe : ∀ c, U c = ((∑ i, c i • b i : V) : ℂ → ℝ) := fun c => by simp [hU]
  have hUne : ∀ c, c ≠ 0 → U c ≠ 0 := by
    intro c hc h0
    apply hc
    have h1 : (∑ i, c i • b i : V) = 0 := by
      apply Subtype.ext; rw [← hUcoe]; exact h0
    ext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent c h1 i
  have hsurj : ∀ u ∈ V, ∃ c, U c = u := by
    intro u hu
    refine ⟨b.repr ⟨u, hu⟩, ?_⟩
    rw [hUcoe]
    have := b.sum_repr ⟨u, hu⟩
    exact congrArg Subtype.val this
  -- the boundary seminorm in coordinates
  set G : (Fin (k+1) → ℝ) → ℂ → ℝ := fun c => ∑ i, c i • f i with hG
  have hGs : ∀ c, ContDiffOn ℝ ∞ (G c) (↑S)ᶜ := fun c => by
    have : G c = fun a => ∑ i, c i • f i a := by ext; simp [hG]
    rw [this]
    exact ContDiffOn.sum fun i _ => (hfs i).const_smul _
  have hGc : ∀ c, Continuous fun t => G c (circ t) := fun c => by
    refine (hGs c).continuousOn.comp_continuous continuous_circ fun t ht => ?_
    have h1 := hS _ ht
    rw [norm_circ] at h1
    exact lt_irrefl _ h1
  set N : (Fin (k+1) → ℝ) → ℝ≥0∞ := fun c => eLpNorm (fun t => G c (circ t)) 2 (circMeasure ρ)
    with hN
  have hN2 : ∀ c, N c ^ 2 = B₁ (U c) := fun c => by
    rw [← (hT _ (hsm _ (hUmem c))).2.2.2, hTU, weightedBoundaryMass_eq_eLpNorm hρ _ (hGc c)]
  have hNtop : ∀ c, N c ≠ ⊤ := fun c => by
    have h := weightedBoundaryMass_ne_top hρ (hGc c)
    rw [weightedBoundaryMass_eq_eLpNorm hρ _ (hGc c)] at h
    exact fun h' => h (by change N c ^ 2 = ⊤; rw [h']; simp)
  have hNpos : ∀ c, c ≠ 0 → N c ≠ 0 := fun c hc h0 => by
    apply hpos _ (hUmem c) (hUne c hc)
    rw [← hN2, h0]; simp
  have hGadd : ∀ c c', G (c + c') = G c + G c' := fun c c' => by
    simp only [hG, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  have hGsmul : ∀ (a : ℝ) c, G (a • c) = a • G c := fun a c => by
    simp only [hG, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]
  have hNadd : ∀ c c', N (c + c') ≤ N c + N c' := fun c c' => by
    have hfun : (fun t => G (c + c') (circ t)) =
        (fun t => G c (circ t)) + (fun t => G c' (circ t)) := by
      funext t; simp only [hGadd, Pi.add_apply]
    simp only [hN]
    rw [hfun]
    exact eLpNorm_add_le (by norm_num)
  have hNsmul : ∀ (a : ℝ) c, N (a • c) = ‖a‖ₑ * N c := fun a c => by
    have hfun : (fun t => G (a • c) (circ t)) = a • (fun t => G c (circ t)) := by
      funext t; simp only [hGsmul, Pi.smul_apply]
    simp only [hN]
    rw [hfun]
    exact eLpNorm_const_smul (c := a) (f := fun t => G c (circ t)) (p := 2) (μ := circMeasure ρ)
  obtain ⟨K, hK⟩ := exists_sum_le_of_seminorm N hNtop hNadd hNsmul hNpos
  -- energies of the corrections
  have hfE : ∀ i, eLpNorm (fderiv ℝ (f i)) 2 μB ≠ ⊤ := fun i => by
    have h := hE _ (hsm _ (b i).2)
    rw [← (hT _ (hsm _ (b i).2)).2.2.1, dirichletEnergy_eq_eLpNorm_sq] at h
    exact fun h' => h (by rw [← hμB, h']; simp)
  set ε : ℝ → ℝ≥0∞ := fun r => ∑ i, eLpNorm (fderiv ℝ (corr S r (f i) - f i)) 2 μB with hε
  have hεlim : Tendsto ε (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (Fin (k+1)))
      (fun i _ => tendsto_eLpNorm_fderiv_corr_sub hS (hfb i) (hfs i) (hfE i))
    first
      | simpa using this
      | simpa [Function.comp_def] using this
  have hlim : Tendsto (fun r => (Λ ^ (1/2:ℝ) + (K:ℝ≥0∞) * ε r) ^ 2) (𝓝[>] 0) (𝓝 Λ) := by
    have h1 : Tendsto (fun r => (K:ℝ≥0∞) * ε r) (𝓝[>] 0) (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hεlim (Or.inr ENNReal.coe_ne_top)
    exact (tendsto_rayleigh_bound Λ).comp h1
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_goodRadius S hS] with r hr
  -- the corrected test space
  set W := V.map ((corrL S r).comp T) with hW
  have hB : ∀ u ∈ V, weightedBoundaryMass ρ (corr S r (T u)) = B₁ u := fun u hu => by
    rw [weightedBoundaryMass_congr' ρ (fun z hz => corr_eq_on_circle hr (T u) hz.ge)]
    exact (hT u (hsm u hu)).2.2.2
  have hinj : Function.Injective (((corrL S r).comp T).domRestrict V) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro u hu
    apply Subtype.ext
    by_contra hne
    apply hpos u u.2 hne
    rw [← hB u u.2]
    have h0 : corr S r (T u) = 0 := hu
    rw [h0]; simp [weightedBoundaryMass]
  have hWadm : AdmissibleSpace (weightedBoundaryMass ρ) k W := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩; exact corr_contDiff hr (hT u (hsm u hu)).2.1
    · rw [hW, ← LinearMap.range_domRestrict, LinearMap.finrank_range_of_inj hinj, hdim]
    · rintro _ ⟨u, hu, rfl⟩ hne
      have hu0 : u ≠ 0 := by rintro rfl; exact hne (map_zero _)
      change weightedBoundaryMass ρ (corr S r (T u)) ≠ 0
      rw [hB u hu]; exact hpos u hu hu0
  refine (iInf₂_le W hWadm).trans ?_
  refine iSup₂_le fun w hw => iSup_le fun hne => ?_
  obtain ⟨u, hu, rfl⟩ := hw
  obtain ⟨c, rfl⟩ := hsurj u hu
  have hc : c ≠ 0 := by
    rintro rfl
    apply hne
    have hU0 : U 0 = 0 := by simp [hU]
    change corr S r (T (U 0)) = 0
    rw [hU0, map_zero]; ext z; simp [corr]
  change dirichletEnergy _ (corr S r (T (U c))) /
    weightedBoundaryMass ρ (corr S r (T (U c))) ≤ _
  rw [hB _ (hUmem c), ← hN2, hTU, dirichletEnergy_eq_eLpNorm_sq]
  refine rayleigh_bound (a := eLpNorm (fderiv ℝ (∑ i, c i • f i)) 2 μB) (hNpos c hc) (hNtop c)
    ?_ ?_
  · rw [← dirichletEnergy_eq_eLpNorm_sq, ← hTU, (hT _ (hsm _ (hUmem c))).2.2.1, hN2]
    exact le_iSup₂_of_le (f := fun u (_ : u ∈ V) => ⨆ (_ : u ≠ 0), E₁ u / B₁ u) (U c)
      (hUmem c) (le_iSup_of_le (hUne c hc) le_rfl)
  · refine (eLpNorm_fderiv_corr_comb_le hr f hfs c μB
      (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)).trans ?_
    refine add_le_add le_rfl ?_
    calc ∑ i, ‖c i‖ₑ * eLpNorm (fderiv ℝ (corr S r (f i) - f i)) 2 μB
        ≤ ∑ i, ‖c i‖ₑ * ε r := by
          refine Finset.sum_le_sum fun i _ => mul_le_mul_right ?_ _
          exact Finset.single_le_sum (f := fun i => eLpNorm (fderiv ℝ (corr S r (f i) - f i)) 2 μB)
            (fun _ _ => zero_le) (Finset.mem_univ i)
      _ = (∑ i, ‖c i‖ₑ) * ε r := by rw [Finset.sum_mul]
      _ ≤ (K * N c) * ε r := mul_le_mul_left (hK c) _
      _ = K * ε r * N c := by ring

end SteklovBranch
