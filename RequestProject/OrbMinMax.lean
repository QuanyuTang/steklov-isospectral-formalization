module

public import RequestProject.SingularTransfer

/-!
# Min–max over a general class of test functions

`SteklovOrb.minMaxOn P E B k` is the Courant–Fischer min–max value over `(k+1)`-dimensional spaces
of test functions satisfying a predicate `P` (instead of the globally smooth test functions used
by `Steklov.minMax`).  `minMaxOn_le_of_singular_transfer` is the singular-transfer theorem
`SteklovBranch.minMax_le_of_singular_transfer` for such classes (same proof: logarithmic
cut-offs at the finitely many singular points).
-/

@[expose] public section

open MeasureTheory Set Filter Topology Real
open scoped ENNReal ContDiff NNReal

noncomputable section

namespace SteklovOrb

open Steklov SteklovBranch

/-- Admissible test spaces for a class `P` of test functions. -/
def AdmissibleOn (P : (ℂ → ℝ) → Prop) (B : (ℂ → ℝ) → ℝ≥0∞) (k : ℕ)
    (V : Submodule ℝ (ℂ → ℝ)) : Prop :=
  (∀ u ∈ V, P u) ∧ Module.finrank ℝ V = k + 1 ∧ ∀ u ∈ V, u ≠ 0 → B u ≠ 0

/-- Min–max value `inf_V sup_{u ∈ V \ 0} E(u)/B(u)` over admissible `(k+1)`-spaces of `P`-test
functions. -/
def minMaxOn (P : (ℂ → ℝ) → Prop) (E B : (ℂ → ℝ) → ℝ≥0∞) (k : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule ℝ (ℂ → ℝ)) (_ : AdmissibleOn P B k V),
    ⨆ (u : ℂ → ℝ) (_ : u ∈ V) (_ : u ≠ 0), E u / B u

/-- `minMax` is `minMaxOn` for globally smooth test functions. -/
theorem minMax_eq_minMaxOn (E B : (ℂ → ℝ) → ℝ≥0∞) (k : ℕ) :
    minMax E B k = minMaxOn (fun u => ContDiff ℝ ∞ u) E B k := rfl

/-- Enlarging the test class lowers the min–max value. -/
theorem minMaxOn_le_minMax {P : (ℂ → ℝ) → Prop} {E B E' B' : (ℂ → ℝ) → ℝ≥0∞}
    (hP : ∀ u, ContDiff ℝ ∞ u → P u) (hE : ∀ u, ContDiff ℝ ∞ u → E u = E' u)
    (hB : ∀ u, ContDiff ℝ ∞ u → B u = B' u) (k : ℕ) :
    minMaxOn P E B k ≤ minMax E' B' k := by
  unfold minMaxOn minMax
  refine le_iInf₂ fun V hV => ?_
  have hV' : AdmissibleOn P B k V :=
    ⟨fun u hu => hP u (hV.1 u hu), hV.2.1, fun u hu h0 => by rw [hB u (hV.1 u hu)]; exact hV.2.2 u hu h0⟩
  refine (iInf₂_le V hV').trans (le_of_eq ?_)
  refine iSup_congr fun u => iSup_congr fun hu => iSup_congr fun _ => ?_
  rw [hE u (hV.1 u hu), hB u (hV.1 u hu)]

theorem minMaxOn_le_of_singular_transfer {P : (ℂ → ℝ) → Prop} {E₁ B₁ : (ℂ → ℝ) → ℝ≥0∞}
    {ρ : ℂ → ℝ}
    (hρ : Continuous fun t : ℝ => ρ (circ t)) (S : Finset ℂ) (hS : ∀ s ∈ S, ‖s‖ < 1)
    (T : (ℂ → ℝ) →ₗ[ℝ] (ℂ → ℝ))
    (hT : ∀ u, P u → (∃ M, ∀ z ∈ Metric.ball (0:ℂ) 1, |T u z| ≤ M) ∧
      ContDiffOn ℝ ∞ (T u) (↑S)ᶜ ∧
      dirichletEnergy (Metric.ball 0 1) (T u) = E₁ u ∧ weightedBoundaryMass ρ (T u) = B₁ u)
    (hE : ∀ u, P u → E₁ u ≠ ⊤) (k : ℕ) :
    weightedSteklovEigenvalue ρ k ≤ minMaxOn P E₁ B₁ k := by
  unfold weightedSteklovEigenvalue minMaxOn
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

end SteklovOrb
