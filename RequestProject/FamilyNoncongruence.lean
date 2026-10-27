module

public import RequestProject.LocalCoverIneq
public import RequestProject.CongruenceRigidity
public import RequestProject.DiskCoverExistence
public import RequestProject.CriticalValues
public import RequestProject.ActualKernel

/-!
# Ingredients of noncongruence for the actual degree-seven families

* `critSet B`: the critical values of `B` in `𝔻`.
* `critSet_of_aut`, `critSet_of_anti`: `B₁ = η · B₂ ∘ φ` (resp. `η · conj (B₂ ∘ ψ)`) on `𝔻̄` for a
  disk automorphism `φ` (resp. antiholomorphic `ψ`) gives `critSet B₁ = η · critSet B₂`
  (resp. `η · conj (critSet B₂)`).
* `family_facts`: for the normalized disk covers of `paperQ (monicP s a) τ ε` and all small `ε`,
  the critical values in `𝔻` are exactly `{ε, λ_* ε}`, and every point `u` with `|p_s(u)| ≤ 2` is
  of the form `κ ψ(z)`, `z ∈ 𝔻`, `κ = a/τ(ε)`.
* `no_disk_equiv`: the disk covers of `p_s` and `p_{-s}` are not related by a disk automorphism
  (`p_s(κ₁ψ₁) = p_{-s}(κ₂ψ₂ ∘ φ)` on `𝔻` is impossible), via `Degree7.no_local_iso`.
-/

@[expose] public section

open Complex Metric Set Filter Topology Polynomial

noncomputable section

namespace FamilyNoncongr

open SteklovBlaschke SteklovCoalescence SteklovCritical Degree7 DiskAut CongrRigid

/-- Critical values of `B` in the open unit disk. -/
def critSet (B : ℂ → ℂ) : Set ℂ := {w | ∃ z : ℂ, ‖z‖ < 1 ∧ deriv B z = 0 ∧ B z = w}

lemma diskAut_maps {φ : ℂ → ℂ} (hφ : IsDiskAut φ) {z : ℂ} (hz : ‖z‖ < 1) : ‖φ z‖ < 1 := by
  obtain ⟨μ, b, hμ, hb, rfl⟩ := hφ
  rw [norm_mul, hμ, one_mul]; exact SteklovRiemann.norm_bfac_lt hb hz

lemma diskAut_surj {φ : ℂ → ℂ} (hφ : IsDiskAut φ) {w : ℂ} (hw : ‖w‖ < 1) :
    ∃ z, ‖z‖ < 1 ∧ φ z = w := by
  obtain ⟨μ, b, hμ, hb, rfl⟩ := hφ
  have hμ0 : μ ≠ 0 := by rintro rfl; simp at hμ
  have hv : ‖w / μ‖ < 1 := by rw [norm_div, hμ, div_one]; exact hw
  refine ⟨bfac (-b) (w / μ), SteklovRiemann.norm_bfac_lt (norm_neg_lt hb) hv, ?_⟩
  have := bfac_neg_bfac (norm_neg_lt hb) hv
  rw [neg_neg] at this
  show μ * bfac b (bfac (-b) (w / μ)) = w
  rw [this]; field_simp

lemma diskAut_injOn {φ : ℂ → ℂ} (hφ : IsDiskAut φ) : InjOn φ (ball 0 1) := by
  obtain ⟨μ, b, hμ, hb, rfl⟩ := hφ
  have hμ0 : μ ≠ 0 := by rintro rfl; simp at hμ
  intro z hz w hw h
  exact SteklovRiemann.bfac_injOn hb (ball_subset_closedBall hz) (ball_subset_closedBall hw)
    (mul_left_cancel₀ hμ0 h)

lemma diskAut_deriv_ne {φ : ℂ → ℂ} (hφ : IsDiskAut φ) {z : ℂ} (hz : ‖z‖ < 1) : deriv φ z ≠ 0 :=
  HolInv.deriv_ne_zero_of_injOn isOpen_ball
    (fun _ hw => (diskAut_differentiableAt hφ (mem_ball_zero_iff.1 hw).le).differentiableWithinAt)
    (diskAut_injOn hφ) (mem_ball_zero_iff.2 hz)

/-- Critical values under `B₁ = η · B₂ ∘ φ`. -/
theorem critSet_of_aut {B₁ B₂ φ : ℂ → ℂ} {m : ℕ} (hB₂ : IsFiniteBlaschke B₂ m)
    (hφ : IsDiskAut φ) {η : ℂ} (hη : η ≠ 0) (h : ∀ z : ℂ, ‖z‖ ≤ 1 → B₁ z = η * B₂ (φ z)) :
    critSet B₁ = (fun w => η * w) '' critSet B₂ := by
  have hder : ∀ z : ℂ, ‖z‖ < 1 → deriv B₁ z = η * (deriv B₂ (φ z) * deriv φ z) := by
    intro z hz
    have hev : B₁ =ᶠ[𝓝 z] fun w => η * (B₂ ∘ φ) w := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
      exact h w (mem_ball_zero_iff.1 hw).le
    rw [hev.deriv_eq, deriv_const_mul _ ((hB₂.differentiableAt (diskAut_maps hφ hz).le).comp z
      (diskAut_differentiableAt hφ hz.le)), deriv_comp z
      (hB₂.differentiableAt (diskAut_maps hφ hz).le) (diskAut_differentiableAt hφ hz.le)]
  ext w; constructor
  · rintro ⟨z, hz, hd, rfl⟩
    refine ⟨B₂ (φ z), ⟨φ z, diskAut_maps hφ hz, ?_, rfl⟩, (h z hz.le).symm⟩
    rw [hder z hz] at hd
    rcases mul_eq_zero.1 hd with h1 | h1
    · exact absurd h1 hη
    · rcases mul_eq_zero.1 h1 with h2 | h2
      · exact h2
      · exact absurd h2 (diskAut_deriv_ne hφ hz)
  · rintro ⟨_, ⟨z', hz', hd', rfl⟩, rfl⟩
    obtain ⟨z, hz, rfl⟩ := diskAut_surj hφ hz'
    exact ⟨z, hz, by rw [hder z hz, hd', zero_mul, mul_zero], h z hz.le⟩

/-- Critical values under `B₁ = η · conj (B₂ ∘ ψ)`, `ψ = φ ∘ conj`. -/
theorem critSet_of_anti {B₁ B₂ φ : ℂ → ℂ} {m : ℕ} (hB₂ : IsFiniteBlaschke B₂ m)
    (hφ : IsDiskAut φ) {η : ℂ} (hη : η ≠ 0)
    (h : ∀ z : ℂ, ‖z‖ ≤ 1 → B₁ z = η * (starRingEnd ℂ) (B₂ (φ ((starRingEnd ℂ) z)))) :
    critSet B₁ = (fun w => η * (starRingEnd ℂ) w) '' critSet B₂ := by
  have hder : ∀ z : ℂ, ‖z‖ < 1 → deriv B₁ z = η * (starRingEnd ℂ)
      (deriv B₂ (φ ((starRingEnd ℂ) z)) * deriv φ ((starRingEnd ℂ) z)) := by
    intro z hz
    have hzc : ‖(starRingEnd ℂ) z‖ < 1 := by rwa [Complex.norm_conj]
    have hev : B₁ =ᶠ[𝓝 z] fun w => η * ((starRingEnd ℂ) ∘ (B₂ ∘ φ) ∘ (starRingEnd ℂ)) w := by
      filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hz)] with w hw
      exact h w (mem_ball_zero_iff.1 hw).le
    have hd : HasDerivAt (B₂ ∘ φ) (deriv B₂ (φ ((starRingEnd ℂ) z)) * deriv φ ((starRingEnd ℂ) z))
        ((starRingEnd ℂ) z) :=
      (hB₂.differentiableAt (diskAut_maps hφ hzc).le).hasDerivAt.comp _
        (diskAut_differentiableAt hφ hzc.le).hasDerivAt
    have hc := hd.conj_conj
    rw [Complex.conj_conj] at hc
    rw [hev.deriv_eq, (hc.const_mul η).deriv]
  ext w; constructor
  · rintro ⟨z, hz, hd, rfl⟩
    have hzc : ‖(starRingEnd ℂ) z‖ < 1 := by rwa [Complex.norm_conj]
    refine ⟨B₂ (φ ((starRingEnd ℂ) z)), ⟨φ ((starRingEnd ℂ) z), diskAut_maps hφ hzc, ?_, rfl⟩,
      (h z hz.le).symm⟩
    rw [hder z hz] at hd
    rcases mul_eq_zero.1 hd with h1 | h1
    · exact absurd h1 hη
    · rw [map_eq_zero] at h1
      rcases mul_eq_zero.1 h1 with h2 | h2
      · exact h2
      · exact absurd h2 (diskAut_deriv_ne hφ hzc)
  · rintro ⟨_, ⟨z', hz', hd', rfl⟩, rfl⟩
    obtain ⟨z, hz, rfl⟩ := diskAut_surj hφ hz'
    refine ⟨(starRingEnd ℂ) z, by rwa [Complex.norm_conj], ?_, ?_⟩
    · rw [hder _ (by rwa [Complex.norm_conj]), Complex.conj_conj, hd', zero_mul, map_zero,
        mul_zero]
    · rw [h _ (by rw [Complex.norm_conj]; exact hz.le), Complex.conj_conj]

lemma norm_lamStar_sub_one_le : ‖lamStar - 1‖ ≤ 2 := by
  have : lamStar - 1 = 1 + I := by simp only [lamStar]; ring
  rw [this]
  calc ‖(1 : ℂ) + I‖ ≤ ‖(1 : ℂ)‖ + ‖I‖ := norm_add_le _ _
    _ = 2 := by simp; norm_num

lemma exists_crit_zero (hs : s ^ 2 = -7) : ∃ c : ℂ, deriv (pfun s) c = 0 ∧ pfun s c = 0 := by
  obtain ⟨c, hc⟩ : ∃ c, qpoly (cc s) c = 0 := by
    obtain ⟨c, hc⟩ := Complex.exists_root (f := qPoly (cc s)) (by
      rw [degree_eq_natDegree (qPoly_ne_zero _), qPoly_natDegree]; norm_num)
    exact ⟨c, by rw [← qPoly_eval]; exact hc⟩
  exact ⟨c, (deriv_pfun_eq_zero_iff hs c).2 (Or.inr (Or.inr hc)),
    (pfun_critical_values hs).2.2 c hc⟩

/-- **Facts about the actual disk covers for small `ε`**. -/
theorem family_facts {s a : ℂ} (hs : s ^ 2 = -7) (ha : a ^ 7 = -bconst s) {τ : ℝ → ℂ}
    (hτ : ∀ ε, τ ε ^ 7 = (lamStar - 1) * ε) :
    ∃ ε₁ > (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ ψ B : ℂ → ℂ,
      IsNormalizedDiskCover (paperQ (monicP s a) τ ε) 7 ψ B →
      (∀ u : ℂ, ‖pfun s u‖ ≤ 2 → u / (a / τ ε) ∈ ψ '' ball 0 1) ∧
      critSet B = {(ε : ℂ), lamStar * ε} := by
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [zero_pow (by norm_num)] at ha; exact bconst_ne_zero hs (neg_eq_zero.1 ha.symm)
  obtain ⟨c₀, hc₀d, hc₀v⟩ := exists_crit_zero hs
  -- a radius containing `{|p_s| ≤ 2}` and the critical points `1`, `c₀`
  obtain ⟨R₂, hR₂⟩ : ∃ R₂ : ℝ, ∀ u : ℂ, ‖pfun s u‖ ≤ 2 → ‖u‖ ≤ R₂ := by
    have ht := (pPoly s).tendsto_norm_atTop (pPoly_degree_pos hs) (l := Filter.comap norm atTop)
      tendsto_comap
    have hev := ht.eventually (eventually_gt_atTop 2)
    obtain ⟨S, hS, hSsub⟩ := Filter.mem_comap.1 hev
    obtain ⟨R, hR⟩ := Filter.mem_atTop_sets.1 hS
    refine ⟨R, fun u hu => ?_⟩
    by_contra hlt
    push_neg at hlt
    have : u ∈ {x : ℂ | 2 < ‖(pPoly s).eval x‖} := hSsub (hR _ hlt.le)
    simp only [mem_setOf_eq, pPoly_eval] at this
    linarith
  set R : ℝ := max (max R₂ 1) ‖c₀‖ with hRdef
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    (f := pfun s) (by
      have : Continuous (pfun s) := by
        have : pfun s = fun z => (pPoly s).eval z := funext fun z => (pPoly_eval s z).symm
        rw [this]; exact (pPoly s).continuous
      exact this.continuousOn)
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one (le_trans (le_max_right _ _) (le_max_left _ _))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (mem_closedBall_self hR0))
  refine ⟨1 / (1 + 2 * C), by positivity, fun ε hε0 hε1 ψ B hcov => ?_⟩
  set δ : ℂ := (lamStar - 1) * ε with hδdef
  have hδ : δ ≠ 0 := mul_ne_zero lamStar_sub_one_ne_zero (by exact_mod_cast hε0.ne')
  have hτ0 : τ ε ≠ 0 := by
    intro h; have := hτ ε; rw [h, zero_pow (by norm_num)] at this; exact hδ this.symm
  have hδn : ‖δ‖ ≤ 2 * ε := by
    rw [hδdef, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
    exact mul_le_mul_of_nonneg_right norm_lamStar_sub_one_le hε0.le
  have hsmallC : ε + 2 * ε * C < 1 := by
    have h1 : ε * (1 + 2 * C) < 1 := by
      rwa [lt_div_iff₀ (by positivity)] at hε1
    linarith
  set κ : ℂ := a / τ ε with hκ
  have hκ0 : κ ≠ 0 := div_ne_zero ha0 hτ0
  have hQ : ∀ w : ℂ, paperQ (monicP s a) τ ε w = ε + δ * pfun s (κ * w) := by
    intro w
    rw [paperQ, monicP_eval hs ha, hκ]
    congr 2
    field_simp
  obtain ⟨hψd, hψi, -, -, -, hψim, hB, hBψ⟩ := hcov
  -- containment: points of the ball of radius `R`
  have hmemR : ∀ u : ℂ, ‖u‖ ≤ R → u / κ ∈ ψ '' ball 0 1 := by
    intro u hu
    rw [hψim]
    have hseg : segment ℝ (0 : ℂ) (u / κ) ⊆ paperQ (monicP s a) τ ε ⁻¹' ball 0 1 := by
      intro w hw
      obtain ⟨t, ht0, ht1, rfl⟩ : ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ (t : ℂ) * (u / κ) = w := by
        obtain ⟨p, q, hp, hq, hpq, rfl⟩ := hw
        exact ⟨q, hq, by linarith, by simp⟩
      rw [mem_preimage, hQ, mem_ball_zero_iff,
        show κ * ((t : ℂ) * (u / κ)) = (t : ℂ) * u by field_simp]
      have htu : ‖(t : ℂ) * u‖ ≤ R := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
        nlinarith [norm_nonneg u]
      have hb := hC _ (mem_closedBall_zero_iff.2 htu)
      calc ‖(ε : ℂ) + δ * pfun s ((t : ℂ) * u)‖
          ≤ ‖(ε : ℂ)‖ + ‖δ‖ * ‖pfun s ((t : ℂ) * u)‖ := by
            rw [← norm_mul]; exact norm_add_le _ _
        _ ≤ ε + 2 * ε * C := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hε0]
            gcongr
        _ < 1 := hsmallC
    exact (convex_segment _ _).isPreconnected.subset_connectedComponentIn
      (left_mem_segment ℝ _ _) hseg (right_mem_segment ℝ _ _)
  refine ⟨fun u hu => hmemR u (le_trans (hR₂ u hu) (le_trans (le_max_left _ _)
    (le_max_left _ _))), ?_⟩
  -- critical values
  have hBform : ∀ z : ℂ, ‖z‖ < 1 → B z = ε + δ * pfun s (κ * ψ z) := by
    intro z hz; rw [hBψ z (mem_ball_zero_iff.2 hz), hQ]
  have hcrit_pt : ∀ c : ℂ, ‖c‖ ≤ R → deriv (pfun s) c = 0 →
      ∃ z : ℂ, ‖z‖ < 1 ∧ deriv B z = 0 ∧ B z = ε + δ * pfun s c := by
    intro c hc hcd
    obtain ⟨z, hz, hψz⟩ := hmemR c hc
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    have hκψ : κ * ψ z = c := by rw [hψz]; field_simp
    refine ⟨z, hz1, ?_, by rw [hBform z hz1, hκψ]⟩
    have hev : B =ᶠ[𝓝 z] fun w => ε + δ * pfun s (κ * ψ w) := by
      filter_upwards [isOpen_ball.mem_nhds hz] with w hw
      exact hBform w (mem_ball_zero_iff.1 hw)
    have hψd' : HasDerivAt ψ (deriv ψ z) z :=
      (hψd.differentiableAt (isOpen_ball.mem_nhds hz)).hasDerivAt
    have hp : HasDerivAt (pfun s) (deriv (pfun s) (κ * ψ z)) (κ * ψ z) :=
      (hasDerivAt_pfun s _).differentiableAt.hasDerivAt
    have := ((hp.comp z (hψd'.const_mul κ)).const_mul δ).const_add (ε : ℂ)
    rw [hev.deriv_eq]
    refine this.deriv.trans ?_
    rw [hκψ, hcd]; ring
  ext w; constructor
  · rintro ⟨z, hz, hd, rfl⟩
    have := ActualKernel.crit_of_disk hs hδ hκ0 hψd hψi hBform z hz hd
    rcases this with h | h
    · exact Or.inl h
    · right; rw [mem_singleton_iff, h, hδdef]; ring
  · rintro (rfl | rfl)
    · obtain ⟨z, hz, hd, hv⟩ := hcrit_pt c₀ (le_max_right _ _) hc₀d
      exact ⟨z, hz, hd, by rw [hv, hc₀v, mul_zero, add_zero]⟩
    · obtain ⟨z, hz, hd, hv⟩ := hcrit_pt 1 (by
        rw [norm_one]; exact le_trans (le_max_right _ _) (le_max_left _ _))
        ((deriv_pfun_eq_zero_iff hs 1).2 (Or.inl rfl))
      refine ⟨z, hz, hd, ?_⟩
      rw [hv, (pfun_critical_values hs).1, hδdef]; ring

/-- **The two disk covers are not equivalent**: no disk automorphism `φ` satisfies
`p_s(κ₁ψ₁) = p_{-s}(κ₂ψ₂ ∘ φ)` on `𝔻`, provided `κ₁ψ₁(𝔻) ⊇ {|p_s| ≤ 2}`. -/
theorem no_disk_equiv {s : ℂ} (hs : s ^ 2 = -7) {κ₁ κ₂ : ℂ} (hκ₁ : κ₁ ≠ 0) (hκ₂ : κ₂ ≠ 0)
    {ψ₁ ψ₂ φ : ℂ → ℂ} (hψ₁d : DifferentiableOn ℂ ψ₁ (ball 0 1)) (hψ₁i : InjOn ψ₁ (ball 0 1))
    (hψ₂d : DifferentiableOn ℂ ψ₂ (ball 0 1)) (hψ₂i : InjOn ψ₂ (ball 0 1)) (hφ : IsDiskAut φ)
    (hcont : ∀ u : ℂ, ‖pfun s u‖ ≤ 2 → u / κ₁ ∈ ψ₁ '' ball 0 1)
    (hrel : ∀ z : ℂ, ‖z‖ < 1 → pfun s (κ₁ * ψ₁ z) = pfun (-s) (κ₂ * ψ₂ (φ z))) : False := by
  set F : ℂ → ℂ := fun z => κ₁ * ψ₁ z with hF
  have hFd : DifferentiableOn ℂ F (ball 0 1) := hψ₁d.const_mul κ₁
  have hFi : InjOn F (ball 0 1) := fun z hz w hw h => hψ₁i hz hw (mul_left_cancel₀ hκ₁ h)
  set U := F '' ball 0 1 with hU
  have hUo : IsOpen U := HolInv.isOpen_image hFd hFi subset_rfl isOpen_ball
  set g := Function.invFunOn F (ball 0 1) with hg
  have hgF : ∀ z ∈ ball (0 : ℂ) 1, g (F z) = z := fun z hz => HolInv.invFunOn_apply_self hFi hz
  set h : ℂ → ℂ := fun u => κ₂ * ψ₂ (φ (g u)) with hh
  refine no_local_iso hs hUo (h := h) ?_ ?_ ?_ ?_
  · intro u hu
    obtain ⟨z, hz, hψz⟩ := hcont u (by rw [← pPoly_eval]; exact hu)
    exact ⟨z, hz, by simp only [hF, hψz]; field_simp⟩
  · rintro _ ⟨z, hz, rfl⟩
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
    have hgc : ContinuousAt g (F z) := HolInv.continuousAt_invFunOn isOpen_ball hFd hFi hz
    have hφc : ContinuousAt φ (g (F z)) := by
      rw [hgF z hz]; exact (diskAut_differentiableAt hφ hz1.le).continuousAt
    have hψc : ContinuousAt ψ₂ (φ (g (F z))) := by
      rw [hgF z hz]
      exact (hψ₂d.differentiableAt (isOpen_ball.mem_nhds
        (mem_ball_zero_iff.2 (diskAut_maps hφ hz1)))).continuousAt
    exact (continuousAt_const.mul (ContinuousAt.comp (f := φ ∘ g) (x := F z) hψc
      (hφc.comp hgc))).continuousWithinAt
  · rintro _ ⟨z, hz, rfl⟩ _ ⟨w, hw, rfl⟩ hzw
    simp only [hh, hgF z hz, hgF w hw] at hzw
    have h1 := hψ₂i (mem_ball_zero_iff.2 (diskAut_maps hφ (mem_ball_zero_iff.1 hz)))
      (mem_ball_zero_iff.2 (diskAut_maps hφ (mem_ball_zero_iff.1 hw)))
      (mul_left_cancel₀ hκ₂ hzw)
    rw [diskAut_injOn hφ hz hw h1]
  · rintro _ ⟨z, hz, rfl⟩
    show (pPoly (-s)).eval (κ₂ * ψ₂ (φ (g (F z)))) = (pPoly s).eval (F z)
    rw [hgF z hz, pPoly_eval, pPoly_eval]
    exact (hrel z (mem_ball_zero_iff.1 hz)).symm

end FamilyNoncongr

end
