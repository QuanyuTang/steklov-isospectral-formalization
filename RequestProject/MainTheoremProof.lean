module

public import RequestProject.FullAssembly
public import RequestProject.FamilyIsospectral
public import RequestProject.FamilyNoncongruence

/-!
# Proof of Theorem 1.1.2

`mainTheorem_proved : MainTheorem` — all five conclusions, with the original quantifiers.

The family: `P ↦ monicP (i√7) a₊`, `L ↦ monicP (-i√7) a₋`, a common `τ(ε)` with
`τ(ε)⁷ = (λ_* - 1) ε`, the normalized disk covers `B_{i,ε} = Q_{i,ε} ∘ ψ_{i,ε}` and the domains
`Ω_{i,ε} = (1/7) F_{i,ε}(𝔻)` with `F_{i,ε}` the normalized realizing maps of `|B_{i,ε}'|`.

* (i), (iv), (v): `mainTheorem_of_cover_data` (realization, convexity, length, convergence).
* (ii): `FamilyIso.family_spectra_eq` (transplantation with the Fano kernel).
* (iii): a congruence `J` gives a Blaschke (anti)equivalence (`CongrRigid.blaschke_of_congr_hol`,
  `CongrRigid.blaschke_of_congr_anti`); comparing the critical values `{ε, λ_* ε}`
  (`FamilyNoncongr.family_facts`, `critical_values_match`, `critical_values_no_reflection`)
  forces an orientation-preserving equivalence with the same parameter, which is excluded
  between the two labels by the monodromy (`FamilyNoncongr.no_disk_equiv`).
-/

@[expose] public section

open Complex Metric Set Filter Topology SteklovBlaschke Steklov PlaneDomain

noncomputable section

namespace SteklovCoalescence

open SteklovCritical Degree7 DiskAut CongrRigid FamilyNoncongr

/-- **Noncongruence from the critical values.** -/
theorem not_congruent_of_critSet {B₁ B₂ F₁ F₂ : ℂ → ℂ} {n m : ℕ} (hB₁ : IsFiniteBlaschke B₁ n)
    (hB₂ : IsFiniteBlaschke B₂ m) (hF₁ : IsNormalizedRealizing F₁ (fun z => ‖deriv B₁ z‖))
    (hF₂ : IsNormalizedRealizing F₂ (fun z => ‖deriv B₂ z‖)) {c : ℝ} (hc : c ≠ 0)
    {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε')
    (hcv₁ : critSet B₁ = {(ε : ℂ), lamStar * ε}) (hcv₂ : critSet B₂ = {(ε' : ℂ), lamStar * ε'})
    (hne : ε = ε' → ∀ φ, IsDiskAut φ → (∀ z : ℂ, ‖z‖ ≤ 1 → B₁ z = B₂ (φ z)) → False) :
    ¬ PlaneDomain.Congruent ((fun w => (c : ℂ) * F₁ w) '' ball 0 1) ((fun w => (c : ℂ) * F₂ w) '' ball 0 1) := by
  rintro ⟨J, hJ⟩
  have hc' : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc
  obtain ⟨a, b, ha, hform | hform⟩ := isometry_form J
  · have hJ' : (fun z => a * z + b) '' ((fun w => (c : ℂ) * F₁ w) '' ball 0 1) =
        (fun w => (c : ℂ) * F₂ w) '' ball 0 1 := by
      rw [show (fun z => a * z + b) = ⇑J from funext fun z => (hform z).symm]; exact hJ
    obtain ⟨φ, hφ, η, hη, hrel⟩ := blaschke_of_congr_hol hB₁ hB₂ hF₁ hF₂ hc' ha hJ'
    have hη0 : η ≠ 0 := by rintro rfl; simp at hη
    have h := critSet_of_aut hB₂ hφ hη0 hrel
    rw [hcv₁, hcv₂, image_pair, ← mul_assoc] at h
    obtain ⟨rfl, rfl⟩ := critical_values_match hε hε' hη h
    exact hne rfl φ hφ (fun z hz => by rw [hrel z hz, one_mul])
  · have hJ' : (fun z => a * (starRingEnd ℂ) z + b) '' ((fun w => (c : ℂ) * F₁ w) '' ball 0 1) =
        (fun w => (c : ℂ) * F₂ w) '' ball 0 1 := by
      rw [show (fun z => a * (starRingEnd ℂ) z + b) = ⇑J from funext fun z => (hform z).symm]
      exact hJ
    obtain ⟨_, ⟨φ, hφ, rfl⟩, η, hη, hrel⟩ :=
      blaschke_of_congr_anti hB₁ hB₂ hF₁ hF₂ hc' (conj_ofReal c) ha hJ'
    have hη0 : η ≠ 0 := by rintro rfl; simp at hη
    have h := critSet_of_anti hB₂ hφ hη0 hrel
    rw [hcv₁, hcv₂, image_pair, conj_ofReal, map_mul, conj_ofReal, ← mul_assoc] at h
    exact critical_values_no_reflection hε hε' hη h

/-- **No orientation-reversing symmetry, from the critical values.** -/
theorem not_reversing_of_critSet {B F : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n)
    (hF : IsNormalizedRealizing F (fun z => ‖deriv B z‖)) {c : ℝ} (hc : c ≠ 0) {ε : ℝ}
    (hε : 0 < ε) (hcv : critSet B = {(ε : ℂ), lamStar * ε}) :
    ¬ HasOrientationReversingSymmetry ((fun w => (c : ℂ) * F w) '' ball 0 1) := by
  rintro ⟨a, b, ha, hsym⟩
  obtain ⟨_, ⟨φ, hφ, rfl⟩, η, hη, hrel⟩ :=
    blaschke_of_congr_anti hB hB hF hF (ofReal_ne_zero.2 hc) (conj_ofReal c) ha hsym
  have hη0 : η ≠ 0 := by rintro rfl; simp at hη
  have h := critSet_of_anti hB hφ hη0 hrel
  rw [hcv, image_pair, conj_ofReal, map_mul, conj_ofReal, ← mul_assoc] at h
  exact critical_values_no_reflection hε hε hη h

/-- The explicit form of a normalized disk cover of `paperQ (monicP t a) τ ε` on `𝔻`. -/
lemma cover_form {t a : ℂ} (ht : t ^ 2 = -7) (ha : a ^ 7 = -bconst t) {τ : ℝ → ℂ} {ε : ℝ}
    {ψ B : ℂ → ℂ} (hc : IsNormalizedDiskCover (paperQ (monicP t a) τ ε) 7 ψ B) :
    ∀ z : ℂ, ‖z‖ < 1 → B z = ε + (lamStar - 1) * ε * pfun t ((a / τ ε) * ψ z) := by
  intro z hz
  rw [hc.2.2.2.2.2.2.2 z (mem_ball_zero_iff.2 hz), paperQ, monicP_eval ht ha]
  congr 2
  field_simp

/-- **Theorem 1.1.2** (all five conclusions). -/
theorem mainTheorem_proved : MainTheorem := by
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
  refine mainTheorem_of_cover_data (n := 7) (by norm_num) P hPm hPd (fun _ => τ) (fun _ => hτ)
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

end SteklovCoalescence

end
