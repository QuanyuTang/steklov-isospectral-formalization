module

public import RequestProject.Blaschke
public import RequestProject.HolomorphicInverse
public import RequestProject.RiemannMap

/-!
# Holomorphic automorphisms of the disk, and isometries of the plane

* `DiskAut.exists_diskAut`: a holomorphic bijection `f` of `𝔻` onto itself agrees on `𝔻` with a
  Möbius automorphism `z ↦ μ (z - b)/(1 - b̄ z)` (Schwarz lemma and its equality case).
* `DiskAut.isometry_form`: every isometry of `ℂ` is `z ↦ a z + b` or `z ↦ a z̄ + b`, `|a| = 1`.
-/

@[expose] public section

open Complex Metric Set Filter Topology

noncomputable section

namespace DiskAut

open SteklovBlaschke SteklovRiemann

lemma bfac_neg_bfac {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ < 1) : bfac (-a) (bfac a w) = w := by
  have hd : 1 - (starRingEnd ℂ) a * w ≠ 0 := denom_ne_zero ha hw.le
  have haa : 1 - (starRingEnd ℂ) a * a ≠ 0 := by
    have : ‖(starRingEnd ℂ) a * a‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]; nlinarith [norm_nonneg a]
    intro h
    rw [sub_eq_zero] at h
    rw [← h, norm_one] at this
    exact lt_irrefl _ this
  set u := bfac a w with hu_def
  have hu : u * (1 - (starRingEnd ℂ) a * w) = w - a := by
    rw [hu_def, bfac, div_mul_cancel₀ _ hd]
  have hden : 1 + (starRingEnd ℂ) a * u ≠ 0 := by
    intro h0
    apply haa
    have : (1 + (starRingEnd ℂ) a * u) * (1 - (starRingEnd ℂ) a * w) =
        1 - (starRingEnd ℂ) a * a := by
      linear_combination (starRingEnd ℂ) a * hu
    rw [← this, h0, zero_mul]
  show (u - -a) / (1 - (starRingEnd ℂ) (-a) * u) = w
  rw [map_neg, div_eq_iff (by simpa using hden)]
  linear_combination hu

lemma norm_neg_lt {a : ℂ} (ha : ‖a‖ < 1) : ‖-a‖ < 1 := by rwa [norm_neg]

lemma differentiableOn_bfac {a : ℂ} (ha : ‖a‖ < 1) : DifferentiableOn ℂ (bfac a) (ball 0 1) :=
  fun _ hz => (differentiableAt_bfac ha (mem_ball_zero_iff.1 hz).le).differentiableWithinAt

lemma mapsTo_bfac {a : ℂ} (ha : ‖a‖ < 1) : MapsTo (bfac a) (ball 0 1) (ball 0 1) :=
  fun _ hz => mem_ball_zero_iff.2 (norm_bfac_lt ha (mem_ball_zero_iff.1 hz))

/-- **Holomorphic automorphisms of the disk are Möbius maps.** -/
theorem exists_diskAut {f : ℂ → ℂ} (hd : DifferentiableOn ℂ f (ball 0 1))
    (hinj : InjOn f (ball 0 1)) (him : f '' ball 0 1 = ball 0 1) :
    ∃ φ, IsDiskAut φ ∧ EqOn f φ (ball 0 1) := by
  have hmaps : MapsTo f (ball 0 1) (ball 0 1) := fun z hz => him ▸ mem_image_of_mem f hz
  set a := f 0 with ha_def
  have ha : ‖a‖ < 1 := mem_ball_zero_iff.1 (hmaps (mem_ball_self one_pos))
  set k : ℂ → ℂ := fun z => bfac a (f z) with hk
  have hkd : DifferentiableOn ℂ k (ball 0 1) :=
    fun z hz => ((differentiableAt_bfac ha (mem_ball_zero_iff.1 (hmaps hz)).le).comp z
      (hd.differentiableAt (isOpen_ball.mem_nhds hz))).differentiableWithinAt
  have hkm : MapsTo k (ball 0 1) (ball 0 1) := (mapsTo_bfac ha).comp hmaps
  have hk0 : k 0 = 0 := by simp [hk, ← ha_def, bfac_self]
  have hkinj : InjOn k (ball 0 1) := by
    intro z hz w hw h
    have h' := congrArg (bfac (-a)) h
    simp only [hk] at h'
    rw [bfac_neg_bfac ha (mem_ball_zero_iff.1 (hmaps hz)),
      bfac_neg_bfac ha (mem_ball_zero_iff.1 (hmaps hw))] at h'
    exact hinj hz hw h'
  have hksurj : ∀ w ∈ ball (0 : ℂ) 1, ∃ z ∈ ball (0 : ℂ) 1, k z = w := by
    intro w hw
    have hw' : bfac (-a) w ∈ ball (0 : ℂ) 1 := mapsTo_bfac (norm_neg_lt ha) hw
    rw [← him] at hw'
    obtain ⟨z, hz, hfz⟩ := hw'
    refine ⟨z, hz, ?_⟩
    simp only [hk, hfz]
    have := bfac_neg_bfac (norm_neg_lt ha) (mem_ball_zero_iff.1 hw)
    rwa [neg_neg] at this
  -- the inverse of `k`
  set g := Function.invFunOn k (ball 0 1) with hg
  have hgk : ∀ w ∈ ball (0 : ℂ) 1, g w ∈ ball (0 : ℂ) 1 ∧ k (g w) = w := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hksurj w hw
    rw [hg, HolInv.invFunOn_apply_self hkinj hz]
    exact ⟨hz, rfl⟩
  have hgd : DifferentiableOn ℂ g (ball 0 1) := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := hksurj w hw
    exact (HolInv.hasDerivAt_invFunOn isOpen_ball hkd hkinj hz
      (HolInv.deriv_ne_zero_of_injOn isOpen_ball hkd hkinj hz)).differentiableAt.differentiableWithinAt
  have hg0 : g 0 = 0 := by
    have := HolInv.invFunOn_apply_self hkinj (mem_ball_self one_pos)
    rw [hk0] at this; exact this
  -- Schwarz both ways: `|k z| = |z|`
  have hnorm : ∀ z ∈ ball (0 : ℂ) 1, ‖k z‖ = ‖z‖ := by
    intro z hz
    have h1 := Complex.norm_le_norm_of_mapsTo_ball hkd
      (fun w hw => ball_subset_closedBall (hkm hw)) hk0 (mem_ball_zero_iff.1 hz)
    have hkz := hkm hz
    have h2 := Complex.norm_le_norm_of_mapsTo_ball hgd
      (fun w hw => ball_subset_closedBall (hgk w hw).1) hg0 (mem_ball_zero_iff.1 hkz)
    have hgkz : g (k z) = z := by rw [hg]; exact HolInv.invFunOn_apply_self hkinj hz
    rw [hgkz] at h2
    exact le_antisymm h1 h2
  -- equality case: `k z = C z`
  set z₀ : ℂ := 1 / 2
  have hz₀ : z₀ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]; norm_num [z₀]
  have hz₀ne : z₀ ≠ 0 := by norm_num [z₀]
  have hds : ‖dslope k 0 z₀‖ = 1 / 1 := by
    rw [dslope_of_ne _ hz₀ne, slope_def_field, hk0, sub_zero, sub_zero, norm_div, hnorm z₀ hz₀,
      div_self (norm_ne_zero_iff.2 hz₀ne)]
    norm_num
  have haff := Complex.affine_of_mapsTo_ball_of_norm_dslope_eq_div hkd
    (by rw [hk0]; exact fun w hw => ball_subset_closedBall (hkm hw)) hz₀ hds
  set C := dslope k 0 z₀ with hC
  have hC1 : ‖C‖ = 1 := by rw [hds]; norm_num
  have hkC : ∀ z ∈ ball (0 : ℂ) 1, k z = C * z := by
    intro z hz
    have := haff hz
    simp only [hk0, zero_add, sub_zero, smul_eq_mul] at this
    rw [this, mul_comm]
  -- conclusion
  have hCc : C * (starRingEnd ℂ) C = 1 := by
    rw [mul_conj, normSq_eq_norm_sq, hC1]; norm_num
  refine ⟨fun z => C * bfac (-a * (starRingEnd ℂ) C) z, ⟨C, -a * (starRingEnd ℂ) C, hC1,
    by rw [norm_mul, norm_neg, Complex.norm_conj, hC1, mul_one]; exact ha, rfl⟩, ?_⟩
  intro z hz
  have hfz : f z = bfac (-a) (k z) := by
    simp only [hk]; rw [bfac_neg_bfac ha (mem_ball_zero_iff.1 (hmaps hz))]
  have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.1 hz
  have hd1 : 1 - (starRingEnd ℂ) (-a) * (C * z) ≠ 0 := by
    apply denom_ne_zero (norm_neg_lt ha)
    rw [norm_mul, hC1, one_mul]; exact hz1.le
  have hd2 : 1 - (starRingEnd ℂ) (-a * (starRingEnd ℂ) C) * z ≠ 0 := by
    apply denom_ne_zero
    · rw [norm_mul, norm_neg, Complex.norm_conj, hC1, mul_one]; exact ha
    · exact hz1.le
  show f z = C * bfac (-a * (starRingEnd ℂ) C) z
  rw [hfz, hkC z hz]
  show (C * z - -a) / (1 - (starRingEnd ℂ) (-a) * (C * z)) =
    C * ((z - -a * (starRingEnd ℂ) C) / (1 - (starRingEnd ℂ) (-a * (starRingEnd ℂ) C) * z))
  simp only [map_neg, map_mul, Complex.conj_conj]
  rw [← mul_div_assoc]
  congr 1
  · linear_combination (-a) * hCc
  · ring

/-- **Isometries of the plane** are `z ↦ a z + b` or `z ↦ a z̄ + b` with `|a| = 1`. -/
theorem isometry_form (J : ℂ ≃ᵢ ℂ) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ((∀ z, J z = a * z + b) ∨ (∀ z, J z = a * (starRingEnd ℂ) z + b)) := by
  set A := J.toRealAffineIsometryEquiv
  set f := A.linearIsometryEquiv
  have hA : ∀ z, J z = f z + J 0 := by
    intro z
    have h1 : A z = f (z - 0) + A 0 := by
      have := A.map_vadd 0 (z - 0)
      simp only [vadd_eq_add, sub_zero, add_zero] at this
      rw [sub_zero, this]
    simpa using h1
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex f
  · refine ⟨a, J 0, by simp, Or.inl fun z => ?_⟩
    rw [hA, ha, rotation_apply]
  · refine ⟨a, J 0, by simp, Or.inr fun z => ?_⟩
    rw [hA, ha]
    simp [rotation_apply]

end DiskAut

end
