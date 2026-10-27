module

public import RequestProject.BlaschkeFibres
public import RequestProject.CircleFibre
public import RequestProject.HolCover

/-!
# Finite Blaschke products: norms, radii, circle fibres

For a finite Blaschke product `B` of degree `n ≥ 1`:
* `IsFiniteBlaschke.norm_lt_one_iff`, `norm_eq_one_iff`: in a pole-free disk `ball 0 R`,
  `|B p| < 1 ↔ |p| < 1` and `|B p| = 1 ↔ |p| = 1`;
* `IsFiniteBlaschke.exists_radii`: radii `1 < R₀ < R` and `c > 1` with `B` holomorphic on
  `ball 0 R`, finite fibres of size `≤ n` there, `|B| ≥ c` for `R₀ ≤ |p| < R`, and `B' ≠ 0` on
  the closed annulus `1 ≤ |p| ≤ R₀`;
* `IsFiniteBlaschke.circFibre_ncard`: every circle fibre has exactly `n` points.
-/

@[expose] public section

open Complex Metric Set Filter Topology

noncomputable section

namespace SteklovBlaschke

variable {a z : ℂ}

lemma norm_bfac_lt_one' (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖bfac a z‖ < 1 := by
  have hd := denom_ne_zero ha hz.le
  rw [bfac, norm_div, div_lt_one (norm_pos_iff.2 hd)]
  have h1 : normSq a < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have h2 : normSq z < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have := normSq_denom_sub a z
  have h3 : normSq (z - a) < normSq (1 - (starRingEnd ℂ) a * z) := by nlinarith
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at h3
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]

lemma one_lt_norm_bfac' (ha : ‖a‖ < 1) (hz : 1 < ‖z‖) (hd : 1 - (starRingEnd ℂ) a * z ≠ 0) :
    1 < ‖bfac a z‖ := by
  rw [bfac, norm_div, one_lt_div (norm_pos_iff.2 hd)]
  have h1 : normSq a < 1 := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have h2 : 1 < normSq z := by rw [normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have := normSq_denom_sub a z
  have h3 : normSq (1 - (starRingEnd ℂ) a * z) < normSq (z - a) := by nlinarith
  rw [normSq_eq_norm_sq, normSq_eq_norm_sq] at h3
  nlinarith [norm_nonneg (z - a), norm_nonneg (1 - (starRingEnd ℂ) a * z)]

/-- A pole-free radius for the factors. -/
lemma exists_poleFree {n : ℕ} {a : Fin n → ℂ} (ha : ∀ l, ‖a l‖ < 1) :
    ∃ R > 1, ∀ p ∈ ball (0:ℂ) R, ∀ l, 1 - (starRingEnd ℂ) (a l) * p ≠ 0 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨2, by norm_num, fun p _ l => l.elim0⟩
  obtain ⟨m, hm0, hm1, ham⟩ : ∃ m : ℝ, 0 ≤ m ∧ m < 1 ∧ ∀ l, ‖a l‖ ≤ m := by
    refine ⟨Finset.univ.sup' ⟨⟨0, hn⟩, Finset.mem_univ _⟩ fun l => ‖a l‖, ?_, ?_, fun l =>
      Finset.le_sup' (fun l => ‖a l‖) (Finset.mem_univ l)⟩
    · exact (norm_nonneg _).trans (Finset.le_sup' (fun l => ‖a l‖) (Finset.mem_univ ⟨0, hn⟩))
    · exact (Finset.sup'_lt_iff _).2 fun l _ => ha l
  refine ⟨2 / (1 + m), by show 1 < 2 / (1 + m); rw [lt_div_iff₀ (by linarith)]; linarith,
    fun p hp l h => ?_⟩
  have h1 : (starRingEnd ℂ) (a l) * p = 1 := by linear_combination -h
  have hmR : m * (2 / (1 + m)) < 1 := by
    rw [mul_div_assoc', div_lt_one (by linarith)]; linarith
  have : ‖(starRingEnd ℂ) (a l) * p‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    rw [mem_ball_zero_iff] at hp
    calc ‖a l‖ * ‖p‖ ≤ m * (2 / (1 + m)) := mul_le_mul (ham l) hp.le (norm_nonneg _) hm0
      _ < 1 := hmR
  rw [h1, norm_one] at this
  exact lt_irrefl _ this

lemma prod_lt_one_aux {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (h0 : ∀ l, 0 ≤ f l)
    (h1 : ∀ l, f l < 1) : ∏ l, f l < 1 := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ⟨0, hn⟩)]
  exact mul_lt_one_of_nonneg_of_lt_one_left (h0 _) (h1 _)
    (Finset.prod_le_one₀ (fun l _ => h0 l) (fun l _ => (h1 l).le))

lemma one_lt_prod_aux {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (h1 : ∀ l, 1 < f l) :
    1 < ∏ l, f l := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ⟨0, hn⟩)]
  have hrest : 1 ≤ ∏ l ∈ Finset.univ.erase ⟨0, hn⟩, f l := by
    exact Finset.one_le_prod₀ (s := Finset.univ.erase ⟨0, hn⟩) fun l _ => (h1 l).le
  nlinarith [h1 ⟨0, hn⟩]

/-- Norm trichotomy for a finite Blaschke product in a pole-free disk. -/
theorem IsFiniteBlaschke.exists_norm_iff {B : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n)
    (hn : 0 < n) : ∃ R > 1, ∀ p ∈ ball (0:ℂ) R,
      (‖B p‖ < 1 ↔ ‖p‖ < 1) ∧ (‖B p‖ = 1 ↔ ‖p‖ = 1) := by
  obtain ⟨η, a, hη, ha, rfl⟩ := hB
  obtain ⟨R, hR, hpole⟩ := exists_poleFree ha
  refine ⟨R, hR, fun p hp => ?_⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  simp only [norm_mul, hη, one_mul, norm_prod]
  have hlt : ‖p‖ < 1 → ∏ l, ‖bfac (a l) p‖ < 1 := fun h =>
    prod_lt_one_aux hn _ (fun _ => norm_nonneg _) (fun l => norm_bfac_lt_one' (ha l) h)
  have heq : ‖p‖ = 1 → ∏ l, ‖bfac (a l) p‖ = 1 := fun h =>
    Finset.prod_eq_one fun l _ => norm_bfac_eq_one (ha l) h
  have hgt : 1 < ‖p‖ → 1 < ∏ l, ‖bfac (a l) p‖ := fun h =>
    one_lt_prod_aux hn _ (fun l => one_lt_norm_bfac' (ha l) h (hpole p hp l))
  rcases lt_trichotomy ‖p‖ 1 with h | h | h
  · have := hlt h
    exact ⟨⟨fun _ => h, fun _ => this⟩, ⟨fun h' => absurd h' this.ne, fun h' => absurd h' h.ne⟩⟩
  · have := heq h
    exact ⟨⟨fun h' => absurd this h'.ne, fun h' => absurd h h'.ne⟩, ⟨fun _ => h, fun _ => this⟩⟩
  · have := hgt h
    exact ⟨⟨fun h' => absurd h' (not_lt.2 this.le), fun h' => absurd h' (not_lt.2 h.le)⟩,
      ⟨fun h' => absurd h' this.ne', fun h' => absurd h' h.ne'⟩⟩

/-- Points of an annulus near the circle are in its closed thickening. -/
lemma mem_cthickening_sphere {p : ℂ} {δ : ℝ} (h1 : 1 ≤ ‖p‖) (h2 : ‖p‖ ≤ 1 + δ) :
    p ∈ cthickening δ (sphere (0:ℂ) 1) := by
  have hp0 : ‖p‖ ≠ 0 := by linarith
  have hp0' : (‖p‖ : ℂ) ≠ 0 := by exact_mod_cast hp0
  refine mem_cthickening_of_dist_le p (p / ‖p‖) δ _ ?_ ?_
  · rw [mem_sphere_zero_iff_norm, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), div_self hp0]
  · rw [dist_eq_norm]
    have : p - p / ‖p‖ = ((1 - ‖p‖⁻¹ : ℝ) : ℂ) * p := by
      push_cast; field_simp
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by
      rw [sub_nonneg]; exact inv_le_one_of_one_le₀ h1)]
    rw [sub_mul, inv_mul_cancel₀ hp0]
    linarith

/-- **Radii for a finite Blaschke product.** -/
theorem IsFiniteBlaschke.exists_radii {B : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n)
    (hn : 0 < n) : ∃ R R₀ c : ℝ, 1 < R₀ ∧ R₀ < R ∧ 1 < c ∧
      DifferentiableOn ℂ B (ball 0 R) ∧
      (∀ p ∈ ball (0:ℂ) R, (‖B p‖ < 1 ↔ ‖p‖ < 1) ∧ (‖B p‖ = 1 ↔ ‖p‖ = 1)) ∧
      (∀ w, {p | p ∈ ball (0:ℂ) R ∧ B p = w}.Finite) ∧
      (∀ w, {p | p ∈ ball (0:ℂ) R ∧ B p = w}.ncard ≤ n) ∧
      (∀ p ∈ ball (0:ℂ) R, R₀ ≤ ‖p‖ → c ≤ ‖B p‖) ∧
      (∀ p : ℂ, 1 ≤ ‖p‖ → ‖p‖ ≤ R₀ → deriv B p ≠ 0) := by
  obtain ⟨R₁, hR₁, hd₁, hfin₁, hcard₁, hout₁⟩ := hB.exists_nbhd hn
  obtain ⟨R₂, hR₂, hnorm₂⟩ := hB.exists_norm_iff hn
  set R := min R₁ R₂ with hRdef
  have hR : 1 < R := lt_min hR₁ hR₂
  have hRR₁ : ball (0:ℂ) R ⊆ ball 0 R₁ := ball_subset_ball (min_le_left _ _)
  have hRR₂ : ball (0:ℂ) R ⊆ ball 0 R₂ := ball_subset_ball (min_le_right _ _)
  have hd : DifferentiableOn ℂ B (ball 0 R) := hd₁.mono hRR₁
  -- the derivative does not vanish near the circle
  have hdd : DifferentiableOn ℂ (deriv B) (ball 0 R) := hd.deriv isOpen_ball
  obtain ⟨q, -, hqpos, -, -, -, -, hqd⟩ := blaschke_circle_data hB hn
  have hsph : sphere (0:ℂ) 1 ⊆ ball 0 R ∩ {p | deriv B p ≠ 0} := by
    intro p hp
    have hp1 : ‖p‖ = 1 := mem_sphere_zero_iff_norm.1 hp
    obtain ⟨t, rfl⟩ := circle_surj hp1
    refine ⟨mem_ball_zero_iff.2 (by rw [hp1]; exact hR), fun h => ?_⟩
    have := hqd t
    rw [h, norm_zero] at this
    exact (hqpos t).ne' this.symm
  have hopen : IsOpen (ball (0:ℂ) R ∩ {p | deriv B p ≠ 0}) :=
    hdd.continuousOn.isOpen_inter_preimage isOpen_ball isOpen_ne
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_sphere (0:ℂ) 1).exists_cthickening_subset_open hopen hsph
  set R₀ := min (1 + δ) ((1 + R) / 2) with hR₀def
  have hR₀1 : 1 < R₀ := lt_min (by linarith) (by linarith)
  have hR₀R : R₀ < R := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  obtain ⟨c, hc, hout⟩ := hout₁ R₀ hR₀1 (lt_of_lt_of_le hR₀R (min_le_left _ _))
  refine ⟨R, R₀, c, hR₀1, hR₀R, hc, hd, fun p hp => hnorm₂ p (hRR₂ hp), fun w => ?_,
    fun w => ?_, fun p hp hp' => hout p (hRR₁ hp) hp', fun p h1 h2 => ?_⟩
  · exact (hfin₁ w).subset fun p hp => ⟨hRR₁ hp.1, hp.2⟩
  · exact (Set.ncard_le_ncard (t := {p | p ∈ ball (0:ℂ) R₁ ∧ B p = w})
      (fun p hp => ⟨hRR₁ hp.1, hp.2⟩) (hfin₁ w)).trans (hcard₁ w)
  · exact (hδsub (mem_cthickening_sphere h1 (h2.trans (min_le_left _ _)))).2

/-- Near the closed disk, `|B| < c` for any `c > 1`. -/
theorem exists_radius_norm_lt {B : ℂ → ℂ} {R : ℝ} (hR : 1 < R) (hd : DifferentiableOn ℂ B (ball 0 R))
    (hnorm : ∀ p ∈ ball (0:ℂ) R, (‖B p‖ < 1 ↔ ‖p‖ < 1) ∧ (‖B p‖ = 1 ↔ ‖p‖ = 1))
    {c : ℝ} (hc : 1 < c) {R₀ : ℝ} (hR₀ : 1 < R₀) :
    ∃ RU, 1 < RU ∧ RU < R₀ ∧ ∀ p ∈ closedBall (0:ℂ) RU, ‖B p‖ < c := by
  have hsph : sphere (0:ℂ) 1 ⊆ ball 0 R ∩ {p | ‖B p‖ < c} := by
    intro p hp
    have hp1 : ‖p‖ = 1 := mem_sphere_zero_iff_norm.1 hp
    have hpR : p ∈ ball (0:ℂ) R := mem_ball_zero_iff.2 (by rw [hp1]; exact hR)
    refine ⟨hpR, ?_⟩
    show ‖B p‖ < c
    rw [(hnorm p hpR).2.2 hp1]; exact hc
  have hopen : IsOpen (ball (0:ℂ) R ∩ {p | ‖B p‖ < c}) :=
    hd.continuousOn.norm.isOpen_inter_preimage isOpen_ball isOpen_Iio
  obtain ⟨δ, hδ, hδsub⟩ := (isCompact_sphere (0:ℂ) 1).exists_cthickening_subset_open hopen hsph
  set RU := min (1 + δ) ((1 + R₀) / 2)
  refine ⟨RU, lt_min (by linarith) (by linarith), lt_of_le_of_lt (min_le_right _ _)
    (by linarith), fun p hp => ?_⟩
  rw [mem_closedBall_zero_iff] at hp
  rcases lt_or_ge ‖p‖ 1 with h | h
  · have hpR : p ∈ ball (0:ℂ) R := mem_ball_zero_iff.2 (by linarith)
    exact ((hnorm p hpR).1.2 h).trans hc
  · exact (hδsub (mem_cthickening_sphere h (hp.trans (min_le_left _ _)))).2

/-- **Circle fibres have exactly `n` points.** -/
theorem IsFiniteBlaschke.circFibre_ncard {B : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n)
    (hn : 0 < n) {w : ℂ} (hw : ‖w‖ = 1) : {z : ℂ | ‖z‖ = 1 ∧ B z = w}.ncard = n := by
  obtain ⟨q, hq, hpos, hper, hint, hderiv, hnorm, -⟩ := blaschke_circle_data hB hn
  obtain ⟨y, rfl⟩ := circle_surj hw
  obtain ⟨c, hlift⟩ := exists_lift hq hderiv hnorm
  have hsum := circFibreSum_eq_sum (liftFun_strictMono c hq hpos)
    (liftFun_surjective c hq hpos hper hint hn) (liftFun_add_period c hq hper hint) hlift
    (fun _ => 1) y
  unfold circFibreSum at hsum
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hsum
  have hfin := circFibre_finite hB hn (exp (y * I))
  haveI : Finite {z : ℂ // ‖z‖ = 1 ∧ B z = exp (y * I)} := hfin.to_subtype
  haveI := Fintype.ofFinite {z : ℂ // ‖z‖ = 1 ∧ B z = exp (y * I)}
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  have : Fintype.card {z : ℂ // ‖z‖ = 1 ∧ B z = exp (y * I)} = n := by exact_mod_cast hsum
  rw [← _root_.Nat.card_coe_set_eq]
  exact (Nat.card_eq_fintype_card (α := {z : ℂ // ‖z‖ = 1 ∧ B z = exp (y * I)})).trans this

end SteklovBlaschke

end
