module

public import RequestProject.BlaschkeCover
public import RequestProject.MonodromyTransfer

/-!
# The covering defined by a finite Blaschke product near the closed disk

Let `B` be a finite Blaschke product of degree `n ≥ 1` with radii `1 < R₀ < R`, `c > 1` as in
`IsFiniteBlaschke.exists_radii` (packaged as `BRadii`).  For an open base `Xs ⊆ ball 0 c`
containing no critical value of `B` in `𝔻`, the map `B : B⁻¹(Xs) ∩ closedBall 0 R₀ → Xs` is a
covering map (`isCoveringMap_bproj`).  Its fibre over `x` is the full fibre
`{p ∈ ball 0 R | B p = x}` (`fibreEquiv`), which has exactly `n` points if `Xs` is path connected
and contains the unit circle (`card_fibre`).  The inclusion of the total space into `ℂ` is an
open embedding (`isOpenEmbedding_ev`).
-/

@[expose] public section

open Complex Metric Set Filter Topology

noncomputable section

namespace BCover

open SteklovBlaschke

/-- The radius data of a finite Blaschke product (the conclusion of `exists_radii`). -/
def BRadii (B : ℂ → ℂ) (n : ℕ) (R R₀ c : ℝ) : Prop :=
  1 < R₀ ∧ R₀ < R ∧ 1 < c ∧
    DifferentiableOn ℂ B (ball 0 R) ∧
    (∀ p ∈ ball (0:ℂ) R, (‖B p‖ < 1 ↔ ‖p‖ < 1) ∧ (‖B p‖ = 1 ↔ ‖p‖ = 1)) ∧
    (∀ w, {p | p ∈ ball (0:ℂ) R ∧ B p = w}.Finite) ∧
    (∀ w, {p | p ∈ ball (0:ℂ) R ∧ B p = w}.ncard ≤ n) ∧
    (∀ p ∈ ball (0:ℂ) R, R₀ ≤ ‖p‖ → c ≤ ‖B p‖) ∧
    (∀ p : ℂ, 1 ≤ ‖p‖ → ‖p‖ ≤ R₀ → deriv B p ≠ 0)

theorem exists_bRadii {B : ℂ → ℂ} {n : ℕ} (hB : IsFiniteBlaschke B n) (hn : 0 < n) :
    ∃ R R₀ c, BRadii B n R R₀ c := hB.exists_radii hn

/-- The compact domain. -/
abbrev Kb (R₀ : ℝ) : Set ℂ := closedBall (0:ℂ) R₀

/-- `B` on the compact domain. -/
def bmap (B : ℂ → ℂ) (R₀ : ℝ) : Kb R₀ → ℂ := fun e => B e

/-- The total space. -/
abbrev Etot (B : ℂ → ℂ) (R₀ : ℝ) (Xs : Set ℂ) : Type := ↥(bmap B R₀ ⁻¹' Xs)

/-- The projection. -/
def bproj (B : ℂ → ℂ) (R₀ : ℝ) (Xs : Set ℂ) : Etot B R₀ Xs → Xs :=
  Xs.restrictPreimage (bmap B R₀)

/-- The point of `ℂ` underlying a point of the total space. -/
def ev {B : ℂ → ℂ} {R₀ : ℝ} {Xs : Set ℂ} (e : Etot B R₀ Xs) : ℂ := ((e : Kb R₀) : ℂ)

variable {B : ℂ → ℂ} {n : ℕ} {R R₀ c : ℝ} {Xs : Set ℂ}

lemma bproj_val (e : Etot B R₀ Xs) : (bproj B R₀ Xs e : ℂ) = B (ev e) := rfl

lemma B_ev_mem (e : Etot B R₀ Xs) : B (ev e) ∈ Xs := e.2

lemma ev_norm_le (e : Etot B R₀ Xs) : ‖ev e‖ ≤ R₀ := mem_closedBall_zero_iff.1 (e : Kb R₀).2

lemma continuous_ev : Continuous (ev : Etot B R₀ Xs → ℂ) :=
  continuous_subtype_val.comp continuous_subtype_val

/-- Points of `ℂ` in the open range give points of the total space. -/
def toE {z : ℂ} (hz : ‖z‖ < R₀) (hBz : B z ∈ Xs) : Etot B R₀ Xs :=
  ⟨⟨z, mem_closedBall_zero_iff.2 hz.le⟩, hBz⟩

@[simp] lemma ev_toE {z : ℂ} (hz : ‖z‖ < R₀) (hBz : B z ∈ Xs) : ev (toE hz hBz) = z := rfl

section radii

variable (h : BRadii B n R R₀ c) (hXc : Xs ⊆ ball 0 c)
include h hXc

lemma norm_lt_R₀ {z : ℂ} (hz : ‖z‖ ≤ R₀) (hBz : B z ∈ Xs) : ‖z‖ < R₀ := by
  obtain ⟨_, hR₀R, -, -, -, -, -, hout, -⟩ := h
  by_contra hle
  push_neg at hle
  have hzR : z ∈ ball (0:ℂ) R := mem_ball_zero_iff.2 (hz.trans_lt hR₀R)
  have := hout z hzR hle
  have := mem_ball_zero_iff.1 (hXc hBz)
  linarith

lemma ev_norm_lt (e : Etot B R₀ Xs) : ‖ev e‖ < R₀ :=
  norm_lt_R₀ h hXc (ev_norm_le e) (B_ev_mem e)

/-- **The Blaschke covering.** -/
theorem isCoveringMap_bproj (hcrit : ∀ z : ℂ, ‖z‖ < 1 → B z ∈ Xs → deriv B z ≠ 0) :
    IsCoveringMap (bproj B R₀ Xs) := by
  obtain ⟨hR₀, hR₀R, -, hd, -, -, -, -, hder⟩ := id h
  refine HolCover.isCoveringMap_of_compact (isCompact_closedBall 0 R₀)
    (hd.continuousOn.mono (closedBall_subset_ball hR₀R)) fun z hz hBz => ?_
  have hlt := norm_lt_R₀ h hXc (mem_closedBall_zero_iff.1 hz) hBz
  refine ⟨?_, ?_, ?_⟩
  · rw [interior_closedBall _ (by linarith)]; exact mem_ball_zero_iff.2 hlt
  · exact hd.analyticAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.2 (hlt.trans hR₀R)))
  · rcases lt_or_ge ‖z‖ 1 with h1 | h1
    · exact hcrit z h1 hBz
    · exact hder z h1 hlt.le

lemma norm_le_R₀_of_fibre {p : ℂ} (hp : p ∈ ball (0:ℂ) R) (hBp : B p ∈ Xs) : ‖p‖ ≤ R₀ := by
  by_contra hle; push_neg at hle
  have := h.2.2.2.2.2.2.2.1 p hp hle.le
  have h2 := mem_ball_zero_iff.1 (hXc hBp)
  linarith

/-- The fibre over `x` is the full fibre of `B` in `ball 0 R`. -/
def fibreEquiv (x : Xs) :
    bproj B R₀ Xs ⁻¹' {x} ≃ {p : ℂ // p ∈ ball (0:ℂ) R ∧ B p = x} where
  toFun e := ⟨ev e.1, mem_ball_zero_iff.2 ((ev_norm_lt h hXc e.1).trans h.2.1),
    congrArg Subtype.val e.2⟩
  invFun p := ⟨⟨⟨p.1, mem_closedBall_zero_iff.2 (norm_le_R₀_of_fibre h hXc p.2.1
      (by rw [p.2.2]; exact x.2))⟩, show B p.1 ∈ Xs by rw [p.2.2]; exact x.2⟩,
    Subtype.ext p.2.2⟩
  left_inv e := rfl
  right_inv p := rfl

lemma fibreEquiv_val (x : Xs) (e : bproj B R₀ Xs ⁻¹' {x}) :
    ((fibreEquiv h hXc x e : {p : ℂ // p ∈ ball (0:ℂ) R ∧ B p = x}) : ℂ) = ev e.1 := rfl

lemma card_fibre_le (x : Xs) : Nat.card (bproj B R₀ Xs ⁻¹' {x}) ≤ n := by
  rw [Nat.card_congr (fibreEquiv h hXc x)]
  exact h.2.2.2.2.2.2.1 x

lemma finite_fibre (x : Xs) : Finite (bproj B R₀ Xs ⁻¹' {x}) := by
  haveI : Finite {p : ℂ // p ∈ ball (0:ℂ) R ∧ B p = x} := (h.2.2.2.2.2.1 x).to_subtype
  exact Finite.of_equiv _ (fibreEquiv h hXc x).symm

/-- **Every fibre has exactly `n` points.** -/
theorem card_fibre (hB : IsFiniteBlaschke B n) (hn : 0 < n)
    (hcrit : ∀ z : ℂ, ‖z‖ < 1 → B z ∈ Xs → deriv B z ≠ 0) [PathConnectedSpace Xs]
    (hsph : sphere (0:ℂ) 1 ⊆ Xs) (x : Xs) : Nat.card (bproj B R₀ Xs ⁻¹' {x}) = n := by
  have cov := isCoveringMap_bproj h hXc hcrit
  have h1 : (1 : ℂ) ∈ Xs := hsph (by simp)
  set w : Xs := ⟨1, h1⟩
  have hw : Nat.card (bproj B R₀ Xs ⁻¹' {w}) = n := by
    refine le_antisymm (card_fibre_le h hXc w) ?_
    rw [Nat.card_congr (fibreEquiv h hXc w)]
    have hsub : {z : ℂ | ‖z‖ = 1 ∧ B z = 1} ⊆ {p : ℂ | p ∈ ball (0:ℂ) R ∧ B p = 1} :=
      fun z hz => ⟨mem_ball_zero_iff.2 (by rw [hz.1]; linarith [h.1, h.2.1]), hz.2⟩
    have := Set.ncard_le_ncard hsub (h.2.2.2.2.2.1 1)
    rw [hB.circFibre_ncard hn (by simp)] at this
    exact this
  rw [← hw]
  exact Nat.card_congr (Equiv.ofBijective _ (cov.monodromy_bijective
    (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x w))))

lemma isOpen_range_ev (hXo : IsOpen Xs) : IsOpen (range (ev : Etot B R₀ Xs → ℂ)) ∧
    range (ev : Etot B R₀ Xs → ℂ) = {z | ‖z‖ < R₀ ∧ B z ∈ Xs} := by
  have hr : range (ev : Etot B R₀ Xs → ℂ) = {z | ‖z‖ < R₀ ∧ B z ∈ Xs} := by
    ext z
    constructor
    · rintro ⟨e, rfl⟩; exact ⟨ev_norm_lt h hXc e, B_ev_mem e⟩
    · rintro ⟨hz, hBz⟩
      exact ⟨⟨⟨z, mem_closedBall_zero_iff.2 hz.le⟩, hBz⟩, rfl⟩
  refine ⟨?_, hr⟩
  rw [hr]
  have := (h.2.2.2.1.continuousOn.mono (ball_subset_ball h.2.1.le)).isOpen_inter_preimage
    isOpen_ball hXo
  convert this using 1
  ext z; simp

/-- The inclusion of the total space in `ℂ` is an open embedding. -/
theorem isOpenEmbedding_ev (hXo : IsOpen Xs) : IsOpenEmbedding (ev : Etot B R₀ Xs → ℂ) :=
  ⟨Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal,
    (isOpen_range_ev h hXc hXo).1⟩

/-- Sums over the fibre of `B` in `ball 0 R` are sums over the covering fibre. -/
lemma finsum_fibre (x : Xs) {S' : Set ℂ} (hS' : S' = {p | p ∈ ball (0:ℂ) R ∧ B p = x})
    [Fintype (bproj B R₀ Xs ⁻¹' {x})] (f : ℂ → ℝ) :
    ∑ᶠ z ∈ S', f z = ∑ e : bproj B R₀ Xs ⁻¹' {x}, f (ev e.1) := by
  subst hS'
  rw [← finsum_set_coe_eq_finsum_mem, ← finsum_eq_sum_of_fintype]
  exact (finsum_comp_equiv (fibreEquiv h hXc x)
    (f := fun p : {p : ℂ // p ∈ ball (0:ℂ) R ∧ B p = x} => f p)).symm

end radii

/-! ### Path connectedness of the base -/

theorem isPathConnected_ball_diff {r : ℝ} (hr : 0 < r) {C : Set ℂ} (hC : C.Finite) :
    IsPathConnected (ball (0:ℂ) r \ C) := by
  set f := OpenPartialHomeomorph.univBall (0:ℂ) r
  have hinj : InjOn f univ := by
    have := f.injOn; rwa [OpenPartialHomeomorph.univBall_source] at this
  have hfin : (f ⁻¹' C).Finite := hC.preimage (hinj.mono (subset_univ _))
  have hpc : IsPathConnected (f ⁻¹' C)ᶜ :=
    hfin.countable.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
  have himg : f '' (f ⁻¹' C)ᶜ = ball (0:ℂ) r \ C := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, hz⟩
      rw [← OpenPartialHomeomorph.univBall_target (0:ℂ) hr]
      exact f.map_source (by rw [OpenPartialHomeomorph.univBall_source]; trivial)
    · rintro ⟨hw, hwC⟩
      have hwt : w ∈ f.target := by rwa [OpenPartialHomeomorph.univBall_target (0:ℂ) hr]
      refine ⟨f.symm w, ?_, f.right_inv hwt⟩
      show f (f.symm w) ∉ C
      rw [f.right_inv hwt]; exact hwC
  rw [← himg]
  exact hpc.image (OpenPartialHomeomorph.continuous_univBall (0:ℂ) r)

end BCover

end
