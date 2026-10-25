module

public import RequestProject.BlaschkeCoverData
public import RequestProject.CoverKernel
public import RequestProject.TransplantKernel

/-!
# Spectral comparison for two finite Blaschke products with a monodromy-invariant matrix

Let `B₁, B₂` be finite Blaschke products of the same degree `n ≥ 1` whose critical values in the
disk lie in a finite set `C ⊆ ball 0 ρ`, `ρ < 1`.  Over the base `Xs = ball 0 c' \ C` (`c' > 1`
small) both are coverings (`BCover.isCoveringMap_bproj`).  Given bijective labellings of the fibres
over a base point `x₀` and a matrix `T` with orthonormal columns that is invariant under the
monodromy of all loops in the small disk `|w| ≤ ρ`, the transported kernel
(`CoverKernel.kernel`) satisfies **all** hypotheses of
`SteklovTransplant.weightedSteklovEigenvalue_le_of_kernel`, whence
`σ_k(𝔻, |B₂'|) ≤ σ_k(𝔻, |B₁'|)` for all `k` (`BKernel.weightedSteklovEigenvalue_le`).
-/

@[expose] public section

open Complex Metric Set Filter Topology

noncomputable section

namespace BKernel

open SteklovBlaschke BCover

/-- The base `ball 0 c' \ C`. -/
abbrev Xb (c' : ℝ) (C : Set ℂ) : Set ℂ := ball (0:ℂ) c' \ C

section base

variable {c' ρ : ℝ} {C : Set ℂ}

lemma isOpen_Xb (hC : C.Finite) : IsOpen (Xb c' C) := isOpen_ball.sdiff hC.isClosed

lemma sphere_subset_Xb (hc' : 1 < c') (hρ1 : ρ < 1) (hCρ : C ⊆ ball 0 ρ) :
    sphere (0:ℂ) 1 ⊆ Xb c' C := by
  intro w hw
  have hw1 : ‖w‖ = 1 := mem_sphere_zero_iff_norm.1 hw
  refine ⟨mem_ball_zero_iff.2 (by rw [hw1]; exact hc'), fun hwC => ?_⟩
  have := mem_ball_zero_iff.1 (hCρ hwC)
  linarith

lemma isRadStable_Xb (hρ0 : 0 < ρ) (hCρ : C ⊆ ball 0 ρ) :
    MonoTransfer.IsRadStable ρ (Xb c' C) := by
  intro t ht0 ht1 w ⟨hw, hwC⟩
  refine ⟨mem_ball_zero_iff.2 ((MonoTransfer.norm_rad_le w hρ0 ht0 ht1).trans_lt
    (mem_ball_zero_iff.1 hw)), fun hC' => ?_⟩
  rcases le_or_gt ‖w‖ ρ with hle | hlt
  · rw [MonoTransfer.rad_of_le hle hρ0] at hC'; exact hwC hC'
  · have h1 := MonoTransfer.le_norm_rad w hρ0 ht0 ht1 hlt.le
    have h2 := mem_ball_zero_iff.1 (hCρ hC')
    linarith

lemma pathConnected_Xb (hc' : 1 < c') (hC : C.Finite) : PathConnectedSpace (Xb c' C) :=
  isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_ball_diff (by linarith) hC)

end base

section single

variable {B : ℂ → ℂ} {n : ℕ} {R R₀ c : ℝ} {c' ρ : ℝ} {C : Set ℂ}

lemma Xb_subset (hcc : c' ≤ c) : Xb c' C ⊆ ball 0 c :=
  fun _ hw => ball_subset_ball hcc hw.1

lemma crit_Xb (hcrit : ∀ z : ℂ, ‖z‖ < 1 → deriv B z = 0 → B z ∈ C) :
    ∀ z : ℂ, ‖z‖ < 1 → B z ∈ Xb c' C → deriv B z ≠ 0 :=
  fun z hz hBz hd => hBz.2 (hcrit z hz hd)

/-- **A finite Blaschke product maps the disk onto the disk.** -/
theorem exists_preimage (hB : IsFiniteBlaschke B n) (hn : 0 < n) (h : BRadii B n R R₀ c)
    (hc' : 1 < c') (hcc : c' ≤ c) (hρ1 : ρ < 1) (hC : C.Finite) (hCρ : C ⊆ ball 0 ρ)
    (hcrit : ∀ z : ℂ, ‖z‖ < 1 → deriv B z = 0 → B z ∈ C) {w : ℂ} (hw : ‖w‖ < 1) :
    ∃ z : ℂ, ‖z‖ < 1 ∧ B z = w := by
  haveI := pathConnected_Xb hc' hC
  have hXc := Xb_subset (C := C) hcc
  have hR1 : 1 < R := h.1.trans h.2.1
  -- first for regular values
  have hreg : ∀ w : ℂ, ‖w‖ < 1 → w ∉ C → ∃ z : ℂ, ‖z‖ < 1 ∧ B z = w := by
    intro w hw hwC
    have hwX : w ∈ Xb c' C := ⟨mem_ball_zero_iff.2 (hw.trans hc'), hwC⟩
    have hcard := card_fibre h hXc hB hn (crit_Xb hcrit) (sphere_subset_Xb hc' hρ1 hCρ)
      ⟨w, hwX⟩
    haveI := finite_fibre h hXc ⟨w, hwX⟩
    have hne : Nonempty (bproj B R₀ (Xb c' C) ⁻¹' {⟨w, hwX⟩}) :=
      Nat.card_pos_iff.1 (by rw [hcard]; exact hn) |>.1
    obtain ⟨e⟩ := hne
    set p := fibreEquiv h hXc _ e
    have hpB : B p.1 = w := p.2.2
    refine ⟨p.1, ?_, hpB⟩
    exact ((h.2.2.2.2.1 p.1 p.2.1).1).1 (by rw [hpB]; exact hw)
  by_cases hwC : w ∈ C
  swap
  · exact hreg w hw hwC
  -- a limit argument for the finitely many critical values
  have hK : IsCompact (B '' closedBall 0 1) :=
    (isCompact_closedBall 0 1).image_of_continuousOn
      (h.2.2.2.1.continuousOn.mono (closedBall_subset_ball hR1))
  have hsub : ball (0:ℂ) 1 ∩ Cᶜ ⊆ B '' closedBall 0 1 := by
    rintro v ⟨hv, hvC⟩
    obtain ⟨z, hz, rfl⟩ := hreg v (mem_ball_zero_iff.1 hv) hvC
    exact ⟨z, mem_closedBall_zero_iff.2 hz.le, rfl⟩
  have hcl : ball (0:ℂ) 1 ⊆ closure (ball (0:ℂ) 1 ∩ Cᶜ) :=
    (hC.countable.dense_compl ℝ).open_subset_closure_inter isOpen_ball
  obtain ⟨z, hz, hzw⟩ := (closure_minimal hsub hK.isClosed) (hcl (mem_ball_zero_iff.2 hw))
  refine ⟨z, ?_, hzw⟩
  rcases (mem_closedBall_zero_iff.1 hz).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hzR : z ∈ ball (0:ℂ) R := mem_ball_zero_iff.2 (by rw [heq]; exact hR1)
    have := ((h.2.2.2.2.1 z hzR).2).2 heq
    rw [hzw] at this; linarith

end single

section pair

variable {B₁ B₂ : ℂ → ℂ} {n : ℕ} {R₁ R₀₁ c₁ R₂ R₀₂ c₂ c' ρ : ℝ} {C : Set ℂ}

open Classical in
/-- **Spectral comparison for a pair of finite Blaschke products** with a monodromy-invariant
matrix `T` with orthonormal columns (no kernel, isometry or spectral equality is assumed: the
kernel is constructed by parallel transport and all hypotheses of the transplantation theorem
are verified). -/
theorem weightedSteklovEigenvalue_le
    (hB₁ : IsFiniteBlaschke B₁ n) (hB₂ : IsFiniteBlaschke B₂ n) (hn : 0 < n)
    (h₁ : BRadii B₁ n R₁ R₀₁ c₁) (h₂ : BRadii B₂ n R₂ R₀₂ c₂)
    (hc' : 1 < c') (hc₁ : c' ≤ c₁) (hc₂ : c' ≤ c₂) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hC : C.Finite) (hCρ : C ⊆ ball 0 ρ)
    (hcr₁ : ∀ z : ℂ, ‖z‖ < 1 → deriv B₁ z = 0 → B₁ z ∈ C)
    (hcr₂ : ∀ z : ℂ, ‖z‖ < 1 → deriv B₂ z = 0 → B₂ z ∈ C)
    (x₀ : Xb c' C) (hx₀ : ‖(x₀ : ℂ)‖ ≤ ρ)
    {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
    (L₂ : bproj B₂ R₀₂ (Xb c' C) ⁻¹' {x₀} → ι) (L₁ : bproj B₁ R₀₁ (Xb c' C) ⁻¹' {x₀} → κ)
    (hL₂ : Function.Bijective L₂) (hL₁ : Function.Bijective L₁)
    (T : ι → κ → ℝ) (hcol : ∀ j j', ∑ i, T i j * T i j' = if j = j' then 1 else 0)
    (hT : ∀ (cov₂ : IsCoveringMap (bproj B₂ R₀₂ (Xb c' C)))
      (cov₁ : IsCoveringMap (bproj B₁ R₀₁ (Xb c' C))) (γ : Path x₀ x₀),
      (∀ s, ‖(γ s : ℂ)‖ ≤ ρ) → ∀ a b,
        T (L₂ (cov₂.monodromy (Path.Homotopic.Quotient.mk γ) a))
          (L₁ (cov₁.monodromy (Path.Homotopic.Quotient.mk γ) b)) = T (L₂ a) (L₁ b))
    (k : ℕ) :
    Steklov.weightedSteklovEigenvalue (fun z => ‖deriv B₂ z‖) k ≤
      Steklov.weightedSteklovEigenvalue (fun z => ‖deriv B₁ z‖) k := by
  have hXo : IsOpen (Xb c' C) := isOpen_Xb hC
  haveI := pathConnected_Xb hc' hC
  haveI : LocallyPathConnectedSpace (Xb c' C) := hXo.locPathConnectedSpace
  have hXc₁ : Xb c' C ⊆ ball 0 c₁ := Xb_subset hc₁
  have hXc₂ : Xb c' C ⊆ ball 0 c₂ := Xb_subset hc₂
  have cov₁ := isCoveringMap_bproj h₁ hXc₁ (crit_Xb hcr₁)
  have cov₂ := isCoveringMap_bproj h₂ hXc₂ (crit_Xb hcr₂)
  have hinv : CoverKernel.IsInvariant cov₂ cov₁ x₀ L₂ L₁ T := by
    intro γ a b
    induction γ using Path.Homotopic.Quotient.ind with | mk γ =>
    obtain ⟨γ', hγ', heq⟩ :=
      MonoTransfer.exists_homotopic_small hρ0 (isRadStable_Xb hρ0 hCρ) hx₀ γ
    rw [heq]
    exact hT cov₂ cov₁ γ' hγ' a b
  have hR₂1 : 1 < R₂ := h₂.1.trans h₂.2.1
  have hR₁1 : 1 < R₁ := h₁.1.trans h₁.2.1
  obtain ⟨RU, hRU1, hRU, hBU⟩ := exists_radius_norm_lt hR₂1 h₂.2.2.2.1 h₂.2.2.2.2.1 hc' h₂.1
  have hUR₂ : ball (0:ℂ) RU ⊆ ball 0 R₂ := ball_subset_ball (hRU.le.trans h₂.2.1.le)
  -- the exceptional set
  have hSfin : {z : ℂ | ‖z‖ < 1 ∧ B₂ z ∈ C}.Finite := by
    refine (hC.biUnion fun c _ => h₂.2.2.2.2.2.1 c).subset ?_
    rintro z ⟨hz, hzC⟩
    exact mem_biUnion hzC ⟨mem_ball_zero_iff.2 (hz.trans hR₂1), rfl⟩
  set S := hSfin.toFinset with hSdef
  have hmemS : ∀ z, z ∈ (S : Set ℂ) ↔ ‖z‖ < 1 ∧ B₂ z ∈ C := fun z => by
    simp [hSdef]
  have hCS : ∀ w : ℂ, ‖w‖ < 1 → w ∈ C → w ∈ B₂ '' (S : Set ℂ) := by
    intro w hw hwC
    obtain ⟨z, hz, rfl⟩ := exists_preimage hB₂ hn h₂ hc' hc₂ hρ1 hC hCρ hcr₂ hw
    exact ⟨z, (hmemS z).2 ⟨hz, hwC⟩, rfl⟩
  have hUX : ∀ z' ∈ ball (0:ℂ) RU, z' ∉ (S : Set ℂ) → B₂ z' ∈ Xb c' C := by
    intro z' hz' hzS
    have hlt := hBU z' (ball_subset_closedBall hz')
    refine ⟨mem_ball_zero_iff.2 hlt, fun hC' => hzS ((hmemS z').2 ⟨?_, hC'⟩)⟩
    have h1 := mem_ball_zero_iff.1 (hCρ hC')
    exact ((h₂.2.2.2.2.1 z' (hUR₂ hz')).1).1 (by linarith)
  have hW₁R₀ : ∀ p ∈ ball (0:ℂ) R₁, B₁ p ∈ Xb c' C → ‖p‖ < R₀₁ := fun p hp hX =>
    norm_lt_R₀ h₁ hXc₁ (norm_le_R₀_of_fibre h₁ hXc₁ hp hX) hX
  -- the kernel on `ℂ × ℂ`
  set K₀ := CoverKernel.kernel cov₂ cov₁ x₀ L₂ L₁ T with hK₀
  let Kc : ℂ → ℂ → ℝ := fun z' p =>
    if hz : ‖z'‖ < R₀₂ ∧ B₂ z' ∈ Xb c' C then
      if hp : ‖p‖ < R₀₁ ∧ B₁ p ∈ Xb c' C then K₀ (toE hz.1 hz.2) (toE hp.1 hp.2) else 0
    else 0
  have hKev : ∀ e₂ e₁, Kc (ev e₂) (ev e₁) = K₀ e₂ e₁ := by
    intro e₂ e₁
    simp only [Kc, dif_pos (show _ ∧ _ from ⟨ev_norm_lt h₂ hXc₂ e₂, B_ev_mem e₂⟩),
      dif_pos (show _ ∧ _ from ⟨ev_norm_lt h₁ hXc₁ e₁, B_ev_mem e₁⟩)]
    rfl
  set M := Finset.univ.sup' Finset.univ_nonempty fun ij : ι × κ => |T ij.1 ij.2| with hM
  have hM0 : 0 ≤ M := (abs_nonneg _).trans
    (Finset.le_sup' (fun ij : ι × κ => |T ij.1 ij.2|) (Finset.mem_univ (Classical.arbitrary _)))
  have hKb : ∃ M, ∀ z' p, |Kc z' p| ≤ M := by
    refine ⟨M, fun z' p => ?_⟩
    simp only [Kc]
    split_ifs
    · exact CoverKernel.abs_kernel_le _ _
    · rw [abs_zero]; exact hM0
    · rw [abs_zero]; exact hM0
  -- orthonormality on fibres
  have key : ∀ (x : Xb c' C) (S' : Set ℂ), S' = {z | z ∈ ball (0:ℂ) R₂ ∧ B₂ z = x} →
      ∀ p p' : ℂ, ‖p‖ < R₀₁ → B₁ p = x → ‖p'‖ < R₀₁ → B₁ p' = x →
      ∑ᶠ z' ∈ S', Kc z' p * Kc z' p' = if p = p' then 1 else 0 := by
    intro x S' hS' p p' hp hpx hp' hp'x
    haveI := finite_fibre h₂ hXc₂ x
    haveI := finite_fibre h₁ hXc₁ x
    haveI := Fintype.ofFinite (bproj B₂ R₀₂ (Xb c' C) ⁻¹' {x})
    have hpX : B₁ p ∈ Xb c' C := by rw [hpx]; exact x.2
    have hp'X : B₁ p' ∈ Xb c' C := by rw [hp'x]; exact x.2
    set b : bproj B₁ R₀₁ (Xb c' C) ⁻¹' {x} := ⟨toE hp hpX, Subtype.ext hpx⟩
    set b' : bproj B₁ R₀₁ (Xb c' C) ⁻¹' {x} := ⟨toE hp' hp'X, Subtype.ext hp'x⟩
    rw [finsum_fibre h₂ hXc₂ x hS']
    have hterm : ∀ a : bproj B₂ R₀₂ (Xb c' C) ⁻¹' {x},
        Kc (ev a.1) p * Kc (ev a.1) p' =
          CoverKernel.fibK cov₂ cov₁ x₀ L₂ L₁ T x a b *
            CoverKernel.fibK cov₂ cov₁ x₀ L₂ L₁ T x a b' := by
      intro a
      have e1 : Kc (ev a.1) p = Kc (ev a.1) (ev b.1) := rfl
      have e2 : Kc (ev a.1) p' = Kc (ev a.1) (ev b'.1) := rfl
      rw [e1, e2, hKev, hKev, hK₀, CoverKernel.kernel_fibre, CoverKernel.kernel_fibre]
    rw [Finset.sum_congr rfl fun a _ => hterm a,
      CoverKernel.fibK_sum_mul hL₂ hL₁.1 hcol b b']
    by_cases hpp : p = p'
    · subst hpp
      have hbb : b = b' := rfl
      simp [hbb]
    · have hbb : b ≠ b' := fun h =>
        hpp (congrArg (fun e : bproj B₁ R₀₁ (Xb c' C) ⁻¹' {x} => ev e.1) h)
      simp [hbb, hpp]
  refine SteklovTransplant.weightedSteklovEigenvalue_le_of_kernel hB₁ hn hB₂ hn
    (U := ball 0 RU) isOpen_ball (closedBall_subset_ball hRU1) (h₂.2.2.2.1.mono hUR₂)
    (W₁ := ball 0 R₁) isOpen_ball (closedBall_subset_ball hR₁1) h₁.2.2.2.1
    (fun p hp hBp => ((h₁.2.2.2.2.1 p hp).2).1 hBp)
    (fun p hp hBp => ((h₁.2.2.2.2.1 p hp).1).1 hBp) h₁.2.2.2.2.2.1 ⟨n, fun w => ?_⟩
    (L := closedBall 0 R₀₁) (V := ball 0 c') (isCompact_closedBall _ _)
    (closedBall_subset_ball h₁.2.1) isOpen_ball ?_ ?_ ?_ Kc hKb S ?_ ?_ ?_ ?_ ?_ ?_ ?_ k
  · rw [← Set.ncard_eq_toFinset_card _ (h₁.2.2.2.2.2.1 w)]
    exact h₁.2.2.2.2.2.2.1 w
  · rintro _ ⟨z, hz, rfl⟩
    exact mem_ball_zero_iff.2 (hBU z (ball_subset_closedBall hz))
  · intro p hp hBp
    rw [mem_closedBall_zero_iff]
    by_contra hle; push_neg at hle
    have := h₁.2.2.2.2.2.2.2.1 p hp hle.le
    have := mem_ball_zero_iff.1 hBp
    linarith
  · intro w
    exact (h₂.2.2.2.2.2.1 w).subset fun z hz => ⟨mem_ball_zero_iff.2 (hz.1.trans hR₂1), hz.2⟩
  · intro z hz
    exact ((hmemS z).1 hz).1
  · intro p hp hBp hd
    exact hBp (hCS _ (((h₁.2.2.2.2.1 p (mem_ball_zero_iff.2 (hp.trans hR₁1))).1).2 hp)
      (hcr₁ p hp hd))
  · intro z' hz' hzS p hp hpz hd
    have hX : B₁ p ∈ Xb c' C := by rw [hpz]; exact hUX z' hz' hzS
    rcases lt_or_ge ‖p‖ 1 with h1 | h1
    · exact crit_Xb hcr₁ p h1 hX hd
    · exact h₁.2.2.2.2.2.2.2.2 p h1 (hW₁R₀ p hp hX).le hd
  · intro z hz hBz hd
    exact hBz ⟨z, (hmemS z).2 ⟨hz, hcr₂ z hz hd⟩, rfl⟩
  · intro z' hz' hzS p hp hpz
    have hX₂ := hUX z' hz' hzS
    have hX₁ : B₁ p ∈ Xb c' C := by rw [hpz]; exact hX₂
    have hz'R : ‖z'‖ < R₀₂ := (mem_ball_zero_iff.1 hz').trans hRU
    have hpR := hW₁R₀ p hp hX₁
    set e₂ : Etot B₂ R₀₂ (Xb c' C) := toE hz'R hX₂
    set e₁ : Etot B₁ R₀₁ (Xb c' C) := toE hpR hX₁
    have hpe : bproj B₁ R₀₁ (Xb c' C) e₁ = bproj B₂ R₀₂ (Xb c' C) e₂ := Subtype.ext hpz
    have hev := CoverKernel.kernel_eventually_eq hinv hpe
    have emb := (isOpenEmbedding_ev h₂ hXc₂ hXo).prodMap (isOpenEmbedding_ev h₁ hXc₁ hXo)
    have hnhds : 𝓝 (z', p) = Filter.map (Prod.map ev ev) (𝓝 (e₂, e₁)) :=
      (emb.map_nhds_eq (e₂, e₁)).symm
    rw [hnhds, Filter.eventually_map]
    filter_upwards [hev] with q hq hBq
    have hq' : bproj B₁ R₀₁ (Xb c' C) q.2 = bproj B₂ R₀₂ (Xb c' C) q.1 :=
      Subtype.ext hBq.symm
    show Kc (ev q.1) (ev q.2) = Kc (ev e₂) (ev e₁)
    rw [hKev, hKev]; exact hq hq'
  · intro w hw hwS p p' hp hpw hp' hp'w
    have hwC : w ∉ C := fun h => hwS (hCS w hw h)
    have hwX : w ∈ Xb c' C := ⟨mem_ball_zero_iff.2 (hw.trans hc'), hwC⟩
    refine key ⟨w, hwX⟩ _ ?_ p p' (hp.trans h₁.1) hpw (hp'.trans h₁.1) hp'w
    ext z
    constructor
    · rintro ⟨hz, hzw⟩; exact ⟨mem_ball_zero_iff.2 (hz.trans hR₂1), hzw⟩
    · rintro ⟨hz, hzw⟩
      exact ⟨((h₂.2.2.2.2.1 z hz).1).1 (by rw [hzw]; exact hw), hzw⟩
  · intro w hw p p' hp hpw hp' hp'w
    have hwX : w ∈ Xb c' C := sphere_subset_Xb hc' hρ1 hCρ (mem_sphere_zero_iff_norm.2 hw)
    refine key ⟨w, hwX⟩ _ ?_ p p' (by rw [hp]; exact h₁.1) hpw (by rw [hp']; exact h₁.1) hp'w
    ext z
    constructor
    · rintro ⟨hz, hzw⟩; exact ⟨mem_ball_zero_iff.2 (by rw [hz]; exact hR₂1), hzw⟩
    · rintro ⟨hz, hzw⟩
      exact ⟨((h₂.2.2.2.2.1 z hz).2).1 (by rw [hzw]; exact hw), hzw⟩

end pair

end BKernel

end
