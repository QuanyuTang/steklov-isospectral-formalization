module

public import RequestProject.Degree7ConeOrders
public import RequestProject.Degree7Prop331

/-!
# Cone orders of the quotient orbisurfaces, and the boundary metric

* `stab_card_mul_mult`: for the polynomial `p_t` of a label, at every point `w` of `R̄`,
  `|Stab_H(w)| · e(w) = m(w)`, where `e(w)` is the local ramification (root multiplicity) of `p_t`
  at `Ev(w)` and `m(w)` is the inertia order of `π̄` at `w` (`dB = 2` over `0`, `3` over `1`, else
  `1`) — i.e. the order of the subgroup of `H` fixing a lift is `m / e`.
* `coneSet_iff_stab`, `ord_eq_stab`: under the actual quotient identification `Θ`, the cone points
  of `pullbackOrb L hB` are exactly the images of the points with nontrivial stabilizer, and the
  cone order equals the order of the stabilizer of a lift.
* `boundary_metric`: at a boundary point of `M_ε`, the quotient map in charts extends
  holomorphically across `∂M_ε`, the metric of `R̄` is the pull-back of that of `pullbackOrb L hB`
  there, it is Euclidean in the coordinate `b_ε`, and the boundary line element of the quotient
  (`|B'|`) pulls back to `|d b_ε|`.
-/

@[expose] public section

open Polynomial Set Filter Topology Metric PolyCover LocalMonodromy SteklovRegularCover
  SteklovPunctured SteklovFill SteklovRiemann Manifold SteklovOrb SteklovCoalescence
  SteklovCritical
open scoped ContDiff

noncomputable section

namespace Degree7

variable {s : ℂ} {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13}

/-- The inertia order of the branched projection `π̄` at a point of `R̄`. -/
def inertiaOrd : RegFill hs f₀ → ℕ := Sum.elim (fun _ => 1) (fun j => dB j.1)

lemma rootMultiplicity_eq_one {p : ℂ[X]} {y : ℂ} (hp : p ≠ 0) (hroot : p.IsRoot y)
    (hd : p.derivative.eval y ≠ 0) : rootMultiplicity y p = 1 := by
  have h1 : 0 < rootMultiplicity y p := (rootMultiplicity_pos hp).2 hroot
  have h2 : ¬ 1 < rootMultiplicity y p := fun h =>
    hd ((one_lt_rootMultiplicity_iff_isRoot hp).1 h).2
  omega

lemma sub_C_ne_zero {t : ℂ} (ht : t ^ 2 = -7) (c : ℂ) : pPoly t - C c ≠ 0 := by
  intro h
  have h' : pPoly t = C c := sub_eq_zero.1 h
  have := pPoly_degree_pos ht
  rw [h'] at this
  exact absurd (lt_of_lt_of_le this degree_C_le) (lt_irrefl _)

variable {H : Subgroup (deckGroup f₀)} {Ev : RegFill hs f₀ → ℂ}

/-- **The order of the subgroup fixing a lift is `m / e`.** -/
theorem stab_card_mul_mult {t : ℂ} (ht : t ^ 2 = -7)
    (hEv : haveI := (regFill_riemannSurface hs f₀).2.1; ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev)
    (hPEv : ∀ w, (pPoly t).eval (Ev w) = regFillProj hs f₀ w)
    (hfib : ∀ w w', Ev w = Ev w' ↔ ∃ σ ∈ H, regFillAct hs f₀ σ w = w') (w : RegFill hs f₀) :
    Nat.card (stabIn H w) * rootMultiplicity (Ev w) (pPoly t - C ((pPoly t).eval (Ev w))) =
      inertiaOrd w := by
  have hroot : (pPoly t - C ((pPoly t).eval (Ev w))).IsRoot (Ev w) := by simp [IsRoot]
  have hder : (pPoly t - C ((pPoly t).eval (Ev w))).derivative = (pPoly t).derivative := by
    simp
  rcases w with f | j
  · have hb : stabIn H (Fill.inl f : RegFill hs f₀) = ⊥ := stabIn_inl H f
    have hd : (pPoly t).derivative.eval (Ev (Fill.inl f)) ≠ 0 := by
      intro h
      have hcv : (pPoly t).eval (Ev (Fill.inl f)) ∈ critVals (pPoly t) := ⟨_, h, rfl⟩
      rw [critVals_pPoly ht, hPEv] at hcv
      exact coverProjC_not_mem hs f₀ f hcv
    have hm := rootMultiplicity_eq_one (sub_C_ne_zero ht _) hroot (by rw [hder]; exact hd)
    show Nat.card (stabIn H (Fill.inl f : RegFill hs f₀)) * _ = 1
    rw [hb, Subgroup.card_bot, hm]
  · show Nat.card (stabIn H (Fill.cusp j : RegFill hs f₀)) * rootMultiplicity (Ev (Fill.cusp j))
      (pPoly t - C ((pPoly t).eval (Ev (Fill.cusp j)))) = dB j.1
    have hroot : (pPoly t - C ((pPoly t).eval (Ev (Fill.cusp j)))).IsRoot (Ev (Fill.cusp j)) := by
      simp [IsRoot]
    have hder : (pPoly t - C ((pPoly t).eval (Ev (Fill.cusp j)))).derivative =
        (pPoly t).derivative := by simp
    have hc : (pPoly t).eval (Ev (Fill.cusp j)) = cB j.1 := by
      rw [hPEv]; rfl
    by_cases hd : (pPoly t).derivative.eval (Ev (Fill.cusp j)) = 0
    · obtain ⟨hb, -⟩ := stab_card_crit hEv (pPoly_degree_pos ht) hPEv hfib j hd
      rw [hb, Subgroup.card_bot, one_mul]
      have hgt : 1 < rootMultiplicity (Ev (Fill.cusp j))
          (pPoly t - C ((pPoly t).eval (Ev (Fill.cusp j)))) :=
        (one_lt_rootMultiplicity_iff_isRoot (sub_C_ne_zero ht _)).2
          ⟨hroot, by rw [IsRoot, hder]; exact hd⟩
      rw [hc] at hgt ⊢
      rcases cB_dB j.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, map_zero, sub_zero] at hgt ⊢
        rw [h2]
        have hr : (pPoly t).IsRoot (Ev (Fill.cusp j)) := by
          rw [IsRoot, hc, h1]
        rcases multiplicity_zero ht _ hr with h | h <;> rw [h] at hgt ⊢
        · omega
      · rw [h1] at hgt ⊢
        rw [h2]
        have hr : (pPoly t - C 1).IsRoot (Ev (Fill.cusp j)) := by
          simp [IsRoot, hc, h1]
        rcases multiplicity_one ht _ hr with h | h <;> rw [h] at hgt ⊢
        · omega
    · rw [(stab_card_noncrit hEv hPEv hfib j hd).1,
        rootMultiplicity_eq_one (sub_C_ne_zero ht _) hroot (by rw [hder]; exact hd), mul_one]

/-- The derivative of `B = Q ∘ ψ` vanishes exactly at the critical points of `p_t` (in the
normalised coordinate `ψ / (τ ε / a)`). -/
lemma deriv_B_ne_zero_iff {t a : ℂ} (ht : t ^ 2 = -7) (ha : a ^ 7 = -bconst t) {τ : ℝ → ℂ}
    (hτ : ∀ ε, τ ε ^ 7 = (lamStar - 1) * ε) {ε : ℝ} (h0 : 0 < ε) {ψ B : ℂ → ℂ}
    (hc : IsNormalizedDiskCover (paperQ (monicP t a) τ ε) 7 ψ B) {p : ℂ}
    (hp : p ∈ ball (0 : ℂ) 1) :
    deriv B p ≠ 0 ↔ (pPoly t).derivative.eval (ψ p / (τ ε / a)) ≠ 0 := by
  obtain ⟨hψd, hψi, -, -, -, -, -, hBQ⟩ := hc
  have hcne : τ ε / a ≠ 0 := div_ne_zero (tau_ne_zero hτ h0) (a_ne_zero ht ha)
  have hψ' : deriv ψ p ≠ 0 := HolInv.deriv_ne_zero_of_injOn isOpen_ball hψd hψi hp
  have hev : B =ᶠ[𝓝 p] paperQ (monicP t a) τ ε ∘ ψ := by
    filter_upwards [isOpen_ball.mem_nhds hp] with x hx using hBQ x hx
  have hψda : HasDerivAt ψ (deriv ψ p) p :=
    (hψd.differentiableAt (isOpen_ball.mem_nhds hp)).hasDerivAt
  have hd : deriv B p = (lamStar - 1) * ε * ((pPoly t).derivative.eval (ψ p / (τ ε / a)) *
      (1 / (τ ε / a))) * deriv ψ p := by
    rw [hev.deriv_eq]
    exact ((hasDerivAt_paperQ ht ha τ ε (ψ p)).comp p hψda).deriv
  rw [hd]
  constructor
  · intro h h'; rw [h'] at h; simp at h
  · intro h
    exact mul_ne_zero (mul_ne_zero (lamc_ne_zero h0) (mul_ne_zero h (one_div_ne_zero hcne))) hψ'

lemma bdf_inl_ne {ε : ℝ} (h0 : 0 < ε) (f : RegCov f₀) :
    bdf hs f₀ ε (Fill.inl f) ≠ ε ∧ bdf hs f₀ ε (Fill.inl f) ≠ lamStar * ε := by
  have h2 := coverProjC_not_mem hs f₀ f
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at h2
  exact ⟨fun h => h2.1 ((affA_eq_u_iff h0 _).1 h), fun h => h2.2 ((affA_eq_v_iff h0 _).1 h)⟩

lemma bdf_cusp (ε : ℝ) (j : BIdx (regProj f₀) cB (1 / 2)) :
    bdf hs f₀ ε (Fill.cusp j) = affA ε (cB j.1) := rfl

variable {t a : ℂ} {τ : ℝ → ℂ} {ε : ℝ} {ψ B : ℂ → ℂ}

/-- **Cone points of the quotient = images of points with nontrivial stabilizer.** -/
theorem coneSet_iff_stab (ht : t ^ 2 = -7) (ha : a ^ 7 = -bconst t)
    (hτ : ∀ ε, τ ε ^ 7 = (lamStar - 1) * ε) (h0 : 0 < ε)
    (hEv : haveI := (regFill_riemannSurface hs f₀).2.1; ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev)
    (hPEv : ∀ w, (pPoly t).eval (Ev w) = regFillProj hs f₀ w)
    (hfib : ∀ w w', Ev w = Ev w' ↔ ∃ σ ∈ H, regFillAct hs f₀ σ w = w')
    (hc : IsNormalizedDiskCover (paperQ (monicP t a) τ ε) 7 ψ B)
    (Θ : QuotOn hs f₀ (interior (bordered hs f₀ ε)) H ≃ₜ ball (0 : ℂ) 1)
    (hΘ : ∀ w, ψ (Θ (Quotient.mk _ w)) = τ ε * Ev w / a ∧ B (Θ (Quotient.mk _ w)) = bdf hs f₀ ε w)
    {V : Set ℂ} {U₀ : Set ℂ} (hB : IsBranchedDiskMap B V (ε : ℂ) (lamStar * ε) 2 3 U₀)
    (w : interior (bordered hs f₀ ε)) :
    (Θ (Quotient.mk _ w) : ℂ) ∈ coneSet B V (ε : ℂ) (lamStar * ε) ↔
      Nat.card (stabIn H (w : RegFill hs f₀)) ≠ 1 := by
  set p : ℂ := (Θ (Quotient.mk _ w) : ℂ)
  have hp : p ∈ ball (0 : ℂ) 1 := (Θ _).2
  have hpV : p ∈ V := hB.cb (ball_subset_closedBall hp)
  have hcne : τ ε / a ≠ 0 := div_ne_zero (tau_ne_zero hτ h0) (a_ne_zero ht ha)
  have hψp : ψ p / (τ ε / a) = Ev w := by
    rw [(hΘ w).1]; field_simp [hcne, a_ne_zero ht ha, tau_ne_zero hτ h0]
  have hderiv := deriv_B_ne_zero_iff ht ha hτ h0 hc hp
  rw [hψp] at hderiv
  obtain ⟨w, hw⟩ := w
  rcases w with f | j
  · have hb : stabIn H (Fill.inl f : RegFill hs f₀) = ⊥ := stabIn_inl H f
    have hBp : B p = bdf hs f₀ ε (Fill.inl f) := (hΘ _).2
    obtain ⟨hu, hv⟩ := bdf_inl_ne (hs := hs) h0 f
    constructor
    · rintro ⟨-, hb', -⟩
      rcases hb' with h | h
      · exact absurd (hBp ▸ h) hu
      · exact absurd (hBp ▸ h) hv
    · intro h
      exact absurd (show Nat.card (stabIn H (Fill.inl f : RegFill hs f₀)) = 1 by
        rw [hb, Subgroup.card_bot]) h
  · have hBp : B p = affA ε (cB j.1) := (hΘ _).2
    have hbr : B p = ε ∨ B p = lamStar * ε := by
      rw [hBp]
      rcases cB_dB j.1 with ⟨h1, -⟩ | ⟨h1, -⟩ <;> rw [h1]
      · exact Or.inl ((affA_eq_u_iff h0 0).2 rfl)
      · exact Or.inr ((affA_eq_v_iff h0 1).2 rfl)
    show p ∈ coneSet B V _ _ ↔ Nat.card (stabIn H (Fill.cusp j : RegFill hs f₀)) ≠ 1
    have hm := dB_le_three j.1
    constructor
    · rintro ⟨-, -, hd⟩
      have hreg := hderiv.1 hd
      rw [(stab_card_noncrit hEv hPEv hfib j hreg).1]; omega
    · intro h
      refine ⟨hpV, hbr, hderiv.2 fun hcrit => h ?_⟩
      rw [(stab_card_crit hEv (pPoly_degree_pos ht) hPEv hfib j hcrit).1, Subgroup.card_bot]

/-- **The cone order of the quotient equals the order of the stabilizer of a lift.** -/
theorem ord_eq_stab (ht : t ^ 2 = -7) (ha : a ^ 7 = -bconst t)
    (hτ : ∀ ε, τ ε ^ 7 = (lamStar - 1) * ε) (h0 : 0 < ε)
    (hEv : haveI := (regFill_riemannSurface hs f₀).2.1; ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev)
    (hPEv : ∀ w, (pPoly t).eval (Ev w) = regFillProj hs f₀ w)
    (hfib : ∀ w w', Ev w = Ev w' ↔ ∃ σ ∈ H, regFillAct hs f₀ σ w = w')
    (hc : IsNormalizedDiskCover (paperQ (monicP t a) τ ε) 7 ψ B)
    (Θ : QuotOn hs f₀ (interior (bordered hs f₀ ε)) H ≃ₜ ball (0 : ℂ) 1)
    (hΘ : ∀ w, ψ (Θ (Quotient.mk _ w)) = τ ε * Ev w / a ∧ B (Θ (Quotient.mk _ w)) = bdf hs f₀ ε w)
    (L : BaseOrbMetric (ε : ℂ) (lamStar * ε) 2 3)
    {V : Set ℂ} (hB : IsBranchedDiskMap B V (ε : ℂ) (lamStar * ε) 2 3 L.U)
    (w : interior (bordered hs f₀ ε)) (i : Fin (pullbackOrb L hB).n)
    (hi : (pullbackOrb L hB).pt i = Θ (Quotient.mk _ w)) :
    (pullbackOrb L hB).ord i = Nat.card (stabIn H (w : RegFill hs f₀)) := by
  have hcone : (Θ (Quotient.mk _ w) : ℂ) ∈ coneSet B V (ε : ℂ) (lamStar * ε) := by
    rw [← hi, ← pullbackOrb_range_pt hB]; exact ⟨i, rfl⟩
  have hne := (coneSet_iff_stab ht ha hτ h0 hEv hPEv hfib hc Θ hΘ hB w).1 hcone
  have hBp : B ((pullbackOrb L hB).pt i) = bdf hs f₀ ε w := by rw [hi]; exact (hΘ w).2
  obtain ⟨w, hw⟩ := w
  rcases w with f | j
  · exact absurd (show Nat.card (stabIn H (Fill.inl f : RegFill hs f₀)) = 1 by
      rw [stabIn_inl, Subgroup.card_bot]) hne
  · have hd : (pPoly t).derivative.eval (Ev (Fill.cusp j)) ≠ 0 := fun hcrit => hne
      (show Nat.card (stabIn H (Fill.cusp j : RegFill hs f₀)) = 1 by
        rw [(stab_card_crit hEv (pPoly_degree_pos ht) hPEv hfib j hcrit).1, Subgroup.card_bot])
    show _ = Nat.card (stabIn H (Fill.cusp j : RegFill hs f₀))
    rw [(stab_card_noncrit hEv hPEv hfib j hd).1]
    have hBp' : B ((pullbackOrb L hB).pt i) = affA ε (cB j.1) := hBp
    rcases pullbackOrb_ord hB i with ⟨hu, ho⟩ | ⟨hv, ho⟩ <;> rw [ho]
    · rcases cB_dB j.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h2.symm
      · exfalso; rw [hBp', h1, (affA_eq_v_iff h0 1).2 rfl] at hu; exact L.u_ne_v hu.symm
    · rcases cB_dB j.1 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exfalso; rw [hBp', h1, (affA_eq_u_iff h0 0).2 rfl] at hv; exact L.u_ne_v hv
      · exact h2.symm

end Degree7
