module

public import RequestProject.PolynomialCover

/-!
# Transfer of monodromy, and a radial retraction of loops

* `MonoTransfer.monodromy_transfer`: if `Φ : E → ℂ` sends a covering `E → Y` to a polynomial
  covering, compatibly with a map of bases along a path `γ` (`P(Φ e) = α(p e)`, `Φ` continuous over
  the path), then lifting commutes with `Φ`: the polynomial monodromy along `α ∘ γ` sends `Φ e` to
  `Φ` of the endpoint of the lift of `γ`.  Proved by uniqueness of lifts.
* `MonoTransfer.exists_homotopic_small`: in `Xs ⊆ ℂ` stable under the radial retractions
  `w ↦ ((1-t) + t ρ / max(|w|, ρ)) w`, every loop at a base point with `|x₀| ≤ ρ` is homotopic to a
  loop inside the closed disk of radius `ρ`.
-/

@[expose] public section

open Set Filter Topology Polynomial PolyCover

noncomputable section

namespace MonoTransfer

/-! ### Transfer -/

theorem monodromy_transfer {Y E : Type*} [TopologicalSpace Y] [TopologicalSpace E] {pE : E → Y}
    (cov : IsCoveringMap pE) {P : ℂ[X]} (Φ : E → ℂ) (α : Y → ℂ) {y₀ y₁ : Y} (γ : Path y₀ y₁)
    {b₀ b₁ : Base P} (β : Path b₀ b₁) (hβ : ∀ t, (β t : ℂ) = α (γ t)) (G : Set Y)
    (hγG : ∀ t, γ t ∈ G) (hΦc : ∀ e', pE e' ∈ G → ContinuousAt Φ e')
    (hΦ : ∀ e', pE e' ∈ G → P.eval (Φ e') = α (pE e')) (e : pE ⁻¹' {y₀})
    (e' : proj P ⁻¹' {b₀}) (he' : ((e' : Total P) : ℂ) = Φ e) :
    (((isCoveringMap P).monodromy (Path.Homotopic.Quotient.mk β) e' : Total P) : ℂ) =
      Φ (cov.monodromy (Path.Homotopic.Quotient.mk γ) e) := by
  set Γ := cov.liftPath (γ : C(unitInterval, Y)) e (γ.source.trans e.2.symm) with hΓ
  have hΓp : ∀ t, pE (Γ t) = γ t := fun t => congr_fun (cov.liftPath_lifts _ _ _) t
  have hmem : ∀ t, P.eval (Φ (Γ t)) ∈ (critVals P)ᶜ := fun t => by
    rw [hΦ _ (by rw [hΓp]; exact hγG t), hΓp, ← hβ]; exact (β t).2
  set Γ' : C(unitInterval, Total P) := ⟨fun t => ⟨Φ (Γ t), hmem t⟩, by
    refine Continuous.subtype_mk ?_ _
    exact continuous_iff_continuousAt.2 fun t =>
      (hΦc _ (by rw [hΓp]; exact hγG t)).comp Γ.continuous.continuousAt⟩ with hΓ'
  have hlift : Γ' = (isCoveringMap P).liftPath (β : C(unitInterval, Base P)) e'
      (β.source.trans e'.2.symm) := by
    rw [(isCoveringMap P).eq_liftPath_iff']
    refine ⟨funext fun t => Subtype.ext ?_, Subtype.ext ?_⟩
    · show P.eval (Φ (Γ t)) = (β t : ℂ)
      rw [hΦ _ (by rw [hΓp]; exact hγG t), hΓp, hβ]
    · show Φ (Γ 0) = ((e' : Total P) : ℂ)
      rw [he']
      congr 1
      exact cov.liftPath_zero _ _ _
  show (((isCoveringMap P).liftPath (β : C(unitInterval, Base P)) e' _ 1 : Total P) : ℂ) =
    Φ (cov.liftPath (γ : C(unitInterval, Y)) e _ 1)
  rw [← hlift]
  rfl

/-! ### Radial retraction -/

/-- The radial retraction factor. -/
def radF (ρ t : ℝ) (w : ℂ) : ℝ := (1 - t) + t * (ρ / max ‖w‖ ρ)

/-- The radial retraction. -/
def rad (ρ t : ℝ) (w : ℂ) : ℂ := (radF ρ t w : ℂ) * w

lemma rad_of_le {ρ t : ℝ} {w : ℂ} (h : ‖w‖ ≤ ρ) (hρ : 0 < ρ) : rad ρ t w = w := by
  have : max ‖w‖ ρ = ρ := max_eq_right h
  simp [rad, radF, this, div_self hρ.ne']

lemma radF_mem {ρ t : ℝ} (w : ℂ) (hρ : 0 < ρ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ρ / max ‖w‖ ρ ≤ radF ρ t w ∧ radF ρ t w ≤ 1 := by
  have hM : ρ ≤ max ‖w‖ ρ := le_max_right _ _
  have hq0 : 0 < ρ / max ‖w‖ ρ := div_pos hρ (hρ.trans_le hM)
  have hq1 : ρ / max ‖w‖ ρ ≤ 1 := (div_le_one (hρ.trans_le hM)).2 hM
  unfold radF
  constructor <;> nlinarith

lemma norm_rad {ρ t : ℝ} (w : ℂ) (hρ : 0 < ρ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖rad ρ t w‖ = radF ρ t w * ‖w‖ := by
  have h := radF_mem w hρ ht0 ht1
  have hM : ρ ≤ max ‖w‖ ρ := le_max_right _ _
  have hq0 : 0 < ρ / max ‖w‖ ρ := div_pos hρ (hρ.trans_le hM)
  rw [rad, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hq0.trans_le h.1)]

lemma norm_rad_le {ρ t : ℝ} (w : ℂ) (hρ : 0 < ρ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖rad ρ t w‖ ≤ ‖w‖ := by
  rw [norm_rad w hρ ht0 ht1]
  have h := radF_mem w hρ ht0 ht1
  nlinarith [norm_nonneg w]

lemma le_norm_rad {ρ t : ℝ} (w : ℂ) (hρ : 0 < ρ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hw : ρ ≤ ‖w‖) : ρ ≤ ‖rad ρ t w‖ := by
  rw [norm_rad w hρ ht0 ht1]
  have h := radF_mem w hρ ht0 ht1
  have hM : max ‖w‖ ρ = ‖w‖ := max_eq_left hw
  rw [hM] at h
  have hw0 : 0 < ‖w‖ := hρ.trans_le hw
  have : ρ / ‖w‖ * ‖w‖ = ρ := div_mul_cancel₀ ρ hw0.ne'
  nlinarith

lemma norm_rad_one_le {ρ : ℝ} (w : ℂ) (hρ : 0 < ρ) : ‖rad ρ 1 w‖ ≤ ρ := by
  rw [norm_rad w hρ zero_le_one le_rfl]
  simp only [radF, sub_self, one_mul, zero_add]
  have hM : 0 < max ‖w‖ ρ := hρ.trans_le (le_max_right _ _)
  rw [div_mul_eq_mul_div, div_le_iff₀ hM]
  exact mul_le_mul_of_nonneg_left (le_max_left _ _) hρ.le

lemma continuous_rad {ρ : ℝ} (hρ : 0 < ρ) :
    Continuous fun p : ℝ × ℂ => rad ρ p.1 p.2 := by
  unfold rad radF
  have hM : ∀ p : ℝ × ℂ, max ‖p.2‖ ρ ≠ 0 := fun p => (hρ.trans_le (le_max_right _ _)).ne'
  refine Continuous.mul ?_ continuous_snd
  refine Complex.continuous_ofReal.comp ?_
  refine (continuous_const.sub continuous_fst).add (continuous_fst.mul ?_)
  exact continuous_const.div (continuous_snd.norm.max continuous_const) hM

/-- The radial retraction of a set `Xs` stable under it. -/
def IsRadStable (ρ : ℝ) (Xs : Set ℂ) : Prop :=
  ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ w ∈ Xs, rad ρ t w ∈ Xs

/-- **Loops are homotopic to small loops.** -/
theorem exists_homotopic_small {ρ : ℝ} (hρ : 0 < ρ) {Xs : Set ℂ} (hX : IsRadStable ρ Xs)
    {x₀ : Xs} (hx₀ : ‖(x₀ : ℂ)‖ ≤ ρ) (γ : Path x₀ x₀) :
    ∃ γ' : Path x₀ x₀, (∀ s, ‖(γ' s : ℂ)‖ ≤ ρ) ∧
      Path.Homotopic.Quotient.mk γ = Path.Homotopic.Quotient.mk γ' := by
  have hc : Continuous fun p : unitInterval × unitInterval =>
      rad ρ (p.1 : ℝ) ((γ p.2 : Xs) : ℂ) :=
    (continuous_rad hρ).comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp (γ.continuous.comp continuous_snd)))
  let H : unitInterval × unitInterval → Xs := fun p =>
    ⟨rad ρ (p.1 : ℝ) (γ p.2), hX _ p.1.2.1 p.1.2.2 _ (γ p.2).2⟩
  have hHc : Continuous H := hc.subtype_mk _
  have hend : ∀ t : unitInterval, H (t, 0) = x₀ ∧ H (t, 1) = x₀ := fun t => by
    constructor <;> apply Subtype.ext <;> simp [H, rad_of_le hx₀ hρ]
  let γ' : Path x₀ x₀ :=
    { toFun := fun s => H (1, s)
      continuous_toFun := hHc.comp (continuous_const.prodMk continuous_id)
      source' := (hend 1).1
      target' := (hend 1).2 }
  refine ⟨γ', fun s => norm_rad_one_le _ hρ, ?_⟩
  apply Path.Homotopic.Quotient.eq.2
  have hprop : ∀ (t : unitInterval) (s : unitInterval), s ∈ ({0, 1} : Set unitInterval) →
      H (t, s) = γ s := by
    intro t s hs
    rcases hs with rfl | hs
    · rw [(hend t).1]; exact γ.source.symm
    · rw [Set.mem_singleton_iff] at hs; subst hs
      rw [(hend t).2]; exact γ.target.symm
  exact ⟨{
    toFun := H
    continuous_toFun := hHc
    map_zero_left := fun s => Subtype.ext (by simp [H, rad, radF])
    map_one_left := fun s => rfl
    prop' := fun t s hs => hprop t s hs }⟩

end MonoTransfer
