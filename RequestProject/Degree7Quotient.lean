module

public import RequestProject.Degree7Bordered
public import RequestProject.FillExtend
public import RequestProject.Degree7CommonCover

/-!
# The completed quotient identifications

Let `R̄ = RegFill hs f₀` be the branched completion of the common regular cover and
`H ≤ GL(3, 𝔽₂)` a label stabilizer.  A continuous coordinate `k : R → ℂ` with `P ∘ k = π`,
whose fibres are exactly the `H`-orbits and which hits every regular point of the polynomial
`P` (as do the two coordinate maps of `Degree7.common_regular_cover`, with `P = p_s`, `H` = point
stabilizer, resp. `P = p_{-s}`, `H` = line stabilizer), extends to the completion
(`quotient_ident`):

* `Ev = Fill.extend k : R̄ → ℂ` is holomorphic, proper and onto `ℂ`, with `P ∘ Ev = π̄`;
* its fibres are exactly the orbits of `H` acting on `R̄` by the extended deck transformations,
  i.e. `Ev` identifies `R̄ / H` with the plane `ℂ` of the polynomial cover `P : ℂ → ℂ`;
* `q_ε ∘ Ev = A_ε ∘ π̄` (`q_ε = ε + (λ_* - 1) ε P` the polynomial of Lemma 3.2.1), so `Ev` maps
  the compact bordered piece `M_ε` onto the closed disk-type domain `q_ε⁻¹(closed unit disk)`
  (the closure of the disk cover `Y_ε` of Lemma 3.2.1), with fibres the `H`-orbits.

`completed_quotient_identifications` packages this for the actual cover and both covers.
-/

@[expose] public section

open Polynomial Set PolyCover LocalMonodromy SteklovRegularCover SteklovPunctured SteklovFill
  SteklovRiemann Topology Manifold SteklovCritical SteklovCoalescence GL3F2
open scoped ContDiff

noncomputable section

namespace Degree7

variable {s : ℂ}

lemma coverProjC_not_mem (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) (f : RegCov f₀) :
    coverProjC hs f₀ f ∉ ({0, 1} : Set ℂ) := by
  rw [← critVals_pPoly hs]; exact (regProj f₀ f).2

/-- **The completed quotient identification** for a coordinate `k` of the regular cover. -/
theorem quotient_ident (hs : s ^ 2 = -7) (f₀ : OrdFib (projSum hs) 13) {P : ℂ[X]}
    (hP : 0 < P.degree) {k : RegCov f₀ → ℂ} (hk : Continuous k)
    (hPk : ∀ f, P.eval (k f) = coverProjC hs f₀ f) (hP' : ∀ f, P.derivative.eval (k f) ≠ 0)
    (H : Set (deckGroup f₀))
    (hfib : ∀ f f', k f = k f' ↔ ∃ σ ∈ H, regAct f₀ σ f = f')
    (hsurj : ∀ z, P.eval z ∉ ({0, 1} : Set ℂ) → ∃ f, k f = z) :
    ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (Fill.extend (E := regEnds hs f₀) k) ∧
    (∀ f, Fill.extend (E := regEnds hs f₀) k (Fill.inl f) = k f) ∧
    (∀ w, P.eval (Fill.extend (E := regEnds hs f₀) k w) = regFillProj hs f₀ w) ∧
    (∀ w w', Fill.extend (E := regEnds hs f₀) k w = Fill.extend (E := regEnds hs f₀) k w' ↔
      ∃ σ ∈ H, regFillAct hs f₀ σ w = w') ∧
    Function.Surjective (Fill.extend (E := regEnds hs f₀) k) ∧
    IsProperMap (Fill.extend (E := regEnds hs f₀) k) ∧
    (∀ (ε : ℝ) w, (SteklovDiskCovers.coverPoly P ε).eval (Fill.extend (E := regEnds hs f₀) k w)
      = affA ε (regFillProj hs f₀ w)) := by
  set E := regEnds hs f₀
  set Ev := Fill.extend (E := E) k
  have hπ := chartsAre_regCov hs f₀
  have hpow := regEnds_pow hs f₀
  have hd : ∀ j : BIdx (regProj f₀) cB (1 / 2), 0 < dB j.1 := fun j => dB_pos j.1
  have hcont : Continuous Ev := Fill.continuous_extend (E := E) (fun j => cB j.1)
    (fun j => dB j.1) hpow hP hk hPk hP'
  have heval : ∀ w, P.eval (Ev w) = regFillProj hs f₀ w :=
    Fill.eval_extend (E := E) (fun j => cB j.1) (fun j => dB j.1) hd hpow hP hk hPk hP'
  have hAct := regFill_deckAction hs f₀
  -- invariance under `H`
  have hinv : ∀ σ ∈ H, Ev ∘ regFillAct hs f₀ σ = Ev := by
    intro σ hσ
    refine Continuous.ext_on Fill.dense_range_inl (hcont.comp (continuous_regFillAct hs f₀ σ))
      hcont ?_
    rintro _ ⟨f, rfl⟩
    show k (regAct f₀ σ f) = k f
    exact ((hfib f (regAct f₀ σ f)).2 ⟨σ, hσ, rfl⟩).symm
  have hcuspVal : ∀ j, P.eval (Ev (Fill.cusp j)) ∈ ({0, 1} : Set ℂ) := by
    intro j
    rw [heval]
    rcases j with ⟨i, Q⟩
    cases i
    · exact Or.inl rfl
    · exact Or.inr rfl
  refine ⟨?_, fun f => rfl, heval, fun w w' => ⟨fun h => ?_, ?_⟩, ?_, ?_, fun ε w => ?_⟩
  · haveI := Fill.isManifold_fill hπ _ _ hd hpow
    exact Fill.contMDiff_extend (E := E) (fun j => cB j.1) (fun j => dB j.1) hpow hP hk hPk hP' hπ
  · rcases w with f | j <;> rcases w' with f' | j'
    · obtain ⟨σ, hσ, h'⟩ := (hfib f f').1 h
      exact ⟨σ, hσ, by rw [← h']; rfl⟩
    · exfalso
      have h1 := hcuspVal j'
      change Ev (Fill.inl f) = Ev (Fill.cusp j') at h
      rw [← h] at h1
      exact coverProjC_not_mem hs f₀ f (by rw [← hPk]; exact h1)
    · exfalso
      have h1 := hcuspVal j
      change Ev (Fill.cusp j) = Ev (Fill.inl f') at h
      rw [h] at h1
      exact coverProjC_not_mem hs f₀ f' (by rw [← hPk]; exact h1)
    · obtain ⟨y, hy, y', hy', hyy⟩ := Fill.exists_common_of_cuspVal_eq (E := E) (fun j => cB j.1)
        (fun j => dB j.1) hd hpow hP hk hPk hP' h
      obtain ⟨σ, hσ, hσy⟩ := (hfib y y').1 hyy
      refine ⟨σ, hσ, ?_⟩
      obtain ⟨hmem, -⟩ := endCompat_regAct hs f₀ σ j y hy
      rw [hσy] at hmem
      have : cuspAct hs f₀ σ j = j' := by
        by_contra hne
        exact Set.disjoint_left.1 (E.disj hne) hmem hy'
      show Fill.cusp (cuspAct hs f₀ σ j) = Fill.cusp j'
      rw [this]
  · rintro ⟨σ, hσ, rfl⟩
    exact (congrFun (hinv σ hσ) w).symm
  · -- surjectivity: the image is closed and dense
    have hproper : ∀ K : Set ℂ, IsCompact K → IsCompact (Ev ⁻¹' K) := by
      intro K hK
      refine (isCompact_preimage_regFillProj hs f₀ (hK.image P.continuous)).of_isClosed_subset
        (hK.isClosed.preimage hcont) fun w hw => ?_
      exact ⟨Ev w, hw, heval w⟩
    have hPM : IsProperMap Ev := isProperMap_iff_isCompact_preimage.2 ⟨hcont, hproper⟩
    have hclosed : IsClosed (range Ev) := hPM.isClosedMap.isClosed_range
    have hfin : (P.eval ⁻¹' ({0, 1} : Set ℂ)).Finite := by
      have : P.eval ⁻¹' ({0, 1} : Set ℂ) = P.eval ⁻¹' {0} ∪ P.eval ⁻¹' {1} := by
        ext z; simp
      rw [this]; exact (fibre_finite hP 0).union (fibre_finite hP 1)
    have hdense : Dense (P.eval ⁻¹' ({0, 1} : Set ℂ))ᶜ := hfin.countable.dense_compl ℂ
    have hsub : (P.eval ⁻¹' ({0, 1} : Set ℂ))ᶜ ⊆ range Ev := by
      intro z hz
      obtain ⟨f, hf⟩ := hsurj z hz
      exact ⟨Fill.inl f, hf⟩
    intro z
    have : z ∈ closure (range Ev) := by
      apply closure_mono hsub
      rw [hdense.closure_eq]; exact mem_univ z
    rw [hclosed.closure_eq] at this
    exact this
  · refine isProperMap_iff_isCompact_preimage.2 ⟨hcont, fun K hK => ?_⟩
    refine (isCompact_preimage_regFillProj hs f₀ (hK.image P.continuous)).of_isClosed_subset
      (hK.isClosed.preimage hcont) fun w hw => ?_
    exact ⟨Ev w, hw, heval w⟩
  · rw [affA_coverPoly, heval]

/-- The data of a coordinate map to a polynomial cover, transported to `ℂ`-valued form. -/
lemma coord_data {P : ℂ[X]} {hs : s ^ 2 = -7} {f₀ : OrdFib (projSum hs) 13}
    {e : Base P ≃ₜ Base (pPoly s)} (he : ∀ x, (e x : ℂ) = x)
    {ev : RegCov f₀ → Total P} (hc : Continuous ev) (hsurj : Function.Surjective ev)
    (hp : ∀ f, e (proj P (ev f)) = regProj f₀ f) (hcv : critVals P = {0, 1}) :
    Continuous (fun f => (ev f : ℂ)) ∧
    (∀ f, P.eval (ev f : ℂ) = coverProjC hs f₀ f) ∧
    (∀ f, P.derivative.eval (ev f : ℂ) ≠ 0) ∧
    (∀ z, P.eval z ∉ ({0, 1} : Set ℂ) → ∃ f, (ev f : ℂ) = z) := by
  refine ⟨continuous_subtype_val.comp hc, fun f => ?_, fun f => ?_, fun z hz => ?_⟩
  · have := congrArg Subtype.val (hp f)
    rw [he] at this
    exact this
  · have := derivative_ne_zero_of_total (ev f)
    rwa [Polynomial.deriv] at this
  · have hzT : z ∈ P.eval ⁻¹' (critVals P)ᶜ := by rw [hcv]; exact hz
    obtain ⟨f, hf⟩ := hsurj ⟨z, hzT⟩
    exact ⟨f, congrArg Subtype.val hf⟩

/-- **Completed quotient identifications for the actual common regular cover.**  For `s² = -7`
there is an ordered fibre `f₀` (the one of `common_regular_cover`) such that the branched
completion `R̄ = RegFill hs f₀` carries holomorphic, proper, surjective maps
`Ev₁, Ev₂ : R̄ → ℂ` with `p_s ∘ Ev₁ = π̄ = p_{-s} ∘ Ev₂`, whose fibres are exactly the orbits of
the point stabilizer `{σ | σ 0 = 0}`, resp. the line stabilizer `{σ | σ 7 = 7}`, of the deck group
`≅ GL(3, 𝔽₂)` acting by extended deck transformations; for every `ε`,
`q_ε^± ∘ Ev_{1,2} = A_ε ∘ π̄` with the polynomials `q_ε^± = ε + (λ_* - 1) ε p_{±s}` of
Lemma 3.2.1. -/
theorem completed_quotient_identifications (hs : s ^ 2 = -7) :
    ∃ f₀ : OrdFib (projSum hs) 13,
      Nonempty (G ≃* deckGroup f₀) ∧ Nat.card (deckGroup f₀) = 168 ∧
      ∃ Ev₁ Ev₂ : RegFill hs f₀ → ℂ,
        ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev₁ ∧ ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω Ev₂ ∧
        (∀ w, (pPoly s).eval (Ev₁ w) = regFillProj hs f₀ w) ∧
        (∀ w, (pPoly (-s)).eval (Ev₂ w) = regFillProj hs f₀ w) ∧
        (∀ w w', Ev₁ w = Ev₁ w' ↔ ∃ σ : deckGroup f₀, σ.1 0 = 0 ∧ regFillAct hs f₀ σ w = w') ∧
        (∀ w w', Ev₂ w = Ev₂ w' ↔ ∃ σ : deckGroup f₀, σ.1 7 = 7 ∧ regFillAct hs f₀ σ w = w') ∧
        Function.Surjective Ev₁ ∧ Function.Surjective Ev₂ ∧
        IsProperMap Ev₁ ∧ IsProperMap Ev₂ ∧
        (∀ (ε : ℝ) w, (SteklovDiskCovers.coverPoly (pPoly s) ε).eval (Ev₁ w) =
          affA ε (regFillProj hs f₀ w)) ∧
        (∀ (ε : ℝ) w, (SteklovDiskCovers.coverPoly (pPoly (-s)) ε).eval (Ev₂ w) =
          affA ε (regFillProj hs f₀ w)) := by
  obtain ⟨A, f₀, -, -, -, -, hiso, hcard, -, -, -, -, ⟨ev₁, hc₁, hs₁, hp₁, hf₁⟩,
    ⟨ev₂, hc₂, hs₂, hp₂, hf₂⟩⟩ := common_regular_cover hs
  have hs' : (-s) ^ 2 = -7 := by rw [neg_sq]; exact hs
  obtain ⟨hk₁, hPk₁, hP'₁, hsu₁⟩ := coord_data (e := Homeomorph.refl _)
    (fun _ => rfl) hc₁ hs₁ hp₁ (critVals_pPoly hs)
  obtain ⟨hk₂, hPk₂, hP'₂, hsu₂⟩ := coord_data
    (e := baseHomeoG (critVals_neg hs)) (baseHomeoG_val _) hc₂ hs₂ hp₂ (critVals_pPoly hs')
  have hfib₁ : ∀ f f', (ev₁ f : ℂ) = ev₁ f' ↔ ∃ σ ∈ {σ : deckGroup f₀ | σ.1 0 = 0},
      regAct f₀ σ f = f' := fun f f' => Subtype.ext_iff.symm.trans (hf₁ f f')
  have hfib₂ : ∀ f f', (ev₂ f : ℂ) = ev₂ f' ↔ ∃ σ ∈ {σ : deckGroup f₀ | σ.1 7 = 7},
      regAct f₀ σ f = f' := fun f f' => Subtype.ext_iff.symm.trans (hf₂ f f')
  obtain ⟨m₁, -, e₁, q₁, su₁, pr₁, c₁⟩ :=
    quotient_ident hs f₀ (pPoly_degree_pos hs) hk₁ hPk₁ hP'₁ _ hfib₁ hsu₁
  obtain ⟨m₂, -, e₂, q₂, su₂, pr₂, c₂⟩ :=
    quotient_ident hs f₀ (pPoly_degree_pos hs') hk₂ hPk₂ hP'₂ _ hfib₂ hsu₂
  exact ⟨f₀, hiso, hcard, _, _, m₁, m₂, e₁, e₂, q₁, q₂, su₁, su₂, pr₁, pr₂, c₁, c₂⟩

end Degree7
