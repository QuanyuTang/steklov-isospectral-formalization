module

public import RequestProject.CoverFamily
public import RequestProject.FamilyIsospectral

/-!
# Theorem 1.1.2 (i), (ii), (iv), (v) — unconditional

Combining the proved cover input (`exists_paper_diskCover_eventually`), the conditional assembly
`mainTheorem_except_iii_of_spectral_transfer`, and the **proved** isospectrality of the actual
degree-seven families (`FamilyIso.family_spectra_eq`, built from the genuine polynomial monodromy
`Degree7.monodromy_full` and the Fano intertwiner `Degree7.fanoT`), we obtain conclusions
(i), (ii), (iv), (v) of Theorem 1.1.2 with no remaining hypotheses.

The labels: `P ↦ monicP (i√7) a₊`, `L ↦ monicP (-i√7) a₋` (monic degree-seven normalizations
of `p_{±s}`), with a common `τ(ε)` satisfying `τ(ε)⁷ = (λ_* - 1) ε`.

Conclusion (iii) (noncongruence) is **not** addressed here.
-/

@[expose] public section

open Complex Metric Set Filter Topology SteklovBlaschke Steklov

noncomputable section

namespace SteklovCoalescence

open SteklovCritical Degree7 in
/-- **Theorem 1.1.2, conclusions (i), (ii), (iv), (v)**, proved unconditionally. -/
theorem mainTheoremExceptNoncongruence_proved : MainTheoremExceptNoncongruence := by
  set s : ℂ := I * Real.sqrt 7
  have hs : s ^ 2 = -7 := i_sqrt7_sq.1
  have hs' : (-s) ^ 2 = -7 := neg_sq_seven hs
  obtain ⟨aP, -, haP, hmP, hdP, -, -⟩ := exists_monic_normalization hs
  obtain ⟨aM, -, haM, hmM, hdM, -, -⟩ := exists_monic_normalization hs'
  choose τ hτ using fun ε : ℝ =>
    IsAlgClosed.exists_pow_nat_eq ((lamStar - 1) * (ε : ℂ)) (by norm_num : 0 < 7)
  let P : Label → Polynomial ℂ := fun i => match i with
    | Label.P => monicP s aP
    | Label.L => monicP (-s) aM
  refine mainTheorem_except_iii_of_spectral_transfer (n := 7) (by norm_num) P
    (fun i => by cases i <;> assumption) (fun i => by cases i <;> assumption)
    (fun _ => τ) (fun _ => hτ) ?_
  intro ψ B hcov
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε < 1 / 10 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num))
  filter_upwards [hcov Label.P, hcov Label.L, self_mem_nhdsWithin, hsmall] with ε h1 h2 hε0 hε1
  exact FamilyIso.family_spectra_eq hs haP haM hτ hε0 hε1 h1 h2

end SteklovCoalescence
