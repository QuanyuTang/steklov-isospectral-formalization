module

public import RequestProject.Defs

/-!
# Statement of Theorem 1.1.2 (main theorem of arXiv:2608.10557v2)

This file records the theorem as the proposition `MainTheorem`. The proof entry is
`SteklovCoalescence.mainTheorem_proved` in `MainTheoremProof.lean`; the stronger entry in
`MainTheoremClassical.lean` also supplies the Sobolev and classical PDE interpretation.
The statement keeps the original quantifier structure: one `ε₀ > 0` and one simultaneous
family `Ω i ε` for `i ∈ {P, L}` and `0 < ε < ε₀`. No unproved geometric or spectral premise
is added to the theorem.
-/

@[expose] public section

open Set PlaneDomain Steklov

/-
The definition `MainTheorem` (Theorem 1.1.2, all five conclusions, unchanged source text) now
lives at the end of `RequestProject.Defs`, which this module publicly re-exports.  Keeping it in
the same module as the definitions it mentions makes its elaborated declaration identical to the
copy in `Challenge.lean` (see the note there in `Defs.lean`).
-/

end
