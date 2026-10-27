module

public import RequestProject.MainTheoremClassical

/-!
# Proved submission entry

This module deliberately does not import Challenge.lean. The statement and proof
are compiled independently; Comparator must compare their shared declarations.
The stronger classical-PDE theorem remains available in the imported development.
-/

public section

/-- Theorem 1.1.2, all five conclusions, proved by the explicit degree-seven construction. -/
theorem SteklovSubmission.main_result : MainTheorem :=
  SteklovCoalescence.mainTheorem_proved


end
