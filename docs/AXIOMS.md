# Foundations and axiom audit

The recorded transitive axiom set for the main proof is exactly:

| Constant | Meaning |
| --- | --- |
| `propext` | Logically equivalent propositions are equal. |
| `Classical.choice` | A nonempty type has a chosen element. |
| `Quot.sound` | Equivalent representatives have equal quotient classes. |

No paper-specific axiom, `sorryAx`, or `Lean.ofReduceBool` occurs in the audited proof closure. The proof library has no `sorry`, `admit`, `axiom`, or `native_decide` code. `Challenge.lean` deliberately contains one statement-only `sorry`; the Solution does not import it.

Inspect the headline proofs:

```lean
import RequestProject.MainTheoremClassical
import RequestProject.Degree7Prop331Full

#print axioms SteklovCoalescence.mainTheoremClassical_proved
#print axioms Degree7.prop_3_3_1_full
```

The original build audited 589 unique exported declarations. This number includes proofs, constructions, and a predicate definition; it is not a count of 589 independent mathematical theorems. See `verification/recorded/local-verification.json` for the inventory.

The public entry adds one target, giving 590 distinct audit declarations. On
recorded commit `fd44fc6172c412ccdc844c112dea5d3df9a26383`, the same complete
inventory and proof/type contracts passed with Lean 4.35.0-rc2 after a fresh
project build. Every reported target has only the permitted axiom dependencies.
See [exact evidence](lean435-build-audit-evidence.json).

These checks do not establish semantic fidelity automatically. The translation
of the paper into the formal definitions needs separate mathematical review.
Recorded fidelity review was AI-assisted, not independent human expert review.
NanoDa accepted the exported main proof on the recorded candidate; the runner
shut down during Lean's independent replay, so the full required verification
is still incomplete. No Palomar verification or registration is claimed.
