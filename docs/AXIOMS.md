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

These axiom checks do not establish semantic fidelity automatically. Lean checks a formal statement relative to its type theory, definitions, and trusted kernel. The translation of the paper into those definitions requires separate mathematical review. Recorded fidelity review was AI-assisted, not an independent human expert review. Comparator and independent-kernel checks required for Palomar have not been performed for this release.
