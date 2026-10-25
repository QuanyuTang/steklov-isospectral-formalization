# Mathematical scope and source correspondence

Source: Hu, Shi, Tang, *Strictly Convex Steklov-Isospectral Plane Domains*, arXiv:2608.10557v2. The TeX is preserved in `paper/tex/`.

The advertised declaration `SteklovSubmission.main_result` proves **all five conclusions of Theorem 1.1.2**. It has no unproved geometric or spectral hypotheses. Its spectral equality is defined by the full min–max sequence, hence includes multiplicities. `SteklovCoalescence.mainTheoremClassical_proved` additionally identifies this with the Sobolev weak problem and the classical harmonic / outward-normal-derivative problem on each constructed domain.

| Paper result | Lean entry | Scope qualification |
| --- | --- | --- |
| Theorem 1.1.2 | `SteklovCoalescence.mainTheorem_proved`; `mainTheoremClassical_proved` | All five conclusions for one simultaneous two-label parameter family. |
| Proposition 2.1.1 | `SteklovC1.prop_2_1_1_C1_weak` | Full weak spectrum; C¹ maps and inverses represented by ambient extensions. |
| Proposition 2.2.1 | `SteklovOrb.DiskOrbisurface.prop_2_2_1_metric` | Metric Sobolev and spectral correspondence in a given conformal disk coordinate. |
| Proposition 2.3.1 | `OuterConvergence.prop_2_3_1_complete` | Outer-function realization near any positive constant and all-order convergence. |
| Lemma 2.4.1 | `SteklovBlaschke.blaschke_boundary_rigidity` and `_anti` | Holomorphic and antiholomorphic boundary-modulus rigidity. |
| Lemma 3.1.1 | `group_input`; `GL3F2.group_input_GL` | Actual GL(3,F₂), point/line stabilizers, and (2,3,7) generation. |
| Lemma 3.2.1 | `SteklovDiskCovers.lemma_3_2_1` | Polynomial disk-cover geometry; the chosen pair has explicit realization and proved monodromy. |
| Proposition 3.3.1 | `Degree7.prop_3_3_1_full` | Actual degree-168 common cover and metric quotients for the chosen degree-seven pair. |
| Proposition 3.4.1 | `SteklovCoalescence.prop_3_4_1_unconditional` | Normalized covers and smooth coalescence for arbitrary monic positive-degree polynomials. |

## Alternative proof route and omitted generality

The spectral step of the main proof uses direct weighted-disk transplantation for the explicit degree-seven construction. The common regular cover, completed connected bordered surface, stabilizer identifications, and metric quotient geometry are developed separately, including cone origins and the boundary.

The general Riemann existence theorem for **arbitrary** permutation data is not formalized. It is replaced by verified explicit polynomials and their actual monodromy. The geometric development does not constitute a general orbifold library: the relevant quotients are identified with concrete metric orbifold disk models, and spectra are transported through the proved identifications. The common-cover result is specialized to this construction, rather than asserted for every finite group and every abstract orbisurface.

The original statement correspondence and qualifications are recorded in `verification/completion-requirements.json` and `verification/recorded/completion-audit.json`. These are review records, not substitutes for reading the statements and checking the proofs.
