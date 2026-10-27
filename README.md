# Strictly Convex Steklov-Isospectral Plane Domains

**Authors: [Tao Hu](https://github.com/taohu-hub), [Jiachen Shi](https://github.com/RGConj), [Quanyu Tang](https://github.com/QuanyuTang).**

[![Lean verification](https://github.com/taohu-hub/steklov-isospectral-formalization/actions/workflows/lean.yml/badge.svg?branch=main)](https://github.com/taohu-hub/steklov-isospectral-formalization/actions/workflows/lean.yml?query=branch%3Amain)
[![Palomar Comparator](https://github.com/taohu-hub/steklov-isospectral-formalization/actions/workflows/palomar.yml/badge.svg?branch=main)](https://github.com/taohu-hub/steklov-isospectral-formalization/actions/workflows/palomar.yml?query=branch%3Amain)

**Machine-checked proof snapshot:** Recorded commit `6932e18512a776e4edae15bc076f4224ec85e4ad` passed a fresh Lean 4.35.0-rc2 build of all 176 modules, the complete 590-target proof/type and transitive axiom audit, official metadata/source checks, and sandboxed Comparator replay with the bundled Lean and NanoDa kernels. con-ron also accepted. See [status](PALOMAR_STATUS.md) and [exact evidence](docs/lean435-build-audit-evidence.json).

**A Lean 4 formalization of Theorem 1.1.2 of Hu–Shi–Tang, with an explicit degree-seven construction.**

[中文说明](README.zh-CN.md) · [Paper](https://arxiv.org/abs/2608.10557v2) · [Statement](Challenge.lean) · [Proof entry](Solution.lean) · [Scope and theorem map](docs/RESULTS.md)

The development proves the existence of pairs of bounded, simply connected, strictly convex plane domains with real-analytic boundaries and identical Steklov spectra, including multiplicities. The domains have perimeter **2π**, are mutually noncongruent across distinct labels and parameters, have no orientation-reversing Euclidean symmetry, and converge to the disk through normalized conformal maps in **C∞**.

The result concerns inverse spectral geometry for the Dirichlet-to-Neumann operator: the full Steklov spectrum does not determine a plane domain up to Euclidean congruence, even among strictly convex analytic domains arbitrarily close to a disk. Its research audience includes spectral geometry, inverse problems and complex analysis.

| Item | Baseline evidence and current target |
| --- | --- |
| Proof development | 176 library modules + 4 preserved audit templates; no proof placeholders |
| Current target | Lean **4.35.0-rc2**, Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`; fresh full build and 590-target audit passed on recorded commit `6932e18512a7` |
| Verified baseline | Lean **4.28.0**, Mathlib `8f9d9cff6bd728b17a24e163c9402775d9e6a365`; original successful logs included |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only |
| Palomar | **Prepared for submission; not submitted or registered** |
| Review | AI-assisted statement/source review; no independent human mathematical review claimed |

## What is proved

All five conclusions of the main theorem are present in `SteklovSubmission.main_result`. The stronger `SteklovCoalescence.mainTheoremClassical_proved` also supplies the weak Sobolev and classical harmonic-PDE interpretations of the spectrum on the constructed domains.

The proof uses explicit degree-seven polynomials, verified monodromy, and weighted-disk transplantation. The common-cover and quotient geometry is also developed. This is **not** a claim to formalize every general result mentioned in the article: arbitrary-data Riemann existence is not formalized, and the orbifold geometry uses proved concrete disk models. [Precise scope](docs/RESULTS.md).

## Build and inspect

Install [elan](https://github.com/leanprover/elan), Git, and a C/C++ toolchain supported by Lean. From the repository root:

```sh
lake exe cache get
lake build
python3 scripts/audit.py
python3 scripts/check-release.py
python3 -m pip install jsonschema==4.25.1
python3 scripts/validate-metadata.py
```

`lean-toolchain` selects the exact Lean release; the committed manifest pins the dependency closure. Do not run `lake update` just to reproduce this release. A deliberate `sorry` occurs **only in `Challenge.lean`**, as Palomar's statement/proof separation permits. It is not imported by `Solution.lean` or the proof library.

After an intentional repository edit, run `python3 scripts/refresh-release.py` to regenerate the source checksums, structural report and publication manifest together, then rerun verification. Check both workflows on the **exact commit being submitted**; a green badge on another commit is insufficient. The [final source review](verification/final-review.json) records the statement and core-proof review and its limits.

The recorded full build reported 8206 successful jobs. That historical count need not equal a fresh incremental build's count. Machine logs are in [`verification/recorded/`](verification/recorded/). [Reproduction details](docs/REPRODUCIBILITY.md).

The Lean 4.28 baseline release layout was also built and audited in an independent directory: **8206 build jobs succeeded, and all 590 unique axiom-inventory targets used only the three standard axioms**, including the new public entry. See the [release verification report](verification/package-verification.json), [build log](verification/package-build.log), and [audit log](verification/package-audit.log). These historical logs certify the baseline only; the separate target-version evidence records the later Comparator and independent-kernel checks.

## Repository map

```text
Challenge.lean             Independent statement; imports Mathlib only
Solution.lean              Proved public entry
RequestProject/            Complete Lean proof development
comparator.json            Statement/proof comparison configuration
formalization.yaml         Sources, authorship, AI use, scope, and review disclosures
paper/                     Original arXiv PDF, TeX, and source archive
verification/              Re-runnable audit and recorded evidence
docs/                      Scope, foundations, provenance, and submission instructions
scripts/                   Build checks and Palomar preflight
.github/workflows/         GitHub Actions build and axiom checks
```

## Palomar submission status

Recorded commit `6932e18512a776e4edae15bc076f4224ec85e4ad` passed a fresh Lean 4.35.0-rc2 build of all 176 modules, the complete 590-target proof/type and transitive axiom audit, official metadata/source checks, and sandboxed Comparator replay with the bundled Lean and NanoDa kernels. con-ron also accepted. These are checks of that exact snapshot. Subsequent commits require their own successful runs. No Palomar submission, editorial acceptance or registration is claimed.

Palomar reviews the full SHA of a **public GitHub repository**. This preparation repository remains private until the owner approves publication. The ZIP transports the source to GitHub; it is not a standalone Palomar submission. See [the submission guide](docs/PALOMAR.md) and [recorded evidence](docs/lean435-build-audit-evidence.json).

## Attribution and citation

Repository maintainers: [Tao Hu](https://github.com/taohu-hub), [Jiachen Shi](https://github.com/RGConj), [Quanyu Tang](https://github.com/QuanyuTang). Proof generation was primarily performed with **Aristotle (Harmonic)**, with **OpenAI Codex** used for orchestration, intermediate scaffolding, local checks, and packaging. [Full provenance](docs/PROVENANCE.md).

Mathematical source: **Tao Hu, Jiachen Shi, Quanyu Tang**, *Strictly Convex Steklov-Isospectral Plane Domains*, [arXiv:2608.10557v2](https://arxiv.org/abs/2608.10557v2). The maintainers report that the authors have reviewed the manuscript and take responsibility for its mathematical claims. This is distinct from independent human review of the Lean formalization, which is not claimed.
```bibtex
@misc{hu2026strictly,
  title = {Strictly Convex Steklov-Isospectral Plane Domains},
  author = {Hu, Tao and Shi, Jiachen and Tang, Quanyu},
  year = {2026},
  eprint = {2608.10557},
  archivePrefix = {arXiv},
  primaryClass = {math.SP},
  doi = {10.48550/arXiv.2608.10557},
  url = {https://arxiv.org/abs/2608.10557v2}
}
```

## Licensing

The formalization and new documentation use **Apache-2.0**; see [LICENSE](LICENSE) and [NOTICE](NOTICE). The paper files retain their authors' rights and are excluded from this grant. arXiv lists its non-exclusive distribution license for this paper; it does not grant a general reuse license. [Paper provenance and rights](paper/README.md).

## Errata and deviations

The [source comparison record](docs/ERRATA-AND-DEVIATIONS.md) asserts no paper errata
and records four deviations: explicit polynomial realization, concrete metric
orbifold models, the weighted-disk spectral proof route, and the variational
encoding with its proved PDE bridge. All five main conclusions are retained.
Release-tooling attribution is recorded in [third-party notices](docs/THIRD_PARTY_NOTICES.md).
