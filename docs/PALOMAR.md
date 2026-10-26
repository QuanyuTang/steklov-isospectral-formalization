# GitHub publication and Palomar submission

## Current status: migration verification in progress

As checked on **2026-10-26**, the official [toolchain policy](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json) specifies a minimum of **Lean v4.35.0-rc2**. This project pins that release and its canonical Mathlib revision. Recorded commit `fd44fc6172c412ccdc844c112dea5d3df9a26383` passed the fresh full-library build, all 590 audit targets, metadata and strict source checks. Lean's independent replay is still unfinished; this is not yet a fully verified submission candidate. [Exact evidence](lean435-build-audit-evidence.json).

The package contains `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`, a standard root license, all proof sources, and pinned dependencies. The Challenge imports only Mathlib, stays below 1000 lines / 100 KiB, and states all five main conclusions. Its one deliberate `sorry` is not a proof dependency.

The bundled sandboxed Comparator reached NanoDa acceptance on the recorded commit, then the runner shut down during Lean's replay. No Lean acceptance or rejection was recorded. Subsequent attempts are recorded by commit in CI; no completed Lean replay is claimed here. Both mandatory kernel acceptances remain necessary; con-ron is attempted afterward under [the official mechanical policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md#5-what-mechanical-verification-establishes). An inconclusive local advisory timeout is never described as acceptance.

## Publish the repository

1. The preparation repository is `taohu-hub/steklov-isospectral-formalization`, with review in draft PR #1. Publication needs the owner's final approval.
2. Put this folder's contents at the repository root. Commit hidden files too (`.github/`, `.gitignore`, `.gitattributes`). Do not upload `.lake/`, caches, account credentials, or another enclosing directory.
3. Review the maintainer name and chosen code license in `formalization.yaml`, README, and NOTICE. The included paper retains its own rights; its arXiv license does not itself grant third-party redistribution. The publisher must hold the necessary rights or permission for public paper-file distribution.
4. After all checks and the final review, publish the approved snapshot and save its full 40-character commit SHA. A document-only follow-up commit still needs checks on its own exact snapshot.

The ZIP is a transport package for GitHub, not a direct Palomar submission artifact. Uploading the ZIP as one opaque repository file is not sufficient.

## Complete the port before submission

1. Preserve the Lean 4.28 baseline and the documented statement, definition and implementation-helper migration records.
2. Keep the exact supported Lean release and corresponding canonical Mathlib revision pinned together.
3. Run the complete build, combined proof/type and public-entry axiom audit (`python3 scripts/audit.py`), and source checks. The only permitted proof axioms are `propext`, `Classical.choice`, and `Quot.sound`.
4. On Linux, run `bash scripts/verify-required-comparator.sh` in its sandbox, then attempt the unchanged upstream `bash scripts/verify-comparator.sh`. Retain the real kernel outcomes and pinned environment. A runner interruption or advisory timeout is not acceptance.
5. Update `formalization.yaml` and README with the actual new checks and known limitations; preserve accurate AI and human-review disclosures.
6. After the owner's approval, use the exact public repository and full commit SHA through [Palomar](https://submit.palomar-registry.org). Use the repository root, `comparator.json` and `formalization.yaml`. Claim authorship/maintenance authorization truthfully. The [submission guide](https://palomar-registry.org/how-to-submit) describes the form; an agent must read the submission host's `llms.txt` before using its agent protocol.

Palomar separately performs mechanical checks and automated editorial review, and registration is a later explicit action. This release makes no claim about the outcome.

## Primary references

- [How to submit](https://palomar-registry.org/how-to-submit)
- [Submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
- [Current toolchain minimum](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json)
- [Official starter project](https://github.com/PalomarRegistry/PalomarTemplate)
