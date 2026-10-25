# GitHub publication and Palomar submission

## Current status: migration verification in progress

As checked on **2026-10-25**, the official [toolchain policy](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json) specifies a minimum of **Lean v4.35.0-rc2** for new submissions. The current target is **Lean v4.35.0-rc2**, with canonical Mathlib pinned in the manifest. The verified baseline is Lean 4.28.0. The first Linux run passed the source, metadata and sandbox checks, then found source compatibility errors; this candidate has not yet passed the new build and proof replay.

The package contains `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`, a standard root license, all proof sources, and pinned dependencies. The Challenge imports only Mathlib, stays below 1000 lines / 100 KiB, and states all five main conclusions. Its one deliberate `sorry` is not a proof dependency.

Comparator was invoked in Linux CI but stopped at Solution build errors before successful proof replay. NanoDa and con-ron have not passed this candidate. A successful local Lean build and source audit must not be described as those checks. The included comparison configuration must also be validated against the Comparator shipped with the eventual supported toolchain.

## Publish the repository

1. Create a public GitHub repository, for example `steklov-isospectral-formalization`.
2. Put this folder's contents at the repository root. Commit hidden files too (`.github/`, `.gitignore`, `.gitattributes`). Do not upload `.lake/`, caches, account credentials, or another enclosing directory.
3. Review the maintainer name and chosen code license in `formalization.yaml`, README, and NOTICE. The included paper retains its own rights; its arXiv license does not itself grant third-party redistribution. The publisher must hold the necessary rights or permission for public paper-file distribution.
4. Push the commit. Save its full 40-character SHA with `git rev-parse HEAD`.

The ZIP is a transport package for GitHub, not a direct Palomar submission artifact. Uploading the ZIP as one opaque repository file is not sufficient.

## Complete the port before submission

1. Keep this Lean 4.28 release as an immutable baseline.
2. Select a supported Lean release and the canonical Mathlib revision using that exact toolchain. Port the full proof development and update both pins and the manifest together.
3. Run the complete build, combined proof/type and public-entry axiom audit (`python3 scripts/audit.py`), and source checks. The only permitted proof axioms are `propext`, `Classical.choice`, and `Quot.sound`.
4. On a supported Linux environment, run `bash scripts/verify-comparator.sh`, the official PalomarTemplate script. The script supplies the independent kernels from the selected toolchain as required by current upstream practice; reread the linked requirements if they have changed.
5. Update `formalization.yaml` and README with the actual new checks and known limitations; preserve accurate AI and human-review disclosures.
6. Commit, push, and submit the exact public repository and full commit SHA through [Palomar](https://submit.palomar-registry.org). Use the repository root as the project path, `comparator.json` as configuration, and `formalization.yaml` as metadata. Claim authorship/maintenance authorization truthfully.

Palomar separately performs mechanical checks and automated editorial review, and registration is a later explicit action. This release makes no claim about the outcome.

## Primary references

- [How to submit](https://palomar-registry.org/how-to-submit)
- [Submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
- [Current toolchain minimum](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json)
- [Official starter project](https://github.com/PalomarRegistry/PalomarTemplate)
