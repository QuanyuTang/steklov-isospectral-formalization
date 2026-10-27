# GitHub publication and Palomar submission

## Current status: verified proof snapshot; publication pending

As checked on **2026-10-27**, the official [toolchain policy](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json) specifies minimum **Lean v4.35.0-rc2**. Recorded commit `6932e18512a776e4edae15bc076f4224ec85e4ad` passed a fresh Lean 4.35.0-rc2 build of all 176 modules, the complete 590-target proof/type and transitive axiom audit, official metadata/source checks, and sandboxed Comparator replay with the bundled Lean and NanoDa kernels. con-ron also accepted. These are checks of that exact snapshot. Subsequent commits require their own successful runs. No Palomar submission, editorial acceptance or registration is claimed.

The root project contains the pinned Lake configuration/manifest, short independent Challenge, proved Solution, Comparator configuration and v0.4 metadata. Challenge imports canonical Mathlib only, has one deliberate statement hole and is never a Solution dependency. Comparator compares concrete definitions in full and has no fillable definition targets. [Evidence](lean435-build-audit-evidence.json).

## Publish the repository

1. The preparation repository is `taohu-hub/steklov-isospectral-formalization`. The migration in PR #1 has been merged; use the final verified commit on `main`. Publication remains a separate owner action.
2. Put this folder's contents at the repository root. Commit hidden files too (`.github/`, `.gitignore`, `.gitattributes`). Do not upload `.lake/`, caches, account credentials, or another enclosing directory.
3. Review the maintainer name and chosen code license in `formalization.yaml`, README, and NOTICE. The included paper retains its own rights; its arXiv license does not itself grant third-party redistribution. The publisher must hold the necessary rights or permission for public paper-file distribution.
4. After all checks and the final review, publish the approved snapshot and save its full 40-character commit SHA. A document-only follow-up commit still needs checks on its own exact snapshot.

The ZIP is a transport package for GitHub, not a direct Palomar submission artifact. Uploading the ZIP as one opaque repository file is not sufficient.

## Reproduce checks before submitting a new snapshot

1. Preserve the Lean 4.28 baseline and the documented statement, definition and implementation-helper migration records.
2. Keep the exact supported Lean release and corresponding canonical Mathlib revision pinned together.
3. Run the complete build, combined proof/type and public-entry axiom audit (`python3 scripts/audit.py`), and source checks. The only permitted proof axioms are `propext`, `Classical.choice`, and `Quot.sound`.
4. On Linux, run `bash scripts/verify-required-comparator.sh` in its sandbox, then attempt the unchanged upstream `bash scripts/verify-comparator.sh`. Retain the real kernel outcomes and pinned environment. A runner interruption or advisory timeout is not acceptance.
5. Update `formalization.yaml` and README with the actual new checks and known limitations; preserve accurate AI and human-review disclosures.
   Run `python3 scripts/refresh-release.py` after intentional edits, commit the resulting checksums and manifests, and require both GitHub workflows to pass on that exact final commit. Keep the SHA and workflow URLs in the submission record; do not make another documentation commit merely to insert its own SHA.
6. After the owner's approval, use the exact public repository and full commit SHA through [Palomar](https://submit.palomar-registry.org). Use the repository root, `comparator.json` and `formalization.yaml`. Claim authorship/maintenance authorization truthfully. The [submission guide](https://palomar-registry.org/how-to-submit) describes the form; an agent must read the submission host's `llms.txt` before using its agent protocol.

Palomar separately performs mechanical checks and automated editorial review, and registration is a later explicit action. This release makes no claim about the outcome.

## Primary references

- [How to submit](https://palomar-registry.org/how-to-submit)
- [Submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
- [Current toolchain minimum](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json)
- [Official starter project](https://github.com/PalomarRegistry/PalomarTemplate)
