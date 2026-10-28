# GitHub publication and Palomar submission

## Current status: version 1 registered; author-name metadata revision

[PALOMAR-2026-10-27-000029, version 1](https://palomar-registry.org/entry?id=PALOMAR-2026-10-27-000029&version=1)
records commit `54fddf140bb5fb86ce2eb8fceddb46f20bac1842`.
The current revision corrects author and maintainer display names in the source
metadata. It requires a new verified commit and an ordinary subsequent submission
under this existing Palomar ID; it does not alter the registered version 1.

As checked on **2026-10-27**, the official [toolchain policy](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json) specifies minimum **Lean v4.35.0-rc2**. Recorded commit `6932e18512a776e4edae15bc076f4224ec85e4ad` passed a fresh Lean 4.35.0-rc2 build of all 176 modules, the complete 590-target proof/type and transitive axiom audit, official metadata/source checks, and sandboxed Comparator replay with the bundled Lean and NanoDa kernels. con-ron also accepted. These are checks of that exact snapshot. Subsequent commits require their own successful runs. These historical checks do not establish successful Palomar verification, editorial acceptance or registration.

The user's [actual submission](https://github.com/PalomarRegistry/PalomarSubmission/actions/runs/40533988514) of
`e5e5383838201fb674f87042dcb8c86ccc761fb2` failed canonical Challenge compilation.
Its successful personal-repository build/audit and bundled Comparator checks did
not include that stage and inherited candidate Lake options. The canonical repair
added a single scoped elaboration option to `Label` and preserved all declaration
text and proof-library sources. The [migration record](../verification/challenge-canonical-20261027/migration.json)
retains the old Challenge and historical hashes without claiming new acceptance.

The root project contains the pinned Lake configuration/manifest, short independent Challenge, proved Solution, Comparator configuration and v0.4 metadata. Challenge imports canonical Mathlib only, has one deliberate statement hole and is never a Solution dependency. Comparator compares concrete definitions in full and has no fillable definition targets. [Evidence](lean435-build-audit-evidence.json).

## Public repository and final snapshot

1. The preparation repository is `QuanyuTang/steklov-isospectral-formalization`, a public independent copy preserving the original repository's full `main` history through `5de09135cd688ce5e6487b16bd44e64f056f7fbc`. Use the final verified commit on this repository's `main`. It was made public at the owner's explicit request. See [copy provenance](PROVENANCE.md#public-personal-copy).
2. The project contents are already at the repository root, including hidden files (`.github/`, `.gitignore`, `.gitattributes`). Keep `.lake/`, caches and account credentials outside the committed source; do not add another enclosing directory.
3. Review the maintainer name and chosen code license in `formalization.yaml`, README, and NOTICE. The included paper retains its own rights; its arXiv license does not itself grant third-party redistribution. The publisher must hold the necessary rights or permission for public paper-file distribution.
4. After all checks and the final review, select the approved public snapshot and save its full 40-character commit SHA. A document-only follow-up commit still needs checks on its own exact snapshot.

The ZIP is a transport package for GitHub, not a direct Palomar submission artifact. Uploading the ZIP as one opaque repository file is not sufficient.

## Reproduce checks before submitting a new snapshot

1. Preserve the Lean 4.28 baseline and the documented statement, definition and implementation-helper migration records.
2. Keep the exact supported Lean release and corresponding canonical Mathlib revision pinned together.
3. Run the complete build, combined proof/type and public-entry axiom audit (`python3 scripts/audit.py`), and source checks. The only permitted proof axioms are `propext`, `Classical.choice`, and `Quot.sound`.
4. Require the **Palomar mechanical preflight** workflow (`palomar-mechanical.yml`) on the exact commit. It invokes official PalomarSubmission `c02bbeaed888df45c4e28c4e99dba540ad21552a` in **full** mode with `palomar-standard-v1`, including canonical Challenge compilation. The upstream `preflight` mode alone omits this stage. On Linux, retain the additional bundled Comparator checks (`bash scripts/verify-required-comparator.sh`, then `bash scripts/verify-comparator.sh`); these use candidate Lake settings and do not replace the official path. Preserve real kernel outcomes and pinned environments. A runner interruption or advisory timeout is not acceptance.
5. Update `formalization.yaml` and README with the actual new checks and known limitations; preserve accurate AI and human-review disclosures.
   Run `python3 scripts/refresh-release.py` after intentional edits, commit the resulting checksums and manifests, and require all three GitHub workflows to pass on that exact final commit. Keep the SHA and workflow URLs in the submission record; do not make another documentation commit merely to insert its own SHA.
6. After the owner's approval for a subsequent submission, use the exact public repository and full commit SHA through [Palomar](https://submit.palomar-registry.org). Enter **Existing Palomar ID `PALOMAR-2026-10-27-000029`** so this is a new version of the existing result. Use the repository root, `comparator.json` and `formalization.yaml`. The metadata's `version: v0.4` is its schema version and must not be changed to `2`. Claim authorship/maintenance authorization truthfully. The [submission guide](https://palomar-registry.org/how-to-submit) describes the form; an agent must read the submission host's `llms.txt` before using its agent protocol.

The own-repository mechanical workflow does not create a registry submission. Palomar separately performs mechanical checks and automated editorial review on an actual submission; registration of each subsequent version remains an explicit action. The existing version 1 does not establish the outcome of this metadata revision.

## Primary references

- [How to submit](https://palomar-registry.org/how-to-submit)
- [Submission policy](https://github.com/PalomarRegistry/PalomarPolicy/blob/main/CONTRIBUTING.md)
- [Current toolchain minimum](https://raw.githubusercontent.com/PalomarRegistry/PalomarSubmission/main/toolchains.json)
- [Official starter project](https://github.com/PalomarRegistry/PalomarTemplate)
