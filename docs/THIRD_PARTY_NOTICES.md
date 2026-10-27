# Third-party notices

The formalization and new repository code use Apache-2.0. The original paper
files retain the separate rights documented in [paper/README.md](../paper/README.md).

- The official Comparator script, [scripts/verify-comparator.sh](../scripts/verify-comparator.sh),
  comes from [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate),
  licensed under Apache-2.0. Its source revision is recorded in
  [the provenance record](../verification/comparator-script-provenance.json).
- The bundled formalization metadata schema comes from
  [mathlib-initiative/formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml),
  licensed under Apache-2.0; see [its source record](../verification/schema/provenance.json).
- The hosted-runner disk cleanup excerpt in the two workflow files is adapted
  from **LeanAutoformalizationSkills by Scott Armstrong**, specifically
  [lean-public-release](https://github.com/scottnarmstrong/LeanAutoformalizationSkills/blob/1837b95b3d5a9fd8d311367603902ad7fe261adf/skills/lean-public-release/SKILL.md),
  licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/).
  The workflow organization, separate cache prefixes, Ubuntu selection and
  project-specific verification commands were adapted for this repository.
  The original excerpt retains CC BY 4.0. This credit does not imply endorsement.

Lean, Mathlib and their dependency closure are fetched at pinned revisions
and retain their upstream licenses; they are not vendored in this repository.
