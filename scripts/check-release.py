#!/usr/bin/env python3
"""Supplementary release checks. This does not replace Lean or Comparator."""
from pathlib import Path
import argparse
import hashlib
import json
import re
import tarfile

from release_manifest import DERIVED_FILES, file_hash, release_files

ROOT = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--write-report", action="store_true",
                    help="write the structural report; skip the derived publication manifest during refresh")
args = parser.parse_args()
checks = []

def require(condition, description):
    if not condition:
        raise SystemExit("FAIL: " + description)
    checks.append(description)

def code_only(text):
    """Remove nested Lean comments and quoted strings before token scanning."""
    out = []
    i = 0
    depth = 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                if text[i] == "\n":
                    out.append("\n")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
            out.append(" ")
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise SystemExit("Unclosed Lean block comment")
    return "".join(out)

required = ["README.md", "README.zh-CN.md", "LICENSE", "NOTICE", "Challenge.lean",
            "scripts/verify-required-comparator.sh",
            "Solution.lean", "comparator.json", "formalization.yaml", "lean-toolchain",
            "lakefile.toml", "lake-manifest.json", "SOURCE_SHA256SUMS", "paper/README.md",
            "paper/2608.10557v2.pdf", "paper/2608.10557v2-source.tar", "verification/templates/Run20Audit.lean.in"]
require(all((ROOT / p).is_file() for p in required), "required release files present")
require(not (ROOT / "lakefile.lean").exists(), "exactly one Lake configuration")
lean_files = sorted(p for p in ROOT.rglob("*.lean") if not any(x in {".lake", ".git"} for x in p.relative_to(ROOT).parts))
proofs = sorted((ROOT / "RequestProject").rglob("*.lean"))
require(len(proofs) == 176, "176 original library/configuration modules")
require(len(list((ROOT / "verification/templates").glob("Audit*.lean.in"))) == 4,
        "four original command-only audit inventories preserved as templates")
tokens_by_path = {}
for p in lean_files:
    text = p.read_text(encoding="utf-8")
    rel = p.relative_to(ROOT).as_posix()
    require(not p.is_symlink(), "regular Lean source: " + rel)
    require(len(text.splitlines()) <= 10000, "Lean line cap: " + rel)
    code = code_only(text)
    require(re.match(r"\s*module\b", code) is not None, "module header: " + rel)
    tokens_by_path[rel] = code

challenge = ROOT / "Challenge.lean"
require(len(challenge.read_text(encoding="utf-8").splitlines()) <= 1000 and challenge.stat().st_size <= 100 * 1024,
        "Challenge within 1000 lines and 100 KiB")
imports = re.findall(r"^\s*(?:public\s+)?import\s+([^\n]+)", tokens_by_path["Challenge.lean"], re.M)
require(imports == ["Mathlib"], "Challenge imports canonical Mathlib only")
require(len(re.findall(r"\bsorry\b", tokens_by_path["Challenge.lean"])) == 1,
        "exactly one deliberate Challenge placeholder")
for rel, code in tokens_by_path.items():
    if rel == "Challenge.lean":
        continue
    require(re.search(r"\b(sorry|admit|axiom|native_decide|unsafe|implemented_by)\b", code) is None,
            "no proof placeholders or forbidden shortcuts: " + rel)
require("import Challenge" not in tokens_by_path["Solution.lean"], "Solution does not import Challenge")
cfg = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
require(cfg["challenge_module"] == "Challenge" and cfg["solution_module"] == "Solution", "comparison module paths")
require(cfg["theorem_names"] == ["SteklovSubmission.main_result"], "all five main conclusions selected")
require(set(cfg["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"}, "only three standard permitted axioms")
require("external_kernels" not in cfg, "no submitter-selected external checker")
require(cfg["definition_names"] == [], "concrete statement definitions compared in full, with no fillable definition holes")
metadata = json.loads((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
require(metadata["version"] == "v0.4", "formalization.yaml v0.4 (JSON-compatible YAML)")
require(metadata["project"]["license"] == "Apache-2.0", "chosen Apache-2.0 code license")
require(bool(metadata["project"]["authors"]) and bool(metadata["project"]["responsible_maintainers"]), "public authorship and maintenance metadata")
require(metadata["status"]["sorry_count"] == 0 and metadata["status"]["sorry_in_definitions"] == 0,
        "proof-development placeholder counts exclude Challenge")
require(bool(metadata["automation"]["methods"]) and bool(metadata["review"]["status"]), "AI use and review disclosures")
pin = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
require(pin == "leanprover/lean4:v4.35.0-rc2", "migration target Lean toolchain pinned")
manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
require(mathlib["rev"] == "065356127b1dc0016f66b7283ce0ce2c4055aa55", "canonical Mathlib release commit pinned")
source_hashes = {}
for line in (ROOT / "SOURCE_SHA256SUMS").read_text(encoding="utf-8").splitlines():
    require(re.fullmatch(r"[0-9a-f]{64}  .+", line) is not None, "valid source checksum entry")
    digest, name = line.split("  ", 1)
    require(name not in source_hashes, "unique source checksum entry: " + name)
    require(not Path(name).is_absolute() and ".." not in Path(name).parts and "\\" not in name,
            "repository-relative checksum path: " + name)
    source_hashes[name] = digest
    p = ROOT / name
    require(p.is_file() and not p.is_symlink() and hashlib.sha256(p.read_bytes()).hexdigest() == digest,
            "source hash: " + name)
bound_sources = {p.relative_to(ROOT).as_posix() for p in lean_files}
bound_sources.update(set(required) - {"SOURCE_SHA256SUMS"})
bound_sources.update(p.relative_to(ROOT).as_posix() for p in (ROOT / "scripts").iterdir() if p.is_file())
bound_sources.update(p.relative_to(ROOT).as_posix() for p in (ROOT / ".github").rglob("*") if p.is_file())
require(bound_sources <= source_hashes.keys(),
        "all Lean sources, required release files, scripts and CI files bound by source checksums; missing: "
        + ", ".join(sorted(bound_sources - source_hashes.keys())))
inventory = set(release_files(ROOT))
require(set(source_hashes) == inventory - DERIVED_FILES,
        "source checksum inventory exactly covers all nonderived release files")
windows_report = ROOT / "verification/local-windows-20261027/report.json"
windows_proof_inputs = set()
if windows_report.is_file():
    # Bind historical local evidence to its exact proof inputs. Refreshing the
    # release manifests must never silently certify changed proof development.
    # This integrity check makes no claim of a Linux sandbox or current CI run.
    windows_record = json.loads(windows_report.read_text(encoding="utf-8"))
    recorded_inputs = windows_record.get("proof_input_sha256")
    require(isinstance(recorded_inputs, dict), "recorded Windows proof-input hash mapping present")
    windows_proof_inputs = {p.relative_to(ROOT).as_posix() for p in lean_files}
    windows_proof_inputs.update({"lean-toolchain", "lakefile.toml", "lake-manifest.json",
                                 "comparator.json", "scripts/audit.py"})
    windows_proof_inputs.update(p.relative_to(ROOT).as_posix()
                               for p in (ROOT / "verification/templates").glob("*.lean.in")
                               if p.is_file())
    require(set(recorded_inputs) == windows_proof_inputs,
            "recorded Windows proof-input inventory exactly covers current proof inputs")
    for name in sorted(windows_proof_inputs):
        digest = recorded_inputs[name]
        require(isinstance(digest, str) and re.fullmatch(r"[0-9a-f]{64}", digest) is not None
                and digest == source_hashes.get(name), "recorded Windows proof-input hash: " + name)
if not args.write_report:
    publication = json.loads((ROOT / "publication-manifest.json").read_text(encoding="utf-8"))
    publication_hashes = publication.get("file_sha256", {})
    require(set(publication_hashes) == inventory - {"publication-manifest.json"},
            "publication manifest exactly covers all other release files")
    for name, digest in publication_hashes.items():
        require(re.fullmatch(r"[0-9a-f]{64}", digest) is not None
                and file_hash(ROOT, name) == digest, "publication hash: " + name)
frozen = json.loads((ROOT / "verification/recorded/final-source-manifest.json").read_text(encoding="utf-8"))
header_only_files = {"RequestProject/Main.lean"}
audit_template_files = {"RequestProject/" + n for n in
                        ["Audit.lean", "AuditRun18.lean", "AuditRun19.lean", "AuditRun20.lean"]}
changed_sources = []
normalize = lambda data: re.sub(r"\s+", " ", code_only(data.decode("utf-8"))).strip()
original_statement = (ROOT / "verification/templates/MainStatement.original.lean.in").read_bytes()
original_defs = (ROOT / "verification/templates/Defs.original.lean.in").read_bytes()
statement_code = code_only(original_statement.decode("utf-8"))
statement_start = statement_code.index("def MainTheorem : Prop :=")
statement_end = re.search(r"\bend\s*\Z", statement_code).start()
main_block = statement_code[statement_start:statement_end]
defs_code = code_only(original_defs.decode("utf-8"))
defs_end = re.search(r"\bend\s*\Z", defs_code).start()
expected_defs = (defs_code[:defs_end] + "\nopen Set PlaneDomain Steklov\n" + main_block + "\nend\n").encode("utf-8")
expected_forwarder = (statement_code[:statement_start] + "\nend\n").encode("utf-8")
for name, expected in frozen["lean_source_sha256"].items():
    source_path = ROOT / name
    if name in audit_template_files:
        source_path = ROOT / "verification/templates" / (Path(name).name + ".in")
    content = source_path.read_bytes()
    if name in header_only_files:
        require(content.startswith(b"module\n\n"), "new audit-module header: " + name)
        content = content[len(b"module\n\n"):]
    actual = hashlib.sha256(content).hexdigest()
    if name == "RequestProject/MainStatement.lean":
        require(hashlib.sha256(original_statement).hexdigest() == expected, "original main statement source archived byte-for-byte")
        require(normalize(content) == normalize(expected_forwarder), "MainStatement only re-exports original definitions and relocated main statement")
    elif name == "RequestProject/Defs.lean":
        require(hashlib.sha256(original_defs).hexdigest() == expected, "original definition source archived byte-for-byte")
        require(normalize(content) == normalize(expected_defs), "all original definition code and MainTheorem preserved exactly under the documented module move")
    elif name in audit_template_files:
        require(actual == expected, "unchanged baseline statement or audit inventory: " + name)
    if actual != expected:
        changed_sources.append({"file": name, "baseline_sha256": expected, "migrated_sha256": actual})
changes = json.loads((ROOT / "verification/migration-changes.json").read_text(encoding="utf-8"))
require(changes["changed_original_sources"] == changed_sources, "migration changes recorded against the frozen Lean 4.28 baseline")
require(hashlib.sha256((ROOT / "paper/tex/pdes40_arxiv_v2.tex").read_bytes()).hexdigest() == frozen["original_tex_sha256"],
        "original TeX byte identity")
with tarfile.open(ROOT / "paper/2608.10557v2-source.tar", "r:*") as archive:
    members = [m for m in archive.getmembers() if m.isfile()]
    require({Path(m.name).name for m in members} == {"00README.json", "pdes40_arxiv_v2.tex"}, "complete original TeX archive contents")
    for member in members:
        require(archive.extractfile(member).read() == (ROOT / "paper/tex" / Path(member.name).name).read_bytes(), "unmodified archived source: " + member.name)
require((ROOT / "paper/2608.10557v2.pdf").read_bytes().startswith(b"%PDF"), "original paper PDF header")
require("Apache License" in (ROOT / "LICENSE").read_text(encoding="utf-8"), "standard Apache license file")
require("not relicensed" in (ROOT / "NOTICE").read_text(encoding="utf-8"), "paper rights kept separate")
summary = {
    "status": "source_release_structural_and_integrity_checks_passed",
    "library_modules": len(proofs), "preserved_original_audit_templates": 4,
    "original_source_file_count": 180, "all_regular_lean_files": len(lean_files),
    "checks_passed": len(checks), "toolchain": pin,
    "challenge_placeholder_count": 1, "proof_placeholder_count": 0,
    "original_sources_unchanged_except_one_config_module_header": not changed_sources,
    "changed_original_source_count": len(changed_sources),
    "byte_identical_original_source_contents": 179 - len(changed_sources),
    "module_header_only_adaptations": sorted(header_only_files),
    "original_tex_and_archive_match": True,
    "source_manifest_coverage_complete": True,
    "publication_manifest_checked": not args.write_report,
    "recorded_windows_proof_input_binding_checked": windows_report.is_file(),
    "recorded_windows_proof_input_count": len(windows_proof_inputs),
    "observed_palomar_toolchain_minimum_satisfied": True,
    "palomar_registration_claimed": False,
    "kernel_acceptance_established_by_this_source_check": False,
    "not_a_Lean_build_or_semantic_fidelity_proof": True,
}
if args.write_report:
    (ROOT / "verification/release-check.json").write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8", newline="\n")
print(json.dumps(summary, indent=2))
