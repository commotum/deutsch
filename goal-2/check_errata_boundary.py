#!/usr/bin/env python3
"""Check the two-library import boundary and original-form provenance."""

from __future__ import annotations

import hashlib
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

EXPECTED_FILE_SHA256 = {
    Path("deutsch-2000/deutsch-2000.md"):
        "f18273e9da7109c3be329b17b3942f0fa0b6f064904e7334befbdee66732d032",
    Path("deutsch-2000/deutsch-2000.pdf"):
        "d90c9051e2a652c22fb7ccf5a41bede5b1f4aae797cb159d36068ac525f87edb",
}

EXPECTED_GIT_OBJECT_SHA256 = {
    "fd2e2d1^:deutsch-2000/deutsch-2000-verified.md":
        "02468f4b0a6b731a4f733bab928c858b6f7ddcaf6142ac952a5495b404ed785b",
    "fd2e2d1^:deutsch-2000/deutsch-2000.md":
        "0e16b16e9308beb01f3eb4d746951cb0a8a40971a434b1bcb71b6a03d910cb3b",
}

EXPECTED_ERRATA_ROOT_IMPORTS = (
    "DeutschErrata.Rotation",
    "DeutschErrata.EPR",
    "DeutschErrata.Teleportation",
    "DeutschErrata.Bell",
)

EXPECTED_ERRATA_MODULE_IMPORTS = {
    "DeutschErrata/Rotation.lean": ("Deutsch.Gates.AxisRotation",),
    "DeutschErrata/EPR.lean": ("Deutsch.EPR.RecordStatistics",),
    "DeutschErrata/Teleportation.lean": ("Deutsch.Teleportation.Statistics",),
    "DeutschErrata/Equation45.lean": (
        "Mathlib.Data.Bool.Basic",
        "Mathlib.Tactic.NormNum",
    ),
    "DeutschErrata/Bell.lean": (
        "Deutsch.Bell.Moments",
        "DeutschErrata.Equation45",
    ),
}

EXPECTED_DEFAULT_TARGETS = (
    "Deutsch",
    "DeutschErrata",
    "DeutschTests",
    "DeutschErrataTests",
)

EXPECTED_ERRATA_TEST_ROOT_IMPORTS = (
    "DeutschErrataTests.Comparisons",
    "DeutschErrataTests.Audit",
)

EXPECTED_COMPARISON_DECLARATIONS = (
    "equation18_exponential_check",
    "equation18_quarter_turn_comparison",
    "equations28_and_41_four_wire_derivation",
    "equations28_and_41_equal_setting_comparison",
    "equation35_five_wire_endpoint",
    "equation37_operator_comparison",
    "equation45_value_fixture",
    "equation45_failure_fixture",
    "equation45_complementary_partition_check",
    "equation45_real_partition_check",
    "equation46_direct_moments_check",
)

EXPECTED_ERRATA_AUDIT_TARGETS = (
    "DeutschErrata.Rotation.printedEquation18Y",
    "DeutschErrata.Rotation.printedEquation18Z",
    "DeutschErrata.Rotation.derivedEquation18",
    "DeutschErrata.Rotation.equation18_pi_div_two_mismatch",
    "DeutschErrata.EPR.printedEquation28Probability",
    "DeutschErrata.EPR.printedEquation41Probability",
    "DeutschErrata.EPR.derivedEquations28And41",
    "DeutschErrata.EPR.equations28And41_equal_settings_mismatch",
    "DeutschErrata.Teleportation.equation35PrintedEffectAtPiOverTwo",
    "DeutschErrata.Teleportation.equation35PrintedEffectAtPiOverTwo_op",
    "DeutschErrata.Teleportation.equation35_endpoint_probabilities_at_pi_div_two",
    "DeutschErrata.Teleportation.equation37PrintedOperator",
    "DeutschErrata.Teleportation.equation37_operator_ne_printed_at_pi_div_four",
    "DeutschErrata.Equation45.boolValue",
    "DeutschErrata.Equation45.boolValue_false",
    "DeutschErrata.Equation45.boolValue_true",
    "DeutschErrata.Equation45.numericOr",
    "DeutschErrata.Equation45.numericOr_eq_boolValue_or",
    "DeutschErrata.Equation45.equation45PrintedLeft",
    "DeutschErrata.Equation45.equation45PrintedRight",
    "DeutschErrata.Equation45.equation45ComplementaryRight",
    "DeutschErrata.Equation45.equation45_printed_values_at_one_zero_one",
    "DeutschErrata.Equation45.equation45_printed_form_fails_at_one_zero_one",
    "DeutschErrata.Equation45.equation45_complementary_partition",
    "DeutschErrata.Bell.equation45_derived_real_partition",
    "DeutschErrata.Bell.equation46_derived_form_contradiction",
)

ALLOWED_ERRATA_IMPORT_PREFIXES = (
    "Deutsch.",
    "DeutschErrata.",
    "Mathlib.",
)

HISTORICAL_PRODUCTION_PATTERN = re.compile(
    r"\bprinted\b|\bcorrected\b|source\s*correction|source\s*defect|"
    r"\berrata?\b|\bbookkeeping\b|\btypo\b|\binconsistent\b|"
    r"sign[-\s]+correction|typed\s+correction",
    flags=re.IGNORECASE,
)

SUPERSEDED_MAIN_NAMES = (
    "Deutsch.Bell.SourceCorrection",
    "equation35CorrectedEffect",
    "equation35_corrected_effect_op",
    "corrected_epr_three_settings_refute_local_assignments",
    "no_local_assignments_reproduce_corrected_epr_three_settings",
    "corrected_epr_three_settings_refute_normalized_local_model",
    "no_normalized_local_model_reproduces_corrected_epr_three_settings",
    "rotationX_heisenberg_y_pi_div_two_ne_printed",
    "rotationX_heisenberg_z_pi_div_two_ne_printed",
    "equation28_printed_equal_angle_counterexample",
    "equation41_printed_equal_angle_counterexample",
    "equation29_q1_y_pi_div_two_ne_printed",
    "equation31_q1_y_pi_div_two_ne_printed",
    "equation32_q2_y_pi_div_two_ne_printed",
    "equation34_q5_y_pi_div_two_ne_printed",
    "equation37_q5_z_pi_div_four_ne_printed",
    "equation35PrintedMinusSineAtPiOverTwo",
    "equation35_printed_minus_sine_at_pi_div_two_op",
    "equation35_printed_minus_sine_probability_zero_at_pi_div_two",
)


def sha256(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def imports(path: Path) -> tuple[str, ...]:
    return tuple(
        re.findall(
            r"(?m)^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$",
            path.read_text(encoding="utf-8"),
        )
    )


def fail(message: str) -> None:
    raise SystemExit(f"Errata boundary/provenance audit FAILED: {message}")


def declared_names(path: Path) -> tuple[str, ...]:
    return tuple(
        re.findall(
            r"(?m)^\s*(?:def|theorem|abbrev|structure)\s+"
            r"([A-Za-z_][A-Za-z0-9_']*)",
            path.read_text(encoding="utf-8"),
        )
    )


def axiom_targets(path: Path) -> tuple[str, ...]:
    return tuple(
        re.findall(
            r"(?m)^\s*#print\s+axioms\s+([A-Za-z_][A-Za-z0-9_'.]*)\s*$",
            path.read_text(encoding="utf-8"),
        )
    )


def main() -> None:
    for relative, expected in EXPECTED_FILE_SHA256.items():
        path = ROOT / relative
        if not path.is_file():
            fail(f"missing canonical artifact: {relative}")
        actual = sha256(path.read_bytes())
        if actual != expected:
            fail(f"hash mismatch for {relative}: expected={expected}, actual={actual}")

    for object_name, expected in EXPECTED_GIT_OBJECT_SHA256.items():
        result = subprocess.run(
            ["git", "show", object_name],
            cwd=ROOT,
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        if result.returncode:
            fail(
                f"cannot read provenance object {object_name}: "
                f"{result.stderr.decode('utf-8', errors='replace').strip()}"
            )
        actual = sha256(result.stdout)
        if actual != expected:
            fail(
                f"hash mismatch for Git object {object_name}: "
                f"expected={expected}, actual={actual}"
            )

    production_files = [
        ROOT / "Deutsch.lean",
        *sorted((ROOT / "Deutsch").rglob("*.lean")),
    ]
    reverse_edges = [
        str(path.relative_to(ROOT))
        for path in production_files
        if any(name.startswith("DeutschErrata") for name in imports(path))
    ]
    if reverse_edges:
        fail("Deutsch imports DeutschErrata in " + ", ".join(reverse_edges))

    main_test_files = [
        ROOT / "DeutschTests.lean",
        *sorted((ROOT / "DeutschTests").rglob("*.lean")),
    ]
    main_test_errata_edges = [
        str(path.relative_to(ROOT))
        for path in main_test_files
        if any(name.startswith("DeutschErrata") for name in imports(path))
    ]
    if main_test_errata_edges:
        fail(
            "DeutschTests imports DeutschErrata in "
            + ", ".join(main_test_errata_edges)
        )

    historical_production_files = [
        str(path.relative_to(ROOT))
        for path in production_files
        if HISTORICAL_PRODUCTION_PATTERN.search(path.read_text(encoding="utf-8"))
    ]
    if historical_production_files:
        fail(
            "editorial history remains in Deutsch production: "
            + ", ".join(historical_production_files)
        )

    main_text = "\n".join(
        path.read_text(encoding="utf-8")
        for path in [*production_files, *main_test_files]
    )
    surviving_superseded_names = [
        name for name in SUPERSEDED_MAIN_NAMES if name in main_text
    ]
    if surviving_superseded_names:
        fail(
            "superseded main-library names remain: "
            + ", ".join(surviving_superseded_names)
        )

    errata_root = ROOT / "DeutschErrata.lean"
    if not errata_root.is_file():
        fail("missing DeutschErrata.lean")
    observed_root_imports = imports(errata_root)
    if observed_root_imports != EXPECTED_ERRATA_ROOT_IMPORTS:
        fail(
            "DeutschErrata root import mismatch: "
            f"expected={EXPECTED_ERRATA_ROOT_IMPORTS!r}, actual={observed_root_imports!r}"
        )

    errata_files = sorted((ROOT / "DeutschErrata").rglob("*.lean"))
    if not errata_files:
        fail("no DeutschErrata modules found")
    unexpected_imports = [
        f"{path.relative_to(ROOT)}:{name}"
        for path in errata_files
        for name in imports(path)
        if not name.startswith(ALLOWED_ERRATA_IMPORT_PREFIXES)
    ]
    if unexpected_imports:
        fail("unexpected Errata imports: " + ", ".join(unexpected_imports))

    observed_errata_files = {
        str(path.relative_to(ROOT)): imports(path) for path in errata_files
    }
    if observed_errata_files != EXPECTED_ERRATA_MODULE_IMPORTS:
        fail(
            "Errata module/import DAG mismatch: "
            f"expected={EXPECTED_ERRATA_MODULE_IMPORTS!r}, "
            f"actual={observed_errata_files!r}"
        )

    lakefile = (ROOT / "lakefile.toml").read_text(encoding="utf-8")
    default_match = re.search(r'(?m)^defaultTargets = \[([^]]*)\]$', lakefile)
    if default_match is None:
        fail("lakefile has no literal defaultTargets list")
    observed_default_targets = tuple(
        re.findall(r'"([^"]+)"', default_match.group(1))
    )
    if observed_default_targets != EXPECTED_DEFAULT_TARGETS:
        fail(
            "Lake default target mismatch: "
            f"expected={EXPECTED_DEFAULT_TARGETS!r}, "
            f"actual={observed_default_targets!r}"
        )
    observed_libraries = tuple(
        re.findall(r'(?m)^\[\[lean_lib\]\]\s*\nname = "([^"]+)"$', lakefile)
    )
    if set(observed_libraries) != set(EXPECTED_DEFAULT_TARGETS):
        fail(
            "Lake library set mismatch: "
            f"expected={EXPECTED_DEFAULT_TARGETS!r}, actual={observed_libraries!r}"
        )

    errata_test_root = ROOT / "DeutschErrataTests.lean"
    if imports(errata_test_root) != EXPECTED_ERRATA_TEST_ROOT_IMPORTS:
        fail(
            "DeutschErrataTests root import mismatch: "
            f"expected={EXPECTED_ERRATA_TEST_ROOT_IMPORTS!r}, "
            f"actual={imports(errata_test_root)!r}"
        )
    comparison_declarations = declared_names(
        ROOT / "DeutschErrataTests/Comparisons.lean"
    )
    if comparison_declarations != EXPECTED_COMPARISON_DECLARATIONS:
        fail(
            "Errata focused-check declaration mismatch: "
            f"expected={EXPECTED_COMPARISON_DECLARATIONS!r}, "
            f"actual={comparison_declarations!r}"
        )
    observed_audit_targets = axiom_targets(ROOT / "DeutschErrataTests/Audit.lean")
    if observed_audit_targets != EXPECTED_ERRATA_AUDIT_TARGETS:
        fail(
            "Errata axiom-target mismatch: "
            f"expected={EXPECTED_ERRATA_AUDIT_TARGETS!r}, "
            f"actual={observed_audit_targets!r}"
        )

    inspected = [
        *errata_files,
        *sorted((ROOT / "DeutschErrataTests").rglob("*.lean")),
        ROOT / "DeutschErrata.lean",
        ROOT / "DeutschErrataTests.lean",
        ROOT / "docs/errata.md",
        ROOT / "lakefile.toml",
    ]
    bqp_references = [
        str(path.relative_to(ROOT))
        for path in inspected
        if path.is_file()
        and re.search(
            r"(?:/home/[^/\s]+/Developer/bqp|(?:^|[/'\"])\.\.?/bqp(?:[/'\"]|$))",
            path.read_text(encoding="utf-8"),
            flags=re.MULTILINE,
        )
    ]
    if bqp_references:
        fail("runtime BQP path reference in " + ", ".join(bqp_references))

    print("Errata boundary/provenance audit passed")
    print(f"  Deutsch production reverse imports: {len(reverse_edges)}")
    print(f"  DeutschTests Errata imports: {len(main_test_errata_edges)}")
    print("  Deutsch production editorial-history tokens: none")
    print("  Superseded main-library names: none")
    print(f"  Errata production modules: {len(errata_files)}")
    print(f"  Lake public/test targets: {len(observed_libraries)}")
    print(
        "  Focused comparison declarations / axiom targets: "
        f"{len(comparison_declarations)}/{len(observed_audit_targets)}"
    )
    print(f"  Canonical file hashes: {len(EXPECTED_FILE_SHA256)}")
    print(f"  Historical Git-object hashes: {len(EXPECTED_GIT_OBJECT_SHA256)}")
    print("  Runtime BQP dependencies: none")


if __name__ == "__main__":
    main()
