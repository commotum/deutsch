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

ALLOWED_ERRATA_IMPORT_PREFIXES = (
    "Deutsch.",
    "DeutschErrata.",
    "Mathlib.",
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

    reverse_edges = [
        str(path.relative_to(ROOT))
        for path in sorted((ROOT / "Deutsch").rglob("*.lean"))
        if any(name.startswith("DeutschErrata") for name in imports(path))
    ]
    root_file = ROOT / "Deutsch.lean"
    if any(name.startswith("DeutschErrata") for name in imports(root_file)):
        reverse_edges.insert(0, "Deutsch.lean")
    if reverse_edges:
        fail("Deutsch imports DeutschErrata in " + ", ".join(reverse_edges))

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
    print(f"  Errata production modules: {len(errata_files)}")
    print(f"  Lake public/test targets: {len(observed_libraries)}")
    print(f"  Canonical file hashes: {len(EXPECTED_FILE_SHA256)}")
    print(f"  Historical Git-object hashes: {len(EXPECTED_GIT_OBJECT_SHA256)}")
    print("  Runtime BQP dependencies: none")


if __name__ == "__main__":
    main()
