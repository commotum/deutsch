#!/usr/bin/env python3
"""Check the required public Markdown inventory and its repository-local links."""

from __future__ import annotations

import re
import sys
from pathlib import Path
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parents[1]
EXPECTED_PUBLIC_DOCS = (
    Path("README.md"),
    Path("docs/conventions.md"),
    Path("docs/representation.md"),
    Path("docs/registers.md"),
    Path("docs/locality.md"),
    Path("docs/descriptors.md"),
    Path("docs/gates.md"),
    Path("docs/information.md"),
    Path("docs/epr.md"),
    Path("docs/teleportation.md"),
    Path("docs/decoherence.md"),
    Path("docs/bell.md"),
    Path("docs/paper.md"),
    Path("docs/reuse.md"),
    Path("docs/project-report.md"),
)
PUBLIC_DOCS = [
    *([ROOT / "README.md"] if (ROOT / "README.md").is_file() else []),
    *sorted((ROOT / "docs").rglob("*.md")),
]
LINK = re.compile(r"!?\[[^]]*\]\(([^)]+)\)")


def main() -> None:
    missing = [path for path in EXPECTED_PUBLIC_DOCS if not (ROOT / path).is_file()]
    errors = [f"missing expected public document: {path}" for path in missing]
    checked = 0
    for document in PUBLIC_DOCS:
        text = document.read_text(encoding="utf-8")
        for line_number, line in enumerate(text.splitlines(), start=1):
            for match in LINK.finditer(line):
                raw = match.group(1).strip()
                target = raw.split(maxsplit=1)[0].strip("<>")
                if target.startswith(("http://", "https://", "mailto:", "#")):
                    continue
                path_part = unquote(target.split("#", 1)[0])
                if not path_part:
                    continue
                checked += 1
                resolved = (document.parent / path_part).resolve()
                try:
                    resolved.relative_to(ROOT)
                except ValueError:
                    errors.append(
                        f"{document.relative_to(ROOT)}:{line_number}: link escapes repository: {target}"
                    )
                    continue
                if not resolved.exists():
                    errors.append(
                        f"{document.relative_to(ROOT)}:{line_number}: missing target: {target}"
                    )
    if errors:
        print("Documentation link audit FAILED", file=sys.stderr)
        print(
            f"  Expected public Markdown files: {len(EXPECTED_PUBLIC_DOCS)}",
            file=sys.stderr,
        )
        print(
            f"  Discovered public Markdown files: {len(PUBLIC_DOCS)}",
            file=sys.stderr,
        )
        print("\n".join(f"  {error}" for error in errors), file=sys.stderr)
        raise SystemExit(1)
    print("Documentation link audit passed")
    print(f"  Expected public Markdown files: {len(EXPECTED_PUBLIC_DOCS)}")
    print(f"  Discovered public Markdown files: {len(PUBLIC_DOCS)}")
    print(f"  Repository-local links: {checked}")


if __name__ == "__main__":
    main()
