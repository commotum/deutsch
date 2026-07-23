"""Mechanical source, provenance, and ledger-coverage checks.

This does not prove any equation. It only prevents silent omissions and duplicate
ledger identifiers while the mathematical obligations remain explicitly routed.
Compiled E01--E46 proof coverage is checked separately.
"""

from collections import Counter
import hashlib
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "deutsch-2000" / "deutsch-2000.md"
PDF = ROOT / "deutsch-2000" / "deutsch-2000.pdf"
AUDIT = ROOT / "goal-1" / "1-SOURCE-AUDIT.md"

EXPECTED_ARTIFACT_SHA256 = {
    PDF: "d90c9051e2a652c22fb7ccf5a41bede5b1f4aae797cb159d36068ac525f87edb",
    ROOT / "deutsch-2000" / "images" / "figure-1-bell-gate.png":
        "8c5070722164b9a804f26ad2931aaa357d382575be0e092c58f11cad1fafcbed",
    ROOT / "deutsch-2000" / "images" / "figure-2-epr-experiment.png":
        "5f262a847f99cb25440a76783bac8b16c323a163e229bd9a164e4691e625c4e2",
    ROOT / "deutsch-2000" / "images" / "figure-3-quantum-teleportation.png":
        "22a3b7c5e3dc95c61151ceef02338ed4e0573c731fc0d0c33dfe931a2cab87d3",
}
EXPECTED_TAGGED_EQUATION_BUNDLE_SHA256 = (
    "b70465f98004c0581e6e68500a14f3ef82e24953e08cecf915fd1bacb351e69f"
)
EXPECTED_EQUATION35_PROSE_SHA256 = (
    "3e017d03353e9bfbec7e71f5c1e5b2afeca0fee0a791d608a8027643c7f64c22"
)


def require_exact(label: str, actual: list[int], expected: list[int]) -> None:
    if actual != expected:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        duplicates = sorted({item for item in actual if actual.count(item) > 1})
        raise SystemExit(
            f"{label} mismatch: missing={missing}, extra={extra}, "
            f"duplicates={duplicates}, actual={actual}"
        )


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


source_bytes = SOURCE.read_bytes()
if not source_bytes.endswith(b"\n"):
    raise SystemExit("canonical source must end with a newline")
source = source_bytes.decode("utf-8")
audit = AUDIT.read_text(encoding="utf-8")

for path, expected_sha256 in EXPECTED_ARTIFACT_SHA256.items():
    if not path.is_file():
        raise SystemExit(f"missing canonical artifact: {path}")
    actual_sha256 = sha256_bytes(path.read_bytes())
    if actual_sha256 != expected_sha256:
        raise SystemExit(
            f"canonical artifact hash mismatch for {path}: "
            f"expected={expected_sha256}, actual={actual_sha256}"
        )

expected_source_opening = (
    "# Information Flow in Entangled Quantum Systems\n\n"
    "**David Deutsch and Patrick Hayden**\n"
)
if not source.startswith(expected_source_opening):
    raise SystemExit("canonical title/author structure mismatch")
if not re.search(r"^## Abstract\n\n\*[^\n]+\*\n\n## 1\. ", source, flags=re.MULTILINE):
    raise SystemExit("canonical abstract heading/body structure mismatch")
if re.search(r"^### ", source, flags=re.MULTILINE):
    raise SystemExit("canonical source contains an unexpected level-three heading")
expected_headings = [
    "# Information Flow in Entangled Quantum Systems",
    "## Abstract",
    "## 1. Quantum information",
    "## 2. Quantum theory of computation in the Heisenberg picture",
    "## 3. Some specific quantum gates",
    "## 4. Information flow in Einstein-Podolski-Rosen experiments",
    "## 5. Information flow in quantum teleportation",
    "## 6. Locally inaccessible information",
    "## 7. Irrelevance of Bell’s theorem",
    "## 8. ‘Nonlocality’ of the Schrödinger picture",
    "## Acknowledgement",
    "## References",
]
actual_headings = re.findall(r"^#{1,6} .+$", source, flags=re.MULTILINE)
if actual_headings != expected_headings:
    raise SystemExit(
        f"canonical heading hierarchy mismatch: expected={expected_headings}, "
        f"actual={actual_headings}"
    )

stale_bell_qualifiers = (
    "Deutsch.Bell.Finite.",
    "Deutsch.Bell.Quantum.",
    "Deutsch.Bell.Contradiction.",
)
found_stale_bell_qualifiers = [
    qualifier for qualifier in stale_bell_qualifiers if qualifier in audit
]
if found_stale_bell_qualifiers:
    raise SystemExit(
        "audit uses nonexistent Bell declaration qualifiers; declarations live directly in "
        f"Deutsch.Bell: {found_stale_bell_qualifiers}"
    )

source_equations = [int(value) for value in re.findall(r"\\tag\{(\d+)\}", source)]
require_exact("source equation tags", source_equations, list(range(1, 47)))

equation_pairs = [
    (int(audit_id), int(source_id))
    for audit_id, source_id in re.findall(
        r"^\| E(\d{2}) \| \((\d+)\) \|", audit, flags=re.MULTILINE
    )
]
require_exact("audit equation IDs", [pair[0] for pair in equation_pairs], list(range(1, 47)))
require_exact("audit equation sources", [pair[1] for pair in equation_pairs], list(range(1, 47)))
if any(audit_id != source_id for audit_id, source_id in equation_pairs):
    raise SystemExit(f"equation ID/source mismatch: {equation_pairs}")

source_sections = [
    int(value) for value in re.findall(r"^## (\d+)\. ", source, flags=re.MULTILINE)
]
require_exact("numbered source sections", source_sections, list(range(1, 9)))

display_blocks = re.findall(
    r"^\$\$\s*\n(.*?)\n\$\$\s*$", source, flags=re.MULTILINE | re.DOTALL
)
tagged_blocks = [block for block in display_blocks if re.search(r"\\tag\{\d+\}", block)]
untagged_blocks = [
    block for block in display_blocks if not re.search(r"\\tag\{\d+\}", block)
]
if (len(display_blocks), len(tagged_blocks), len(untagged_blocks)) != (47, 46, 1):
    raise SystemExit(
        "display block mismatch: "
        f"total={len(display_blocks)}, tagged={len(tagged_blocks)}, "
        f"untagged={len(untagged_blocks)}"
    )

tagged_bundle_sha256 = sha256_bytes("\n\n".join(tagged_blocks).encode("utf-8"))
if tagged_bundle_sha256 != EXPECTED_TAGGED_EQUATION_BUNDLE_SHA256:
    raise SystemExit(
        "canonical tagged-equation bundle changed: "
        f"expected={EXPECTED_TAGGED_EQUATION_BUNDLE_SHA256}, "
        f"actual={tagged_bundle_sha256}"
    )

tagged_blocks_by_number = {
    int(re.search(r"\\tag\{(\d+)\}", block).group(1)): block
    for block in tagged_blocks
}
equation45_compact = re.sub(r"\s+", "", tagged_blocks_by_number[45])
corrected_equation45_signature = (
    r"a(\theta_0)\left(1-\left(a(\theta_1)\lora(\theta_2)\right)\right)"
)
if corrected_equation45_signature not in equation45_compact:
    raise SystemExit("canonical corrected Equation (45) complement signature mismatch")

compact_math = lambda value: re.sub(r"\s+", "", value)
untagged_signature = (
    r"\frac{1}{2}\left\langle\hat{1}-\hat{q}_{5z}(5)\right\rangle=1."
)
if untagged_signature not in compact_math(untagged_blocks[0]):
    raise SystemExit("unnumbered post-Equation-(37) display signature mismatch")

source_compact = compact_math(source)
display_blocks_compact = [compact_math(block) for block in display_blocks]
inline_signatures = {
    "U01": r"\hat{\mathbf{q}}_a(0)=U^\dagger\left(",
    "U03": (
        r"\left\langle\hat{q}_{4z}(1)\hat{q}_{5z}(1)\right\rangle\neq"
    ),
}
for identifier, signature in inline_signatures.items():
    if source_compact.count(signature) != 1:
        raise SystemExit(
            f"inline formula {identifier} signature count mismatch: "
            f"{source_compact.count(signature)}"
        )
    if any(signature in block for block in display_blocks_compact):
        raise SystemExit(f"inline formula {identifier} unexpectedly occurs in a display")

equation35_paragraphs = [
    paragraph
    for paragraph in source.split("\n\n")
    if paragraph.startswith("Teleportation is now (at $t=4$) complete.")
]
if len(equation35_paragraphs) != 1:
    raise SystemExit("Equation (35) introductory prose is missing or duplicated")
equation35_prose_sha256 = sha256_bytes(equation35_paragraphs[0].encode("utf-8"))
if equation35_prose_sha256 != EXPECTED_EQUATION35_PROSE_SHA256:
    raise SystemExit(
        "Equation (35) introductory prose changed: "
        f"expected={EXPECTED_EQUATION35_PROSE_SHA256}, "
        f"actual={equation35_prose_sha256}"
    )

correction_note = source.split("\n---\n", 1)
if len(correction_note) != 2:
    raise SystemExit("canonical source must contain exactly one correction-note separator")
required_correction_note_signatures = (
    "*Editorial note.* This edition corrects one index and three minor bookkeeping slips:",
    "the operator expressions in (28) and (40)",
    r"\hat{q}_{1z}(3)\hat{q}_{4z}(3)",
    "Equation (44) is unchanged.",
    "the subsequent expansion and contradiction are unchanged.",
)
for signature in required_correction_note_signatures:
    if signature not in correction_note[1]:
        raise SystemExit(f"canonical correction-note signature missing: {signature}")

audit_additional_math = [
    (int(audit_id), int(section_id))
    for audit_id, section_id in re.findall(
        r"^\| U(\d{2}) \| Section (\d+),", audit, flags=re.MULTILINE
    )
]
expected_unnumbered = [(1, 2), (2, 5), (3, 6)]
if audit_additional_math != expected_unnumbered:
    raise SystemExit(
        f"auxiliary formula ledger mismatch: expected={expected_unnumbered}, "
        f"actual={audit_additional_math}"
    )

source_figure_pairs = [
    (int(number), target)
    for number, target in re.findall(
        r"!\[Fig\. (\d+):[^\]]+\]\(([^)]+)\)", source
    )
]
require_exact(
    "source figures", [number for number, _ in source_figure_pairs], list(range(1, 4))
)
expected_figure_paths = [
    (SOURCE.parent / "images" / f"figure-{number}-{suffix}.png").resolve()
    for number, suffix in (
        (1, "bell-gate"),
        (2, "epr-experiment"),
        (3, "quantum-teleportation"),
    )
]
source_figure_paths = [
    (SOURCE.parent / target).resolve() for _, target in source_figure_pairs
]
if source_figure_paths != expected_figure_paths:
    raise SystemExit(
        f"source figure target mismatch: expected={expected_figure_paths}, "
        f"actual={source_figure_paths}"
    )
if any(not path.is_file() for path in source_figure_paths):
    raise SystemExit(f"missing source figure target among: {source_figure_paths}")

audit_figure_pairs = [
    (int(audit_id), int(source_id))
    for audit_id, source_id in re.findall(
        r"^\| F(\d{2}) \| Fig\. (\d+) \|", audit, flags=re.MULTILINE
    )
]
expected_figure_pairs = [(number, number) for number in range(1, 4)]
if audit_figure_pairs != expected_figure_pairs:
    raise SystemExit(
        f"figure ID/source mismatch: expected={expected_figure_pairs}, "
        f"actual={audit_figure_pairs}"
    )

for prefix, final in (("D", 11), ("C", 66), ("I", 10)):
    identifiers = [
        int(value)
        for value in re.findall(rf"^\| {prefix}(\d{{2}}) \|", audit, flags=re.MULTILINE)
    ]
    require_exact(
        f"{prefix} ledger identifiers", identifiers, list(range(1, final + 1))
    )

audit_link_targets = [
    (AUDIT.parent / target).resolve()
    for target in re.findall(r"\[[^\]]+\]\(([^)]+)\)", audit)
]
for expected_path in expected_figure_paths:
    if audit_link_targets.count(expected_path) != 1:
        raise SystemExit(
            f"audit must contain exactly one resolved link to {expected_path}; "
            f"found {audit_link_targets.count(expected_path)}"
        )

claim_lifecycle_rows = [
    (int(index), int(claim), classification.strip(), status.strip())
    for index, claim, classification, status in re.findall(
        r"^\| LC(\d{2}) \| C(\d{2}) \| ([^|]+) \| ([^|]+) \|$",
        audit,
        flags=re.MULTILINE,
    )
]
expected_claim_pairs = [(number, number) for number in range(1, 67)]
if [(index, claim) for index, claim, _, _ in claim_lifecycle_rows] != expected_claim_pairs:
    raise SystemExit("prose-claim classification/lifecycle index is incomplete or mispaired")

planned_claim_statuses = [
    index
    for index, _, _, status in claim_lifecycle_rows
    if status == "Planned"
]
if planned_claim_statuses:
    raise SystemExit(
        "final prose-claim lifecycle still contains Planned rows: "
        f"{planned_claim_statuses}"
    )

allowed_statuses = {"Corrected", "Partial", "Excluded", "Unresolved"}
bad_claim_statuses = [
    (index, status)
    for index, _, _, status in claim_lifecycle_rows
    if status not in allowed_statuses
]
if bad_claim_statuses:
    raise SystemExit(f"invalid prose-claim lifecycle statuses: {bad_claim_statuses}")

equation_rows = re.findall(r"^\| E\d{2} \|.*$", audit, flags=re.MULTILINE)
item_lifecycle_statuses: list[str] = []
for row_kind, rows in (
    ("equation", equation_rows),
    (
        "unnumbered display",
        re.findall(r"^\| U\d{2} \|.*$", audit, flags=re.MULTILINE),
    ),
    ("definition", re.findall(r"^\| D\d{2} \|.*$", audit, flags=re.MULTILINE)),
    ("figure", re.findall(r"^\| F\d{2} \|.*$", audit, flags=re.MULTILINE)),
):
    for row in rows:
        match = re.search(
            r"\|\s*(Planned|Oracle verified|Corrected|Partial|Excluded|Unresolved|Proved)\b[^|]*\|\s*$",
            row,
        )
        if match is None:
            raise SystemExit(f"{row_kind} row lacks an allowed lifecycle status: {row}")
        status = match.group(1)
        if status == "Planned":
            raise SystemExit(
                f"final {row_kind} lifecycle is still Planned: {row}"
            )
        if status == "Proved":
            raise SystemExit(f"{row_kind} row is prematurely marked proved: {row}")
        item_lifecycle_statuses.append(status)

print("source equations: 46 (tags 1..46, unique)")
print("audit equations: 46 (E01..E46, exact source match)")
print("source displays: 47 (46 tagged; 1 unnumbered)")
print("source auxiliary formulas: U01/U03 inline; U02 displayed")
print("source sections: 8; figures: 3; F01..F03 and link targets exact")
print("source/PDF/figure provenance: canonical hashes PASS")
print("tagged equation bundle and Equation (35) prose guards: PASS")
print("canonical corrected Equation (45) complement signature: PASS")
print("contiguous ledger IDs: definitions 11; prose claims 66; interpretation groups 10")
claim_status_counts = Counter(status for _, _, _, status in claim_lifecycle_rows)
item_status_counts = Counter(item_lifecycle_statuses)
print(
    "claim lifecycle statuses: LC01..LC66 exact; "
    f"Corrected={claim_status_counts['Corrected']}, "
    f"Partial={claim_status_counts['Partial']}, "
    f"Excluded={claim_status_counts['Excluded']}, "
    f"Unresolved={claim_status_counts['Unresolved']}; Planned=0"
)
print(
    "item lifecycle statuses: E/U/D/F final; "
    f"Oracle verified={item_status_counts['Oracle verified']}, "
    f"Corrected={item_status_counts['Corrected']}, "
    f"Partial={item_status_counts['Partial']}, "
    f"Excluded={item_status_counts['Excluded']}, "
    f"Unresolved={item_status_counts['Unresolved']}; Planned=0; Proved=0"
)
print("Bell declaration qualifiers: direct Deutsch.Bell namespace PASS")
print("source-audit coverage check: PASS")
