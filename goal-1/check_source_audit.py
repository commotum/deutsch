"""Mechanical coverage checks for Stage 1's paper audit.

This does not prove any equation. It only prevents silent omissions and duplicate
ledger identifiers while the mathematical obligations remain explicitly routed.
"""

from collections import Counter
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "deutsch-2000" / "deutsch-2000.md"
AUDIT = ROOT / "goal-1" / "1-SOURCE-AUDIT.md"


def require_exact(label: str, actual: list[int], expected: list[int]) -> None:
    if actual != expected:
        missing = sorted(set(expected) - set(actual))
        extra = sorted(set(actual) - set(expected))
        duplicates = sorted({item for item in actual if actual.count(item) > 1})
        raise SystemExit(
            f"{label} mismatch: missing={missing}, extra={extra}, "
            f"duplicates={duplicates}, actual={actual}"
        )


source = SOURCE.read_text(encoding="utf-8")
audit = AUDIT.read_text(encoding="utf-8")

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
if (len(display_blocks), len(tagged_blocks), len(untagged_blocks)) != (49, 46, 3):
    raise SystemExit(
        "display block mismatch: "
        f"total={len(display_blocks)}, tagged={len(tagged_blocks)}, "
        f"untagged={len(untagged_blocks)}"
    )

untagged_signatures = (
    r"\hat{\mathbf q}_a(0)=U^\dagger",
    r"\frac12\left\langle\hat 1-\hat q_{5z}(5)\right\rangle=1",
    r"\bigl\langle\hat q_{4z}(1)\hat q_{5z}(1)\bigr\rangle",
)
for index, (block, signature) in enumerate(zip(untagged_blocks, untagged_signatures), 1):
    if signature not in block:
        raise SystemExit(f"unnumbered display U{index:02d} signature mismatch")

audit_unnumbered = [
    (int(audit_id), int(section_id))
    for audit_id, section_id in re.findall(
        r"^\| U(\d{2}) \| Section (\d+),", audit, flags=re.MULTILINE
    )
]
expected_unnumbered = [(1, 2), (2, 5), (3, 6)]
if audit_unnumbered != expected_unnumbered:
    raise SystemExit(
        f"unnumbered display ledger mismatch: expected={expected_unnumbered}, "
        f"actual={audit_unnumbered}"
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

if (
    "a_0=1`, `a_1=0`, `a_2=1" not in audit
    or "contradicted as printed" not in audit.lower()
):
    raise SystemExit("equation (45) counterexample/corrective disposition is missing")


def boolean_or(left: int, right: int) -> int:
    return left + right - left * right


counterexample = (1, 0, 1)
a_0, a_1, a_2 = counterexample
printed_left = a_0
printed_right = a_0 * boolean_or(a_1, a_2) + a_0 * boolean_or(1 - a_1, a_2)
if (printed_left, printed_right) != (1, 2):
    raise SystemExit("the recorded counterexample to printed equation (45) was not reproduced")

for a_0 in (0, 1):
    for a_1 in (0, 1):
        for a_2 in (0, 1):
            corrected_right = (
                a_0 * boolean_or(a_1, a_2) + a_0 * (1 - a_1) * (1 - a_2)
            )
            if a_0 != corrected_right:
                raise SystemExit(
                    "the proposed corrected partition for equation (45) failed at "
                    f"{(a_0, a_1, a_2)}"
                )

print("source equations: 46 (tags 1..46, unique)")
print("audit equations: 46 (E01..E46, exact source match)")
print("source displays: 49 (46 tagged; 3 unnumbered mapped to U01..U03)")
print("source sections: 8; figures: 3; F01..F03 and link targets exact")
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
print("equation (45): printed form falsified at (1,0,1); corrected partition truth-table PASS")
print("source-audit coverage check: PASS")
