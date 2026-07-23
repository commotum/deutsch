# 2-SOURCE

## Current Facts

- Stage 1 established the canonical Markdown/PDF/figure hashes and their Git/BQP provenance.
- The canonical source has 1255 lines, 46 uniquely tagged equations, 47 display blocks
  (46 tagged and one untagged), eight numbered sections, three figures, and two separately audited
  inline formulas formerly classified as U01 and U03.
- The current mathematical equations are the accepted corrected baseline. No further equation edit
  is authorized in this stage.
- The current headings use an H2 author and H3 abstract/sections. The agreed structure is an ordinary
  bold author line, H2 abstract, H2 numbered sections, H2 acknowledgement, and H2 references.
- The abstract body is already wholly italicized and its heading must remain.
- The correction note currently begins at line 1244 and describes four categories of changes, but
  it does not clearly expose the three root bookkeeping slips or the recomputed intermediate
  operator in Equation (28).
- The prose before Equation (35) must remain unchanged. In particular, this stage must not add
  “non-trivial,” “rank-one,” or equivalent language.
- `goal-1/check_source_audit.py` currently encodes the compact transcription's 49-display model,
  stale U01/U03 display signatures, the old printed Equation (45) fixture, and lifecycle assumptions
  that cannot serve as the final compiled equation registry.
- Public source-fidelity documentation still contains stale claims that no PDF/facsimile comparison
  exists.

## Updated Assumptions

- A minimal heading and correction-note diff can make the Markdown semantically faithful without
  touching any equation or substantive prose.
- The source checker should continue to validate source structure and ledger completeness during
  the transition, but printed-form Eq45 verification should ultimately move to `DeutschErrata`.
- Stable PDF/figure provenance should be checked in-repository without reading the sibling BQP
  checkout.
- Old `goal-1` stage documents are historical records. Their stale facts should be corrected where
  they are consumed as present-tense authoritative evidence, without rewriting their entire history.

## Big Picture Objective

- Finalize the canonical corrected Markdown as a faithful, minimally edited source.
- Rewrite the end note as a polite disclosure of the harmless index correction and three root
  bookkeeping slips.
- Repair semantic heading structure while preserving the abstract and all paper content.
- Make source/provenance verification accurately reflect the PDF-backed 47-display source.
- Reconcile present-tense source-fidelity documentation with the now-available PDF comparison.

## Detailed Implementation Plan

- Change the author from H2 to ordinary bold text.
- Promote Abstract, sections 1–8, Acknowledgement, and References from H3 to H2.
- Rewrite the correction note to cover:
  1. `k -> n` after Equation (3);
  2. Equation (18)'s sine orientation and mechanical propagation;
  3. retention of the leading `q4z` sign in Equation (28), restoring the same/different and
     equal-setting formulas;
  4. explicit grouping of Equation (45)'s complement, already expanded in Equation (46).
- Mention Equation (28)'s recomputed intermediate operator, use natural outcome language, and avoid
  presenting propagated displays as independent mistakes.
- Update `goal-1/check_source_audit.py` to recognize:
  - the H2 numbered sections;
  - 47/46/1 display counts;
  - U01/U03 as inline formulas;
  - the canonical corrected Equation (45) signature.
- Add stable in-repository PDF/figure provenance validation, either to the source checker or a
  narrowly separate checker, without pinning the pre-edit Markdown hash.
- Correct stale present-tense PDF/source-structure claims in the main source audit and public project
  report as needed for truthful current documentation.
- Run focused source/provenance checks, documentation links, exact content guards, and diff review.

## No-Cheating Checks

- Diff the Equation (35) prose against the Stage 1/parent Git version and require exact equality.
- Require the equation-tag sequence to remain exactly 1 through 46.
- Require all displayed equation bodies to remain byte-identical across this stage.
- Require all three image paths and image bytes to remain unchanged.
- Do not reformat U01 or U03 into display math to satisfy the stale checker.
- Do not retain the printed Equation (45) as a source requirement; the canonical source must be
  checked against the corrected complement form.
- Do not claim compiled E01–E46 proof coverage from this source-only stage.
- Do not create a BQP filesystem dependency.

## Completion Requirements

- A focused source diff contains only the agreed author/heading and correction-note changes.
- The Equation (35) prose and all 46 equation bodies are unchanged.
- The correction note is concise, polite, complete, and organized around the three root slips.
- The source has exactly 46 unique tags, 47 display blocks, three figures, and eight H2 numbered
  sections.
- U01/U03 remain inline and are verified as such.
- PDF and figure hashes match the Stage 1 provenance.
- The source audit and documentation-link audit pass.
- Present-tense public documentation no longer says the PDF/facsimile is unavailable.
- `git diff --check` passes and all Stage 2 changes are recorded below.

## Stage Results

- In progress.

