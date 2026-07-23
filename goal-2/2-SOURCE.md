# 2-SOURCE

## Status

- Complete with source, provenance, build, integrity, documentation, and diff evidence on
  2026-07-23.

## Current Facts

- Stage 1 established the canonical Markdown/PDF/figure hashes and their Git/BQP provenance.
- The Stage 1 baseline had 1255 lines; after the agreed heading/note rewrite, the canonical source
  has 1258 lines, 46 uniquely tagged equations, 47 display blocks
  (46 tagged and one untagged), eight numbered sections, three figures, and two separately audited
  inline formulas formerly classified as U01 and U03.
- The mathematical equations remain the accepted corrected baseline; this stage made no equation
  edit.
- The current hierarchy is an ordinary bold author line, H2 abstract, H2 numbered sections, H2
  acknowledgement, and H2 references. The abstract body remains wholly italicized.
- The editorial note begins at line 1244 and now describes one harmless index correction and three
  root bookkeeping slips, including the recomputed intermediate operator in Equation (28).
- The prose before Equation (35) must remain unchanged. In particular, this stage must not add
  “non-trivial,” “rank-one,” or equivalent language.
- `goal-1/check_source_audit.py` has been separated conceptually from compiled proof coverage: it
  now checks the canonical source structure, stable provenance, ledger completeness, and protected
  source content. A compiled equation registry remains a later stage.
- Present-tense source-fidelity documentation has been reconciled with the available PDF and
  verified-transcription comparison.
- The final canonical Markdown SHA-256 is
  `f18273e9da7109c3be329b17b3942f0fa0b6f064904e7334befbdee66732d032`.

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

- The canonical source edit is exactly the agreed structural and editorial change:
  - the author is an ordinary bold line;
  - Abstract, sections 1–8, Acknowledgement, and References are H2 headings;
  - the italic abstract body is unchanged;
  - the end note now presents one index correction and three minor bookkeeping slips, explicitly
    names the recomputed Equation (28) operator, records the propagated displays, states that
    Equation (44) is unchanged, and explains the grouped complement in Equations (45)–(46).
- Comparing the source commit with its parent gives 27 added and 24 removed lines. Inspection of
  that focused diff shows only the author/heading replacements and editorial-note rewrite.
- The Stage 1 source SHA-256 was
  `b07b7bdafb13db21021b7e0d77efe74c2711fa6841772b00d3f369a67481b208`;
  the final source SHA-256 is
  `f18273e9da7109c3be329b17b3942f0fa0b6f064904e7334befbdee66732d032`.
- The checker pins the unchanged tagged-equation bundle at
  `b70465f98004c0581e6e68500a14f3ef82e24953e08cecf915fd1bacb351e69f`
  and the unchanged Equation (35) introductory prose at
  `3e017d03353e9bfbec7e71f5c1e5b2afeca0fee0a791d608a8027643c7f64c22`.
  This directly enforces the user's no-qualifier decision as well as preservation of all numbered
  displays.
- The source/provenance checker now validates 46 tags in exact order, 47 displays (46 tagged and
  one untagged), U01/U03 inline, U02 displayed, the full H1/H2 hierarchy, figure links, stable
  PDF/figure hashes, the corrected Equation (45) signature, the tagged-equation bundle, and the
  Equation (35) prose. It has no BQP filesystem dependency and no longer truth-tables the original
  Equation (45).
- Present-tense source facts were corrected in `goal-1/0-plan.md`,
  `goal-1/1-SOURCE-AUDIT.md`, `goal-1/12-LIBRARY-AUDIT.md`, and
  `docs/project-report.md`. Dated historical command evidence elsewhere in Goal 1 was not rewritten.
  The source ledger now explicitly records that pair-state EPR statistics and the independent
  pigeonhole Bell theorem do not yet constitute the required direct source-shaped derivations.
- Verification passed:
  - `lake build Deutsch DeutschTests`: 3309 jobs.
  - `python3 -B goal-1/check_lean_integrity.py`: 65 Lean sources, 402 representative axiom
    reports, no forbidden declarations or proof holes, and only `Classical.choice`, `Quot.sound`,
    and `propext`.
  - `python3 -B goal-1/check_source_audit.py`: all source, provenance, protected-content, and ledger
    checks passed.
  - `python3 -B goal-1/check_doc_links.py`: 14 expected/discovered public Markdown files and 118
    repository-local links.
  - `git diff --check` and the focused trailing-whitespace scan passed.
- Stage 3 can therefore work entirely against the finalized corrected source. No source edit is
  anticipated or authorized by the four-wire EPR implementation.
