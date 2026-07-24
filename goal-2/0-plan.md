# Goal 2: Corrected Paper and Two-Library Lean Cutover

Shorthand: `LEAN-PAPER-CUTOVER`

## Big-Picture Objective

Turn the reviewed Deutsch--Hayden formalization into two clean public Lean libraries:

1. `Deutsch`, a neutral, reusable derivation of the corrected paper that reads as though the
   corrected source had been used from the beginning and gives direct compiled coverage of all
   forty-six numbered equations.
2. `DeutschErrata`, a deliberately small companion that politely demonstrates the few bookkeeping
   defects in the printed paper, proves the corrected forms are forced by the surrounding
   conventions, and shows that Deutsch's intended mathematical conclusions remain intact.

The canonical Markdown should preserve Deutsch and Hayden's presentation as closely as possible.
Its existing corrected equations are the accepted mathematical baseline. The end note should be
rewritten to explain the corrections as three root bookkeeping slips rather than a long collection
of independent errors.

Completion means more than moving declarations or making builds green. The corrected equations
must be independently derived in Lean under explicit finite-dimensional assumptions, the direct
source argument must be represented where requested, the historical comparison must be isolated
from production, and every claim of coverage must be backed by a compiled declaration and an
auditable source mapping.

## Non-Negotiable Constraints and No-Cheating Rules

- Do not alter the purity prose before Equation (35) to add “non-trivial,” “rank-one,” or a similar
  qualifier. The user has explicitly decided that the existing Boolean-observable convention is
  clear and should remain faithful to the paper.
- Treat the current corrected forms of Equations (18), (25), (27)–(29), (31), (32), (34)–(37),
  (40)–(43), (45), and (46) as the canonical source baseline. Do not introduce a different
  convention or correction merely because it shortens a Lean proof.
- Rewrite the correction note at the end of `deutsch-2000/deutsch-2000.md` politely and concisely.
  Present the mathematical changes as three root bookkeeping slips:
  1. the sine orientation in the expansion from (17) to (18), with mechanical propagation;
  2. the lost leading sign in the EPR joint correlation, which swapped same/different outcomes;
  3. the missing grouping around the complement in (45), already revealed by (46).
  Retain the harmless `k`/`n` index correction and disclose all mechanically affected displays
  without making them sound like independent mistakes.
- Preserve every numbered equation, equation number, section, figure, image, and substantive piece
  of source prose except for the explicitly agreed correction-note and Markdown-structure work.
  If later proof work appears to require another source correction, stop, record the evidence, and
  obtain review before editing the source.
- `Deutsch` must contain only the corrected mathematics and neutral terminology. It must not expose
  declarations, comments, imports, or compatibility aliases named `printed`, `corrected`,
  `sourceCorrection`, `source defect`, or equivalent historical language.
- `DeutschErrata` may import narrow `Deutsch` modules. `Deutsch` must never import
  `DeutschErrata`, either directly or transitively.
- Keep physical teleportation terminology such as `Correction`, `correctionGate`, and branch
  corrections. Those names describe the protocol and are not editorial history.
- Do not preserve old public theorem names through backwards-compatibility aliases. This is a full
  cutover.
- Do not prove an equation by assuming that equation, encoding its desired conclusion as a premise,
  or choosing definitions solely so the target is reflexive without proving that those definitions
  implement the paper's matrices, circuits, probabilities, or stochastic model.
- Keep exact operator equality, global-phase equivalence, state/effect probability equality,
  reduced-state equality, and equality on positive-measure support distinct.
- A pair-state calculation does not count as a direct proof about Figure 2's four-wire record and
  comparison circuit until a compiled bridge proves the two formulations agree.
- The existing pigeonhole Bell proof does not count as a formalization of corrected Equations
  (42)–(46). Both routes must compile independently.
- Equation (43) must be formalized as almost-sure equality or equality on positive-weight support;
  zero-weight hidden assignments must not be constrained without justification.
- Equation (17)'s arbitrary-axis result must not be claimed from the existing `x`-axis closed form.
  Any matrix-exponential theorem must connect the exponential, unitary, Pauli-axis definition, and
  conjugation formula explicitly.
- Do not use `sorry`, `admit`, `by_contra!` as concealment, `unsafe`, project-specific `axiom`,
  `opaque`, or unexplained classical assumptions.
- Do not claim that Lean proves authorial intent, an ontology, or an assumption-free statement that
  physical reality is local. The formal result should establish the corrected finite mathematics,
  the operational locality statements under named hypotheses, and the exact inconsistent
  single-outcome stochastic assumptions.
- The repository build and audits must not depend on the sibling
  `/home/jake/Developer/bqp` checkout. Record original-form provenance using the in-repository PDF,
  Git history, and stable checksums or explicit errata fixtures.
- Preserve unrelated user changes and keep generated files out of source patches.

## Current Facts

- The current canonical source is `deutsch-2000/deutsch-2000.md`; the corresponding PDF and all
  three figures are present under `deutsch-2000/`.
- After the agreed heading/note rewrite, the canonical Markdown has 1258 lines and exactly 47
  display-math blocks: 46 uniquely tagged equations numbered (1)–(46) and one unnumbered display
  following (37). Two formulas classified as U01 and U03 in the old audit are inline in both the
  PDF and verified transcription; only the compact original transcription promoted them to display
  blocks.
- The earlier compact and verified transcriptions remain available for review in
  `/home/jake/Developer/bqp/papers/deutsch-2000/`, but they are external to this repository and
  cannot be runtime or build dependencies.
- A second independent mathematical review found no better correction to the numbered equations
  and no remaining false numbered display.
- The seventeen changed equation displays reduce to three root bookkeeping slips. Equation (44)
  remains unchanged and is the point at which the repaired EPR/Bell route rejoins the printed
  argument.
- The editorial note at `deutsch-2000/deutsch-2000.md:1244` now describes one harmless index
  correction and three root bookkeeping slips, including the recomputed Equation (28) operator,
  their mechanical propagation, and Equation (44)'s unchanged status.
- The current Markdown uses an ordinary bold author line, `## Abstract`, `## 1.` through `## 8.`,
  `## Acknowledgement`, and `## References`; the abstract body remains wholly italicized.
- The protected tagged-equation bundle and Equation (35) prose hashes are unchanged from Stage 1.
  The canonical Markdown SHA-256 after the Stage 2 rewrite is
  `f18273e9da7109c3be329b17b3942f0fa0b6f064904e7334befbdee66732d032`.
- The Lake package is pinned to Lean/mathlib `v4.32.0` and currently defines the `Deutsch` and
  `DeutschTests` libraries.
- A fresh Stage 1 build completed 3309 jobs. The integrity audit scanned 65 Lean
  sources and reported no proof holes, project axioms, unsafe declarations, or opaque escapes. Its
  accepted dependency axioms were only `Classical.choice`, `Quot.sound`, and `propext`.
- Most reusable mathematics already exists in the production tree: finite registers, subsystem
  embeddings, Heisenberg locality, descriptor algebra, gates, EPR states and descriptors,
  teleportation correctness, channels/decoherence, and a finite Bell contradiction.
- Historical comparison currently leaks into production through:
  - `Deutsch/Bell/SourceCorrection.lean`;
  - `*_ne_printed` declarations in gate, EPR, and teleportation modules;
  - `equation35CorrectedEffect` and printed Equation (35) fixtures;
  - `corrected_` Bell theorem names and correction-oriented public documentation.
- The Stage 1 declaration audit classifies the existing finite production mathematics as 31 direct
  equation implementations, seven wrapper/packaging gaps (E08, E09, E13, E14, E19, E26, E45), and
  eight substantive proof gaps (E17, E28, E40–E44, E46). Every item will still receive a canonical
  source-shaped `Deutsch.Paper` entry in Stage 5.
- The substantive gaps comprise Equation (17)'s arbitrary-axis exponential, Figure 2's literal
  four-wire route for Equations (28), (40), and (41), and the direct corrected expectation route
  through Equations (42)–(44) and (46). The existing Bell contradiction is an independent
  agreement/pigeonhole proof rather than that displayed chain.
- Present-tense source-fidelity claims in the project report and old goal ledger now acknowledge
  the PDF/verified-transcription comparison; dated historical stage evidence was left unchanged.
- The canonical PDF is a 24-page A4 file with 1999-06-02 creation metadata and is byte-identical to
  the BQP comparison PDF. The repository figures are byte-identical to BQP's verified figure set,
  and Git history retains the deleted compact, verified, and corrected Markdown variants.
- The only direct production import of a wholly historical module is
  `Deutsch/Bell.lean -> Deutsch.Bell.SourceCorrection`. Additional printed-form witnesses are
  embedded in the gate, EPR, and teleportation modules and have exact Stage 6 destinations.
- `Deutsch.Gates.AxisRotation` now derives arbitrary real unit-axis Pauli rotations from the actual
  Banach-algebra matrix exponential, proves unitarity and Rodrigues conjugation, and specializes to
  the existing `X`-axis convention. `Deutsch.Gates.AxisRotationRegister` lifts and transports the
  construction to a named qubit in an arbitrary unitary Heisenberg frame.
- The historically neutral `Deutsch.Paper` façade now exposes exactly one bare declaration
  `equation01` through `equation46`. Equations (28), (40), and (41) expose their literal four-wire
  circuit statements and pair-state bridges; Equations (42)--(46) use the direct all-real-angle
  finite-moment chain rather than the independent pigeonhole route.
- `DeutschTests.Paper` contains all 46 exact compile checks plus eight focused no-cheating wrappers.
  The integrity checker independently scans declaration locations, the contiguous compile
  registry, and all 46 axiom targets.
- A complete Stage 5 build finished 3327 jobs. The integrity audit scanned 79 Lean sources and
  checked 517 representative axiom reports; only `Classical.choice`, `Quot.sound`, and `propext`
  occurred. Source, provenance, documentation-link, whitespace, and diff checks also pass.
- The package now has four Lake targets: `Deutsch`, `DeutschErrata`, `DeutschTests`, and
  `DeutschErrataTests`. `DeutschErrata` consists of five small production modules with exact narrow
  imports; no `Deutsch` source imports it.
- The errata layer contains decisive checks for Equation (18)'s exponential-forced orientation,
  literal four-wire Equations (28)/(41), the propagated Equation (35) probability and Equation
  (37) operator endpoints, Equation (45)'s `(1,0,1)` Boolean values and universal complement, and
  the direct moment-chain Equation (46) contradiction. It does not duplicate a circuit.
- `DeutschErrataTests` has 11 focused wrappers and 26 axiom targets. The four-target build completed
  3338 jobs; its axiom reports contain only `Classical.choice`, `Quot.sound`, and `propext`.
- The errata boundary/provenance checker verifies the exact import DAG, absence of reverse imports
  and BQP runtime paths, the canonical Markdown/PDF hashes, and both original-transcription Git
  object hashes.
- The Stage 7 cutover is complete. `Deutsch/Bell/SourceCorrection.lean` and all embedded
  original-form comparisons are gone from `Deutsch`; all six reusable APIs have neutral names
  with no compatibility aliases, and the main tests and public documentation use only those
  names.
- The strengthened integrity and boundary audits enforce all four Lake roots, one-way imports,
  exact neutral declarations, absence of editorial-history tokens under `Deutsch` and
  `DeutschTests`, and the exact E01--E46 registry.  A 3337-job four-target build and both audits
  pass with only `Classical.choice`, `Quot.sound`, and `propext`.

## Current Assumptions to Test

- The existing corrected formulas will survive a literal four-wire EPR derivation and a direct
  Equation (42)–(46) formalization without further source edits.
- A public `Deutsch.Paper` façade can give exact equation-by-equation traceability while the topical
  core retains descriptive, reusable theorem names.
- The arbitrary-axis Equation (17) can be proved cleanly using a unit Pauli-axis matrix, its square
  relation, a closed exponential form, and a Rodrigues-style conjugation theorem in the pinned
  mathlib version.
- A small `DeutschErrata` can reuse neutral production results for general corrected formulas while
  retaining a tiny Mathlib-level elementary layer for decisive independent special cases.
- The finite deterministic-response Bell model can be connected to a finite factorizable stochastic
  model by an explicit refinement/distribution construction without adding a new physical premise.
- The paper's mixed-state fixed-reference sentence can be supported in a precise enlarged-register
  or purification formulation without pretending that a same-register unitary changes a mixed
  state into a pure state. This is Lean-side scope clarification, not authorization to rewrite the
  paper's prose.
- The existing coherent teleportation and semantic identity-channel results can be connected
  without reimplementing the protocol.

## Success Metrics and Verification Requirements

- The canonical Markdown contains the agreed corrected equations, figures, abstract styling, and
  section structure, with a concise end note organized around the three root bookkeeping slips.
- The prose before Equation (35) is byte-for-byte unchanged except for any unrelated line movement
  caused by heading edits.
- `Deutsch` exposes neutral reusable mathematics and a compiled `Deutsch.Paper` mapping for exactly
  E01 through E46.
- Every numbered equation is represented by a production declaration with explicit scope and
  assumptions; no source-ledger label substitutes for compilation.
- Equations (28), (40), and (41) are proved through the four-wire circuit and shown equal to the
  independent pair-state calculations.
- Corrected Equations (42)–(46) compile as the literal finite-expectation derivation, including the
  complementary partition and positive-support treatment.
- The direct Equation (42)–(46) proof and the independent pigeonhole Bell proof both derive the
  contradiction from clearly listed assumptions.
- Equation (17) has a genuine arbitrary-axis matrix-exponential theorem, or the goal remains
  incomplete with an explicit unresolved proof obligation; it may not be silently downgraded.
- `DeutschErrata` alone contains the printed-form fixtures and decisive counterexamples. It explains
  downstream sign differences as propagation and does not duplicate entire circuits.
- Production imports are one-way: `DeutschErrata -> Deutsch`, never the reverse.
- No historical compatibility aliases or correction-oriented declarations remain in `Deutsch`.
- A finite stochastic-local refinement theorem connects the stated stochastic model to the
  deterministic-table contradiction, or its exact missing assumption remains explicit and prevents
  an overbroad final claim.
- Supporting hardening theorems precisely handle the mixed-state/purification boundary, the actual
  EPR resource's entanglement, and the coherent-circuit/identity-channel connection to the extent
  needed by the final advertised scope.
- Separate production and errata tests and axiom audits pass.
- All builds, focused tests, source checks, documentation-link checks, import-boundary scans,
  forbidden-token scans, whitespace checks, and `git diff --check` pass.
- Axiom reports contain no `sorryAx` or project axioms and no unexpected dependency axiom beyond the
  explicitly accepted mathlib foundations.
- Original printed formulas have stable in-repository provenance; no verifier reads from the sibling
  BQP checkout.
- Documentation states exactly what is proved: corrected finite-dimensional mathematics,
  operational locality under explicit support/channel assumptions, teleportation/EPR results, and
  the inconsistency of the named single-outcome stochastic model. It does not promote historical or
  ontological interpretation into a theorem.

## Stages

### 1-BASELINE

#### Status

Complete with recorded evidence in `goal-2/1-BASELINE.md`.

#### Big Picture Objective

Freeze a trustworthy starting point, resolve the exact public contract, and turn every reviewed
gap into a tracked obligation before changing source or Lean declarations.

#### Detailed Implementation Plan

- Inspect the current worktree, branch, source hashes, PDF/images, Lake configuration, module graph,
  tests, and all existing audits.
- Record stable hashes for the canonical corrected Markdown, PDF, and three figures.
- Re-run the current build, integrity audit, documentation audit, source audit, and whitespace/diff
  checks; distinguish pre-existing stale checks from mathematical failures.
- Produce the exact E01–E46 declaration map, marking existing reusable theorem, wrapper-only gap, or
  substantive proof gap.
- Inventory every correction-oriented name/comment/import that must leave `Deutsch`.
- Lock the two-public-library dependency rule and the source-edit boundary, including the explicit
  prohibition on changing the purity prose before Equation (35).

#### Completion Requirements

- Baseline commands and results are recorded with no unexamined failure.
- Every E01–E46 item and every historical production declaration has a destination.
- The source, PDF, and figure hashes are recorded.
- The planned scope distinguishes equations, operational prose claims, and interpretation.
- No implementation file has been changed beyond the stage record and any narrowly necessary
  baseline tooling fix that is itself documented and verified.

### 2-SOURCE

#### Status

Complete with recorded evidence in `goal-2/2-SOURCE.md`.

#### Big Picture Objective

Finalize the corrected Markdown as a faithful, minimally edited canonical source.

#### Detailed Implementation Plan

- Rewrite the correction note at line 1244 around the three root bookkeeping slips, the `k`/`n`
  index correction, and their mechanical propagation.
- Mention that Equation (28)'s intermediate operator product was recomputed as well as its final
  probability.
- Replace “joint paper-one probability” with natural source-facing language such as “the probability
  that both recorded outcomes are 1.”
- Correct the Markdown hierarchy: author as ordinary emphasized/bold text, `## Abstract`, numbered
  sections at `##`, while preserving the italic abstract body.
- Preserve the purity prose before Equation (35) and all corrected mathematical displays.
- Update the source checker and source-fidelity documentation only as required by the canonical
  hierarchy and now-present PDF.

#### Completion Requirements

- A focused diff shows only the agreed correction-note, heading/author formatting, and directly
  corresponding audit/documentation changes.
- The Equation (35) purity prose remains unchanged.
- All 46 equation tags, 47 display blocks (46 tagged and one untagged), three figures, and eight
  numbered sections are present. The two audited inline formulas remain present and are checked as
  inline source signatures rather than being reformatted into displays.
- Source, image, and documentation-link checks pass.
- The correction note is complete, polite, concise, and describes root mistakes rather than
  seventeen independent mathematical failures.

### 3-EPR-BRIDGE

#### Status

Complete with recorded evidence in `goal-2/3-EPR-BRIDGE.md`.

#### Big Picture Objective

Derive Equations (28), (40), and (41) from Figure 2's literal four-wire chronology and connect them
to the independent two-qubit pair calculations.

#### Detailed Implementation Plan

- Add a production record-statistics module with four-wire reference, time-three, and time-four
  state/density definitions tied to the existing circuit.
- Define the paper-one effects on record qubits `q1` and `q4`, their joint effect, and the final
  comparison effect.
- Prove the two record marginals, joint-one probability, and different-outcome comparison
  probability.
- Prove an explicit bridge equating those circuit statistics to the existing pair-state statistics.
- Add boundary tests at equal settings and a relative angle of `pi`, keeping raw-index and paper-bit
  conventions explicit.

#### Completion Requirements

- Canonical production theorems for Equations (28), (40), and (41) mention the four-wire records or
  final comparison circuit directly.
- Pair-state and four-wire results are proved equal rather than merely sharing a formula.
- Equal-setting and opposite-setting boundary tests compile.
- No measurement-collapse or outcome-conditioned instrument is silently assumed for coherent record
  CNOTs.
- Focused EPR tests, the full build, and the axiom audit pass.

### 4-BELL-MOMENTS

#### Status

Complete with recorded evidence in `goal-2/4-BELL-MOMENTS.md`.

#### Big Picture Objective

Formalize the corrected Equations (42)–(46) exactly as Deutsch's finite expectation argument while
retaining the independent pigeonhole proof.

#### Detailed Implementation Plan

- Add neutral Boolean-indicator and finite weighted-expectation infrastructure over `ℝ`.
- State the three-setting EPR moment-reproduction assumptions using the corrected Equation (40) and
  (41) statistics.
- Derive Equation (42)'s mean square, Equation (43)'s equality on positive-weight support, and
  Equation (44)'s counterfactual Alice moment on one common finite probability space.
- Prove Equation (45)'s complementary partition in a form that feeds averaging directly.
- Compile every equality/inequality in Equation (46), including nonnegativity of the triple product,
  and derive the contradiction.
- Keep the existing agreement/pigeonhole proof independent and add a theorem or test showing both
  routes reject the same named finite model.

#### Completion Requirements

- Each of Equations (42)–(46) has a neutral production theorem matching the corrected source.
- Equation (43) does not constrain zero-weight assignments.
- Equation (45) uses an actual complementary event rather than relying on natural-number truncated
  subtraction.
- The final `1/2 <= 3/8` contradiction is derived without importing errata or the alternative
  pigeonhole theorem.
- Both Bell proofs compile and pass separate axiom reports.

### 5-EQUATIONS

#### Status

Complete with recorded evidence in `goal-2/5-EQUATIONS.md`.

#### Big Picture Objective

Close every remaining literal E01–E46 proof or packaging gap and expose a clean paper-facing façade
over reusable topical mathematics.

#### Detailed Implementation Plan

- Implement Equation (17)'s arbitrary unit-axis Pauli rotation, matrix exponential or proved closed
  exponential form, unitarity, and Heisenberg conjugation.
- Package the existing foundations and gate results into exact source-shaped theorems where the
  mathematics already exists.
- Close the time-indexed Equation (9), Equation (13)'s other-qubit invariance, and current-descriptor
  forms of Equations (14) and (19).
- Handle Equation (8)'s eigenbasis statement with explicit phase/degeneracy assumptions rather than
  claiming a canonical basis where none is supplied.
- Add `Deutsch.Paper` modules organized by source section and a root façade exposing exactly one
  canonical entry for each E01–E46.
- Add a compiled equation registry that fails if any equation entry is missing, renamed without
  reconciliation, or routed only to tests.

#### Completion Requirements

- E01–E46 all resolve to compiled production declarations under explicit hypotheses.
- Equation (17) is genuinely arbitrary-axis and connected to the same rotation convention used by
  Equation (18).
- Definitions, schemas, and equalities are distinguished in the façade rather than forced into one
  misleading theorem shape.
- Global phase qualifications for Equations (22) and (38) remain explicit.
- The exact equation registry, focused tests, full build, and axiom audit pass.

### 6-ERRATA

#### Status

Complete with recorded evidence in `goal-2/6-ERRATA.md`.

#### Big Picture Objective

Create a small, polite historical library that proves the printed defects are localized bookkeeping
errors and that the corrected forms are the natural intended results.

#### Detailed Implementation Plan

- Add the `DeutschErrata` Lake library and root without changing `Deutsch` imports.
- Add a tiny elementary layer for decisive raw matrix/Boolean checks where independence materially
  improves confidence.
- Add narrow modules for:
  - Equation (18)'s two printed signs and the `pi/2` witness;
  - Equations (28)/(41)'s same/different swap and equal-setting witnesses;
  - one or two teleportation endpoint witnesses showing mechanical propagation, preferably
    Equations (35) and (37), without duplicating the whole circuit;
  - Equation (45)'s `(1,0,1)` counterexample and universal complementary replacement;
  - the fact that corrected Equation (46) restores the intended contradiction.
- Record the `k`/`n` typo and source provenance in concise errata documentation rather than creating
  artificial Lean theorems.
- Add `DeutschErrataTests` and a separate axiom audit.

#### Completion Requirements

- `DeutschErrata` is independently importable and depends only on Mathlib plus narrow neutral
  `Deutsch` modules.
- The errata root exports only decisive comparison results; redundant counterexamples for every
  propagated descriptor are absent.
- The prose consistently says “printed form,” “derived form,” and “complementary partition,” avoiding
  polemical claims about the authors.
- Printed formulas and their provenance exist only in errata-facing files.
- Focused errata tests, its axiom audit, and the full build pass.

### 7-CUTOVER

#### Status

Complete with recorded evidence in `goal-2/7-CUTOVER.md`.

#### Big Picture Objective

Remove all historical correction residue from `Deutsch` and make the one-way two-library
architecture real.

#### Detailed Implementation Plan

- Move or delete production `*_ne_printed` declarations after their minimal errata replacements
  compile.
- Remove `Deutsch/Bell/SourceCorrection.lean` from the production import graph and replace any
  reusable Boolean content with neutral modules.
- Rename correction-oriented production definitions and theorems, including Equation (35) and final
  Bell declarations, without compatibility aliases.
- Neutralize module docstrings, public roots, examples, reports, and reuse documentation.
- Preserve physical teleportation correction names.
- Update import-closure and integrity tooling to enforce both library boundaries and separate test
  roots.

#### Completion Requirements

- A repository scan finds no editorial `printed`, `corrected`, `SourceCorrection`, or equivalent
  history in `Deutsch` production sources, excluding quotations in intentionally separate errata
  documentation.
- `Deutsch` has no direct or transitive import of `DeutschErrata` or any test root.
- Every original-form comparison is reachable through `DeutschErrata` and nowhere else.
- No compatibility alias preserves a superseded public name.
- Production examples compile using only neutral APIs.

### 8-STOCHASTIC

#### Status

In progress. See `goal-2/8-STOCHASTIC.md`.

#### Big Picture Objective

Connect the finite deterministic response-table contradiction to a conventional finite
factorizable stochastic local model so the advertised Bell scope exactly matches the stated
stochastic premise.

#### Detailed Implementation Plan

- Define finite setting-local stochastic response kernels, normalized hidden-variable weights,
  factorization, and setting independence.
- Construct an explicit distribution over deterministic local response tables, using finite local
  random seeds or the equivalent convex refinement.
- Prove preservation of all relevant pair and marginal probabilities.
- Apply the production Bell contradiction to rule out a stochastic model reproducing the corrected
  three-setting EPR table.
- Keep the assumptions visible and avoid claims about continuum settings or every possible Bell
  formalism.

#### Completion Requirements

- The stochastic-to-deterministic refinement is constructive and probability preserving.
- The final stochastic contradiction lists normalization, nonnegativity, setting independence, and
  factorization explicitly.
- No counterfactual joint assignment is smuggled in as an extra axiom; it is produced by the finite
  refinement.
- Focused stochastic tests, full build, and axiom audit pass.

### 9-ANALYSIS

#### Big Picture Objective

Harden the supporting mathematical analysis needed for the strongest accurate account of the
paper, without turning interpretation into theorem.

#### Detailed Implementation Plan

- Prove an enlarged-register/purification fixed-reference theorem for arbitrary finite density
  states while retaining the same-register purity obstruction as a scope boundary.
- Promote or rederive a production theorem that the actual EPR resource used by the paper is
  non-product/entangled, rather than treating a few correlation moments as an entanglement witness.
- Connect the literal coherent teleportation circuit to the semantic identity channel, preferably
  with an arbitrary finite reference system if supported by the existing factorization.
- Reconcile the operational information/locality documentation with these strengthened theorems.
- State the final theorem contract narrowly: finite-dimensional corrected equations, supported
  locality/no-signalling, circuit-level EPR and teleportation, and the named Bell-model
  contradiction.

#### Completion Requirements

- Mixed-state fixed-reference claims explicitly state the enlarged-system construction and never
  assert rank-changing same-register unitary equivalence.
- The actual paper resource has a compiled entanglement/non-product proof.
- Any claimed teleportation identity-channel bridge is derived from the literal circuit, not merely
  placed beside a separately defined semantic channel.
- Documentation cleanly separates mathematical results, operational interpretations, historical
  inference, and ontology.
- No source prose is changed as part of this stage without separate user review.

### 10-AUDIT

#### Big Picture Objective

Verify the entire cutover from a clean generated state and leave a precise, reproducible public
result.

#### Detailed Implementation Plan

- Run focused builds and tests for every stage, then clean only generated project outputs and run all
  public and verification targets.
- Run the production and errata axiom audits, forbidden-token scans, import-boundary scans,
  E01–E46 registry, source audit, documentation-link audit, whitespace scan, and `git diff --check`.
- Verify stable source/PDF/image provenance and absence of any BQP runtime dependency.
- Review every public theorem and document claim against the final scope.
- Produce concise corrected-paper, main-library, errata, reuse, and verification documentation.
- Record exact commands, toolchain revisions, counts, hashes, and results in the stage report and
  fold them into this plan.

#### Completion Requirements

- All four intended targets (`Deutsch`, `DeutschErrata`, `DeutschTests`, `DeutschErrataTests`) build
  from a clean generated state.
- Every E01–E46 registry entry compiles and both Bell proof routes pass.
- Both axiom inventories contain only the explicitly accepted foundations and no `sorryAx`.
- Source, provenance, documentation, import, hygiene, and diff checks all pass.
- `Deutsch` is historically neutral; `DeutschErrata` is minimal and complete.
- The final report states exact finite scope and limitations without claiming authorial intent or
  ontology as mechanically proved.
- No required stage or unresolved proof obligation is hidden behind optimistic wording.
