# 5-DESCRIPTORS

## Status

- Complete with evidence on 2026-07-16.

## Current Facts

- Stages 1–5 are complete with evidence; Stage 6 is the first incomplete stage.
- `Deutsch.Descriptor` exports global triples, nonredundant validity, named-coordinate initial families, shared unitary evolution, constructive generation, an explicit Pauli-word basis/reconstruction, and separated comparison relations.
- Initial `X/Y/Z` components have exact singleton support, every same-factor signed Pauli law, and all arbitrary distinct-label cross-axis commutators.
- `DescriptorFamily.initial_generates_operator_algebra` constructively builds every global matrix unit and proves that the initial components generate the full operator algebra. `PauliWord.reconstruction` independently supplies exact coefficients for every operator.
- `DescriptorFamily.GeneratesOperatorAlgebra.evolve` and `PauliWord.evolvedReconstruction` preserve both completeness interfaces under arbitrary bundled unitary evolution.
- The source's unqualified individual-triple completeness prose is not asserted. Joint algebra generation, basis reconstruction, unitary conjugacy, and fixed-reference component expectations are distinct formal notions.

## Updated Assumptions

- A descriptor should be a typed triple of global operators plus a validity predicate/structure containing exactly the Hermitian cyclic Pauli relations. Cross-factor commutation belongs to a family-level condition, not to one triple in isolation.
- Initial descriptors are `xAt/yAt/zAt`; evolved descriptors conjugate all three components by the same unitary.
- Preservation proofs should reuse Heisenberg algebra homomorphism laws and not re-evaluate finite matrix entries.
- “Complete” is replaced by two compiled exact results: constructive full-algebra generation through explicit matrix units, and a genuine Pauli-word basis with a coefficient reconstruction formula.
- Fixed-reference equality of predictions is weaker than descriptor-operator equality and must not be used as a substitute for algebraic generation.
- Gauge/conjugacy names one shared bundled unitary. A compiled `-Z` reference-stabilizer regression changes the valid initial `X` component to `-X` while preserving all fixed-reference descriptor-component expectations, proving that this weaker relation does not imply operator equality.

## Big Picture Objective

- Export reusable, valid global Pauli descriptor triples and families, prove their initial and unitary-evolved invariants, and replace the paper's completeness prose with a precise reconstruction/generation theorem or an exact obstruction plus the strongest proved substitute.

## Detailed Implementation Plan

1. Define a readable Pauli-axis type and a descriptor triple over `Operator Q`, with component access and an explicit validity predicate/structure.
2. Define initial descriptor triples/families from `xAt/yAt/zAt`; prove Hermiticity, squares, cyclic signed products, anticommutation, support, and cross-label commutation.
3. Define simultaneous unitary descriptor evolution and prove validity and family cross-commutation preservation from generic Heisenberg laws.
4. Relate descriptor evolution componentwise to circuit/operator conjugation without introducing named gate formulas early.
5. Investigate and compile the strongest exact completeness result: Pauli-string basis/reconstruction, algebra generation, or matrix-unit reconstruction. Record failed representations and do not rename a mere cardinality fact “complete.”
6. State a separate fixed-reference/gauge comparison only if its hypotheses and equality level are explicit.
7. Add one-/two-/three-qubit positive examples and negative invalid triples/families that falsify missing validity clauses.
8. Add public docs, source-ledger lifecycle locations, audit targets, and the full verification record; fold results into `0-plan.md` before completion.

Expected files include:

- `Deutsch/Descriptor.lean` or a small `Deutsch/Descriptor/*` hierarchy
- `DeutschTests/Descriptor.lean`
- `docs/descriptors.md`
- updates to the public roots, integrity/axiom audit, source ledger, and `0-plan.md`

## Paper Mapping

- E01/D04/C08: define a global Hermitian descriptor triple with register/factor identity carried by types or family indices.
- E02/C09: bundle/prove the cyclic Pauli relations, same-factor anticommutation, cross-factor commutation, and preservation under unitary interaction.
- E05/C10: identify the initial descriptor family exactly with the arbitrary named-coordinate embeddings from Stage 3.
- E07/C11/C15: define componentwise descriptor evolution by `U† A U`; named gate functions and calculations remain Stage 6.
- E08 remains the vector-level theorem from Stage 3; descriptor validity does not select a canonical basis in degenerate spaces.
- C04/C17: replace “complete description” with an explicit algebraic reconstruction/generation theorem and keep ontological language outside Lean.
- C12/C14 retain the Stage 3 pure fixed-reference theorem; descriptor completeness must not be inferred from one-state expectations.

## No-Cheating Checks

- Initial validity is proved from public embedded Pauli theorems, not stored as axioms or made definitionally true by erasing fields.
- Unitary evolution preservation explicitly consumes unitarity wherever multiplication/identity preservation is used.
- A family theorem quantifies every distinct label and every component pair; checking only `X` against `Z` is insufficient.
- Completeness evidence must reconstruct/generate arbitrary operators. Counting descriptors, listing their dimensions, or proving injectivity of a naming function is not reconstruction.
- Operator equality, equality up to simultaneous conjugation, and equality of fixed-reference predictions remain separate relations.
- Invalid-triple tests demonstrate that Hermiticity alone, squares alone, or one cyclic product alone does not establish the full descriptor API.
- No philosophical “real factual situation” or information-location claim appears as a Lean conclusion without a separate mathematical definition.
- Completed modules contain no proof holes, unsafe declarations, or project axioms; principal descriptor theorems enter `DeutschTests/Audit.lean`.

## Completion Requirements

- [x] Initial embedded descriptors satisfy the full documented same-factor Pauli and arbitrary cross-factor relations.
- [x] Arbitrary unitary simultaneous conjugation preserves descriptor and family validity.
- [x] A mathematically explicit completeness/reconstruction theorem compiles, or an exact formal obstruction is recorded with the strongest useful substitute.
- [x] Descriptor operator equality, conjugacy/gauge, and fixed-reference prediction equality are separate documented APIs/results.
- [x] Focused examples and negative validity tests cover one-, two-, and three-qubit families.
- [x] E01–E08 and surrounding descriptor/completeness claims receive updated conservative lifecycle dispositions.
- [x] Focused tests, full build, source/doc audits, integrity scan, axiom audit, and whitespace/worktree checks pass and are recorded.
- [x] Findings and evidence are folded into `0-plan.md`; Stage 6 is then the first incomplete stage.

## Stage Results

- `Deutsch/Descriptor/Basic.lean` defines `Axis`, raw triples, minimal `Descriptor.Valid`, all derived reverse products/anticommutators/unitarity, initial support/validity, family-wide cross commutation, chronology, and validity preservation under explicit unitarity.
- `Deutsch/Descriptor/Generation.lean` uses `Z`-derived coordinate projectors, unordered commuting products, exact bit-flip permutations, and projector sandwiches to prove `reconstructedMatrixUnit_eq_single`, membership of every matrix unit, and `initial_generates_operator_algebra`. The theorem covers arbitrary finite label types, including `Empty`, with no order or nonempty hypothesis.
- `DescriptorFamily.GeneratesOperatorAlgebra` is a public generic predicate. `GeneratesOperatorAlgebra.evolve` maps component sets through the unitary star-algebra automorphism and proves preservation; `evolved_initial_generates` packages the main instance.
- `Deutsch/Descriptor/PauliBasis.lean` defines four-letter Pauli words, exact dual coefficients, Kronecker-delta orthogonality, a two-sided analysis/synthesis equivalence, a genuine `Module.Basis`, initial/evolved reconstruction, and exact one-site bridges to initial/evolved descriptor components.
- `Deutsch/Descriptor/Comparison.lean` proves shared-unitary conjugacy and fixed-reference component-expectation equivalence are equivalence relations. It exposes exact-equality and reference-fixing implications without converses.
- `DeutschTests/Descriptor.lean` verifies one-/two-/three-label validity, every cross-axis relation, empty and three-qubit completeness/reconstruction, evolved validity/completeness, three distinct invalidity failures, empty/singleton boundaries, and a valid conjugate/reference-equivalent but operator-unequal family.
- Focused compilation `lake env lean DeutschTests/Descriptor.lean` exits 0 without output. `lake build Deutsch.Descriptor DeutschTests.Descriptor DeutschTests.Audit` succeeds with 3261 jobs, and the full `lake build` succeeds with 3268 jobs.
- `goal-1/check_lean_integrity.py` scans 24 Lean sources, requires 25 descriptor oracles and 20 Stage 5 public declarations, compiles 77 representative axiom reports, and accepts only `Classical.choice`, `Quot.sound`, and `propext`; it finds no proof holes, unsafe declarations, public umbrella tactic import, or project axioms.
- `goal-1/check_source_audit.py` passes after conservative E01–E08/D04/C04/C08–C18 lifecycle updates. `goal-1/check_doc_links.py` passes over 6 Markdown files and 38 local links.
- `git diff --check` exits 0, and the project trailing-whitespace scan exits 1 with no matches. The worktree remains intentionally unstaged/untracked from Stages 1–5; no unrelated user material was removed or staged.

## Resume Point

- Begin Stage 6 by inventorying equations (9)–(21), publicizing the already convention-tested one- and two-qubit gate matrices without duplicating Stage 2 definitions, and compiling arbitrary-register lifted gate actions through `embedQubit`/`embedAlong`.
- Keep exact matrix action, Heisenberg descriptor transformation, global phase, and basis-label permutation as separate statements while deriving every named gate identity.
