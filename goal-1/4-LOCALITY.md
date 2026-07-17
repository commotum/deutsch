# 4-LOCALITY

## Status

- Complete with evidence (2026-07-16)

## Current Facts

- Stages 1–3 were complete prerequisites; Stage 4 now publicly exports the finite supported-operation locality layer.
- `Deutsch.Register.IsSupportedOn s A` is an explicit witness that `A` is a reindexed `a ⊗ I` on selected labels `s`.
- `embedSubsystem_apply_ite` states the complete entry behavior of an arbitrary selected-subsystem embedding.
- `Deutsch.Locality.Basic` promotes the arbitrary disjoint selected-subsystem proof: its unique intermediate assignment is `fun q ↦ if q ∈ s then y q else x q`, and the result is lifted through semantic support witnesses.
- `Deutsch.Locality.Heisenberg` separates the nonunitary Gram residue, minimal isometry cancellation, physical unitary specialization, and arbitrary-ket expectation corollaries.
- Stage 3's singleton `embedQubit_commute_of_ne` is now a special case of the arbitrary-`Finset` theorem rather than the locality endpoint.

## Updated Assumptions

- Confirmed: disjoint-support commutation is purely algebraic and needs no unitarity or state hypothesis.
- Refined: fixing a commuting observable needs only `Uᴴ * U = 1`; `heisenberg_eq_gram_mul_of_commute` exposes `(Uᴴ * U) * A` without cancellation, and the public physical theorem takes unitary-group membership.
- Confirmed: expectation invariance is derived from operator equality for every ket, so no separability assumption enters.
- Confirmed boundary: the exact theorem concerns supported finite-register operations and supplies no continuum topology, circuit-limit error estimate, channel no-signalling theorem, or ontological conclusion.
- Confirmed by computation: `bellKet` is normalized and is formally refuted as a product vector before the locality expectation theorem is instantiated on it.

## Big Picture Objective

- Prove the paper's discrete locality core as arbitrary selected-subsystem commutation, unitary Heisenberg fixing, and arbitrary-state prediction invariance.
- Keep support, disjointness, unitarity, operator equality, expectation equality, and broad physical interpretation at distinct logical levels.

## Detailed Implementation Plan

1. Promote the compile-clean product-entry and disjoint-embedding commutation proof into a public `Deutsch.Locality` module.
2. Lift the embedding theorem through `IsSupportedOn` witnesses to arbitrary global operators supported on disjoint `Finset` subsystems.
3. Prove a nonunitary algebraic factorization of Heisenberg conjugation for commuting operators, then the exact fixed-observable theorem under unitary cancellation.
4. Provide bundled-unitary and arbitrary-ket expectation/state-action corollaries without product-state assumptions.
5. Test singleton, nonadjacent, multi-label, empty, overlap, unsupported, and nonunitary cases. Include a formally non-product two-qubit ket example.
6. Add `docs/locality.md`, source-ledger lifecycle locations, public-root imports, focused tests, and representative axiom reports.
7. Run the focused and full verification ladder, record exact evidence, and fold findings into `0-plan.md` before marking the stage complete.

Expected files include:

- `Deutsch/Locality.lean` and public-root imports
- `DeutschTests/Locality.lean` and audit additions
- `docs/locality.md`
- updates to `goal-1/check_lean_integrity.py`, `goal-1/1-SOURCE-AUDIT.md`, and `goal-1/0-plan.md`

## Paper Mapping

- E02/C16: prove arbitrary disjoint selected-subsystem commutation; Stage 3 already covers complete same-factor Pauli algebra and the singleton special case.
- E07/C15: show a supported unitary's Heisenberg conjugation has exact typed locality behavior.
- C02/C18: prove that a supported unitary on one subsystem fixes a disjoint observable as an operator, hence preserves its expectation for every state, including entangled states.
- E24 is only structurally supported here; its named untouched EPR descriptors remain a Stage 8 circuit application.
- C19 remains partial/unresolved: no continuum or arbitrary-spatial-dynamics extrapolation follows from the finite supported-gate theorem alone.
- C01/C06/C60 remain interpretative unless restated through the explicit support theorem; Stage 4 does not prove an ontological definition of locality.

## No-Cheating Checks

- Derive commutation entrywise from `embedSubsystem`; do not postulate it as a support axiom or prove only singleton Pauli cases.
- State and test that commutation itself needs only disjoint support, while fixed Heisenberg evolution needs unitarity.
- Prove operator equality before deriving expectation equality; do not infer an operator theorem from one state's scalar prediction.
- Include an overlapping-support counterexample and a nonunitary counterexample to show the hypotheses are operational.
- Prove the chosen Bell-like ket is outside the defined product-vector class before using it as the entangled regression example.
- Do not call syntax, parameter absence, or one expectation value a complete subsystem-information theorem.
- Completed modules contain no proof holes, unsafe declarations, or project axioms; principal locality theorems enter `DeutschTests/Audit.lean`.

## Completion Requirements

- [x] Arbitrary disjoint selected-subsystem embeddings commute, and `IsSupportedOn` exposes the result for arbitrary supported global operators.
- [x] A unitary supported on one subsystem fixes every observable supported on a disjoint subsystem under `U† A U`.
- [x] Arbitrary-ket expectation invariance follows from operator equality with no separability hypothesis.
- [x] A formally normalized, non-product two-qubit example instantiates the locality theorem.
- [x] Negative tests cover overlap/support and nonunitarity; they do not merely fail by type mismatch.
- [x] Documentation states the exact finite supported-gate scope and separates it from no-signalling channels, continuum dynamics, information location, and ontology.
- [x] Focused tests, full build, source/doc audits, integrity scan, axiom audit, and whitespace/worktree checks pass and are recorded.
- [x] Findings and exact evidence are folded into `0-plan.md`; Stage 5 is then the first incomplete stage.

## Stage Results

- `Deutsch/Locality/Basic.lean` proves `embedSubsystem_mul_embedSubsystem_apply_of_disjoint` entrywise, then `embedSubsystem_commute_of_disjoint` for arbitrary selected finite sets and `supportedOperators_commute_of_disjoint` for global operators carrying exact support witnesses.
- `Deutsch/Locality/Heisenberg.lean` proves the strongest nearby nonunitary formula `heisenberg U A = (Uᴴ * U) * A` from commutation alone. It then supplies minimal isometry cancellation, support-aware isometry and unitary forms, bundled `evolve` locality, and both Heisenberg- and Schrödinger-form expectation invariance for every ket.
- `DeutschTests/Locality.lean` instantiates arbitrary matrices on nonadjacent multi-label supports `{0,2}` and `{1,4}` in a five-qubit register, semantic support commutation, empty support, and singleton remote-observable fixing.
- The same test file defines `bellKet = (|00⟩+|11⟩)/√2`, proves its four coordinates, norm one, the determinant identity for every product vector, and `bellKet_not_product`, then proves both locality expectation forms on that ket.
- Negative regressions prove same-coordinate `X` and `Z` do not commute, compute `X†ZX=-Z`, package overlap plus failed invariance, refute a fabricated remote support witness, and show a zero nonunitary matrix with disjoint support does not fix a nonzero remote `Z`.
- `docs/locality.md` documents the proof hierarchy and exact scope. It explicitly excludes channel no-signalling, density/POVM semantics, information location, continuum extrapolation, and ontology. The register/representation/convention docs and README link the new layer.
- The source ledger conservatively records Stage 4 evidence for E02/E07/E24 and C01/C02/C06/C15/C16/C18/C19/C60. Descriptor/EPR applications, channel/density semantics, and general dynamics remain routed downstream.
- Focused checks passed without warnings: `lake env lean DeutschTests/Locality.lean` exited 0, and `lake build Deutsch.Locality DeutschTests.Locality` succeeded with 3095 jobs. The full `lake build` succeeded with 3259 jobs.
- `python3 -B goal-1/check_lean_integrity.py` passed over 18 Lean sources with no forbidden constructs; it required 37 foundation, 18 register, and 17 locality regression oracles plus 26 Stage 3 and 9 Stage 4 public declarations. All 57 representative axiom reports use only `Classical.choice`, `Quot.sound`, and `propext`.
- `python3 -B goal-1/check_source_audit.py` passed exact ledger coverage and the equation-(45) diagnostic. `python3 -B goal-1/check_doc_links.py` passed 5 Markdown files and 28 repository-local links.
- `git diff --check` produced no findings. The targeted trailing-whitespace scan over all public/test Lean, docs, stage files, checkers, and toolchain files produced no matches; `git status --short` was inspected without deleting or staging any user material.

## Resume Point

- Stage 5 is the first incomplete stage. Define typed descriptor triples from global embedded Pauli operators and bundle exactly the validity relations actually needed.
- Prove that unitary Heisenberg conjugation preserves descriptor Hermiticity, squares, signed Pauli products, and cross-factor commutation by reusing the Stage 3/4 algebra rather than recomputing entries.
- Challenge the paper's “complete description” wording with an explicit algebra-generation/reconstruction statement and a separately documented fixed-reference/gauge analysis; do not turn locality into an information-location theorem by syntax.
