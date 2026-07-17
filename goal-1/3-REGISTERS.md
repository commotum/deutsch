# 3-REGISTERS

## Status

- Complete with evidence (2026-07-16)

## Current Facts

- Stages 1 and 2 were complete prerequisites; this stage now adds the public `Deutsch.Register` layer under pinned Lean/mathlib `v4.32.0`.
- Stage 2 fixes paper logical bit `1` as raw index `0`, paper logical bit `0` as raw index `1`, first tensor factor on the left/product-first coordinate, and Heisenberg evolution as `U† A U`.
- `Deutsch.Register.Basic` defines arbitrary finite named register bases, coordinate vectors, Hilbert kets, matrices, the matrix/endomorphism adjoint bridge, and generic Heisenberg conjugation.
- `Deutsch.Register.Embedding` implements selected-`Finset`, singleton-qubit, and ordered-injection embeddings as proved algebra homomorphisms. `IsSupportedOn` is an explicit image witness, not a syntactic label.
- `Deutsch.Register.Pauli` publicly proves the local and embedded Pauli algebra, paper-bit projector algebra, and arbitrary one-qubit commutation on distinct named coordinates.
- `Deutsch.Register.State` defines normalized pure states and expectations, proves unitary norm preservation, constructs a unitary preparation for every normalized finite-register ket, proves fixed-reference prediction equivalence for every operator, and proves qualified eigenvector transport.
- General density/effect/POVM semantics, descriptor validity, named gates, and arbitrary disjoint-`Finset` locality remain deliberately downstream.

## Updated Assumptions

- Confirmed: a register is indexed by an arbitrary finite qubit-label type `Q`, with basis `Q → Fin 2`; `Fin n` is only a specialization.
- Confirmed: selected subsystems are `Finset Q` values with typed selected/complement basis assignments. Ordered placement additionally takes an injection `K ↪ Q`, because a range `Finset` alone forgets input-factor order.
- Confirmed: subsystem, single-qubit, and ordered embeddings are bundled algebra homomorphisms; identity, linearity, multiplication, injectivity, adjoint, Hermiticity, and unitarity are theorems rather than fields postulated by callers.
- Confirmed: exact image support is sufficient for Stage 4. The compile-clean `/tmp/embed_disjoint_probe.lean` derives arbitrary disjoint selected-subsystem commutation from `embedSubsystem_apply_ite` using a unique intermediate assignment.
- Confirmed: arbitrary pure-state standardization is noncomputable but theorem-level: singleton orthonormal extension produces a unitary taking the paper-zero reference ket to any normalized ket.
- Retained boundary: this construction says nothing false about mixed states; density/effect probabilities and the mixed-state correction remain Stage 7.
- Confirmed: `heisenberg_eigenvector` transports a specified vector/eigenvalue pair with explicit unitarity and makes no canonical choice in a degenerate eigenspace.

## Big Picture Objective

- Export a reusable finite-qubit register algebra with arbitrary selected-subsystem embeddings, typed support witnesses, unitary Heisenberg evolution, pure expectations, and explicit one-/two-/three-qubit regression examples.
- Connect the general API back to Stage 2's bit and tensor conventions without silently identifying different coordinate types.

## Detailed Implementation Plan

1. Define finite register basis assignments, state vectors, square complex operators, reference paper-zero assignment/ket, dimensions, Hermitian and unitary predicates, and pure expectation.
2. Define selected- and complement-basis types for a `Finset ι` and an explicit splitting equivalence.
3. Define subsystem embedding by reindexing `A ⊗ I`; prove zero/add/scalar/identity/composition, adjoint, Hermiticity, and unitarity preservation.
4. Define single-qubit embedding as a specialization with a direct raw-coordinate behavior theorem for every basis assignment.
5. Define `SupportedOn A s` by an explicit local-operator witness; prove embeddings, products, adjoints, and supported Heisenberg evolution remain supported on the same selected set.
6. Define register Heisenberg evolution `U† A U`; prove identity, chronology/composition, adjoint/Hermiticity preservation, and unitary specialization.
7. Define normalized pure vectors and expectation; prove unitary norm preservation and the fixed-reference prediction equivalence for `Ψ = U|0…0⟩`.
8. Prove a qualified eigenvector transport theorem: if `A v = λv` and `U` is unitary, then `U†v` is a `λ` eigenvector of `U†AU`.
9. Add one-, two-, and three-qubit executable examples for dimension, paper-zero basis, selected-factor action, a nonadjacent three-qubit factor, and swapped-factor negative discrimination.
10. Extend source-ledger lifecycle locations, integrity/axiom checks, public documentation, and the full verification record; fold conclusions into `0-plan.md` only after every check passes.

Expected files include:

- `Deutsch/Register.lean` and public-root imports
- `DeutschTests/Register.lean` and axiom-audit additions
- `docs/registers.md`
- updates to `goal-1/check_lean_integrity.py`, `goal-1/1-SOURCE-AUDIT.md`, and `goal-1/0-plan.md`

## Paper Mapping

- E01/D04 descriptor bundling remains Stage 5, but Stage 3 supplies its global operator and factor identity types.
- E02 supplies cross-factor algebra obligations; Stage 3 establishes embedding laws and Stage 4 proves the full disjoint-support theorem.
- E04/D05 reuse the Stage 2 bit/projector oracle; stable measurement semantics remain Stage 7.
- E05/C10 route to selected-subsystem and single-qubit embeddings plus explicit basis behavior.
- E06/C14 route here only for pure vector expectation and operator prediction; complete measurement-family semantics remain Stage 7.
- E07/C11/C15 route to typed Heisenberg evolution, chronology, and supported embedding/conjugation laws; named gate calculations remain Stage 6.
- E08 routes to a qualified eigenvector-transport theorem, not a canonical eigenbasis choice.
- U01/C12 route to pure fixed-reference prediction equivalence with explicit `Ψ = U|0…0⟩`; the mixed-state source wording stays corrected/deferred.
- C16's disjoint same-step commutation is Stage 4, using the support and embedding API created here.

## No-Cheating Checks

- Embedding laws must be derived from reindexing and Kronecker multiplication, not bundled as unproved assumptions.
- Basis-action examples must calculate all relevant finite cases; one convenient entry is not evidence for arbitrary-factor behavior.
- Single-qubit and selected-subsystem support must carry the selected labels in their types or witnesses; theorem names alone do not establish locality.
- Unitarity is explicit wherever inverse cancellation is used. Algebraic `U† A U` remains definable for arbitrary `U` but is not called physical evolution without that hypothesis.
- Pure fixed-reference equivalence does not justify the paper's mixed-state sentence. No rank/spectrum-changing unitary claim is admitted.
- Eigenvector transport states a vector/eigenvalue theorem and does not manufacture a canonical basis through degeneracy.
- Coordinate bridges between function-valued assignments, product indices, and any flattened `Fin (2^n)` index are named equivalences with executable tests.
- Completed modules contain no proof holes, unsafe declarations, or project axioms; principal Stage 3 theorems enter `DeutschTests/Audit.lean`.

## Completion Requirements

- [x] Public finite-register basis, vector, operator, adjoint/unitary/Hermitian, expectation, and Heisenberg APIs compile.
- [x] Arbitrary selected-subsystem and single-qubit embeddings compile with identity, composition, adjoint, Hermiticity, and unitarity laws.
- [x] A semantic support predicate/witness is sufficient for Stage 4 and is closed under the same-subsystem operations needed there.
- [x] Pure reference-state prediction equivalence and qualified eigenvector transport compile with explicit hypotheses.
- [x] One-, two-, and three-qubit examples pin dimensions, paper-zero labels, selected-factor behavior, and a nonadjacent factor.
- [x] Documentation distinguishes coordinate equality, operator equality, pure expectation equality, and deferred measurement/distribution claims.
- [x] Focused tests, full build, source coverage, documentation links, integrity scan, axiom audit, and whitespace/worktree checks pass and are recorded.
- [x] Findings and exact evidence are folded into `0-plan.md`; Stage 4 is then the first incomplete stage.

## Stage Results

- Public modules are `Deutsch/Register/Basic.lean`, `Embedding.lean`, `Pauli.lean`, and `State.lean`, re-exported by `Deutsch/Register.lean` and the project root.
- `Basis Q`, `Ket Q`, and `Operator Q` separate computational labels, Hilbert vectors, and matrices. `card_basis` proves dimension `2^|Q|`. `matrixEndEquiv` and `matrixEndEquiv_conjTranspose` connect matrices to Hilbert endomorphisms and adjoints without changing the executable carrier.
- `embedSubsystemAlgHom` is reindexed `A ⊗ I`; `embedSubsystem_apply_ite` gives its complete entry behavior. Its zero/one/add/scalar/multiplication, adjoint, injectivity, Hermiticity, unitarity, and Heisenberg laws all compile.
- `embedAlongAlgHom (p : K ↪ Q)` preserves domain ordering explicitly. Tests use two injections with the same ambient range but opposite order and prove the resulting nonsymmetric placements differ.
- `IsSupportedOn s A := ∃ a, A = embedSubsystem s a` is closed under zero, one, addition, scalar multiplication, multiplication, adjoint, and same-support Heisenberg conjugation. A separate compiled probe proves the intended arbitrary-disjoint commutation route; its theorem is reserved for Stage 4.
- `xAt`, `yAt`, and `zAt` satisfy all three squares, all six signed Pauli products, Hermiticity, unitarity, and anticommutation. `embedQubit_commute_of_ne` proves arbitrary one-qubit operators commute on distinct named coordinates.
- `paperBitOneProjectorAt` and `paperBitZeroProjectorAt` implement the paper's reversed logical labels. Their formula, Hermiticity, idempotence, complementarity, two-sided orthogonality, and `Z=±1` sector laws compile as operator equalities.
- `referenceKet Q` is the all-raw-`1` assignment because paper bit zero is raw index `1`. `PureState.exists_fixed_reference_representation` combines exact unitary preparation with expectation equality for every matrix operator. No density or mixed-state claim is inferred.
- `DeutschTests/Register.lean` checks 1/2/3-qubit dimensions, paper-zero labels, exact left/right two-factor bridges, exhaustive outer-coordinate three-qubit entries, nonadjacent commutation, swapped ordered placements, support closure, nonunitary norm/identity failures, and eigenvector transport.
- `docs/registers.md` documents the API and explicitly separates coordinate equality, operator equality, one-state expectation equality, all-state equality, and joint-distribution equality. `docs/conventions.md`, `docs/representation.md`, and `README.md` link the new layer and preserve downstream boundaries.
- The source ledger records conservative `Partial` Stage 3 dispositions for E02 and E04–E08, U01, D01/D05–D07, and C10–C16; arbitrary selected-subsystem locality, descriptors, measurements, and mixed states remain routed.
- Focused checks passed without warnings: `lake env lean DeutschTests/Register.lean`; `lake build Deutsch.Register.Embedding DeutschTests.Register` (3092 jobs); and `lake build` (3255 jobs).
- `python3 -B goal-1/check_lean_integrity.py` passed over 14 Lean sources with no forbidden constructs, 37 foundation oracles, 18 register verification oracles, 26 required Stage 3 public declarations, and 48 axiom reports. The only observed axioms are `Classical.choice`, `Quot.sound`, and `propext`.
- `python3 -B goal-1/check_source_audit.py` passed exact source/ledger coverage and the equation-(45) diagnostics. `python3 -B goal-1/check_doc_links.py` passed 4 Markdown files and 18 repository-local links.
- `git diff --check` produced no findings. A targeted trailing-whitespace scan over all project Lean, test, documentation, stage, checker, and toolchain files produced no matches. `git status --short` was inspected; all pre-existing source/scaffold material was preserved and the stage's intentionally unstaged files remain visible.

## Resume Point

- Stage 4 is the first incomplete stage. Promote the compile-clean general disjoint-embedding proof from `/tmp/embed_disjoint_probe.lean` into `Deutsch.Locality` (or a narrowly shared register lemma) and expose it through `IsSupportedOn` witnesses.
- Prove that conjugation by a unitary supported on `s` fixes every operator supported on disjoint `t`; keep the stronger algebraic and physical-unitary statements distinct.
- Add arbitrary-state expectation corollaries only after proving operator equality, plus empty/support-overlap and nonunitary negative tests. Do not broaden this exact gate-support theorem into an unsupported continuum-dynamics claim.
