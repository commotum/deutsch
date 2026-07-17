# 2-FOUNDATIONS

## Status

- Complete with evidence on 2026-07-16

## Current Facts

- Stage 1 is complete with an exact source/ledger coverage check and remains the authoritative paper-claim map.
- The repository now pins Lean `v4.32.0` and mathlib `v4.32.0`; the manifest resolves mathlib to commit `81a5d257c8e410db227a6665ed08f64fea08e997`.
- Repository-local `lean --version` reports Lean commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`; Lake reports `5.0.0-src+8c9756b`.
- Direct checks of the official release tags on 2026-07-16 established `v4.32.0` as the stable Lean/mathlib pair; `v4.33.0-rc1` was a prerelease. This corrected an initially stale search-index result for `v4.30.0`.
- The public Stage 2 representation is a concrete matrix convention kernel. A compiled abstract finite-Hilbert endomorphism layer is selected for future basis-independent locality/measurement semantics but remains verification-only until its public invariants are complete.
- Compiled examples pin the paper's reversed bit labels, raw/product basis order, left/right tensor factors, `U† A U`, CNOT target/control, all four CNOT basis actions, all six CNOT Pauli conjugations, `R_x(π/2)` signs, and the Bell/inverse chronology.
- General Born-weight reality and `[0,1]` bounds, arbitrary selected-factor embeddings, multi-factor association, and an explicit matrix/endomorphism coordinate bridge remain later-stage obligations rather than assumptions.

## Updated Assumptions

- Concrete `Matrix (Fin n) (Fin n) ℂ` values are the executable convention oracle and initial finite circuit-calculation layer.
- The selected long-term architecture is hybrid: abstract `Module.End ℂ H` supports concise basis-independent locality, while concrete matrices retain transparent finite calculation. Bridges must be explicit.
- Mixed states are positive trace-one operators, not vectors. No unitary-purification claim is admitted; the rank/spectrum obstruction is documented for later formal proof.
- Mathlib's `Matrix.trace` is unnormalized. Density invariants therefore require trace exactly one, and measurement completeness is an explicit finite sum of effects equal to the identity.
- Kronecker order is fixed by all-basis executable examples: the first product coordinate is the first/left factor, and raw pairs flatten as `00,01,10,11`.
- Stage 3 remains responsible for the public register and arbitrary-subsystem embedding APIs; Stage 7 owns stable density/effect/channel types and the missing general Born bounds.

## Big Picture Objective

- Establish a reproducible Lean 4/mathlib project, compile the relevant concrete and abstract APIs, select a representation with evidence, and make every global convention executable.
- Leave a baseline build, forbidden-token scan, and axiom-audit mechanism that later stages can extend.

## Detailed Implementation Plan

1. Added `lean-toolchain`, `lakefile.toml`, and a resolved `lake-manifest.json` pinning Lean/mathlib `v4.32.0`.
2. Created separate `Deutsch` public and `DeutschTests` verification targets; the integrity checker prevents public imports of `Mathlib.Tactic`.
3. Compiled concrete probes for multiplication, adjoint/Hermiticity, unitarity, trace, positivity, Kronecker products, basis vectors, mixed density matrices, effects, and finite measurement normalization.
4. Compiled abstract probes for finite complex endomorphisms, adjoints, tensor embeddings, trace-one densities, effects, finite measurement normalization, and binary locality.
5. Wrote `docs/conventions.md` and the complete Stage 2 executable convention suite.
6. Wrote `docs/representation.md`, including the decision, rejected alternatives, mixed-state policy, missing proofs, and migration risks.
7. Added `goal-1/check_lean_integrity.py`, `DeutschTests/Audit.lean`, and `goal-1/check_doc_links.py`; ran all focused, full, integrity, source, axiom, link, and worktree checks.

Expected files include:

- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`
- `Deutsch.lean`, `Deutsch/Foundations/*.lean`
- `DeutschTests.lean`, `DeutschTests/Foundations/*.lean`, `DeutschTests/Audit.lean`
- `docs/conventions.md`, `goal-1/check_lean_integrity.py`

## Paper Mapping

- Equations (3)–(5) supply the Pauli, bit-projector, and initial tensor-factor convention obligations.
- Equations (7)–(8) supply the adjoint/evolution and circuit-chronology checks.
- Equations (15)–(21) and Fig. 1 supply CNOT control/target, rotation, Hadamard, and Bell convention checks; their general proofs remain Stage 6 work.
- Equations (22), (28), (29), and (36) supply phase, outcome-label, and Bloch-vector cross-check values, but EPR/teleportation proofs remain in Stages 8–9.
- Stage 2 will update intended imports/declaration locations in the source ledger but will not mark later paper equations proved merely because finite examples compute.

## No-Cheating Checks

- The mathlib dependency must be pinned by both release revision and resolved manifest commit.
- Convention examples must evaluate explicit matrices or all relevant finite basis cases; restating a desired equality as a hypothesis does not count.
- CNOT receives both a four-case basis test and six-generator conjugation tests, preventing one mistaken convention from validating the other by circular definition.
- Bell and inverse are defined by named composition order and tested in both directions.
- Concrete and abstract representation conclusions require compiling probes; API inspection alone is insufficient.
- No completed project module may contain `sorry`, `admit`, `by_contra!`, an unsafe declaration, or a project `axiom`.
- `#print axioms` output for principal Stage 2 declarations must be recorded and checked for `sorryAx` or project axioms.

## Completion Requirements

- [x] Pinned Lean/toolchain/dependency files exist and resolve to the documented releases/commits.
- [x] A minimal and full default project build succeeds with documented commands.
- [x] Concrete and abstract representation probes compile, and the representation decision records evidence, rejected alternatives, and migration risks.
- [x] Every Stage 2 global algebraic/circuit convention is documented and covered by an executable Lean example.
- [x] Public/probe/test module boundaries and namespace policy are documented.
- [x] A baseline forbidden-token checker and axiom-audit module run successfully.
- [x] Stage 1 map routes source items to selected modules without claiming broader paper identities proved by finite oracles.
- [x] Focused build, full build, convention checks, integrity scan, axiom audit, and diff/whitespace/status checks are recorded.
- [x] Findings and exact evidence are folded into `0-plan.md`.

## Stage Results

- `lean --version` reports Lean `4.32.0`, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`; `lake --version` reports `5.0.0-src+8c9756b`.
- The three focused commands for `Concrete.lean`, `Abstract.lean`, and `MatrixSemantics.lean` each exited 0 with no output or warnings.
- `lake build` completed successfully with `3249` jobs. It built both default targets and emitted the representative axiom report.
- The rotation oracle initially tested the opposite mnemonic signs. Lean reduced two entries to `False`; direct calculation established the project-consistent result `Y ↦ -Z`, `Z ↦ Y` for `(I-iX)/√2` under `U†AU`. The corrected named theorems compile.
- Early smoke builds also caught imports placed after module comments and noncomputable complex inverses. Imports now precede module documentation and the concrete public layer uses an explicit noncomputable section.
- `python3 -B goal-1/check_lean_integrity.py` reports 8 Lean sources, no forbidden constructs, the exact pins, 37 required convention/API oracles, 22 representative axiom reports, and only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake env lean DeutschTests/Audit.lean` prints exactly those same three foundational axioms for every representative declaration; no `sorryAx` or project axiom appears.
- `python3 -B goal-1/check_source_audit.py` still reports exact E01–E46, U01–U03, F01–F03, D01–D11, C01–C66, I01–I10, and LC01–LC66 coverage, plus the equation-(45) counterexample and corrected truth-table pass. The checker now recognizes the distinct `Oracle verified` lifecycle without allowing a paper equation to be marked `Proved`.
- `python3 -B goal-1/check_doc_links.py` reports 3 Markdown files and 9 valid repository-local links.
- The representation probes establish finite-family normalization but deliberately do not claim general Born-weight reality/nonnegativity/bounds. The exact gap and likely square-root/cyclic-trace route are recorded in `docs/representation.md`.
- Final `git diff --check` exited 0. All 18 untracked files passed `git diff --no-index --check /dev/null <file>` with the expected difference-only exit 1 and empty diagnostics. The explicit trailing-whitespace scan exited 1 with no matches.
- Final worktree status after the plan fold was:

  ```text
  ## master...origin/master
   M .gitignore
   M README.md
   M goal-1/0-plan.md
  ?? Deutsch.lean
  ?? Deutsch/
  ?? DeutschTests.lean
  ?? DeutschTests/
  ?? docs/
  ?? goal-1/1-SOURCE-AUDIT.md
  ?? goal-1/2-FOUNDATIONS.md
  ?? goal-1/check_doc_links.py
  ?? goal-1/check_lean_integrity.py
  ?? goal-1/check_source_audit.py
  ?? lake-manifest.json
  ?? lakefile.toml
  ?? lean-toolchain
  ```

  `.lake/` is ignored; no user file was deleted, staged, or committed.

## Resume Point

- Stage 3 (`3-REGISTERS`) is the first incomplete stage. Reinspect the worktree, create `goal-1/3-REGISTERS.md`, and use the hybrid decision to design the smallest public register/operator/embedding API.
- Preserve every Stage 2 convention oracle as a regression test. The first Stage 3 proof should connect a selected-factor embedding to explicit one-, two-, and three-qubit basis behavior without changing the raw/paper bit mapping.
- Do not promote the verification-only density/effect wrappers yet. Stage 3 should expose register algebra and unitary Heisenberg evolution; Stage 7 remains responsible for stable measurement semantics and general Born bounds.
