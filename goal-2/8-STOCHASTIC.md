# 8-STOCHASTIC

## Status

- Complete.

## Current Facts

- `Deutsch.Bell.Finite` proves the independent three-setting inequality for a normalized
  nonnegative weight on deterministic two-party response tables.
- `Deutsch.Bell.Contradiction` connects that table model to the finite EPR agreement family and
  derives both the support-explicit and observable-probability contradictions.
- The direct Equations (42)--(46) route in `Deutsch.Bell.Moments` is separate and remains the
  paper-facing proof.
- What is not yet compiled is the conventional bridge from finite, setting-independent,
  factorizable stochastic response kernels to a distribution over deterministic local response
  tables.
- The refinement must construct the joint response table distribution from the local kernels.  It
  may not assume a pre-existing counterfactual table or identify zero-probability events by fiat.

## Updated Assumptions

- Because the measurement family used for the contradiction has exactly three settings and two
  outcomes, an explicit finite product distribution over complete Alice and Bob response tables is
  sufficient; no measure-theoretic or continuum-setting machinery is required.
- Locality and setting independence can be visible in the types: one hidden-variable weight has no
  setting argument, Alice's kernel receives only Alice's setting, Bob's only Bob's setting, and the
  joint response is their product.
- Summing the product-table refinement over all unobserved table coordinates should preserve every
  local marginal and every Alice--Bob joint outcome probability.
- Agreement-probability preservation then lets the existing independently proved deterministic
  contradiction apply without adding a counterfactual-assignment premise.

## Big Picture Objective

- Give a constructive, probability-preserving reduction from a conventional finite factorizable
  stochastic local model to the existing deterministic response-table model, then exclude any such
  model reproducing the three-setting EPR agreement table.

## Detailed Implementation Plan

- Add a neutral `Deutsch.Bell.Stochastic` module defining:
  - normalized nonnegative response kernels on `Bool`;
  - a finite hidden-variable model with a normalized nonnegative setting-independent weight;
  - local Alice and Bob kernels whose arguments expose parameter independence;
  - factorizable joint and agreement probabilities.
- Define the conditional probability of every complete deterministic local response table as the
  product of all six local response probabilities.
- Sum over the hidden variable to obtain an explicit refined weight on `LocalAssignment`.
- Prove:
  - conditional and refined table weights are nonnegative;
  - each conditional table distribution and the refined distribution normalize to one;
  - Alice and Bob one-party marginals are preserved;
  - every pairwise joint outcome probability is preserved;
  - every pairwise agreement probability is preserved.
- Package reproduction of the three-setting EPR agreement family and derive the final stochastic
  contradiction through `epr_three_settings_refute_normalized_local_model`.
- Export the module from `Deutsch.Bell` and add focused compile tests and axiom targets.
- Update Bell/reuse documentation only after the theorem contract compiles.

## No-Cheating Checks

- Inspect the refinement definition and test a concrete non-deterministic fair-response model: its
  table distribution must be normalized and its pairwise joint probability must be `1/4`, showing
  the construction is not a deterministic fixture in disguise.
- Require compiled preservation theorems for both outcome-level joint probabilities and
  agreement, not merely a final contradiction theorem.
- Confirm the stochastic contradiction's premises contain no response table or perfect-support
  hypothesis; those must be derived from the kernel model and reproduced equal-setting
  probability.
- Keep `Deutsch.Bell.Moments` independent of the refinement so the direct Equation-(42)--(46)
  argument and the stochastic reduction remain separately auditable.
- Audit every new declaration for proof holes, project axioms, unsafe/opaque escapes, and
  unexpected foundational dependencies.

## Completion Requirements

- The stochastic-to-deterministic refinement is explicit, constructive, nonnegative, normalized,
  and preserves all one- and two-party probabilities used by the Bell result.
- Model structure and final theorem visibly state finite hidden-variable normalization,
  nonnegativity, setting-independent weighting, local response normalization/nonnegativity, and
  factorization.
- No counterfactual joint assignment is an input to the stochastic contradiction.
- Focused stochastic wrappers include at least one genuinely non-deterministic numerical witness.
- `Deutsch`, `DeutschTests`, the full four-target build, both axiom audits, integrity/boundary/source
  checks, documentation checks, whitespace, and `git diff --check` pass.

## Stage Results

- Added `Deutsch.Bell.Stochastic` and exported it from `Deutsch.Bell`.
- `BoolResponseKernel` packages a nonnegative normalized Boolean response law.
  `StochasticLocalModel Ω` packages a finite normalized nonnegative hidden weight with no setting
  argument and separate Alice/Bob kernels receiving only their own local setting.
- `stochasticJointOutcomeProbability_factorization` exposes the conditional product law directly.
  The joint model is not inferred from a response table.
- For each hidden value, `conditionalTableWeight` assigns a complete six-response table the
  product of its six local response probabilities. The implementation proves this distribution
  nonnegative and normalized, then averages it into the explicit `refinedLocalWeight`.
- The refinement proves, independently and for arbitrary settings/outcomes:
  - Alice one-party marginal preservation;
  - Bob one-party marginal preservation;
  - every joint-outcome probability preservation; and
  - every agreement-probability preservation.
- `refinedLocalWeight_reproduces_three_setting_agreements` transfers the complete `3 × 3`
  agreement table, including equal-setting probability one, into the existing deterministic-table
  contract. The final `epr_three_settings_refute_stochastic_local_model` invokes
  `epr_three_settings_refute_normalized_local_model`; neither a response-table weight nor a
  perfect-support premise appears in its signature.
- Added 18 focused stochastic wrappers and four concrete axiom-audited witness targets.
  `fairResponseKernel` assigns both Boolean outcomes probability `1/2`; its refined distribution
  normalizes and a specified cross-party joint outcome has probability `1/4`.
- Updated Bell, reuse, and project-report documentation to state the finite factorizable scope,
  explain that cross-setting independence is a freely constructed coupling of unobserved
  coordinates, and keep this reduction separate from the direct Equations (42)--(46) proof.
- Strengthened `goal-1/check_lean_integrity.py` to require the Stochastic module/import edge,
  all 35 public declarations, 18 focused wrappers, 17 production axiom targets, and four witness
  axiom targets.
- Verification completed successfully:
  - `lake build Deutsch.Bell.Stochastic DeutschTests.Bell` built 2725 jobs;
  - `lake build Deutsch.Bell.Stochastic Deutsch.Bell Deutsch` built 2770 jobs;
  - `lake build DeutschTests` built 3326 jobs;
  - `lake build Deutsch DeutschTests DeutschErrata DeutschErrataTests` built 3338 jobs;
  - `python3 goal-1/check_lean_integrity.py` scanned 88 Lean sources and 524 axiom reports;
  - `python3 goal-1/check_source_audit.py`, `python3 goal-1/check_doc_links.py`, and
    `python3 goal-2/check_errata_boundary.py` all passed;
  - the production and test axiom reports contain only `Classical.choice`, `Quot.sound`, and
    `propext`; and
  - forbidden-token scans and `git diff --check` passed.
