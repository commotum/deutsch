# 4-BELL-MOMENTS

## Status

- Complete.

## Current Facts

- The canonical Equations (40) and (41) give one-site means `1/2` and the joint paper-one moment
  `(1/2) cos²((theta - phi)/2)`.
- `Deutsch.EPR.RecordStatistics` now proves those values directly on Figure 2's four-wire record
  state and bridges them to the independently computed two-wire pair density.
- `Deutsch.Bell.Quantum` already fixes the three settings `0`, `2*pi/3`, and `4*pi/3` and proves the
  required trigonometric special values.
- `Deutsch.Bell.Finite` and `Deutsch.Bell.Contradiction` contain an independent agreement-counting
  proof. They do not formalize the displayed expectation chain in Equations (42)--(46).
- Equation (43) follows from a zero mean square only on positive-weight support. A finite model may
  contain zero-weight samples, and no result should constrain their assigned values.
- The canonical Equation (45) uses the actual Boolean complement
  `1 - (a(theta1) or a(theta2))`, so its two summands form a genuine partition.

## Updated Assumptions

- A finite type with a nonnegative normalized real weight is sufficient for the displayed
  expectation argument.
- The source's stochastic Boolean variables can be represented by separate response functions
  `alice sample setting` and `bob sample setting`; their types make the absence of remote-setting
  dependence explicit at this deterministic-response level.
- A production moment-reproduction structure can state exactly the one-site and joint moments
  supplied by Equations (40) and (41), without assuming any later equation.
- The direct chain should prove every equality and inequality in Equation (46) pointwise or by
  finite expectation monotonicity, not appeal to the existing pigeonhole theorem.

## Big Picture Objective

- Formalize Equations (42)--(46) as a literal finite weighted-expectation derivation and derive the
  contradiction independently of the existing agreement-counting Bell proof.

## Detailed Implementation Plan

- Add `Deutsch/Bell/Moments.lean` with:
  - finite normalized nonnegative weights and real weighted expectation;
  - zero-one indicators for Boolean responses;
  - disjunction and its genuine complementary event;
  - a three-setting EPR moment-reproduction contract;
  - Equation (42)'s zero mean square;
  - Equation (43)'s equality on positive-weight support;
  - Equation (44)'s counterfactual Alice--Alice moment;
  - Equation (45)'s pointwise and averaged complementary partitions; and
  - each equality, inequality, numerical reduction, and final contradiction in Equation (46).
- Export the module through `Deutsch.Bell`, add focused tests alongside the independent
  pigeonhole route, and register all principal declarations in the integrity and axiom audits.
- Document the two independent proof routes and their exact assumptions.

## No-Cheating Checks

- Do not import or invoke the agreement/pigeonhole theorem in the direct moment derivation.
- Do not assume Equations (42)--(46), the value `3/8`, or the contradiction as a premise.
- Derive Equation (43) only for samples whose weight is strictly positive.
- Represent Equation (45)'s second event as Boolean negation of the disjunction and prove the
  partition by cases.
- Prove triple-product nonnegativity from zero-one indicators and nonnegative weights.
- Keep this deterministic common-space contract distinct from the Stage 8 construction that will
  derive it from a factorizable stochastic local model.

## Completion Requirements

- Neutral production theorems match each of Equations (42)--(46).
- The Equation (46) theorem exposes the full chain, including `1/2 <= 3/8 - E[triple] <= 3/8`,
  before deriving `False`.
- The direct contradiction has no dependency on `Deutsch.Bell.Finite` or the independent
  pigeonhole theorem.
- Focused tests exercise both proof routes and the zero-weight support boundary.
- The Bell umbrella, full public/test build, integrity audit, axiom audit, documentation links,
  whitespace scan, and `git diff --check` pass.

## Stage Results

- Added and exported `Deutsch/Bell/Moments.lean`. Its assumptions are exactly a finite sample type,
  a pointwise nonnegative normalized real weight, separate Boolean response tables for Alice and
  Bob, Equation (40)'s half-valued marginals, and Equation (41)'s
  `(1/2) cos²((theta-phi)/2)` joint moments.
- The production theorem map is:
  - E42: `equation42_mean_square_zero`;
  - E43: `equation43_equal_on_positive_support`;
  - E44: `equation44_alice_joint_moment`;
  - E45: `equation45_complementary_partition`, backed by the Boolean event
    `complementaryDisjunctionIndicator`;
  - E46: `equation46_first_equality`, `equation46_first_inequality`,
    `equation46_expanded_mean`, `equation46_second_inequality`,
    `equation46_triple_mean_nonnegative`, `equation46_third_inequality`,
    `equation46_chain`, `equation46_impossible_bound`, and `equation46_contradiction`.
- Equation (43) places the strict premise `0 < space.weight sample` on the sample whose responses
  are equated. A concrete two-sample regression test assigns weight zero to one disagreeing sample
  and proves that the mean square is still zero, demonstrating why the support premise is
  necessary.
- Equation (45) is represented both as an actual Boolean event/complement partition and in the
  source's displayed arithmetic form. Equation (46)'s expanded mean is proved exactly equal to
  `3/8 - E[a0*a1*a2]`; the source's inequality is then an immediate weakening, followed by
  independently proved triple-product nonnegativity.
- `Deutsch.Bell.Moments` imports `Deutsch.Bell.Quantum` only. It does not import
  `Deutsch.Bell.Finite`, `Deutsch.Bell.Contradiction`, `Deutsch.Bell.SourceCorrection`, or errata.
  Focused tests invoke the moment-chain contradiction and agreement-counting contradiction in
  separate branches against their respective named reproduction contracts.
- Verification:
  - `lake env lean Deutsch/Bell/Moments.lean`: pass.
  - `lake build Deutsch.Bell.Moments`: pass.
  - `lake build DeutschTests.Bell`: 2724 jobs, pass.
  - `lake build Deutsch.Bell DeutschTests.Bell DeutschTests.Audit`: 3301 jobs, pass.
  - `lake build Deutsch DeutschTests`: 3311 jobs, pass.
  - `python3 goal-1/check_lean_integrity.py`: 68 Lean sources and 447 representative axiom
    reports, pass; observed foundations only `Classical.choice`, `Quot.sound`, and `propext`.
  - `python3 goal-1/check_source_audit.py`: source/provenance and Equation (45) guards pass.
  - `python3 goal-1/check_doc_links.py`: 14 public Markdown files and 120 local links, pass.
  - Direct forbidden-import/token scans and `git diff --check`: pass.
- The direct expectation route and independent agreement/pigeonhole route both compile, but neither
  is used to prove the other.
