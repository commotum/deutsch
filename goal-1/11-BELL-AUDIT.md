# 11-BELL-AUDIT

## Status

- Complete with focused, full-build, source, documentation, integrity, axiom, and hygiene
  evidence; Stage 12 is the first incomplete stage.

## Current Facts

- The source's Equation (45) is false pointwise at `(a₀,a₁,a₂)=(1,0,1)`. The Stage 1
  checker evaluates all eight Boolean triples and verifies a corrected complementary-event
  partition, so the printed derivation cannot be encoded as an assumption or reused as a lemma.
- Stage 8 corrected the source's Equation (41): `pairDensity_jointPaperOne_probability` is
  `1/2 cos²((θ-φ)/2)`, while `pairDensity_different_probability` is
  `sin²((θ-φ)/2)`. At equal settings the two raw/paper outcomes agree with probability
  one. The source's complement relation therefore cannot be imported without an explicit outcome
  relabeling.
- A three-setting Mermin/pigeonhole form avoids both defects. For settings
  `0, 2π/3, 4π/3`, the corrected EPR prediction gives pairwise agreement probability `1/4`.
  Every single Boolean assignment to all three counterfactual settings has at least one agreeing
  pair, so any normalized nonnegative distribution over such assignments has the sum of those
  three probabilities at least `1`, contradicting `3/4`.
- The library's Stage 4 finite-support dynamical locality and Stage 7 channel no-signalling are
  operator/state evolution theorems. Bell locality is a different assumption about a common
  counterfactual outcome model and setting-local response functions; neither notion implies the
  other definitionally.

## Big Picture Objective

- Compile the corrected finite Bell contradiction from a complete, reviewable list of
  counterfactual value-assignment, setting-locality, setting-independent nonnegative normalized
  weights, and corrected quantum-statistics assumptions, deriving positive-support
  perfect-correlation from the probability-one equal-setting predictions while excluding the
  source's philosophical diagnosis from the theorem conclusion.

## Detailed Implementation Plan

1. Audit E40–E46, C53–C59, and D09 against the Stage 8 probability convention and the false
   Equation (45) truth-table witness.
2. Define a finite three-setting deterministic assignment and normalized nonnegative real
   distribution. Make remote-setting independence structural: Alice's value depends only on her
   setting and the common assignment, and likewise for Bob.
3. Prove the pointwise Boolean pigeonhole lemma, the weighted agreement inequality, and the
   contradiction when all three cross-setting agreement probabilities are `1/4`.
4. If the core theorem uses one common response assignment, expose the exact perfect-equal-setting
   reduction hypothesis or add a two-party wrapper whose positive-weight support forces Alice and
   Bob's equal-setting responses to agree.
5. Define the three quantum angles and derive their corrected `1/4` agreement probabilities from
   `pairDensity_different_probability`, including an equal-setting regression and exact trig
   checks. Do not reuse the printed Equation (41).
6. Add the public umbrella, focused tests, documentation, lifecycle statuses, principal axiom
   targets, full build, and hygiene evidence.

## Paper Mapping

- E40/C54: reuse the already compiled `1/2` marginals only as source context; the corrected
  pigeonhole proof needs the three agreement probabilities and perfect equal-setting agreement.
- E41: reject the printed joint-one sine-squared formula. Use the corrected different/same-outcome
  distribution, with the raw/paper-bit convention explicit.
- E42–E43: replace the source's unqualified zero-square/complement statement by the proved finite
  reduction from probability-one equal-setting agreement to agreement on positive-weight support;
  leave zero-weight assignments unconstrained.
- E44: counterfactual cross-setting correlations require all finitely many response values on one
  common assignment space. This is a Bell-model assumption, not a consequence of channel
  no-signalling.
- E45: retain the compiled counterexample to the printed identity. The production contradiction
  uses the direct three-Boolean pigeonhole lemma instead.
- E46/C55: prove a corrected three-setting inequality and contradiction.
- C53/C56: document the precise relationship to deterministic finite Bell locality; do not claim
  equivalence with every stochastic/factorizable formulation without a refinement theorem.
- C57–C59: exclude the source's single-outcome, matrix-descriptor, and many-worlds diagnoses from
  Lean theorem conclusions.
- D09: provide only the finite Boolean/common-weight API actually needed; no measure-theoretic
  almost-sure statement is required.

## No-Cheating Checks

- Equation (45)'s false printed expression never appears as a theorem premise or rewrite rule.
- The quantum `1/4` values are derived from the corrected EPR distribution and exact special-angle
  trigonometry, not asserted inside the contradiction theorem.
- Normalization and nonnegativity of weights are explicit. Zero-weight assignments cannot smuggle
  violations into a support-level perfect-correlation premise.
- Local response functions do not accept the remote setting. The common assignment and the
  counterfactual simultaneous-value assumption remain visible in types and hypotheses.
- Bell locality is not identified with `IsSupportedOn`, disjoint commutation, reduced-state
  no-signalling, or statistical independence.
- The contradiction rejects the listed joint-assignment assumptions only. It does not select the
  source's preferred ontology or interpretation.
- Completed modules contain no proof holes, unsafe declarations, project axioms, or hidden
  probability axioms; principal theorems enter `DeutschTests.Audit`.

## Completion Requirements

- [x] A pointwise three-Boolean pigeonhole theorem and normalized weighted Bell inequality compile.
- [x] A contradiction from the explicit three `1/4` agreement predictions compiles.
- [x] The two-party/local-response or common-assignment reduction assumptions are fully exposed.
- [x] Corrected EPR probabilities at `0,2π/3,4π/3` compile independently of the hidden-variable
      theorem.
- [x] E40–E46, C53–C59, and D09 have final statuses and the false printed steps remain documented.
- [x] Documentation distinguishes Bell counterfactual locality from dynamical locality and
      no-signalling.
- [x] Focused tests, full build, source/doc/integrity/axiom audits, and hygiene checks pass and are
      recorded; Stage 12 is then the first incomplete stage.

## Stage Results

- `Deutsch.Bell.SourceCorrection` compiles the exact `(1,0,1)` counterexample to printed Equation
  (45), with sides `1` and `2`, and verifies the corrected complementary-event partition on all
  eight Boolean triples. The production inequality is independent of both formulas.
- `Deutsch.Bell.Finite` defines common and explicit two-party deterministic three-setting response
  tables. Alice and Bob response functions structurally omit the remote setting, and the real
  weight has no setting argument. Pointwise pigeonhole and normalized weighted inequalities
  compile under explicit nonnegativity and normalization.
- Probability-one agreement at every equal-setting pair implies Alice/Bob equality on every
  positive-weight response table through
  `perfectEqualSettingSupport_of_agreementProbability_one`; zero-weight tables remain
  unconstrained. Thus the strongest inequality and contradiction wrappers do not assume the
  support statement separately.
- `Deutsch.Bell.Quantum` derives the corrected agreement formula
  `cos²((theta-phi)/2)` from Stage 8's independently proved different-outcome Born probability,
  pins raw/paper relabeling, and proves exact probability `1/4` at every distinct pair among
  `0,2π/3,4π/3` plus probability one at equal settings.
- `Deutsch.Bell.corrected_epr_three_settings_refute_normalized_local_model` proves
  that nonnegative normalized setting-independent weights over deterministic setting-local
  response tables cannot reproduce the complete corrected three-setting agreement table;
  `no_normalized_local_model_reproduces_corrected_epr_three_settings` is its reusable negated
  form. No stochastic-refinement equivalence, continuum-setting theorem, or ontological diagnosis
  is claimed.
- `lake build Deutsch.Bell DeutschTests.Bell` completed 2723 jobs, and the full `lake build`
  completed 3308 jobs. `python3 -B goal-1/check_lean_integrity.py` scanned 64 Lean sources,
  required 15 Bell oracles and 34 ordered Bell public declarations, and accepted 402 axiom reports
  containing only `Classical.choice`, `Quot.sound`, and `propext`.
- `python3 -B goal-1/check_source_audit.py` passed all 46 numbered equations, three unnumbered
  displays, three figures, 11 definitions, 66 claims, and ten interpretation groups.
  `python3 -B goal-1/check_doc_links.py` passed 12 Markdown files and 98 repository-local links.
  Forbidden-token, trailing-whitespace, `git diff --check`, and statement/scope review passed.

## Resume Point

- Stage 12 (`12-LIBRARY-AUDIT`) is the first incomplete stage. Reconcile the remaining stale
  lifecycle-summary cells, add compiled public-API reuse examples and a final project report, then
  repeat the verification ladder from a cleaned project build.
