import DeutschErrata

/-!
# Axiom audit for `DeutschErrata`

The commands below cover every public theorem and each source-side definition used
by a decisive comparison.  Their output is checked in CI for `sorryAx`.
-/

#print axioms DeutschErrata.Rotation.printedEquation18Y
#print axioms DeutschErrata.Rotation.printedEquation18Z
#print axioms DeutschErrata.Rotation.derivedEquation18
#print axioms DeutschErrata.Rotation.equation18_pi_div_two_mismatch

#print axioms DeutschErrata.EPR.printedEquation28Probability
#print axioms DeutschErrata.EPR.printedEquation41Probability
#print axioms DeutschErrata.EPR.derivedEquations28And41
#print axioms DeutschErrata.EPR.equations28And41_equal_settings_mismatch

#print axioms DeutschErrata.Teleportation.equation35PrintedEffectAtPiOverTwo
#print axioms DeutschErrata.Teleportation.equation35PrintedEffectAtPiOverTwo_op
#print axioms DeutschErrata.Teleportation.equation35_endpoint_probabilities_at_pi_div_two
#print axioms DeutschErrata.Teleportation.equation37PrintedOperator
#print axioms DeutschErrata.Teleportation.equation37_operator_ne_printed_at_pi_div_four

#print axioms DeutschErrata.Equation45.boolValue
#print axioms DeutschErrata.Equation45.boolValue_false
#print axioms DeutschErrata.Equation45.boolValue_true
#print axioms DeutschErrata.Equation45.numericOr
#print axioms DeutschErrata.Equation45.numericOr_eq_boolValue_or
#print axioms DeutschErrata.Equation45.equation45PrintedLeft
#print axioms DeutschErrata.Equation45.equation45PrintedRight
#print axioms DeutschErrata.Equation45.equation45ComplementaryRight
#print axioms DeutschErrata.Equation45.equation45_printed_values_at_one_zero_one
#print axioms DeutschErrata.Equation45.equation45_printed_form_fails_at_one_zero_one
#print axioms DeutschErrata.Equation45.equation45_complementary_partition

#print axioms DeutschErrata.Bell.equation45_derived_real_partition
#print axioms DeutschErrata.Bell.equation46_derived_form_contradiction
