import Deutsch.EPR.RecordStatistics

/-!
# Paper façade: the four-wire EPR comparison

This module gives the source-shaped entry for Equation (28).  Its probability is computed from
Figure 2's literal four-wire unitary chronology, including both coherent record wires and the
final comparison CNOT.  The second conjunct records the independently proved bridge to the
two-wire density calculation.
-/

namespace Deutsch
namespace Paper

open Foundations Information

noncomputable section

/--
Equation (28): the paper-one result on the final comparison wire has the sine-squared
probability obtained from the literal four-wire circuit, and that probability agrees with the
independent two-wire calculation.
-/
theorem equation28 (theta phi : ℝ) :
    bornProbability (EPR.fourWireTimeFourDensity theta phi)
          EPR.finalComparisonPaperOneEffect =
        bornProbability (EPR.pairDensity theta phi)
            (basisEffect EPR.paperOneZero) +
          bornProbability (EPR.pairDensity theta phi)
            (basisEffect EPR.paperZeroOne) ∧
      bornProbability (EPR.fourWireTimeFourDensity theta phi)
          EPR.finalComparisonPaperOneEffect =
        bornProbability (EPR.pairDensity theta phi) EPR.differentEffect ∧
      bornProbability (EPR.fourWireTimeFourDensity theta phi)
          EPR.finalComparisonPaperOneEffect =
        Real.sin ((theta - phi) / 2) ^ 2 :=
  ⟨EPR.fourWireTimeFour_comparison_probability_eq_unequal_pair_sum theta phi,
    EPR.fourWireTimeFour_comparison_probability_eq_pairDensity theta phi,
    EPR.fourWireTimeFour_comparison_probability theta phi⟩

end
end Paper
end Deutsch
