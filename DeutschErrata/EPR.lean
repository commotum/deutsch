import Deutsch.EPR.RecordStatistics

/-!
# Equations (28) and (41) equal-setting check

The two probability laws from the original printing are recorded only in this
companion module.  Their comparison target is the literal four-wire chronology:
Equation (28) uses the final comparison record, and Equation (41) uses the two
coherent records before that comparison.
-/

namespace DeutschErrata
namespace EPR

open Deutsch.Information

noncomputable section

/-- The Equation (28) probability law as it appeared in the original printing. -/
def printedEquation28Probability (theta phi : ℝ) : ℝ :=
  Real.cos ((theta - phi) / 2) ^ 2

/-- The Equation (41) probability law as it appeared in the original printing. -/
def printedEquation41Probability (theta phi : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.sin ((theta - phi) / 2) ^ 2

/--
The derived forms of Equations (28) and (41), together with their independent
two-wire bridges, are bundled directly from the literal four-wire circuit.
-/
theorem derivedEquations28And41 (theta phi : ℝ) :
    bornProbability
          (Deutsch.EPR.fourWireTimeFourDensity theta phi)
          Deutsch.EPR.finalComparisonPaperOneEffect =
        bornProbability
            (Deutsch.EPR.pairDensity theta phi)
            (Deutsch.Information.basisEffect Deutsch.EPR.paperOneZero) +
          bornProbability
            (Deutsch.EPR.pairDensity theta phi)
            (Deutsch.Information.basisEffect Deutsch.EPR.paperZeroOne) ∧
      bornProbability
          (Deutsch.EPR.fourWireTimeFourDensity theta phi)
          Deutsch.EPR.finalComparisonPaperOneEffect =
        Real.sin ((theta - phi) / 2) ^ 2 ∧
      bornProbability
          (Deutsch.EPR.fourWireTimeThreeDensity theta phi)
          Deutsch.EPR.recordJointPaperOneEffect =
        bornProbability
          (Deutsch.EPR.pairDensity theta phi)
          Deutsch.EPR.jointPaperOneEffect ∧
      bornProbability
          (Deutsch.EPR.fourWireTimeThreeDensity theta phi)
          Deutsch.EPR.recordJointPaperOneEffect =
        (1 / 2 : ℝ) * Real.cos ((theta - phi) / 2) ^ 2 :=
  ⟨Deutsch.EPR.fourWireTimeFour_comparison_probability_eq_unequal_pair_sum
      theta phi,
    Deutsch.EPR.fourWireTimeFour_comparison_probability theta phi,
    Deutsch.EPR.fourWireTimeThree_jointRecord_probability_eq_pairDensity
      theta phi,
    Deutsch.EPR.fourWireTimeThree_jointRecord_probability theta phi⟩

/--
At equal settings the literal comparison record has probability `0`, while the
first printed law gives `1`; the literal joint paper-one record has probability
`1/2`, while the second printed law gives `0`.
-/
theorem equations28And41_equal_settings_mismatch (theta : ℝ) :
    bornProbability
          (Deutsch.EPR.fourWireTimeFourDensity theta theta)
          Deutsch.EPR.finalComparisonPaperOneEffect = 0 ∧
      printedEquation28Probability theta theta = 1 ∧
      bornProbability
          (Deutsch.EPR.fourWireTimeFourDensity theta theta)
          Deutsch.EPR.finalComparisonPaperOneEffect ≠
        printedEquation28Probability theta theta ∧
      bornProbability
          (Deutsch.EPR.fourWireTimeThreeDensity theta theta)
          Deutsch.EPR.recordJointPaperOneEffect = (1 / 2 : ℝ) ∧
      printedEquation41Probability theta theta = 0 ∧
      bornProbability
          (Deutsch.EPR.fourWireTimeThreeDensity theta theta)
          Deutsch.EPR.recordJointPaperOneEffect ≠
        printedEquation41Probability theta theta := by
  have hActual28 :
      bornProbability
          (Deutsch.EPR.fourWireTimeFourDensity theta theta)
          Deutsch.EPR.finalComparisonPaperOneEffect = 0 :=
    Deutsch.EPR.fourWireTimeFour_comparison_equal_settings theta
  have hPrinted28 : printedEquation28Probability theta theta = 1 := by
    simp [printedEquation28Probability]
  have hActual41 :
      bornProbability
          (Deutsch.EPR.fourWireTimeThreeDensity theta theta)
          Deutsch.EPR.recordJointPaperOneEffect = (1 / 2 : ℝ) := by
    rw [Deutsch.EPR.fourWireTimeThree_jointRecord_probability]
    norm_num
  have hPrinted41 : printedEquation41Probability theta theta = 0 := by
    simp [printedEquation41Probability]
  refine ⟨hActual28, hPrinted28, ?_, hActual41, hPrinted41, ?_⟩
  · rw [hActual28, hPrinted28]
    norm_num
  · rw [hActual41, hPrinted41]
    norm_num

end
end EPR
end DeutschErrata
