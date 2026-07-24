import DeutschErrata

/-!
# Focused checks for the errata library

These small wrappers keep the decisive comparisons exercised through the public
`DeutschErrata` interface: the rotation exponential, the literal EPR chronology,
the two propagated teleportation signs, and the Boolean-to-moment Bell chain.
-/

namespace DeutschErrataTests

open Deutsch
open Deutsch.Foundations Deutsch.Gates Deutsch.Information Deutsch.Register
open Deutsch.Teleportation
open scoped Matrix

noncomputable section

theorem equation18_exponential_check (theta : ℝ) :
    NormedSpace.exp
          (Deutsch.Gates.axisRotationGenerator
            Deutsch.Gates.UnitAxis.xAxis theta) =
        Deutsch.Gates.axisRotation Deutsch.Gates.UnitAxis.xAxis theta ∧
      Deutsch.Gates.axisRotation Deutsch.Gates.UnitAxis.xAxis theta =
        Deutsch.Gates.rotationX theta ∧
      Deutsch.Foundations.heisenberg (Deutsch.Gates.rotationX theta)
          Deutsch.Foundations.pauliY =
        (theta.cos : ℂ) • Deutsch.Foundations.pauliY -
          (theta.sin : ℂ) • Deutsch.Foundations.pauliZ ∧
      Deutsch.Foundations.heisenberg (Deutsch.Gates.rotationX theta)
          Deutsch.Foundations.pauliZ =
        (theta.sin : ℂ) • Deutsch.Foundations.pauliY +
          (theta.cos : ℂ) • Deutsch.Foundations.pauliZ :=
  DeutschErrata.Rotation.derivedEquation18 theta

theorem equation18_quarter_turn_comparison :
    Deutsch.Foundations.heisenberg
          (Deutsch.Gates.rotationX (Real.pi / 2))
          Deutsch.Foundations.pauliY =
        -Deutsch.Foundations.pauliZ ∧
      DeutschErrata.Rotation.printedEquation18Y (Real.pi / 2) =
        Deutsch.Foundations.pauliZ ∧
      Deutsch.Foundations.heisenberg
          (Deutsch.Gates.rotationX (Real.pi / 2))
          Deutsch.Foundations.pauliY ≠
        DeutschErrata.Rotation.printedEquation18Y (Real.pi / 2) ∧
      Deutsch.Foundations.heisenberg
          (Deutsch.Gates.rotationX (Real.pi / 2))
          Deutsch.Foundations.pauliZ =
        Deutsch.Foundations.pauliY ∧
      DeutschErrata.Rotation.printedEquation18Z (Real.pi / 2) =
        -Deutsch.Foundations.pauliY ∧
      Deutsch.Foundations.heisenberg
          (Deutsch.Gates.rotationX (Real.pi / 2))
          Deutsch.Foundations.pauliZ ≠
        DeutschErrata.Rotation.printedEquation18Z (Real.pi / 2) :=
  DeutschErrata.Rotation.equation18_pi_div_two_mismatch

theorem equations28_and_41_four_wire_derivation (theta phi : ℝ) :
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
  DeutschErrata.EPR.derivedEquations28And41 theta phi

theorem equations28_and_41_equal_setting_comparison (theta : ℝ) :
    bornProbability
          (Deutsch.EPR.fourWireTimeFourDensity theta theta)
          Deutsch.EPR.finalComparisonPaperOneEffect = 0 ∧
      DeutschErrata.EPR.printedEquation28Probability theta theta = 1 ∧
      bornProbability
          (Deutsch.EPR.fourWireTimeFourDensity theta theta)
          Deutsch.EPR.finalComparisonPaperOneEffect ≠
        DeutschErrata.EPR.printedEquation28Probability theta theta ∧
      bornProbability
          (Deutsch.EPR.fourWireTimeThreeDensity theta theta)
          Deutsch.EPR.recordJointPaperOneEffect = (1 / 2 : ℝ) ∧
      DeutschErrata.EPR.printedEquation41Probability theta theta = 0 ∧
      bornProbability
          (Deutsch.EPR.fourWireTimeThreeDensity theta theta)
          Deutsch.EPR.recordJointPaperOneEffect ≠
        DeutschErrata.EPR.printedEquation41Probability theta theta :=
  DeutschErrata.EPR.equations28And41_equal_settings_mismatch theta

theorem equation35_five_wire_endpoint :
    bornProbability
          (Deutsch.Teleportation.parameterizedTeleportedDensity
            (Real.pi / 2))
          (((Deutsch.Teleportation.parameterizedReceiverDensity
              (Real.pi / 2)).toEffect).embedSubsystem
            ({Deutsch.Teleportation.q5} : Finset
              Deutsch.Teleportation.TeleportQubit)) = 1 ∧
      bornProbability
          (Deutsch.Teleportation.parameterizedTeleportedDensity
            (Real.pi / 2))
          (DeutschErrata.Teleportation.equation35PrintedEffectAtPiOverTwo.embedSubsystem
            ({Deutsch.Teleportation.q5} : Finset
              Deutsch.Teleportation.TeleportQubit)) = 0 :=
  DeutschErrata.Teleportation.equation35_endpoint_probabilities_at_pi_div_two

theorem equation37_operator_comparison :
    (Deutsch.Teleportation.timeFiveDescriptors (Real.pi / 4)
        Deutsch.Teleportation.q5).z ≠
      DeutschErrata.Teleportation.equation37PrintedOperator
        (Real.pi / 4) :=
  DeutschErrata.Teleportation.equation37_operator_ne_printed_at_pi_div_four

theorem equation45_value_fixture :
    DeutschErrata.Equation45.equation45PrintedLeft true = 1 ∧
      DeutschErrata.Equation45.equation45PrintedRight true false true = 2 :=
  DeutschErrata.Equation45.equation45_printed_values_at_one_zero_one

theorem equation45_failure_fixture :
    DeutschErrata.Equation45.equation45PrintedLeft true ≠
      DeutschErrata.Equation45.equation45PrintedRight true false true :=
  DeutschErrata.Equation45.equation45_printed_form_fails_at_one_zero_one

theorem equation45_complementary_partition_check (a₀ a₁ a₂ : Bool) :
    DeutschErrata.Equation45.equation45PrintedLeft a₀ =
      DeutschErrata.Equation45.equation45ComplementaryRight a₀ a₁ a₂ :=
  DeutschErrata.Equation45.equation45_complementary_partition a₀ a₁ a₂

theorem equation45_real_partition_check (a₀ a₁ a₂ : Bool) :
    Deutsch.Bell.booleanIndicator a₀ =
      Deutsch.Bell.booleanIndicator a₀ *
          Deutsch.Bell.disjunctionIndicator a₁ a₂ +
        Deutsch.Bell.booleanIndicator a₀ *
          (1 - Deutsch.Bell.disjunctionIndicator a₁ a₂) :=
  DeutschErrata.Bell.equation45_derived_real_partition a₀ a₁ a₂

theorem equation46_direct_moments_check
    {Ω : Type*} [Fintype Ω]
    (space : Deutsch.Bell.FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces :
      Deutsch.Bell.ReproducesThreeSettingEPRMoments space alice bob) :
    False :=
  DeutschErrata.Bell.equation46_derived_form_contradiction
    space alice bob reproduces

end
end DeutschErrataTests
