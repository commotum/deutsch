import Deutsch.Bell.Moments
import Deutsch.EPR.RecordStatistics

/-!
# Paper façade: the finite Bell expectation argument

Equations (40)--(41) are supplied by Figure 2's literal four-wire record circuit.  Equations
(42)--(46) are the separate finite weighted-expectation derivation over setting-local Boolean
response tables.  They do not route through the independent agreement/pigeonhole proof.

The finite response-space formulation makes the scope explicit.  Equation (43) constrains only
positive-weight samples; assignments of zero weight remain unrestricted.
-/

namespace Deutsch
namespace Paper

open Foundations Information

noncomputable section

/--
Equation (40): the two locally recorded paper-one marginals are each one half in the literal
four-wire circuit.
-/
theorem equation40 (theta phi : ℝ) :
    bornProbability (EPR.fourWireTimeThreeDensity theta phi)
          EPR.recordLeftPaperOneEffect = (1 / 2 : ℝ) ∧
      bornProbability (EPR.fourWireTimeThreeDensity theta phi)
          EPR.recordRightPaperOneEffect = (1 / 2 : ℝ) :=
  ⟨EPR.fourWireTimeThree_leftRecord_probability theta phi,
    EPR.fourWireTimeThree_rightRecord_probability theta phi⟩

/--
Equation (41): the joint paper-one record probability follows the displayed cosine-squared law
in the literal four-wire circuit and agrees with the independent two-wire density calculation.
-/
theorem equation41 (theta phi : ℝ) :
    bornProbability (EPR.fourWireTimeThreeDensity theta phi)
          EPR.recordJointPaperOneEffect =
        (1 / 2 : ℝ) * Real.cos ((theta - phi) / 2) ^ 2 ∧
      bornProbability (EPR.fourWireTimeThreeDensity theta phi)
          EPR.recordJointPaperOneEffect =
        bornProbability (EPR.pairDensity theta phi) EPR.jointPaperOneEffect :=
  ⟨EPR.fourWireTimeThree_jointRecord_probability theta phi,
    EPR.fourWireTimeThree_jointRecord_probability_eq_pairDensity theta phi⟩

/-- Equation (42): equal-setting response differences have zero mean square. -/
theorem equation42
    {Ω : Type*} [Fintype Ω]
    (space : Bell.FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : Bell.ReproducesThreeSettingEPRMoments space alice bob)
    (setting : Fin 3) :
    space.expectation (fun sample =>
      (Bell.aliceValue alice sample setting -
        Bell.bobValue bob sample setting) ^ 2) = 0 :=
  Bell.equation42_mean_square_zero space alice bob reproduces setting

/--
Equation (43): equal settings give equal responses on every positive-weight sample.
No conclusion is made about zero-weight samples.
-/
theorem equation43
    {Ω : Type*} [Fintype Ω]
    (space : Bell.FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : Bell.ReproducesThreeSettingEPRMoments space alice bob)
    {sample : Ω} (samplePositive : 0 < space.weight sample)
    (setting : Fin 3) :
    bob sample setting = alice sample setting :=
  Bell.equation43_equal_on_positive_support
    space alice bob reproduces samplePositive setting

/-- Equation (44): the Alice--Alice joint moment follows on the common finite sample space. -/
theorem equation44
    {Ω : Type*} [Fintype Ω]
    (space : Bell.FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : Bell.ReproducesThreeSettingEPRMoments space alice bob)
    (setting₀ setting₁ : Fin 3) :
    space.expectation (fun sample =>
      Bell.aliceValue alice sample setting₀ *
        Bell.aliceValue alice sample setting₁) =
      Bell.eprJointMoment setting₀ setting₁ :=
  Bell.equation44_alice_joint_moment
    space alice bob reproduces setting₀ setting₁

/--
Equation (45): multiplication by the disjunction and by its actual complement partitions the
Boolean response at the first setting.
-/
theorem equation45 (a₀ a₁ a₂ : Bool) :
    Bell.booleanIndicator a₀ =
      Bell.booleanIndicator a₀ * Bell.disjunctionIndicator a₁ a₂ +
        Bell.booleanIndicator a₀ * (1 - Bell.disjunctionIndicator a₁ a₂) :=
  Bell.equation45_complementary_partition a₀ a₁ a₂

/--
Equation (46): every displayed equality and inequality in the finite expectation
chain.  The independent theorem `Bell.equation46_contradiction` derives `False` from the same
explicit reproduction assumptions.
-/
theorem equation46
    {Ω : Type*} [Fintype Ω]
    (space : Bell.FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : Bell.ReproducesThreeSettingEPRMoments space alice bob) :
    (1 / 2 : ℝ) = Bell.equation46PartitionedMean space alice ∧
      Bell.equation46PartitionedMean space alice ≤
        Bell.equation46ExpandedMean space alice ∧
      Bell.equation46ExpandedMean space alice ≤
        (3 / 8 : ℝ) - Bell.equation46TripleMean space alice ∧
      (3 / 8 : ℝ) - Bell.equation46TripleMean space alice ≤ (3 / 8 : ℝ) :=
  Bell.equation46_chain space alice bob reproduces

/-- The Equation (46) chain has the impossible numerical endpoints `1/2 ≤ 3/8`. -/
theorem equation46_implies_false
    {Ω : Type*} [Fintype Ω]
    (space : Bell.FiniteProbabilityWeight Ω)
    (alice bob : Ω → Fin 3 → Bool)
    (reproduces : Bell.ReproducesThreeSettingEPRMoments space alice bob) :
    False :=
  Bell.equation46_contradiction space alice bob reproduces

end
end Paper
end Deutsch
