import Deutsch.Bell.AngleMoments
import Deutsch.EPR.RecordStatistics

/-!
# Paper façade: the finite Bell expectation argument

Equations (40)--(41) are supplied by Figure 2's literal four-wire record circuit.  Equations
(42)--(44) use response tables defined at every real angle on one finite weighted space.
Equations (45)--(46) restrict those same tables to the three angles needed by the finite
weighted-expectation contradiction.  They do not route through the independent
agreement/pigeonhole proof.

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
          EPR.recordLeftPaperOneEffect =
        bornProbability (EPR.pairDensity theta phi)
          (EPR.paperOneMarginalEffect 0) ∧
      bornProbability (EPR.fourWireTimeThreeDensity theta phi)
          EPR.recordRightPaperOneEffect = (1 / 2 : ℝ) ∧
      bornProbability (EPR.fourWireTimeThreeDensity theta phi)
          EPR.recordRightPaperOneEffect =
        bornProbability (EPR.pairDensity theta phi)
          (EPR.paperOneMarginalEffect 1) :=
  ⟨EPR.fourWireTimeThree_leftRecord_probability theta phi,
    EPR.fourWireTimeThree_leftRecord_probability_eq_pairDensity theta phi,
    EPR.fourWireTimeThree_rightRecord_probability theta phi,
    EPR.fourWireTimeThree_rightRecord_probability_eq_pairDensity theta phi⟩

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
    (alice bob : Ω → ℝ → Bool)
    (reproduces : Bell.ReproducesAngleEPRMoments space id alice bob)
    (setting : ℝ) :
    space.expectation (fun sample =>
      (Bell.angleResponseValue alice sample setting -
        Bell.angleResponseValue bob sample setting) ^ 2) = 0 :=
  Bell.angleEquation42_mean_square_zero
    space id alice bob reproduces setting

/--
Equation (43): equal settings give equal responses on every positive-weight sample.
No conclusion is made about zero-weight samples.
-/
theorem equation43
    {Ω : Type*} [Fintype Ω]
    (space : Bell.FiniteProbabilityWeight Ω)
    (alice bob : Ω → ℝ → Bool)
    (reproduces : Bell.ReproducesAngleEPRMoments space id alice bob)
    {sample : Ω} (samplePositive : 0 < space.weight sample)
    (setting : ℝ) :
    bob sample setting = alice sample setting :=
  Bell.angleEquation43_equal_on_positive_support
    space id alice bob reproduces samplePositive setting

/-- Equation (44): the Alice--Alice joint moment follows on the common finite sample space. -/
theorem equation44
    {Ω : Type*} [Fintype Ω]
    (space : Bell.FiniteProbabilityWeight Ω)
    (alice bob : Ω → ℝ → Bool)
    (reproduces : Bell.ReproducesAngleEPRMoments space id alice bob)
    (theta₀ theta₁ : ℝ) :
    space.expectation (fun sample =>
      Bell.angleResponseValue alice sample theta₀ *
        Bell.angleResponseValue alice sample theta₁) =
      (1 / 2 : ℝ) * Real.cos ((theta₀ - theta₁) / 2) ^ 2 := by
  simpa using Bell.angleEquation44_alice_joint_moment
    space id alice bob reproduces theta₀ theta₁

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
    (alice bob : Ω → ℝ → Bool)
    (reproduces : Bell.ReproducesAngleEPRMoments space id alice bob) :
    let aliceThree : Ω → Fin 3 → Bool :=
      fun sample setting => alice sample (Bell.threeSettingAngle setting)
    (1 / 2 : ℝ) =
        Bell.equation46PartitionedMean space aliceThree ∧
      Bell.equation46PartitionedMean space aliceThree ≤
        Bell.equation46ExpandedMean space aliceThree ∧
      Bell.equation46ExpandedMean space aliceThree ≤
        (3 / 8 : ℝ) - Bell.equation46TripleMean space aliceThree ∧
      (3 / 8 : ℝ) - Bell.equation46TripleMean space aliceThree ≤
        (3 / 8 : ℝ) := by
  let aliceThree : Ω → Fin 3 → Bool :=
    fun sample setting => alice sample (Bell.threeSettingAngle setting)
  let bobThree : Ω → Fin 3 → Bool :=
    fun sample setting => bob sample (Bell.threeSettingAngle setting)
  have restricted :
      Bell.ReproducesThreeSettingEPRMoments space aliceThree bobThree := by
    simpa [aliceThree, bobThree] using
      Bell.restrictRealAngleMomentsToThreeSettings
        space alice bob reproduces
  exact Bell.equation46_chain space aliceThree bobThree restricted

/-- The Equation (46) chain has the impossible numerical endpoints `1/2 ≤ 3/8`. -/
theorem equation46_implies_false
    {Ω : Type*} [Fintype Ω]
    (space : Bell.FiniteProbabilityWeight Ω)
    (alice bob : Ω → ℝ → Bool)
    (reproduces : Bell.ReproducesAngleEPRMoments space id alice bob) :
    False := by
  let aliceThree : Ω → Fin 3 → Bool :=
    fun sample setting => alice sample (Bell.threeSettingAngle setting)
  let bobThree : Ω → Fin 3 → Bool :=
    fun sample setting => bob sample (Bell.threeSettingAngle setting)
  have restricted :
      Bell.ReproducesThreeSettingEPRMoments space aliceThree bobThree := by
    simpa [aliceThree, bobThree] using
      Bell.restrictRealAngleMomentsToThreeSettings
        space alice bob reproduces
  exact Bell.equation46_contradiction
    space aliceThree bobThree restricted

end
end Paper
end Deutsch
