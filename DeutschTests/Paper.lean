import Deutsch.Paper

/-!
# Exact paper-equation registry

The forty-six checks below are the complete canonical `Deutsch.Paper` equation surface.  Focused
theorems then pin the implementation boundaries that a name-only registry cannot verify: current
Heisenberg frames, genuine matrix exponentials, Figure 2's four-wire states, positive-weight
support, all-real settings, and the direct Bell moment chain.
-/

/-! ## Contiguous Equation (1)--(46) surface -/

#check Deutsch.Paper.equation01
#check Deutsch.Paper.equation02
#check Deutsch.Paper.equation03
#check Deutsch.Paper.equation04
#check Deutsch.Paper.equation05
#check Deutsch.Paper.equation06
#check Deutsch.Paper.equation07
#check Deutsch.Paper.equation08
#check Deutsch.Paper.equation09
#check Deutsch.Paper.equation10
#check Deutsch.Paper.equation11
#check Deutsch.Paper.equation12
#check Deutsch.Paper.equation13
#check Deutsch.Paper.equation14
#check Deutsch.Paper.equation15
#check Deutsch.Paper.equation16
#check Deutsch.Paper.equation17
#check Deutsch.Paper.equation18
#check Deutsch.Paper.equation19
#check Deutsch.Paper.equation20
#check Deutsch.Paper.equation21
#check Deutsch.Paper.equation22
#check Deutsch.Paper.equation23
#check Deutsch.Paper.equation24
#check Deutsch.Paper.equation25
#check Deutsch.Paper.equation26
#check Deutsch.Paper.equation27
#check Deutsch.Paper.equation28
#check Deutsch.Paper.equation29
#check Deutsch.Paper.equation30
#check Deutsch.Paper.equation31
#check Deutsch.Paper.equation32
#check Deutsch.Paper.equation33
#check Deutsch.Paper.equation34
#check Deutsch.Paper.equation35
#check Deutsch.Paper.equation36
#check Deutsch.Paper.equation37
#check Deutsch.Paper.equation38
#check Deutsch.Paper.equation39
#check Deutsch.Paper.equation40
#check Deutsch.Paper.equation41
#check Deutsch.Paper.equation42
#check Deutsch.Paper.equation43
#check Deutsch.Paper.equation44
#check Deutsch.Paper.equation45
#check Deutsch.Paper.equation46

namespace DeutschTests
namespace Paper

open Deutsch
open Deutsch.Foundations Deutsch.Gates Deutsch.Information Deutsch.Register
open NormedSpace
open scoped Matrix

noncomputable section

/-! ## Focused no-cheating witnesses -/

/-- Equation (9) acts on computation kets transported into the same current frame as the gate. -/
theorem equation09_uses_current_frame
    (W : QubitMatrix)
    (hW : W ∈ Matrix.unitaryGroup QubitIndex ℂ) :
    (Deutsch.Paper.notGateInFrame W)ᴴ *ᵥ
          Deutsch.Paper.computationKetInFrame W ketOne =
        Deutsch.Paper.computationKetInFrame W ketZero ∧
      (Deutsch.Paper.notGateInFrame W)ᴴ *ᵥ
          Deutsch.Paper.computationKetInFrame W ketZero =
        Deutsch.Paper.computationKetInFrame W ketOne :=
  Deutsch.Paper.equation09 W hW

/--
Equation (17) uses the transported named gate and the genuine Banach-algebra exponential on both
sides of the current descriptor component.
-/
theorem equation17_uses_true_exp_and_transport
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (W : Operator Q) (hW : W ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (q : Q) (n : UnitAxis) (theta : ℝ) (a : Axis) :
    Register.heisenberg
        (Register.heisenberg W (axisRotationAt q n theta))
        (((Descriptor.initial q).evolve W).component a) =
      exp ((Complex.I * (theta / 2 : ℂ)) • currentAxisPauli W q n) *
        ((Descriptor.initial q).evolve W).component a *
        exp ((-Complex.I * (theta / 2 : ℂ)) • currentAxisPauli W q n) :=
  Deutsch.Paper.equation17 W hW q n theta a

/--
Equation (28)'s literal four-wire comparison is bridged structurally to the two unequal pair
outcomes before the trigonometric evaluation.
-/
theorem equation28_has_structural_fourWire_bridge (theta phi : ℝ) :
    bornProbability (EPR.fourWireTimeFourDensity theta phi)
          EPR.finalComparisonPaperOneEffect =
        bornProbability (EPR.pairDensity theta phi)
            (basisEffect EPR.paperOneZero) +
          bornProbability (EPR.pairDensity theta phi)
            (basisEffect EPR.paperZeroOne) :=
  (Deutsch.Paper.equation28 theta phi).1

/-- Equation (40) is stated directly on both literal four-wire record effects. -/
theorem equation40_uses_literal_fourWire_records (theta phi : ℝ) :
    bornProbability (EPR.fourWireTimeThreeDensity theta phi)
          EPR.recordLeftPaperOneEffect = (1 / 2 : ℝ) ∧
      bornProbability (EPR.fourWireTimeThreeDensity theta phi)
          EPR.recordRightPaperOneEffect = (1 / 2 : ℝ) :=
  ⟨(Deutsch.Paper.equation40 theta phi).1,
    (Deutsch.Paper.equation40 theta phi).2.2.1⟩

/-- Equation (41) is stated directly on the literal four-wire joint record effect. -/
theorem equation41_uses_literal_fourWire_joint_record (theta phi : ℝ) :
    bornProbability (EPR.fourWireTimeThreeDensity theta phi)
          EPR.recordJointPaperOneEffect =
        (1 / 2 : ℝ) * Real.cos ((theta - phi) / 2) ^ 2 :=
  (Deutsch.Paper.equation41 theta phi).1

/-- Equation (43) retains the strict positive-weight support premise. -/
theorem equation43_requires_positive_support
    {Ω : Type*} [Fintype Ω]
    (space : Bell.FiniteProbabilityWeight Ω)
    (alice bob : Ω → ℝ → Bool)
    (reproduces : Bell.ReproducesAngleEPRMoments space id alice bob)
    {sample : Ω} (samplePositive : 0 < space.weight sample)
    (theta : ℝ) :
    bob sample theta = alice sample theta :=
  Deutsch.Paper.equation43
    space alice bob reproduces samplePositive theta

/-- Equation (44) quantifies arbitrary real angles and exposes the cosine moment literally. -/
theorem equation44_is_all_real_angles
    {Ω : Type*} [Fintype Ω]
    (space : Bell.FiniteProbabilityWeight Ω)
    (alice bob : Ω → ℝ → Bool)
    (reproduces : Bell.ReproducesAngleEPRMoments space id alice bob)
    (theta₀ theta₁ : ℝ) :
    space.expectation (fun sample =>
      Bell.angleResponseValue alice sample theta₀ *
        Bell.angleResponseValue alice sample theta₁) =
      (1 / 2 : ℝ) * Real.cos ((theta₀ - theta₁) / 2) ^ 2 :=
  Deutsch.Paper.equation44
    space alice bob reproduces theta₀ theta₁

/--
Equation (46) restricts the same all-real response table and exposes the direct expectation chain,
not the independent agreement/pigeonhole proof.
-/
theorem equation46_uses_direct_moment_chain
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
        (3 / 8 : ℝ) :=
  Deutsch.Paper.equation46 space alice bob reproduces

end
end Paper
end DeutschTests
