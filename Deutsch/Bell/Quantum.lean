import Deutsch.EPR.Statistics
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Three-setting quantum predictions

This module isolates the quantum input to the finite Bell argument.  It uses the EPR
probability theorem and makes no hidden-variable assumptions.

The project's computational-basis indices reverse the paper labels on each wire: raw `0` is
paper `1`, and raw `1` is paper `0`.  Reversing both labels preserves whether two outcomes are
equal, so the same/different probabilities below have the same meaning in either convention.
-/

namespace Deutsch
namespace Bell

open EPR Foundations Information Register

noncomputable section

/-- Convert a raw matrix-basis index to the paper's logical bit label. -/
def paperBitOfRaw : QubitIndex → QubitIndex := ![1, 0]

@[simp]
theorem paperBitOfRaw_zero : paperBitOfRaw 0 = 1 := rfl

@[simp]
theorem paperBitOfRaw_one : paperBitOfRaw 1 = 0 := rfl

/-- Reversing the per-wire bit convention preserves equality of two outcomes. -/
theorem paperBits_equal_iff_rawBits_equal (left right : QubitIndex) :
    paperBitOfRaw left = paperBitOfRaw right ↔ left = right := by
  fin_cases left <;> fin_cases right <;> simp

/-- The probability that the two EPR outcomes agree, defined as the complement of the
different-outcome probability. -/
def sameOutcomeProbability (theta phi : ℝ) : ℝ :=
  1 - bornProbability (pairDensity theta phi) differentEffect

/-- The quantum same-outcome prediction is `cos²((theta-phi)/2)`. -/
theorem sameOutcomeProbability_eq_cos_sq (theta phi : ℝ) :
    sameOutcomeProbability theta phi =
      Real.cos ((theta - phi) / 2) ^ 2 := by
  rw [sameOutcomeProbability, pairDensity_different_probability]
  nlinarith [Real.sin_sq_add_cos_sq ((theta - phi) / 2)]

theorem sameOutcomeProbability_comm (theta phi : ℝ) :
    sameOutcomeProbability theta phi = sameOutcomeProbability phi theta := by
  rw [sameOutcomeProbability_eq_cos_sq, sameOutcomeProbability_eq_cos_sq]
  have harg : (phi - theta) / 2 = -((theta - phi) / 2) := by ring
  rw [harg, Real.cos_neg]

/-- Equal settings give perfect agreement. -/
theorem sameOutcomeProbability_equal_setting (theta : ℝ) :
    sameOutcomeProbability theta theta = 1 := by
  rw [sameOutcomeProbability_eq_cos_sq]
  norm_num

/-- First setting: angle `0`. -/
def settingZeroAngle : ℝ := 0

/-- Second setting: angle `2*pi/3`. -/
def settingOneAngle : ℝ := 2 * Real.pi / 3

/-- Third setting: angle `4*pi/3`. -/
def settingTwoAngle : ℝ := 4 * Real.pi / 3

/-- The three angles as a finite setting family. -/
def threeSettingAngle : Fin 3 → ℝ :=
  ![settingZeroAngle, settingOneAngle, settingTwoAngle]

@[simp]
theorem threeSettingAngle_zero : threeSettingAngle 0 = settingZeroAngle := rfl

@[simp]
theorem threeSettingAngle_one : threeSettingAngle 1 = settingOneAngle := rfl

@[simp]
theorem threeSettingAngle_two : threeSettingAngle 2 = settingTwoAngle := rfl

/-- Explicit special-angle calculation for the first unordered pair. -/
theorem cos_half_settingZero_sub_settingOne :
    Real.cos ((settingZeroAngle - settingOneAngle) / 2) = (1 / 2 : ℝ) := by
  rw [show (settingZeroAngle - settingOneAngle) / 2 = -(Real.pi / 3) by
    simp [settingZeroAngle, settingOneAngle]
    ring]
  rw [Real.cos_neg, Real.cos_pi_div_three]

/-- Explicit special-angle calculation for the second unordered pair. -/
theorem cos_half_settingZero_sub_settingTwo :
    Real.cos ((settingZeroAngle - settingTwoAngle) / 2) = -(1 / 2 : ℝ) := by
  rw [show (settingZeroAngle - settingTwoAngle) / 2 = -(2 * Real.pi / 3) by
    simp [settingZeroAngle, settingTwoAngle]
    ring]
  rw [Real.cos_neg]
  rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring]
  rw [Real.cos_pi_sub, Real.cos_pi_div_three]

/-- Explicit special-angle calculation for the third unordered pair. -/
theorem cos_half_settingOne_sub_settingTwo :
    Real.cos ((settingOneAngle - settingTwoAngle) / 2) = (1 / 2 : ℝ) := by
  rw [show (settingOneAngle - settingTwoAngle) / 2 = -(Real.pi / 3) by
    simp [settingOneAngle, settingTwoAngle]
    ring]
  rw [Real.cos_neg, Real.cos_pi_div_three]

/-- Settings `0` and `2*pi/3` have same-outcome probability `1/4`. -/
theorem sameOutcomeProbability_settingZero_settingOne :
    sameOutcomeProbability settingZeroAngle settingOneAngle = (1 / 4 : ℝ) := by
  rw [sameOutcomeProbability_eq_cos_sq,
    cos_half_settingZero_sub_settingOne]
  norm_num

/-- Settings `0` and `4*pi/3` have same-outcome probability `1/4`. -/
theorem sameOutcomeProbability_settingZero_settingTwo :
    sameOutcomeProbability settingZeroAngle settingTwoAngle = (1 / 4 : ℝ) := by
  rw [sameOutcomeProbability_eq_cos_sq,
    cos_half_settingZero_sub_settingTwo]
  norm_num

/-- Settings `2*pi/3` and `4*pi/3` have same-outcome probability `1/4`. -/
theorem sameOutcomeProbability_settingOne_settingTwo :
    sameOutcomeProbability settingOneAngle settingTwoAngle = (1 / 4 : ℝ) := by
  rw [sameOutcomeProbability_eq_cos_sq,
    cos_half_settingOne_sub_settingTwo]
  norm_num

/-- Every pair of distinct members of the finite three-setting family has same-outcome
probability `1/4`; commutativity covers both orderings of each unordered pair. -/
theorem threeSetting_sameOutcomeProbability_of_ne
    (i j : Fin 3) (hij : i ≠ j) :
    sameOutcomeProbability (threeSettingAngle i) (threeSettingAngle j) =
      (1 / 4 : ℝ) := by
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact sameOutcomeProbability_settingZero_settingOne
  · exact sameOutcomeProbability_settingZero_settingTwo
  · rw [sameOutcomeProbability_comm]
    exact sameOutcomeProbability_settingZero_settingOne
  · exact (hij rfl).elim
  · exact sameOutcomeProbability_settingOne_settingTwo
  · rw [sameOutcomeProbability_comm]
    exact sameOutcomeProbability_settingZero_settingTwo
  · rw [sameOutcomeProbability_comm]
    exact sameOutcomeProbability_settingOne_settingTwo
  · exact (hij rfl).elim

/-- Every member of the finite family has perfect equal-setting agreement. -/
theorem threeSetting_sameOutcomeProbability_self (i : Fin 3) :
    sameOutcomeProbability (threeSettingAngle i) (threeSettingAngle i) = 1 :=
  sameOutcomeProbability_equal_setting (threeSettingAngle i)

end

end Bell
end Deutsch
