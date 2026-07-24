import Deutsch.Gates.AxisRotation

/-!
# Equation (18) orientation check

This module keeps the two component formulas from the original printing local to the
errata library.  It compares them with the `x`-axis specialization of the genuine
matrix exponential proved in `Deutsch.Gates.AxisRotation`.
-/

namespace DeutschErrata
namespace Rotation

open Deutsch.Foundations Deutsch.Gates

noncomputable section

/-- The `Y` component as it appeared in the original printing of Equation (18). -/
def printedEquation18Y (theta : ℝ) : QubitMatrix :=
  (theta.cos : ℂ) • pauliY + (theta.sin : ℂ) • pauliZ

/-- The `Z` component as it appeared in the original printing of Equation (18). -/
def printedEquation18Z (theta : ℝ) : QubitMatrix :=
  (theta.cos : ℂ) • pauliZ - (theta.sin : ℂ) • pauliY

/--
The derived Equation (18) is packaged with its exponential origin: the genuine
unit-axis exponential specializes to `rotationX`, whose Heisenberg action has the
displayed `Y` and `Z` components.
-/
theorem derivedEquation18 (theta : ℝ) :
    NormedSpace.exp (axisRotationGenerator UnitAxis.xAxis theta) =
        axisRotation UnitAxis.xAxis theta ∧
      axisRotation UnitAxis.xAxis theta = rotationX theta ∧
      heisenberg (rotationX theta) pauliY =
        (theta.cos : ℂ) • pauliY - (theta.sin : ℂ) • pauliZ ∧
      heisenberg (rotationX theta) pauliZ =
        (theta.sin : ℂ) • pauliY + (theta.cos : ℂ) • pauliZ :=
  ⟨exp_axisRotationGenerator UnitAxis.xAxis theta,
    axisRotation_xAxis theta,
    rotationX_heisenberg_y theta,
    rotationX_heisenberg_z theta⟩

/--
At a quarter turn, both component signs are decided.  The derived exponential sends
`Y` to `-Z` and `Z` to `Y`, while the two locally recorded printed components evaluate
to `Z` and `-Y`, respectively.
-/
theorem equation18_pi_div_two_mismatch :
    heisenberg (rotationX (Real.pi / 2)) pauliY = -pauliZ ∧
      printedEquation18Y (Real.pi / 2) = pauliZ ∧
      heisenberg (rotationX (Real.pi / 2)) pauliY ≠
        printedEquation18Y (Real.pi / 2) ∧
      heisenberg (rotationX (Real.pi / 2)) pauliZ = pauliY ∧
      printedEquation18Z (Real.pi / 2) = -pauliY ∧
      heisenberg (rotationX (Real.pi / 2)) pauliZ ≠
        printedEquation18Z (Real.pi / 2) := by
  have hActualY :
      heisenberg (rotationX (Real.pi / 2)) pauliY = -pauliZ :=
    rotationX_heisenberg_y_pi_div_two
  have hActualZ :
      heisenberg (rotationX (Real.pi / 2)) pauliZ = pauliY :=
    rotationX_heisenberg_z_pi_div_two
  have hPrintedY :
      printedEquation18Y (Real.pi / 2) = pauliZ := by
    simp [printedEquation18Y]
  have hPrintedZ :
      printedEquation18Z (Real.pi / 2) = -pauliY := by
    simp [printedEquation18Z]
  have hY : (-pauliZ : QubitMatrix) ≠ pauliZ := by
    intro h
    have hEntry := congrArg (fun A : QubitMatrix => A 0 0) h
    norm_num [pauliZ] at hEntry
  have hZ : (pauliY : QubitMatrix) ≠ -pauliY := by
    intro h
    have hEntry := congrArg (fun A : QubitMatrix => A 0 1) h
    have hImaginary := congrArg Complex.im hEntry
    norm_num [pauliY] at hImaginary
  refine ⟨hActualY, hPrintedY, ?_, hActualZ, hPrintedZ, ?_⟩
  · rw [hActualY, hPrintedY]
    exact hY
  · rw [hActualZ, hPrintedZ]
    exact hZ

end
end Rotation
end DeutschErrata
