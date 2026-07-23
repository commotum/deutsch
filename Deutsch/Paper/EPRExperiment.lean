import Deutsch.EPR.Circuit
import Deutsch.EPR.Statistics
import Deutsch.Information.Qubit

/-!
# Paper façade: the EPR experiment

Source-shaped entries for Equations (22)--(27).  The literal four-wire comparison result in
Equation (28) is supplied by the dedicated record-statistics bridge and is intentionally not
duplicated here.
-/

namespace Deutsch
namespace Paper

open Foundations Information Register
open scoped Matrix

noncomputable section

/--
Equation (22): the source-labelled EPR ket agrees with the exact inverse-Bell preparation up to
the displayed global phase.
-/
theorem equation22 :
    EPR.equation22Ket = (-Complex.I) • EPR.pairKet :=
  EPR.equation22Ket_eq_globalPhase

/-- Equation (23): both descriptors of the inverse-Bell EPR resource. -/
theorem equation23 :
    EPR.timeOneDescriptors EPR.q2 =
        { x := xAt EPR.q2
          y := -(yAt EPR.q2 * xAt EPR.q3)
          z := -(zAt EPR.q2 * xAt EPR.q3) } ∧
      EPR.timeOneDescriptors EPR.q3 =
        { x := xAt EPR.q2 * zAt EPR.q3
          y := -(xAt EPR.q2 * yAt EPR.q3)
          z := xAt EPR.q3 } :=
  ⟨EPR.equation23_q2, EPR.equation23_q3⟩

/-- Equation (24): the two record wires are unchanged through the EPR setting layer. -/
theorem equation24 (theta phi : ℝ) :
    EPR.timeTwoDescriptors theta phi EPR.q1 = Descriptor.initial EPR.q1 ∧
      EPR.timeTwoDescriptors theta phi EPR.q4 = Descriptor.initial EPR.q4 :=
  ⟨EPR.equation24_q1 theta phi, EPR.equation24_q4 theta phi⟩

/-- Equation (25): both setting-dependent EPR descriptors at time two. -/
theorem equation25 (theta phi : ℝ) :
    EPR.timeTwoDescriptors theta phi EPR.q2 =
        { x := xAt EPR.q2
          y := (theta.cos : ℂ) • (-(yAt EPR.q2 * xAt EPR.q3)) -
            (theta.sin : ℂ) • (-(zAt EPR.q2 * xAt EPR.q3))
          z := (theta.sin : ℂ) • (-(yAt EPR.q2 * xAt EPR.q3)) +
            (theta.cos : ℂ) • (-(zAt EPR.q2 * xAt EPR.q3)) } ∧
      EPR.timeTwoDescriptors theta phi EPR.q3 =
        { x := xAt EPR.q2 * zAt EPR.q3
          y := (phi.cos : ℂ) • (-(xAt EPR.q2 * yAt EPR.q3)) -
            (phi.sin : ℂ) • xAt EPR.q3
          z := (phi.sin : ℂ) • (-(xAt EPR.q2 * yAt EPR.q3)) +
            (phi.cos : ℂ) • xAt EPR.q3 } :=
  ⟨EPR.equation25_q2 theta phi, EPR.equation25_q3 theta phi⟩

@[simp] private theorem densityExpectation_add
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (rho : Density Q) (A B : Operator Q) :
    densityExpectation rho (A + B) =
      densityExpectation rho A + densityExpectation rho B := by
  simp [densityExpectation, Matrix.mul_add, Matrix.trace_add]

@[simp] private theorem densityExpectation_sub
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (rho : Density Q) (A B : Operator Q) :
    densityExpectation rho (A - B) =
      densityExpectation rho A - densityExpectation rho B := by
  simp [densityExpectation, Matrix.mul_sub, Matrix.trace_sub]

@[simp] private theorem densityExpectation_smul
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (rho : Density Q) (c : ℂ) (A : Operator Q) :
    densityExpectation rho (c • A) =
      c * densityExpectation rho A := by
  simp [densityExpectation, Matrix.trace_smul]

@[simp] private theorem densityExpectation_neg
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    (rho : Density Q) (A : Operator Q) :
    densityExpectation rho (-A) = -densityExpectation rho A := by
  simp [densityExpectation, Matrix.mul_neg, Matrix.trace_neg]

private theorem referenceExpectation_xAt (q : EPR.EPRQubit) :
    densityExpectation (referenceDensity EPR.EPRQubit) (xAt q) = 0 := by
  rw [referenceDensity_expectation, referenceKet, basisKet_expectation]
  rw [xAt, embedQubit_apply_ite, if_pos]
  · simp [paperZeroAssignment, pauliX]
  · intro r hr
    exact rfl

private theorem referenceExpectation_y_mul_x
    (q r : EPR.EPRQubit) (hne : q ≠ r) :
    densityExpectation (referenceDensity EPR.EPRQubit)
        (yAt q * xAt r) = 0 := by
  rw [referenceDensity_expectation, referenceKet, basisKet_expectation]
  change
    (embedQubit q pauliY * embedQubit r pauliX)
      (paperZeroAssignment EPR.EPRQubit)
      (paperZeroAssignment EPR.EPRQubit) = 0
  rw [embedQubit_mul_embedQubit_apply_of_ne hne]
  simp [paperZeroAssignment, yAt, xAt, pauliY, pauliX]

private theorem referenceExpectation_z_mul_x
    (q r : EPR.EPRQubit) (hne : q ≠ r) :
    densityExpectation (referenceDensity EPR.EPRQubit)
        (zAt q * xAt r) = 0 := by
  rw [referenceDensity_expectation, referenceKet, basisKet_expectation]
  change
    (embedQubit q pauliZ * embedQubit r pauliX)
      (paperZeroAssignment EPR.EPRQubit)
      (paperZeroAssignment EPR.EPRQubit) = 0
  rw [embedQubit_mul_embedQubit_apply_of_ne hne]
  simp [paperZeroAssignment, zAt, xAt, pauliZ, pauliX]

/--
Equation (26): the fixed-reference expectations of the three displayed time-two descriptor
components of `q2` vanish.
-/
theorem equation26 (theta phi : ℝ) :
    densityExpectation (referenceDensity EPR.EPRQubit)
          (EPR.timeTwoDescriptors theta phi EPR.q2).x = 0 ∧
      densityExpectation (referenceDensity EPR.EPRQubit)
          (EPR.timeTwoDescriptors theta phi EPR.q2).y = 0 ∧
      densityExpectation (referenceDensity EPR.EPRQubit)
          (EPR.timeTwoDescriptors theta phi EPR.q2).z = 0 := by
  constructor
  · rw [EPR.timeTwo_q2_x, referenceExpectation_xAt]
  constructor
  · rw [EPR.timeTwo_q2_y, densityExpectation_sub,
      densityExpectation_smul, densityExpectation_smul,
      densityExpectation_neg, densityExpectation_neg,
      referenceExpectation_y_mul_x EPR.q2 EPR.q3 EPR.q2_ne_q3,
      referenceExpectation_z_mul_x EPR.q2 EPR.q3 EPR.q2_ne_q3]
    simp
  · rw [EPR.timeTwo_q2_z, densityExpectation_add,
      densityExpectation_smul, densityExpectation_smul,
      densityExpectation_neg, densityExpectation_neg,
      referenceExpectation_y_mul_x EPR.q2 EPR.q3 EPR.q2_ne_q3,
      referenceExpectation_z_mul_x EPR.q2 EPR.q3 EPR.q2_ne_q3]
    simp

private theorem equation27_q1_expanded (theta phi : ℝ) :
    EPR.timeThreeDescriptors theta phi EPR.q1 =
      { x := xAt EPR.q1
        y := yAt EPR.q1 *
            (((Real.cos theta : ℂ) • zAt EPR.q2 +
              (Real.sin theta : ℂ) • yAt EPR.q2) * xAt EPR.q3)
        z := zAt EPR.q1 *
            (((Real.cos theta : ℂ) • zAt EPR.q2 +
              (Real.sin theta : ℂ) • yAt EPR.q2) * xAt EPR.q3) } := by
  rw [EPR.equation27_q1, EPR.equation24_q1, EPR.equation25_q2]
  apply Descriptor.ext_components <;> simp only
  · rfl
  · simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    trace_state
    module
  · simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_neg, Matrix.neg_mul, neg_neg]
    module

/-- Equation (27): all four descriptors after the two local coherent records. -/
theorem equation27 (theta phi : ℝ) :
    EPR.timeThreeDescriptors theta phi EPR.q1 =
        { x := (EPR.timeTwoDescriptors theta phi EPR.q1).x
          y := -((EPR.timeTwoDescriptors theta phi EPR.q1).y *
            (EPR.timeTwoDescriptors theta phi EPR.q2).z)
          z := -((EPR.timeTwoDescriptors theta phi EPR.q1).z *
            (EPR.timeTwoDescriptors theta phi EPR.q2).z) } ∧
      EPR.timeThreeDescriptors theta phi EPR.q2 =
        { x := (EPR.timeTwoDescriptors theta phi EPR.q1).x *
            (EPR.timeTwoDescriptors theta phi EPR.q2).x
          y := (EPR.timeTwoDescriptors theta phi EPR.q1).x *
            (EPR.timeTwoDescriptors theta phi EPR.q2).y
          z := (EPR.timeTwoDescriptors theta phi EPR.q2).z } ∧
      EPR.timeThreeDescriptors theta phi EPR.q3 =
        { x := (EPR.timeTwoDescriptors theta phi EPR.q4).x *
            (EPR.timeTwoDescriptors theta phi EPR.q3).x
          y := (EPR.timeTwoDescriptors theta phi EPR.q4).x *
            (EPR.timeTwoDescriptors theta phi EPR.q3).y
          z := (EPR.timeTwoDescriptors theta phi EPR.q3).z } ∧
      EPR.timeThreeDescriptors theta phi EPR.q4 =
        { x := (EPR.timeTwoDescriptors theta phi EPR.q4).x
          y := -((EPR.timeTwoDescriptors theta phi EPR.q4).y *
            (EPR.timeTwoDescriptors theta phi EPR.q3).z)
          z := -((EPR.timeTwoDescriptors theta phi EPR.q4).z *
            (EPR.timeTwoDescriptors theta phi EPR.q3).z) } := by
  exact ⟨EPR.equation27_q1 theta phi, EPR.equation27_q2 theta phi,
    EPR.equation27_q3 theta phi, EPR.equation27_q4 theta phi⟩

end
end Paper
end Deutsch
