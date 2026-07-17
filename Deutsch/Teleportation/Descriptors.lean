import Deutsch.Teleportation.Circuit
import Deutsch.Teleportation.Correction
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# Teleportation descriptors after correction and verification

This module instantiates Equation (33) on record wires `q2,q3` and receiver `q5`, then derives
the receiver descriptors at time four.  The sine-sign correction established in Equation (29)
propagates to Equation (34).  The final verification rotation likewise gives Equation (37) with
the middle `cos θ sin θ` contribution opposite to the sign printed in the source.
-/

namespace Deutsch
namespace Teleportation

open Foundations Gates Locality Register
open scoped Matrix

noncomputable section

/-- Equation (33) instantiated on the two coherent records and the receiver. -/
def teleportCorrectionGate : Operator TeleportQubit :=
  correctionGate q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5

/-- Full coherent teleportation circuit through the correction at time four. -/
def timeFourUnitary (theta : Real) : Operator TeleportQubit :=
  teleportCorrectionGate * timeThreeUnitary theta

theorem teleportCorrectionGate_unitary :
    teleportCorrectionGate ∈
      Matrix.unitaryGroup (Basis TeleportQubit) Complex :=
  correctionGate_unitary q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5

theorem teleportCorrectionGate_isSupportedOn :
    IsSupportedOn ({q2, q3, q5} : Finset TeleportQubit)
      teleportCorrectionGate :=
  correctionGate_isSupportedOn_triple
    q2 q3 q5 q2_ne_q3 q2_ne_q5 q3_ne_q5

theorem timeFourUnitary_unitary (theta : Real) :
    timeFourUnitary theta ∈
      Matrix.unitaryGroup (Basis TeleportQubit) Complex := by
  exact (Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
    teleportCorrectionGate_unitary (timeThreeUnitary_unitary theta)

theorem timeFourUnitary_isSupportedOn (theta : Real) :
    IsSupportedOn ({q1, q2, q3, q4, q5} : Finset TeleportQubit)
      (timeFourUnitary theta) := by
  exact (teleportCorrectionGate_isSupportedOn.mono (by decide)).mul
    (timeThreeUnitary_isSupportedOn theta)

def timeFourDescriptors (theta : Real) : DescriptorFamily TeleportQubit :=
  DescriptorFamily.evolve (timeFourUnitary theta)
    (DescriptorFamily.initial TeleportQubit)

private theorem bellMeasurementGate_fixes_q5 (A : QubitMatrix) :
    heisenberg bellMeasurementGate (embedQubit q5 A) = embedQubit q5 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) bellMeasurementGate_unitary bellMeasurementGate_isSupportedOn
    (embedQubit_isSupportedOn q5 A)

private theorem q1RecordingGate_fixes_q5 (A : QubitMatrix) :
    heisenberg q1RecordingGate (embedQubit q5 A) = embedQubit q5 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) q1RecordingGate_unitary q1RecordingGate_isSupportedOn
    (embedQubit_isSupportedOn q5 A)

private theorem q4RecordingGate_fixes_q5 (A : QubitMatrix) :
    heisenberg q4RecordingGate (embedQubit q5 A) = embedQubit q5 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) q4RecordingGate_unitary q4RecordingGate_isSupportedOn
    (embedQubit_isSupportedOn q5 A)

private theorem recordingLayer_fixes_q5 (A : QubitMatrix) :
    heisenberg recordingLayer (embedQubit q5 A) = embedQubit q5 A := by
  rw [recordingLayer, heisenberg_chronology]
  rw [q4RecordingGate_fixes_q5]
  exact q1RecordingGate_fixes_q5 A

private theorem timeThree_heisenberg_q5_x (theta : Real) :
    heisenberg (timeThreeUnitary theta) (xAt q5) = xAt q4 * zAt q5 := by
  rw [timeThreeUnitary, heisenberg_chronology]
  rw [show heisenberg recordingLayer (xAt q5) = xAt q5 by
    simpa [xAt] using recordingLayer_fixes_q5 pauliX]
  rw [timeTwoUnitary, heisenberg_chronology]
  rw [show heisenberg bellMeasurementGate (xAt q5) = xAt q5 by
    simpa [xAt] using bellMeasurementGate_fixes_q5 pauliX]
  simpa [timeOneDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
    DescriptorFamily.initial, Descriptor.initial] using timeOne_q5_x theta

private theorem timeThree_heisenberg_q5_y (theta : Real) :
    heisenberg (timeThreeUnitary theta) (yAt q5) = -(xAt q4 * yAt q5) := by
  rw [timeThreeUnitary, heisenberg_chronology]
  rw [show heisenberg recordingLayer (yAt q5) = yAt q5 by
    simpa [yAt] using recordingLayer_fixes_q5 pauliY]
  rw [timeTwoUnitary, heisenberg_chronology]
  rw [show heisenberg bellMeasurementGate (yAt q5) = yAt q5 by
    simpa [yAt] using bellMeasurementGate_fixes_q5 pauliY]
  simpa [timeOneDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
    DescriptorFamily.initial, Descriptor.initial] using timeOne_q5_y theta

private theorem timeThree_heisenberg_q5_z (theta : Real) :
    heisenberg (timeThreeUnitary theta) (zAt q5) = xAt q5 := by
  rw [timeThreeUnitary, heisenberg_chronology]
  rw [show heisenberg recordingLayer (zAt q5) = zAt q5 by
    simpa [zAt] using recordingLayer_fixes_q5 pauliZ]
  rw [timeTwoUnitary, heisenberg_chronology]
  rw [show heisenberg bellMeasurementGate (zAt q5) = zAt q5 by
    simpa [zAt] using bellMeasurementGate_fixes_q5 pauliZ]
  simpa [timeOneDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
    DescriptorFamily.initial, Descriptor.initial] using timeOne_q5_z theta

private theorem timeThree_heisenberg_q2_z (theta : Real) :
    heisenberg (timeThreeUnitary theta) (zAt q2) =
      (-((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1)) * zAt q2 *
          (zAt q4 * xAt q5) := by
  simpa [timeThreeDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
    DescriptorFamily.initial, Descriptor.initial] using timeThree_q2_z theta

private theorem timeThree_heisenberg_q3_z (theta : Real) :
    heisenberg (timeThreeUnitary theta) (zAt q3) =
      -(xAt q1 * zAt q3 * xAt q4) := by
  simpa [timeThreeDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
    DescriptorFamily.initial, Descriptor.initial] using timeThree_q3_z theta

/-! ## Corrected Equation (34) -/

theorem timeFour_q5_x (theta : Real) :
    (timeFourDescriptors theta q5).x =
      xAt q1 * zAt q3 * zAt q5 := by
  change heisenberg (timeFourUnitary theta) (xAt q5) = _
  rw [timeFourUnitary, heisenberg_chronology, teleportCorrectionGate,
    equation33_m_x, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeThreeUnitary_unitary theta),
    timeThree_heisenberg_q3_z, timeThree_heisenberg_q5_x]
  simp only [neg_mul, neg_neg]
  rw [Matrix.mul_assoc (xAt q1 * zAt q3) (xAt q4)
      (xAt q4 * zAt q5),
    ← Matrix.mul_assoc (xAt q4) (xAt q4) (zAt q5),
    xAt_mul_xAt, Matrix.one_mul]

theorem timeFour_q5_z (theta : Real) :
    (timeFourDescriptors theta q5).z =
      ((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1) * zAt q2 * zAt q4 := by
  change heisenberg (timeFourUnitary theta) (zAt q5) = _
  rw [timeFourUnitary, heisenberg_chronology, teleportCorrectionGate,
    equation33_m_z, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeThreeUnitary_unitary theta),
    timeThree_heisenberg_q2_z, timeThree_heisenberg_q5_z]
  simp only [neg_mul, neg_neg]
  rw [Matrix.mul_assoc
      (((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1) * zAt q2)
      (zAt q4 * xAt q5) (xAt q5),
    Matrix.mul_assoc (zAt q4) (xAt q5) (xAt q5),
    xAt_mul_xAt, Matrix.mul_one]

private theorem input_z_combination_mul_x (theta : Real) :
    ((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1) * xAt q1 =
      Complex.I • ((theta.cos : Complex) • yAt q1 -
        (theta.sin : Complex) • zAt q1) := by
  rw [Matrix.add_mul, Matrix.smul_mul, Matrix.smul_mul,
    yAt_mul_xAt, zAt_mul_xAt]
  module

theorem timeFour_q5_y (theta : Real) :
    (timeFourDescriptors theta q5).y =
      ((theta.cos : Complex) • yAt q1 -
        (theta.sin : Complex) • zAt q1) *
          zAt q2 * zAt q3 * zAt q4 * zAt q5 := by
  change heisenberg (timeFourUnitary theta) (yAt q5) = _
  rw [timeFourUnitary, heisenberg_chronology, teleportCorrectionGate,
    equation33_m_y,
    heisenberg_mul_of_unitary _ _ _ (timeThreeUnitary_unitary theta),
    heisenberg_mul_of_unitary _ _ _ (timeThreeUnitary_unitary theta),
    timeThree_heisenberg_q2_z, timeThree_heisenberg_q3_z,
    timeThree_heisenberg_q5_y]
  have h_z2_x1 : zAt q2 * xAt q1 = xAt q1 * zAt q2 := by
    simpa [zAt, xAt] using
      embedQubit_commute_of_ne q2_ne_q1 pauliZ pauliX
  have h_z4_x1 : zAt q4 * xAt q1 = xAt q1 * zAt q4 := by
    simpa [zAt, xAt] using
      embedQubit_commute_of_ne q4_ne_q1 pauliZ pauliX
  have h_x5_x1 : xAt q5 * xAt q1 = xAt q1 * xAt q5 := by
    simpa [xAt] using
      embedQubit_commute_of_ne q5_ne_q1 pauliX pauliX
  have h_z4_z3 : zAt q4 * zAt q3 = zAt q3 * zAt q4 := by
    simpa [zAt] using
      embedQubit_commute_of_ne q4_ne_q3 pauliZ pauliZ
  have h_x5_z3 : xAt q5 * zAt q3 = zAt q3 * xAt q5 := by
    simpa [xAt, zAt] using
      embedQubit_commute_of_ne q5_ne_q3 pauliX pauliZ
  have h_x5_x4 : xAt q5 * xAt q4 = xAt q4 * xAt q5 := by
    simpa [xAt] using
      embedQubit_commute_of_ne q5_ne_q4 pauliX pauliX
  have move_z2_x1 (T : Operator TeleportQubit) :
      zAt q2 * (xAt q1 * T) = xAt q1 * (zAt q2 * T) := by
    rw [← Matrix.mul_assoc, h_z2_x1, Matrix.mul_assoc]
  have move_z4_x1 (T : Operator TeleportQubit) :
      zAt q4 * (xAt q1 * T) = xAt q1 * (zAt q4 * T) := by
    rw [← Matrix.mul_assoc, h_z4_x1, Matrix.mul_assoc]
  have move_x5_x1 (T : Operator TeleportQubit) :
      xAt q5 * (xAt q1 * T) = xAt q1 * (xAt q5 * T) := by
    rw [← Matrix.mul_assoc, h_x5_x1, Matrix.mul_assoc]
  have move_z4_z3 (T : Operator TeleportQubit) :
      zAt q4 * (zAt q3 * T) = zAt q3 * (zAt q4 * T) := by
    rw [← Matrix.mul_assoc, h_z4_z3, Matrix.mul_assoc]
  have move_x5_z3 (T : Operator TeleportQubit) :
      xAt q5 * (zAt q3 * T) = zAt q3 * (xAt q5 * T) := by
    rw [← Matrix.mul_assoc, h_x5_z3, Matrix.mul_assoc]
  have move_x5_x4 (T : Operator TeleportQubit) :
      xAt q5 * (xAt q4 * T) = xAt q4 * (xAt q5 * T) := by
    rw [← Matrix.mul_assoc, h_x5_x4, Matrix.mul_assoc]
  have hreorder :
      (((((theta.sin : Complex) • yAt q1 +
          (theta.cos : Complex) • zAt q1) * zAt q2 *
            (zAt q4 * xAt q5)) *
          (xAt q1 * zAt q3 * xAt q4)) *
        (xAt q4 * yAt q5)) =
      ((((((theta.sin : Complex) • yAt q1 +
          (theta.cos : Complex) • zAt q1) * xAt q1) * zAt q2) *
        zAt q3) * zAt q4) *
          ((xAt q4 * xAt q4) * (xAt q5 * yAt q5)) := by
    simp only [Matrix.mul_assoc]
    rw [move_x5_x1, move_z4_x1, move_z2_x1,
      move_x5_z3, move_z4_z3, move_x5_x4, move_x5_x4]
  simp only [neg_mul, mul_neg, neg_neg]
  rw [hreorder, input_z_combination_mul_x,
    xAt_mul_xAt, xAt_mul_yAt]
  simp only [Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, Complex.I_mul_I, neg_smul, neg_neg, one_smul]

/-- Equation (34), corrected by the sine signs already forced in Equation (29). -/
theorem equation34_q5 (theta : Real) :
    timeFourDescriptors theta q5 =
      { x := xAt q1 * zAt q3 * zAt q5
        y := ((theta.cos : Complex) • yAt q1 -
          (theta.sin : Complex) • zAt q1) *
            zAt q2 * zAt q3 * zAt q4 * zAt q5
        z := ((theta.sin : Complex) • yAt q1 +
          (theta.cos : Complex) • zAt q1) * zAt q2 * zAt q4 } := by
  apply Descriptor.ext_components
  · exact timeFour_q5_x theta
  · exact timeFour_q5_y theta
  · exact timeFour_q5_z theta

private theorem neg_unitary_ne_self_descriptor
    (A : Operator TeleportQubit)
    (hA : A ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex) :
    -A ≠ A := by
  intro h
  have hAA : A * Aᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hA.2
  have hcancel := congrArg (fun M : Operator TeleportQubit ↦ M * Aᴴ) h
  rw [neg_mul, hAA] at hcancel
  have hentry := congrFun
    (congrFun hcancel (paperZeroAssignment TeleportQubit))
    (paperZeroAssignment TeleportQubit)
  norm_num [Matrix.one_apply] at hentry

/-- At `θ = π/2`, Equation (34)'s printed `q5.y` has the opposite propagated sign. -/
theorem equation34_q5_y_pi_div_two_ne_printed :
    (timeFourDescriptors (Real.pi / 2) q5).y ≠
      zAt q1 * zAt q2 * zAt q3 * zAt q4 * zAt q5 := by
  rw [timeFour_q5_y]
  simpa using neg_unitary_ne_self_descriptor
    (zAt q1 * zAt q2 * zAt q3 * zAt q4 * zAt q5)
    ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
      ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
        ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
          ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
            (zAt_unitary q1) (zAt_unitary q2))
          (zAt_unitary q3))
        (zAt_unitary q4))
      (zAt_unitary q5))

/-! ## Corrected Equation (37) -/

/-- The receiver-side inverse rotation used to verify the teleported angle. -/
def verificationRotation (theta : Real) : Operator TeleportQubit :=
  rotationXAt q5 (-theta)

/-- Full coherent teleportation circuit through the final verification rotation. -/
def timeFiveUnitary (theta : Real) : Operator TeleportQubit :=
  verificationRotation theta * timeFourUnitary theta

theorem verificationRotation_unitary (theta : Real) :
    verificationRotation theta ∈
      Matrix.unitaryGroup (Basis TeleportQubit) Complex := by
  exact rotationXAt_unitary q5 (-theta)

theorem verificationRotation_isSupportedOn (theta : Real) :
    IsSupportedOn ({q5} : Finset TeleportQubit)
      (verificationRotation theta) :=
  rotationXAt_isSupportedOn q5 (-theta)

theorem timeFiveUnitary_unitary (theta : Real) :
    timeFiveUnitary theta ∈
      Matrix.unitaryGroup (Basis TeleportQubit) Complex := by
  exact (Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
    (verificationRotation_unitary theta) (timeFourUnitary_unitary theta)

theorem timeFiveUnitary_isSupportedOn (theta : Real) :
    IsSupportedOn ({q1, q2, q3, q4, q5} : Finset TeleportQubit)
      (timeFiveUnitary theta) := by
  exact ((verificationRotation_isSupportedOn theta).mono (by decide)).mul
    (timeFourUnitary_isSupportedOn theta)

def timeFiveDescriptors (theta : Real) : DescriptorFamily TeleportQubit :=
  DescriptorFamily.evolve (timeFiveUnitary theta)
    (DescriptorFamily.initial TeleportQubit)

private theorem timeFour_heisenberg_q5_y (theta : Real) :
    heisenberg (timeFourUnitary theta) (yAt q5) =
      ((theta.cos : Complex) • yAt q1 -
        (theta.sin : Complex) • zAt q1) *
          zAt q2 * zAt q3 * zAt q4 * zAt q5 := by
  simpa [timeFourDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
    DescriptorFamily.initial, Descriptor.initial] using timeFour_q5_y theta

private theorem timeFour_heisenberg_q5_z (theta : Real) :
    heisenberg (timeFourUnitary theta) (zAt q5) =
      ((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1) * zAt q2 * zAt q4 := by
  simpa [timeFourDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
    DescriptorFamily.initial, Descriptor.initial] using timeFour_q5_z theta

private theorem timeFive_q5_z_expanded (theta : Real) :
    (timeFiveDescriptors theta q5).z =
      ((theta.cos : Complex) * theta.cos) •
          (zAt q1 * zAt q2 * zAt q4) -
        ((theta.cos : Complex) * theta.sin) •
          (yAt q1 * zAt q2 * zAt q3 * zAt q4 * zAt q5) +
        ((theta.cos : Complex) * theta.sin) •
          (yAt q1 * zAt q2 * zAt q4) +
        ((theta.sin : Complex) * theta.sin) •
          (zAt q1 * zAt q2 * zAt q3 * zAt q4 * zAt q5) := by
  change heisenberg (timeFiveUnitary theta) (zAt q5) = _
  rw [timeFiveUnitary, heisenberg_chronology, verificationRotation,
    rotationXAt_heisenberg_z, heisenberg_add,
    heisenberg_smul, heisenberg_smul,
    timeFour_heisenberg_q5_y, timeFour_heisenberg_q5_z]
  simp only [Real.sin_neg, Real.cos_neg, Complex.ofReal_neg,
    Matrix.sub_mul, Matrix.add_mul, Matrix.smul_mul,
    smul_sub, smul_add, smul_smul]
  module

private theorem zAt_q3_mul_zAt_q5_ne_one :
    zAt q3 * zAt q5 ≠ (1 : Operator TeleportQubit) := by
  intro h
  have hremote : xAt q3 * zAt q5 = zAt q5 * xAt q3 := by
    simpa [xAt, zAt] using
      embedQubit_commute_of_ne q3_ne_q5 pauliX pauliZ
  have hanti :
      xAt q3 * (zAt q3 * zAt q5) =
        -((zAt q3 * zAt q5) * xAt q3) := by
    calc
      xAt q3 * (zAt q3 * zAt q5) =
          (xAt q3 * zAt q3) * zAt q5 := by
            rw [Matrix.mul_assoc]
      _ = (-Complex.I • yAt q3) * zAt q5 := by
            rw [xAt_mul_zAt]
      _ = -((Complex.I • yAt q3) * zAt q5) := by
            simp only [neg_smul, Matrix.neg_mul, Matrix.smul_mul]
      _ = -((zAt q3 * xAt q3) * zAt q5) := by
            rw [zAt_mul_xAt]
      _ = -(zAt q3 * (xAt q3 * zAt q5)) := by
            rw [Matrix.mul_assoc]
      _ = -(zAt q3 * (zAt q5 * xAt q3)) := by rw [hremote]
      _ = -((zAt q3 * zAt q5) * xAt q3) := by
            rw [Matrix.mul_assoc]
  rw [h] at hanti
  simp only [Matrix.mul_one, Matrix.one_mul] at hanti
  exact neg_unitary_ne_self_descriptor (xAt q3) (xAt_unitary q3) hanti.symm

private theorem equation37_middle_operator_ne_zero :
    yAt q1 * zAt q2 *
        (zAt q3 * zAt q4 * zAt q5 - zAt q4) ≠ 0 := by
  intro hzero
  have h43 : zAt q4 * zAt q3 = zAt q3 * zAt q4 := by
    simpa [zAt] using
      embedQubit_commute_of_ne q4_ne_q3 pauliZ pauliZ
  have hmove :
      zAt q3 * (zAt q4 * zAt q5) =
        zAt q4 * (zAt q3 * zAt q5) := by
    calc
      zAt q3 * (zAt q4 * zAt q5) =
          (zAt q3 * zAt q4) * zAt q5 :=
        (Matrix.mul_assoc _ _ _).symm
      _ = (zAt q4 * zAt q3) * zAt q5 := by rw [h43]
      _ = zAt q4 * (zAt q3 * zAt q5) := Matrix.mul_assoc _ _ _
  have hfactor :
      yAt q1 * zAt q2 *
          (zAt q3 * zAt q4 * zAt q5 - zAt q4) =
        (yAt q1 * zAt q2 * zAt q4) *
          (zAt q3 * zAt q5 - 1) := by
    rw [Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
    rw [hmove]
  rw [hfactor] at hzero
  have hU : yAt q1 * zAt q2 * zAt q4 ∈
      Matrix.unitaryGroup (Basis TeleportQubit) Complex :=
    (Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
      ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
        (yAt_unitary q1) (zAt_unitary q2))
      (zAt_unitary q4)
  have hUstar :
      (yAt q1 * zAt q2 * zAt q4)ᴴ *
          (yAt q1 * zAt q2 * zAt q4) = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hU.1
  have hcancel := congrArg
    (fun M : Operator TeleportQubit ↦
      (yAt q1 * zAt q2 * zAt q4)ᴴ * M)
    hzero
  rw [← Matrix.mul_assoc, hUstar, Matrix.one_mul, Matrix.mul_zero] at hcancel
  exact zAt_q3_mul_zAt_q5_ne_one (sub_eq_zero.mp hcancel)

/-- Corrected Equation (37): the displayed middle term in the source has the other sign. -/
theorem timeFive_q5_z (theta : Real) :
    (timeFiveDescriptors theta q5).z =
      ((theta.cos : Complex) * theta.cos) •
          (zAt q1 * zAt q2 * zAt q4) -
        ((theta.cos : Complex) * theta.sin) •
          (yAt q1 * zAt q2 *
            (zAt q3 * zAt q4 * zAt q5 - zAt q4)) +
        ((theta.sin : Complex) * theta.sin) •
          (zAt q1 * zAt q2 * zAt q3 * zAt q4 * zAt q5) := by
  rw [timeFive_q5_z_expanded]
  simp only [Matrix.mul_sub, smul_sub, Matrix.mul_assoc]
  module

private theorem timeFive_q5_z_ne_printed_of_middle_coefficient_ne_zero
    (theta : Real)
    (hcoefficient :
      (theta.cos : Complex) * theta.sin ≠ 0) :
    (timeFiveDescriptors theta q5).z ≠
      ((theta.cos : Complex) * theta.cos) •
          (zAt q1 * zAt q2 * zAt q4) +
        ((theta.cos : Complex) * theta.sin) •
          (yAt q1 * zAt q2 *
            (zAt q3 * zAt q4 * zAt q5 - zAt q4)) +
        ((theta.sin : Complex) * theta.sin) •
          (zAt q1 * zAt q2 * zAt q3 * zAt q4 * zAt q5) := by
  rw [timeFive_q5_z]
  intro h
  have hwithoutLast :
      ((theta.cos : Complex) * theta.cos) •
            (zAt q1 * zAt q2 * zAt q4) -
          ((theta.cos : Complex) * theta.sin) •
            (yAt q1 * zAt q2 *
              (zAt q3 * zAt q4 * zAt q5 - zAt q4)) =
        ((theta.cos : Complex) * theta.cos) •
            (zAt q1 * zAt q2 * zAt q4) +
          ((theta.cos : Complex) * theta.sin) •
            (yAt q1 * zAt q2 *
              (zAt q3 * zAt q4 * zAt q5 - zAt q4)) :=
    add_right_cancel h
  rw [sub_eq_add_neg] at hwithoutLast
  have hmiddleSign :
      -(((theta.cos : Complex) * theta.sin) •
          (yAt q1 * zAt q2 *
            (zAt q3 * zAt q4 * zAt q5 - zAt q4))) =
        ((theta.cos : Complex) * theta.sin) •
          (yAt q1 * zAt q2 *
            (zAt q3 * zAt q4 * zAt q5 - zAt q4)) :=
    add_left_cancel hwithoutLast
  have htwice :
      (2 : Complex) •
          (((theta.cos : Complex) * theta.sin) •
            (yAt q1 * zAt q2 *
              (zAt q3 * zAt q4 * zAt q5 - zAt q4))) = 0 := by
    rw [two_smul]
    calc
      _ = -(((theta.cos : Complex) * theta.sin) •
              (yAt q1 * zAt q2 *
                (zAt q3 * zAt q4 * zAt q5 - zAt q4))) +
            ((theta.cos : Complex) * theta.sin) •
              (yAt q1 * zAt q2 *
                (zAt q3 * zAt q4 * zAt q5 - zAt q4)) := by
          exact congrArg
            (fun M : Operator TeleportQubit ↦
              M + ((theta.cos : Complex) * theta.sin) •
                (yAt q1 * zAt q2 *
                  (zAt q3 * zAt q4 * zAt q5 - zAt q4)))
            hmiddleSign.symm
      _ = 0 := neg_add_cancel _
  have hcoefficientTimesMiddle :
      ((theta.cos : Complex) * theta.sin) •
          (yAt q1 * zAt q2 *
            (zAt q3 * zAt q4 * zAt q5 - zAt q4)) = 0 :=
    (smul_eq_zero.mp htwice).resolve_left (by norm_num)
  have hmiddle :
      yAt q1 * zAt q2 *
          (zAt q3 * zAt q4 * zAt q5 - zAt q4) = 0 :=
    (smul_eq_zero.mp hcoefficientTimesMiddle).resolve_left hcoefficient
  exact equation37_middle_operator_ne_zero hmiddle

/-- At `θ = π/4`, corrected Equation (37) is unequal to its printed middle-sign form. -/
theorem equation37_q5_z_pi_div_four_ne_printed :
    (timeFiveDescriptors (Real.pi / 4) q5).z ≠
      ((Real.cos (Real.pi / 4) : Complex) * Real.cos (Real.pi / 4)) •
          (zAt q1 * zAt q2 * zAt q4) +
        ((Real.cos (Real.pi / 4) : Complex) * Real.sin (Real.pi / 4)) •
          (yAt q1 * zAt q2 *
            (zAt q3 * zAt q4 * zAt q5 - zAt q4)) +
        ((Real.sin (Real.pi / 4) : Complex) * Real.sin (Real.pi / 4)) •
          (zAt q1 * zAt q2 * zAt q3 * zAt q4 * zAt q5) := by
  apply timeFive_q5_z_ne_printed_of_middle_coefficient_ne_zero
  rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
  have hsqrt : Real.sqrt 2 ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  exact mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (div_ne_zero hsqrt (by norm_num)))
    (Complex.ofReal_ne_zero.mpr (div_ne_zero hsqrt (by norm_num)))

end
end Teleportation
end Deutsch
