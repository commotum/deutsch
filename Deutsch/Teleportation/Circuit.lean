import Deutsch.Gates.Bell
import Deutsch.Locality.Heisenberg

/-!
# The five-qubit teleportation circuit through coherent recording

This module fixes the wires and the first three time slices of Figure 3.  Products are
Schrödinger chronological: the rightmost factor acts first.  The time-one input rotation and
resource preparation have disjoint support, as do the two time-three recording CNOTs, so their
chosen written orders do not impose a physical ordering.

The descriptor identities use the project's fixed `U† A U` Heisenberg convention.  Consequently,
Equation (29) has the corrected rotation components `Y ↦ cos θ Y - sin θ Z` and
`Z ↦ sin θ Y + cos θ Z`.  The same correction propagates to the `q1` components of
Equation (31) and the `q2` components of Equation (32).  Equation (30), the `q4` half of
Equation (31), and the `q3` half of Equation (32) agree with the source as printed.
-/

namespace Deutsch
namespace Teleportation

open Foundations Gates Locality Register
open scoped Matrix

noncomputable section

/-- The five wires in Figure 3, ordered from `q1` through `q5`. -/
abbrev TeleportQubit := Fin 5

def q1 : TeleportQubit := 0
def q2 : TeleportQubit := 1
def q3 : TeleportQubit := 2
def q4 : TeleportQubit := 3
def q5 : TeleportQubit := 4

@[simp] theorem q1_ne_q2 : q1 ≠ q2 := by decide
@[simp] theorem q1_ne_q3 : q1 ≠ q3 := by decide
@[simp] theorem q1_ne_q4 : q1 ≠ q4 := by decide
@[simp] theorem q1_ne_q5 : q1 ≠ q5 := by decide
@[simp] theorem q2_ne_q1 : q2 ≠ q1 := by decide
@[simp] theorem q2_ne_q3 : q2 ≠ q3 := by decide
@[simp] theorem q2_ne_q4 : q2 ≠ q4 := by decide
@[simp] theorem q2_ne_q5 : q2 ≠ q5 := by decide
@[simp] theorem q3_ne_q1 : q3 ≠ q1 := by decide
@[simp] theorem q3_ne_q2 : q3 ≠ q2 := by decide
@[simp] theorem q3_ne_q4 : q3 ≠ q4 := by decide
@[simp] theorem q3_ne_q5 : q3 ≠ q5 := by decide
@[simp] theorem q4_ne_q1 : q4 ≠ q1 := by decide
@[simp] theorem q4_ne_q2 : q4 ≠ q2 := by decide
@[simp] theorem q4_ne_q3 : q4 ≠ q3 := by decide
@[simp] theorem q4_ne_q5 : q4 ≠ q5 := by decide
@[simp] theorem q5_ne_q1 : q5 ≠ q1 := by decide
@[simp] theorem q5_ne_q2 : q5 ≠ q2 := by decide
@[simp] theorem q5_ne_q3 : q5 ≠ q3 := by decide
@[simp] theorem q5_ne_q4 : q5 ≠ q4 := by decide

/-! ## Schrödinger circuit chronology -/

/-- The unknown one-parameter input preparation on `q1`. -/
def inputRotation (theta : Real) : Operator TeleportQubit :=
  rotationXAt q1 theta

/-- The inverse-Bell resource preparation on `q4,q5`. -/
def resourcePreparation : Operator TeleportQubit :=
  bellInverseAt q4 q5 q4_ne_q5

/-- Full circuit through time one: input and resource are prepared in parallel. -/
def timeOneUnitary (theta : Real) : Operator TeleportQubit :=
  inputRotation theta * resourcePreparation

/-- The Bell operation on the input `q1` and the resource half `q4`. -/
def bellMeasurementGate : Operator TeleportQubit :=
  bellAt q1 q4 q1_ne_q4

/-- Full circuit through time two. -/
def timeTwoUnitary (theta : Real) : Operator TeleportQubit :=
  bellMeasurementGate * timeOneUnitary theta

/-- Coherently record the `q1` value in target `q2`. -/
def q1RecordingGate : Operator TeleportQubit :=
  cnotAt q2 q1 q2_ne_q1

/-- Coherently record the `q4` value in target `q3`. -/
def q4RecordingGate : Operator TeleportQubit :=
  cnotAt q3 q4 q3_ne_q4

/-- The two disjoint coherent records between times two and three. -/
def recordingLayer : Operator TeleportQubit :=
  q4RecordingGate * q1RecordingGate

/-- Full circuit through time three, immediately before the correction network. -/
def timeThreeUnitary (theta : Real) : Operator TeleportQubit :=
  recordingLayer * timeTwoUnitary theta

/-! ## Unitarity and finite support -/

theorem inputRotation_unitary (theta : Real) :
    inputRotation theta ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex :=
  rotationXAt_unitary q1 theta

theorem resourcePreparation_unitary :
    resourcePreparation ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex :=
  bellInverseAt_unitary q4 q5 q4_ne_q5

theorem timeOneUnitary_unitary (theta : Real) :
    timeOneUnitary theta ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex := by
  exact (Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
    (inputRotation_unitary theta) resourcePreparation_unitary

theorem bellMeasurementGate_unitary :
    bellMeasurementGate ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex :=
  bellAt_unitary q1 q4 q1_ne_q4

theorem timeTwoUnitary_unitary (theta : Real) :
    timeTwoUnitary theta ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex := by
  exact (Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
    bellMeasurementGate_unitary (timeOneUnitary_unitary theta)

theorem q1RecordingGate_unitary :
    q1RecordingGate ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex :=
  cnotAt_unitary q2 q1 q2_ne_q1

theorem q4RecordingGate_unitary :
    q4RecordingGate ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex :=
  cnotAt_unitary q3 q4 q3_ne_q4

theorem recordingLayer_unitary :
    recordingLayer ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex := by
  exact (Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
    q4RecordingGate_unitary q1RecordingGate_unitary

theorem timeThreeUnitary_unitary (theta : Real) :
    timeThreeUnitary theta ∈ Matrix.unitaryGroup (Basis TeleportQubit) Complex := by
  exact (Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
    recordingLayer_unitary (timeTwoUnitary_unitary theta)

theorem inputRotation_isSupportedOn (theta : Real) :
    IsSupportedOn ({q1} : Finset TeleportQubit) (inputRotation theta) :=
  rotationXAt_isSupportedOn q1 theta

theorem resourcePreparation_isSupportedOn :
    IsSupportedOn ({q4, q5} : Finset TeleportQubit) resourcePreparation :=
  bellInverseAt_isSupportedOn q4 q5 q4_ne_q5

theorem bellMeasurementGate_isSupportedOn :
    IsSupportedOn ({q1, q4} : Finset TeleportQubit) bellMeasurementGate :=
  bellAt_isSupportedOn q1 q4 q1_ne_q4

theorem q1RecordingGate_isSupportedOn :
    IsSupportedOn ({q2, q1} : Finset TeleportQubit) q1RecordingGate :=
  cnotAt_isSupportedOn_pair q2 q1 q2_ne_q1

theorem q4RecordingGate_isSupportedOn :
    IsSupportedOn ({q3, q4} : Finset TeleportQubit) q4RecordingGate :=
  cnotAt_isSupportedOn_pair q3 q4 q3_ne_q4

/-- Time one acts only on the input and resource coordinates. -/
theorem timeOneUnitary_isSupportedOn (theta : Real) :
    IsSupportedOn ({q1, q4, q5} : Finset TeleportQubit)
      (timeOneUnitary theta) := by
  exact ((inputRotation_isSupportedOn theta).mono (by decide)).mul
    (resourcePreparation_isSupportedOn.mono (by decide))

/-- The Bell layer introduces no coordinate outside the time-one support. -/
theorem timeTwoUnitary_isSupportedOn (theta : Real) :
    IsSupportedOn ({q1, q4, q5} : Finset TeleportQubit)
      (timeTwoUnitary theta) := by
  exact (bellMeasurementGate_isSupportedOn.mono (by decide)).mul
    (timeOneUnitary_isSupportedOn theta)

/-- The two coherent recording CNOTs act on exactly the four nonreceiver coordinates. -/
theorem recordingLayer_isSupportedOn :
    IsSupportedOn ({q1, q2, q3, q4} : Finset TeleportQubit)
      recordingLayer := by
  exact (q4RecordingGate_isSupportedOn.mono (by decide)).mul
    (q1RecordingGate_isSupportedOn.mono (by decide))

/-- By time three, the coherent chronology has finite support on the five named wires. -/
theorem timeThreeUnitary_isSupportedOn (theta : Real) :
    IsSupportedOn ({q1, q2, q3, q4, q5} : Finset TeleportQubit)
      (timeThreeUnitary theta) := by
  exact (recordingLayer_isSupportedOn.mono (by decide)).mul
    ((timeTwoUnitary_isSupportedOn theta).mono (by decide))

/-- The two time-one preparations commute because their exact supports are disjoint. -/
theorem inputRotation_resourcePreparation_commute (theta : Real) :
    inputRotation theta * resourcePreparation =
      resourcePreparation * inputRotation theta := by
  exact supportedOperators_commute_of_disjoint (by decide)
    (inputRotation_isSupportedOn theta) resourcePreparation_isSupportedOn

/-- The two coherent records commute because their exact supports are disjoint. -/
theorem recordingGates_commute :
    q4RecordingGate * q1RecordingGate =
      q1RecordingGate * q4RecordingGate := by
  exact supportedOperators_commute_of_disjoint (by decide)
    q4RecordingGate_isSupportedOn q1RecordingGate_isSupportedOn

/-! ## Descriptor families -/

def timeOneDescriptors (theta : Real) : DescriptorFamily TeleportQubit :=
  DescriptorFamily.evolve (timeOneUnitary theta)
    (DescriptorFamily.initial TeleportQubit)

def timeTwoDescriptors (theta : Real) : DescriptorFamily TeleportQubit :=
  DescriptorFamily.evolve (timeTwoUnitary theta)
    (DescriptorFamily.initial TeleportQubit)

def timeThreeDescriptors (theta : Real) : DescriptorFamily TeleportQubit :=
  DescriptorFamily.evolve (timeThreeUnitary theta)
    (DescriptorFamily.initial TeleportQubit)

private theorem resourcePreparation_fixes_q1 (A : QubitMatrix) :
    heisenberg resourcePreparation (embedQubit q1 A) = embedQubit q1 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) resourcePreparation_unitary resourcePreparation_isSupportedOn
    (embedQubit_isSupportedOn q1 A)

private theorem inputRotation_fixes_q4 (theta : Real) (A : QubitMatrix) :
    heisenberg (inputRotation theta) (embedQubit q4 A) = embedQubit q4 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) (inputRotation_unitary theta) (inputRotation_isSupportedOn theta)
    (embedQubit_isSupportedOn q4 A)

private theorem inputRotation_fixes_q5 (theta : Real) (A : QubitMatrix) :
    heisenberg (inputRotation theta) (embedQubit q5 A) = embedQubit q5 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) (inputRotation_unitary theta) (inputRotation_isSupportedOn theta)
    (embedQubit_isSupportedOn q5 A)

/-! ## Corrected Equation (29) -/

theorem timeOne_q1_x (theta : Real) :
    (timeOneDescriptors theta q1).x = xAt q1 := by
  change heisenberg (timeOneUnitary theta) (xAt q1) = xAt q1
  rw [timeOneUnitary, heisenberg_chronology, inputRotation,
    rotationXAt_heisenberg_x]
  simpa [xAt] using resourcePreparation_fixes_q1 pauliX

theorem timeOne_q1_y (theta : Real) :
    (timeOneDescriptors theta q1).y =
      (theta.cos : Complex) • yAt q1 - (theta.sin : Complex) • zAt q1 := by
  change heisenberg (timeOneUnitary theta) (yAt q1) = _
  rw [timeOneUnitary, heisenberg_chronology, inputRotation,
    rotationXAt_heisenberg_y, heisenberg_sub,
    heisenberg_smul, heisenberg_smul]
  rw [show heisenberg resourcePreparation (yAt q1) = yAt q1 by
    simpa [yAt] using resourcePreparation_fixes_q1 pauliY]
  rw [show heisenberg resourcePreparation (zAt q1) = zAt q1 by
    simpa [zAt] using resourcePreparation_fixes_q1 pauliZ]

theorem timeOne_q1_z (theta : Real) :
    (timeOneDescriptors theta q1).z =
      (theta.sin : Complex) • yAt q1 + (theta.cos : Complex) • zAt q1 := by
  change heisenberg (timeOneUnitary theta) (zAt q1) = _
  rw [timeOneUnitary, heisenberg_chronology, inputRotation,
    rotationXAt_heisenberg_z, heisenberg_add,
    heisenberg_smul, heisenberg_smul]
  rw [show heisenberg resourcePreparation (yAt q1) = yAt q1 by
    simpa [yAt] using resourcePreparation_fixes_q1 pauliY]
  rw [show heisenberg resourcePreparation (zAt q1) = zAt q1 by
    simpa [zAt] using resourcePreparation_fixes_q1 pauliZ]

/-- Equation (29), corrected to the signs forced by Equation (17). -/
theorem equation29_q1 (theta : Real) :
    timeOneDescriptors theta q1 =
      { x := xAt q1
        y := (theta.cos : Complex) • yAt q1 -
          (theta.sin : Complex) • zAt q1
        z := (theta.sin : Complex) • yAt q1 +
          (theta.cos : Complex) • zAt q1 } := by
  apply Descriptor.ext_components
  · exact timeOne_q1_x theta
  · exact timeOne_q1_y theta
  · exact timeOne_q1_z theta

/-! ## Equation (30), exact as printed -/

theorem timeOne_q4_x (theta : Real) :
    (timeOneDescriptors theta q4).x = xAt q4 := by
  change heisenberg (timeOneUnitary theta) (xAt q4) = xAt q4
  rw [timeOneUnitary, heisenberg_chronology]
  rw [show heisenberg (inputRotation theta) (xAt q4) = xAt q4 by
    simpa [xAt] using inputRotation_fixes_q4 theta pauliX]
  exact bellInverseAt_conjugates_target_x q4 q5 q4_ne_q5

theorem timeOne_q4_y (theta : Real) :
    (timeOneDescriptors theta q4).y = -(yAt q4 * xAt q5) := by
  change heisenberg (timeOneUnitary theta) (yAt q4) = _
  rw [timeOneUnitary, heisenberg_chronology]
  rw [show heisenberg (inputRotation theta) (yAt q4) = yAt q4 by
    simpa [yAt] using inputRotation_fixes_q4 theta pauliY]
  exact bellInverseAt_conjugates_target_y q4 q5 q4_ne_q5

theorem timeOne_q4_z (theta : Real) :
    (timeOneDescriptors theta q4).z = -(zAt q4 * xAt q5) := by
  change heisenberg (timeOneUnitary theta) (zAt q4) = _
  rw [timeOneUnitary, heisenberg_chronology]
  rw [show heisenberg (inputRotation theta) (zAt q4) = zAt q4 by
    simpa [zAt] using inputRotation_fixes_q4 theta pauliZ]
  exact bellInverseAt_conjugates_target_z q4 q5 q4_ne_q5

theorem timeOne_q5_x (theta : Real) :
    (timeOneDescriptors theta q5).x = xAt q4 * zAt q5 := by
  change heisenberg (timeOneUnitary theta) (xAt q5) = _
  rw [timeOneUnitary, heisenberg_chronology]
  rw [show heisenberg (inputRotation theta) (xAt q5) = xAt q5 by
    simpa [xAt] using inputRotation_fixes_q5 theta pauliX]
  exact bellInverseAt_conjugates_control_x q4 q5 q4_ne_q5

theorem timeOne_q5_y (theta : Real) :
    (timeOneDescriptors theta q5).y = -(xAt q4 * yAt q5) := by
  change heisenberg (timeOneUnitary theta) (yAt q5) = _
  rw [timeOneUnitary, heisenberg_chronology]
  rw [show heisenberg (inputRotation theta) (yAt q5) = yAt q5 by
    simpa [yAt] using inputRotation_fixes_q5 theta pauliY]
  exact bellInverseAt_conjugates_control_y q4 q5 q4_ne_q5

theorem timeOne_q5_z (theta : Real) :
    (timeOneDescriptors theta q5).z = xAt q5 := by
  change heisenberg (timeOneUnitary theta) (zAt q5) = _
  rw [timeOneUnitary, heisenberg_chronology]
  rw [show heisenberg (inputRotation theta) (zAt q5) = zAt q5 by
    simpa [zAt] using inputRotation_fixes_q5 theta pauliZ]
  exact bellInverseAt_conjugates_control_z q4 q5 q4_ne_q5

theorem equation30_q4 (theta : Real) :
    timeOneDescriptors theta q4 =
      { x := xAt q4
        y := -(yAt q4 * xAt q5)
        z := -(zAt q4 * xAt q5) } := by
  apply Descriptor.ext_components
  · exact timeOne_q4_x theta
  · exact timeOne_q4_y theta
  · exact timeOne_q4_z theta

theorem equation30_q5 (theta : Real) :
    timeOneDescriptors theta q5 =
      { x := xAt q4 * zAt q5
        y := -(xAt q4 * yAt q5)
        z := xAt q5 } := by
  apply Descriptor.ext_components
  · exact timeOne_q5_x theta
  · exact timeOne_q5_y theta
  · exact timeOne_q5_z theta

/-! ## Corrected Equation (31) -/

theorem timeTwo_q1_x (theta : Real) :
    (timeTwoDescriptors theta q1).x = xAt q1 := by
  change heisenberg (timeTwoUnitary theta) (xAt q1) = xAt q1
  rw [timeTwoUnitary, heisenberg_chronology, bellMeasurementGate,
    bellAt_conjugates_target_x]
  exact timeOne_q1_x theta

theorem timeTwo_q1_y (theta : Real) :
    (timeTwoDescriptors theta q1).y =
      ((theta.cos : Complex) • yAt q1 -
        (theta.sin : Complex) • zAt q1) * (zAt q4 * xAt q5) := by
  change heisenberg (timeTwoUnitary theta) (yAt q1) = _
  rw [timeTwoUnitary, heisenberg_chronology, bellMeasurementGate,
    bellAt_conjugates_target_y, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeOneUnitary_unitary theta)]
  rw [show heisenberg (timeOneUnitary theta) (yAt q1) =
      (theta.cos : Complex) • yAt q1 -
        (theta.sin : Complex) • zAt q1 by
    simpa [timeOneDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
      DescriptorFamily.initial, Descriptor.initial] using timeOne_q1_y theta]
  rw [show heisenberg (timeOneUnitary theta) (zAt q4) =
      -(zAt q4 * xAt q5) by
    simpa [timeOneDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
      DescriptorFamily.initial, Descriptor.initial] using timeOne_q4_z theta]
  simp only [Matrix.mul_neg, neg_neg]

theorem timeTwo_q1_z (theta : Real) :
    (timeTwoDescriptors theta q1).z =
      ((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1) * (zAt q4 * xAt q5) := by
  change heisenberg (timeTwoUnitary theta) (zAt q1) = _
  rw [timeTwoUnitary, heisenberg_chronology, bellMeasurementGate,
    bellAt_conjugates_target_z, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeOneUnitary_unitary theta)]
  rw [show heisenberg (timeOneUnitary theta) (zAt q1) =
      (theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1 by
    simpa [timeOneDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
      DescriptorFamily.initial, Descriptor.initial] using timeOne_q1_z theta]
  rw [show heisenberg (timeOneUnitary theta) (zAt q4) =
      -(zAt q4 * xAt q5) by
    simpa [timeOneDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
      DescriptorFamily.initial, Descriptor.initial] using timeOne_q4_z theta]
  simp only [Matrix.mul_neg, neg_neg]

theorem timeTwo_q4_x (theta : Real) :
    (timeTwoDescriptors theta q4).x = -(zAt q4 * xAt q5) := by
  change heisenberg (timeTwoUnitary theta) (xAt q4) = _
  rw [timeTwoUnitary, heisenberg_chronology, bellMeasurementGate,
    bellAt_conjugates_control_x]
  exact timeOne_q4_z theta

theorem timeTwo_q4_y (theta : Real) :
    (timeTwoDescriptors theta q4).y =
      xAt q1 * (yAt q4 * xAt q5) := by
  change heisenberg (timeTwoUnitary theta) (yAt q4) = _
  rw [timeTwoUnitary, heisenberg_chronology, bellMeasurementGate,
    bellAt_conjugates_control_y, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeOneUnitary_unitary theta)]
  rw [show heisenberg (timeOneUnitary theta) (xAt q1) = xAt q1 by
    simpa [timeOneDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
      DescriptorFamily.initial, Descriptor.initial] using timeOne_q1_x theta]
  rw [show heisenberg (timeOneUnitary theta) (yAt q4) =
      -(yAt q4 * xAt q5) by
    simpa [timeOneDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
      DescriptorFamily.initial, Descriptor.initial] using timeOne_q4_y theta]
  simp only [Matrix.mul_neg, neg_neg]

theorem timeTwo_q4_z (theta : Real) :
    (timeTwoDescriptors theta q4).z = xAt q1 * xAt q4 := by
  change heisenberg (timeTwoUnitary theta) (zAt q4) = _
  rw [timeTwoUnitary, heisenberg_chronology, bellMeasurementGate,
    bellAt_conjugates_control_z,
    heisenberg_mul_of_unitary _ _ _ (timeOneUnitary_unitary theta)]
  rw [show heisenberg (timeOneUnitary theta) (xAt q1) = xAt q1 by
    simpa [timeOneDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
      DescriptorFamily.initial, Descriptor.initial] using timeOne_q1_x theta]
  rw [show heisenberg (timeOneUnitary theta) (xAt q4) = xAt q4 by
    simpa [timeOneDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
      DescriptorFamily.initial, Descriptor.initial] using timeOne_q4_x theta]

/-- Equation (31), with the corrected Equation (29) combinations propagated to `q1`. -/
theorem equation31_q1 (theta : Real) :
    timeTwoDescriptors theta q1 =
      { x := xAt q1
        y := ((theta.cos : Complex) • yAt q1 -
          (theta.sin : Complex) • zAt q1) * (zAt q4 * xAt q5)
        z := ((theta.sin : Complex) • yAt q1 +
          (theta.cos : Complex) • zAt q1) * (zAt q4 * xAt q5) } := by
  apply Descriptor.ext_components
  · exact timeTwo_q1_x theta
  · exact timeTwo_q1_y theta
  · exact timeTwo_q1_z theta

/-- The `q4` half of Equation (31), exact as printed. -/
theorem equation31_q4 (theta : Real) :
    timeTwoDescriptors theta q4 =
      { x := -(zAt q4 * xAt q5)
        y := xAt q1 * (yAt q4 * xAt q5)
        z := xAt q1 * xAt q4 } := by
  apply Descriptor.ext_components
  · exact timeTwo_q4_x theta
  · exact timeTwo_q4_y theta
  · exact timeTwo_q4_z theta

/-! ## Corrected Equation (32): coherent records -/

private theorem q4Recording_fixes_q2 (A : QubitMatrix) :
    heisenberg q4RecordingGate (embedQubit q2 A) = embedQubit q2 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) q4RecordingGate_unitary q4RecordingGate_isSupportedOn
    (embedQubit_isSupportedOn q2 A)

private theorem q1Recording_fixes_q3 (A : QubitMatrix) :
    heisenberg q1RecordingGate (embedQubit q3 A) = embedQubit q3 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) q1RecordingGate_unitary q1RecordingGate_isSupportedOn
    (embedQubit_isSupportedOn q3 A)

private theorem q1Recording_fixes_q4 (A : QubitMatrix) :
    heisenberg q1RecordingGate (embedQubit q4 A) = embedQubit q4 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) q1RecordingGate_unitary q1RecordingGate_isSupportedOn
    (embedQubit_isSupportedOn q4 A)

private theorem recordingLayer_heisenberg_q2_x :
    heisenberg recordingLayer (xAt q2) = xAt q2 := by
  rw [recordingLayer, heisenberg_chronology]
  rw [show heisenberg q4RecordingGate (xAt q2) = xAt q2 by
    simpa [xAt] using q4Recording_fixes_q2 pauliX]
  exact cnotAt_conjugates_target_x q2 q1 q2_ne_q1

private theorem recordingLayer_heisenberg_q2_y :
    heisenberg recordingLayer (yAt q2) = -(yAt q2 * zAt q1) := by
  rw [recordingLayer, heisenberg_chronology]
  rw [show heisenberg q4RecordingGate (yAt q2) = yAt q2 by
    simpa [yAt] using q4Recording_fixes_q2 pauliY]
  exact cnotAt_conjugates_target_y q2 q1 q2_ne_q1

private theorem recordingLayer_heisenberg_q2_z :
    heisenberg recordingLayer (zAt q2) = -(zAt q2 * zAt q1) := by
  rw [recordingLayer, heisenberg_chronology]
  rw [show heisenberg q4RecordingGate (zAt q2) = zAt q2 by
    simpa [zAt] using q4Recording_fixes_q2 pauliZ]
  exact cnotAt_conjugates_target_z q2 q1 q2_ne_q1

private theorem recordingLayer_heisenberg_q3_x :
    heisenberg recordingLayer (xAt q3) = xAt q3 := by
  rw [recordingLayer, heisenberg_chronology, q4RecordingGate,
    cnotAt_conjugates_target_x]
  simpa [xAt] using q1Recording_fixes_q3 pauliX

private theorem recordingLayer_heisenberg_q3_y :
    heisenberg recordingLayer (yAt q3) = -(yAt q3 * zAt q4) := by
  rw [recordingLayer, heisenberg_chronology, q4RecordingGate,
    cnotAt_conjugates_target_y, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ q1RecordingGate_unitary]
  rw [show heisenberg q1RecordingGate (yAt q3) = yAt q3 by
    simpa [yAt] using q1Recording_fixes_q3 pauliY]
  rw [show heisenberg q1RecordingGate (zAt q4) = zAt q4 by
    simpa [zAt] using q1Recording_fixes_q4 pauliZ]

private theorem recordingLayer_heisenberg_q3_z :
    heisenberg recordingLayer (zAt q3) = -(zAt q3 * zAt q4) := by
  rw [recordingLayer, heisenberg_chronology, q4RecordingGate,
    cnotAt_conjugates_target_z, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ q1RecordingGate_unitary]
  rw [show heisenberg q1RecordingGate (zAt q3) = zAt q3 by
    simpa [zAt] using q1Recording_fixes_q3 pauliZ]
  rw [show heisenberg q1RecordingGate (zAt q4) = zAt q4 by
    simpa [zAt] using q1Recording_fixes_q4 pauliZ]

private theorem timeTwo_fixes_q2 (theta : Real) (A : QubitMatrix) :
    heisenberg (timeTwoUnitary theta) (embedQubit q2 A) = embedQubit q2 A := by
  rw [timeTwoUnitary, heisenberg_chronology]
  rw [show heisenberg bellMeasurementGate (embedQubit q2 A) =
      embedQubit q2 A by
    exact heisenberg_eq_self_of_disjoint_support
      (by decide) bellMeasurementGate_unitary bellMeasurementGate_isSupportedOn
      (embedQubit_isSupportedOn q2 A)]
  rw [timeOneUnitary, heisenberg_chronology]
  rw [show heisenberg (inputRotation theta) (embedQubit q2 A) =
      embedQubit q2 A by
    exact heisenberg_eq_self_of_disjoint_support
      (by decide) (inputRotation_unitary theta) (inputRotation_isSupportedOn theta)
      (embedQubit_isSupportedOn q2 A)]
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) resourcePreparation_unitary resourcePreparation_isSupportedOn
    (embedQubit_isSupportedOn q2 A)

private theorem timeTwo_fixes_q3 (theta : Real) (A : QubitMatrix) :
    heisenberg (timeTwoUnitary theta) (embedQubit q3 A) = embedQubit q3 A := by
  rw [timeTwoUnitary, heisenberg_chronology]
  rw [show heisenberg bellMeasurementGate (embedQubit q3 A) =
      embedQubit q3 A by
    exact heisenberg_eq_self_of_disjoint_support
      (by decide) bellMeasurementGate_unitary bellMeasurementGate_isSupportedOn
      (embedQubit_isSupportedOn q3 A)]
  rw [timeOneUnitary, heisenberg_chronology]
  rw [show heisenberg (inputRotation theta) (embedQubit q3 A) =
      embedQubit q3 A by
    exact heisenberg_eq_self_of_disjoint_support
      (by decide) (inputRotation_unitary theta) (inputRotation_isSupportedOn theta)
      (embedQubit_isSupportedOn q3 A)]
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) resourcePreparation_unitary resourcePreparation_isSupportedOn
    (embedQubit_isSupportedOn q3 A)

private theorem yAt_q2_commutes_q1_z_combination (theta : Real) :
    yAt q2 * ((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1) =
      ((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1) * yAt q2 := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul]
  rw [show yAt q2 * yAt q1 = yAt q1 * yAt q2 by
    simpa [yAt] using embedQubit_commute_of_ne q2_ne_q1 pauliY pauliY]
  rw [show yAt q2 * zAt q1 = zAt q1 * yAt q2 by
    simpa [yAt, zAt] using embedQubit_commute_of_ne q2_ne_q1 pauliY pauliZ]

private theorem zAt_q2_commutes_q1_z_combination (theta : Real) :
    zAt q2 * ((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1) =
      ((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1) * zAt q2 := by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.smul_mul]
  rw [show zAt q2 * yAt q1 = yAt q1 * zAt q2 by
    simpa [zAt, yAt] using embedQubit_commute_of_ne q2_ne_q1 pauliZ pauliY]
  rw [show zAt q2 * zAt q1 = zAt q1 * zAt q2 by
    simpa [zAt] using embedQubit_commute_of_ne q2_ne_q1 pauliZ pauliZ]

theorem timeThree_q2_x (theta : Real) :
    (timeThreeDescriptors theta q2).x = xAt q2 := by
  change heisenberg (timeThreeUnitary theta) (xAt q2) = xAt q2
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q2_x]
  simpa [xAt] using timeTwo_fixes_q2 theta pauliX

theorem timeThree_q2_y (theta : Real) :
    (timeThreeDescriptors theta q2).y =
      (-((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1)) * yAt q2 *
          (zAt q4 * xAt q5) := by
  change heisenberg (timeThreeUnitary theta) (yAt q2) = _
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q2_y, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeTwoUnitary_unitary theta)]
  rw [show heisenberg (timeTwoUnitary theta) (yAt q2) = yAt q2 by
    simpa [yAt] using timeTwo_fixes_q2 theta pauliY]
  rw [show heisenberg (timeTwoUnitary theta) (zAt q1) =
      ((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1) * (zAt q4 * xAt q5) by
    simpa [timeTwoDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
      DescriptorFamily.initial, Descriptor.initial] using timeTwo_q1_z theta]
  rw [← Matrix.mul_assoc, yAt_q2_commutes_q1_z_combination]
  simp only [neg_mul]

theorem timeThree_q2_z (theta : Real) :
    (timeThreeDescriptors theta q2).z =
      (-((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1)) * zAt q2 *
          (zAt q4 * xAt q5) := by
  change heisenberg (timeThreeUnitary theta) (zAt q2) = _
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q2_z, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeTwoUnitary_unitary theta)]
  rw [show heisenberg (timeTwoUnitary theta) (zAt q2) = zAt q2 by
    simpa [zAt] using timeTwo_fixes_q2 theta pauliZ]
  rw [show heisenberg (timeTwoUnitary theta) (zAt q1) =
      ((theta.sin : Complex) • yAt q1 +
        (theta.cos : Complex) • zAt q1) * (zAt q4 * xAt q5) by
    simpa [timeTwoDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
      DescriptorFamily.initial, Descriptor.initial] using timeTwo_q1_z theta]
  rw [← Matrix.mul_assoc, zAt_q2_commutes_q1_z_combination]
  simp only [neg_mul]

theorem timeThree_q3_x (theta : Real) :
    (timeThreeDescriptors theta q3).x = xAt q3 := by
  change heisenberg (timeThreeUnitary theta) (xAt q3) = xAt q3
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q3_x]
  simpa [xAt] using timeTwo_fixes_q3 theta pauliX

theorem timeThree_q3_y (theta : Real) :
    (timeThreeDescriptors theta q3).y =
      -(xAt q1 * yAt q3 * xAt q4) := by
  change heisenberg (timeThreeUnitary theta) (yAt q3) = _
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q3_y, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeTwoUnitary_unitary theta)]
  rw [show heisenberg (timeTwoUnitary theta) (yAt q3) = yAt q3 by
    simpa [yAt] using timeTwo_fixes_q3 theta pauliY]
  rw [show heisenberg (timeTwoUnitary theta) (zAt q4) =
      xAt q1 * xAt q4 by
    simpa [timeTwoDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
      DescriptorFamily.initial, Descriptor.initial] using timeTwo_q4_z theta]
  rw [← Matrix.mul_assoc]
  rw [show yAt q3 * xAt q1 = xAt q1 * yAt q3 by
    simpa [yAt, xAt] using embedQubit_commute_of_ne q3_ne_q1 pauliY pauliX]

theorem timeThree_q3_z (theta : Real) :
    (timeThreeDescriptors theta q3).z =
      -(xAt q1 * zAt q3 * xAt q4) := by
  change heisenberg (timeThreeUnitary theta) (zAt q3) = _
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q3_z, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeTwoUnitary_unitary theta)]
  rw [show heisenberg (timeTwoUnitary theta) (zAt q3) = zAt q3 by
    simpa [zAt] using timeTwo_fixes_q3 theta pauliZ]
  rw [show heisenberg (timeTwoUnitary theta) (zAt q4) =
      xAt q1 * xAt q4 by
    simpa [timeTwoDescriptors, DescriptorFamily.evolve, Descriptor.evolve,
      DescriptorFamily.initial, Descriptor.initial] using timeTwo_q4_z theta]
  rw [← Matrix.mul_assoc]
  rw [show zAt q3 * xAt q1 = xAt q1 * zAt q3 by
    simpa [zAt, xAt] using embedQubit_commute_of_ne q3_ne_q1 pauliZ pauliX]

/-- The `q2` half of Equation (32), with the corrected Equation (29) signs propagated. -/
theorem equation32_q2 (theta : Real) :
    timeThreeDescriptors theta q2 =
      { x := xAt q2
        y := (-((theta.sin : Complex) • yAt q1 +
          (theta.cos : Complex) • zAt q1)) * yAt q2 *
            (zAt q4 * xAt q5)
        z := (-((theta.sin : Complex) • yAt q1 +
          (theta.cos : Complex) • zAt q1)) * zAt q2 *
            (zAt q4 * xAt q5) } := by
  apply Descriptor.ext_components
  · exact timeThree_q2_x theta
  · exact timeThree_q2_y theta
  · exact timeThree_q2_z theta

/-- The `q3` half of Equation (32), exact as printed. -/
theorem equation32_q3 (theta : Real) :
    timeThreeDescriptors theta q3 =
      { x := xAt q3
        y := -(xAt q1 * yAt q3 * xAt q4)
        z := -(xAt q1 * zAt q3 * xAt q4) } := by
  apply Descriptor.ext_components
  · exact timeThree_q3_x theta
  · exact timeThree_q3_y theta
  · exact timeThree_q3_z theta

/-! ## Executable evidence for the source-sign discrepancy -/

private theorem neg_unitary_ne_self
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

theorem equation29_q1_y_pi_div_two :
    (timeOneDescriptors (Real.pi / 2) q1).y = -zAt q1 := by
  simpa using timeOne_q1_y (Real.pi / 2)

/-- At `θ = π/2`, Equation (29)'s printed `+Z` result is the opposite operator. -/
theorem equation29_q1_y_pi_div_two_ne_printed :
    (timeOneDescriptors (Real.pi / 2) q1).y ≠ zAt q1 := by
  rw [equation29_q1_y_pi_div_two]
  intro h
  have himage :
      embedQubit q1 ((-1 : Complex) • pauliZ) = embedQubit q1 pauliZ := by
    rw [embedQubit_smul]
    simpa only [neg_one_smul, zAt] using h
  have hlocal := embedQubit_injective q1 himage
  have h00 := congrFun (congrFun hlocal (0 : QubitIndex)) (0 : QubitIndex)
  norm_num [pauliZ] at h00

/-- At `θ = π/2`, Equation (31)'s printed `q1.y` has the opposite propagated sign. -/
theorem equation31_q1_y_pi_div_two_ne_printed :
    (timeTwoDescriptors (Real.pi / 2) q1).y ≠
      zAt q1 * (zAt q4 * xAt q5) := by
  rw [timeTwo_q1_y]
  simpa using neg_unitary_ne_self
    (zAt q1 * (zAt q4 * xAt q5))
    ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
      (zAt_unitary q1)
      ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
        (zAt_unitary q4) (xAt_unitary q5)))

/-- At `θ = π/2`, Equation (32)'s printed `q2.y` has the opposite propagated sign. -/
theorem equation32_q2_y_pi_div_two_ne_printed :
    (timeThreeDescriptors (Real.pi / 2) q2).y ≠
      yAt q1 * yAt q2 * (zAt q4 * xAt q5) := by
  rw [timeThree_q2_y]
  simpa using neg_unitary_ne_self
    (yAt q1 * yAt q2 * (zAt q4 * xAt q5))
    ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
      ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
        (yAt_unitary q1) (yAt_unitary q2))
      ((Matrix.unitaryGroup (Basis TeleportQubit) Complex).mul_mem
        (zAt_unitary q4) (xAt_unitary q5)))

end
end Teleportation
end Deutsch
