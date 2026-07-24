import Deutsch.Gates.Bell
import Deutsch.Locality.Heisenberg

/-!
# The named four-qubit EPR circuit

This module fixes the four wire names and the Schrödinger chronology of Figure 2.  Descriptor
identities are stated in the project's Heisenberg convention.  The time-two sine terms follow
directly from the `rotationX` identities proved in the gate layer.
-/

namespace Deutsch
namespace EPR

open Foundations Gates Locality Register
open scoped Matrix

noncomputable section

/-- The four named wires in Figure 2. -/
abbrev EPRQubit := Fin 4

def q1 : EPRQubit := 0
def q2 : EPRQubit := 1
def q3 : EPRQubit := 2
def q4 : EPRQubit := 3

@[simp] theorem q1_ne_q2 : q1 ≠ q2 := by decide
@[simp] theorem q1_ne_q3 : q1 ≠ q3 := by decide
@[simp] theorem q1_ne_q4 : q1 ≠ q4 := by decide
@[simp] theorem q2_ne_q1 : q2 ≠ q1 := by decide
@[simp] theorem q2_ne_q3 : q2 ≠ q3 := by decide
@[simp] theorem q2_ne_q4 : q2 ≠ q4 := by decide
@[simp] theorem q3_ne_q1 : q3 ≠ q1 := by decide
@[simp] theorem q3_ne_q2 : q3 ≠ q2 := by decide
@[simp] theorem q3_ne_q4 : q3 ≠ q4 := by decide
@[simp] theorem q4_ne_q1 : q4 ≠ q1 := by decide
@[simp] theorem q4_ne_q2 : q4 ≠ q2 := by decide
@[simp] theorem q4_ne_q3 : q4 ≠ q3 := by decide

/-! ## Schrödinger circuit chronology -/

/-- Time one: prepare the EPR pair on `q2,q3` with the inverse Bell gate. -/
def timeOneUnitary : Operator EPRQubit :=
  bellInverseAt q2 q3 q2_ne_q3

/-- The two spacelike-separated setting rotations between times one and two. -/
def rotationLayer (theta phi : Real) : Operator EPRQubit :=
  rotationXAt q3 phi * rotationXAt q2 theta

/-- Full preparation through time two. -/
def timeTwoUnitary (theta phi : Real) : Operator EPRQubit :=
  rotationLayer theta phi * timeOneUnitary

/-- The coherent recording CNOT in region A. -/
def leftRecordingGate : Operator EPRQubit :=
  cnotAt q1 q2 q1_ne_q2

/-- The coherent recording CNOT in region B. -/
def rightRecordingGate : Operator EPRQubit :=
  cnotAt q4 q3 q4_ne_q3

/-- The two local coherent recording CNOTs between times two and three. -/
def recordingLayer : Operator EPRQubit :=
  rightRecordingGate * leftRecordingGate

/-- Full preparation through time three. -/
def timeThreeUnitary (theta phi : Real) : Operator EPRQubit :=
  recordingLayer * timeTwoUnitary theta phi

/-- The final comparison CNOT, with transported `q4` controlling target `q1`. -/
def comparisonGate : Operator EPRQubit :=
  cnotAt q1 q4 q1_ne_q4

/-- Full circuit through time four. -/
def timeFourUnitary (theta phi : Real) : Operator EPRQubit :=
  comparisonGate * timeThreeUnitary theta phi

theorem timeOneUnitary_unitary :
    timeOneUnitary ∈ Matrix.unitaryGroup (Basis EPRQubit) Complex := by
  exact bellInverseAt_unitary q2 q3 q2_ne_q3

theorem rotationLayer_unitary (theta phi : Real) :
    rotationLayer theta phi ∈ Matrix.unitaryGroup (Basis EPRQubit) Complex := by
  exact (Matrix.unitaryGroup (Basis EPRQubit) Complex).mul_mem
    (rotationXAt_unitary q3 phi) (rotationXAt_unitary q2 theta)

theorem timeTwoUnitary_unitary (theta phi : Real) :
    timeTwoUnitary theta phi ∈
      Matrix.unitaryGroup (Basis EPRQubit) Complex := by
  exact (Matrix.unitaryGroup (Basis EPRQubit) Complex).mul_mem
    (rotationLayer_unitary theta phi) timeOneUnitary_unitary

theorem recordingLayer_unitary :
    recordingLayer ∈ Matrix.unitaryGroup (Basis EPRQubit) Complex := by
  exact (Matrix.unitaryGroup (Basis EPRQubit) Complex).mul_mem
    (cnotAt_unitary q4 q3 q4_ne_q3)
    (cnotAt_unitary q1 q2 q1_ne_q2)

theorem leftRecordingGate_unitary :
    leftRecordingGate ∈ Matrix.unitaryGroup (Basis EPRQubit) Complex := by
  exact cnotAt_unitary q1 q2 q1_ne_q2

theorem rightRecordingGate_unitary :
    rightRecordingGate ∈ Matrix.unitaryGroup (Basis EPRQubit) Complex := by
  exact cnotAt_unitary q4 q3 q4_ne_q3

theorem timeThreeUnitary_unitary (theta phi : Real) :
    timeThreeUnitary theta phi ∈
      Matrix.unitaryGroup (Basis EPRQubit) Complex := by
  exact (Matrix.unitaryGroup (Basis EPRQubit) Complex).mul_mem
    recordingLayer_unitary (timeTwoUnitary_unitary theta phi)

theorem comparisonGate_unitary :
    comparisonGate ∈ Matrix.unitaryGroup (Basis EPRQubit) Complex := by
  exact cnotAt_unitary q1 q4 q1_ne_q4

theorem timeFourUnitary_unitary (theta phi : Real) :
    timeFourUnitary theta phi ∈
      Matrix.unitaryGroup (Basis EPRQubit) Complex := by
  exact (Matrix.unitaryGroup (Basis EPRQubit) Complex).mul_mem
    comparisonGate_unitary (timeThreeUnitary_unitary theta phi)

/-! ## Explicit circuit support -/

theorem timeOneUnitary_isSupportedOn :
    IsSupportedOn ({q2, q3} : Finset EPRQubit) timeOneUnitary := by
  exact bellInverseAt_isSupportedOn q2 q3 q2_ne_q3

private theorem rotationQ2_isSupportedOn_pair (theta : Real) :
    IsSupportedOn ({q2, q3} : Finset EPRQubit) (rotationXAt q2 theta) := by
  let p := targetControlPlacement q2 q3 q2_ne_q3
  have hs := embedAlong_isSupportedOn p (rotationXAt (0 : Fin 2) theta)
  rw [show placementFinset p = ({q2, q3} : Finset EPRQubit) by
    exact placementFinset_targetControl q2 q3 q2_ne_q3] at hs
  have heq : embedAlong p (rotationXAt (0 : Fin 2) theta) =
      rotationXAt q2 theta := by
    unfold rotationXAt
    rw [embedAlong_embedQubit]
    rfl
  rw [heq] at hs
  exact hs

private theorem rotationQ3_isSupportedOn_pair (phi : Real) :
    IsSupportedOn ({q2, q3} : Finset EPRQubit) (rotationXAt q3 phi) := by
  let p := targetControlPlacement q2 q3 q2_ne_q3
  have hs := embedAlong_isSupportedOn p (rotationXAt (1 : Fin 2) phi)
  rw [show placementFinset p = ({q2, q3} : Finset EPRQubit) by
    exact placementFinset_targetControl q2 q3 q2_ne_q3] at hs
  have heq : embedAlong p (rotationXAt (1 : Fin 2) phi) =
      rotationXAt q3 phi := by
    unfold rotationXAt
    rw [embedAlong_embedQubit]
    rfl
  rw [heq] at hs
  exact hs

theorem rotationLayer_isSupportedOn (theta phi : Real) :
    IsSupportedOn ({q2, q3} : Finset EPRQubit) (rotationLayer theta phi) := by
  exact (rotationQ3_isSupportedOn_pair phi).mul
    (rotationQ2_isSupportedOn_pair theta)

theorem timeTwoUnitary_isSupportedOn (theta phi : Real) :
    IsSupportedOn ({q2, q3} : Finset EPRQubit) (timeTwoUnitary theta phi) := by
  exact (rotationLayer_isSupportedOn theta phi).mul timeOneUnitary_isSupportedOn

theorem leftRecordingGate_isSupportedOn :
    IsSupportedOn ({q1, q2} : Finset EPRQubit)
      leftRecordingGate := by
  exact cnotAt_isSupportedOn_pair q1 q2 q1_ne_q2

theorem rightRecordingGate_isSupportedOn :
    IsSupportedOn ({q4, q3} : Finset EPRQubit)
      rightRecordingGate := by
  exact cnotAt_isSupportedOn_pair q4 q3 q4_ne_q3

theorem comparisonGate_isSupportedOn :
    IsSupportedOn ({q1, q4} : Finset EPRQubit) comparisonGate := by
  exact cnotAt_isSupportedOn_pair q1 q4 q1_ne_q4

/-! ## Descriptor families -/

def timeOneDescriptors : DescriptorFamily EPRQubit :=
  DescriptorFamily.evolve timeOneUnitary (DescriptorFamily.initial EPRQubit)

def timeTwoDescriptors (theta phi : Real) : DescriptorFamily EPRQubit :=
  DescriptorFamily.evolve (timeTwoUnitary theta phi)
    (DescriptorFamily.initial EPRQubit)

def timeThreeDescriptors (theta phi : Real) : DescriptorFamily EPRQubit :=
  DescriptorFamily.evolve (timeThreeUnitary theta phi)
    (DescriptorFamily.initial EPRQubit)

/-! Equation (23), already fixed by the inverse-Bell gate convention. -/

theorem equation23_q2 :
    timeOneDescriptors q2 =
      { x := xAt q2
        y := -(yAt q2 * xAt q3)
        z := -(zAt q2 * xAt q3) } := by
  simpa [timeOneDescriptors, timeOneUnitary] using
    bellInverseAt_evolves_target_descriptor q2 q3 q2_ne_q3

theorem equation23_q3 :
    timeOneDescriptors q3 =
      { x := xAt q2 * zAt q3
        y := -(xAt q2 * yAt q3)
        z := xAt q3 } := by
  simpa [timeOneDescriptors, timeOneUnitary] using
    bellInverseAt_evolves_control_descriptor q2 q3 q2_ne_q3

/-! Equation (24): the preparation and setting rotations never touch `q1` or `q4`. -/

theorem equation24_q1 (theta phi : Real) :
    timeTwoDescriptors theta phi q1 = Descriptor.initial q1 := by
  apply Descriptor.ext_components
  · change heisenberg (timeTwoUnitary theta phi) (xAt q1) = xAt q1
    exact heisenberg_eq_self_of_disjoint_support
      (by decide) (timeTwoUnitary_unitary theta phi)
      (timeTwoUnitary_isSupportedOn theta phi) (xAt_isSupportedOn q1)
  · change heisenberg (timeTwoUnitary theta phi) (yAt q1) = yAt q1
    exact heisenberg_eq_self_of_disjoint_support
      (by decide) (timeTwoUnitary_unitary theta phi)
      (timeTwoUnitary_isSupportedOn theta phi) (yAt_isSupportedOn q1)
  · change heisenberg (timeTwoUnitary theta phi) (zAt q1) = zAt q1
    exact heisenberg_eq_self_of_disjoint_support
      (by decide) (timeTwoUnitary_unitary theta phi)
      (timeTwoUnitary_isSupportedOn theta phi) (zAt_isSupportedOn q1)

theorem equation24_q4 (theta phi : Real) :
    timeTwoDescriptors theta phi q4 = Descriptor.initial q4 := by
  apply Descriptor.ext_components
  · change heisenberg (timeTwoUnitary theta phi) (xAt q4) = xAt q4
    exact heisenberg_eq_self_of_disjoint_support
      (by decide) (timeTwoUnitary_unitary theta phi)
      (timeTwoUnitary_isSupportedOn theta phi) (xAt_isSupportedOn q4)
  · change heisenberg (timeTwoUnitary theta phi) (yAt q4) = yAt q4
    exact heisenberg_eq_self_of_disjoint_support
      (by decide) (timeTwoUnitary_unitary theta phi)
      (timeTwoUnitary_isSupportedOn theta phi) (yAt_isSupportedOn q4)
  · change heisenberg (timeTwoUnitary theta phi) (zAt q4) = zAt q4
    exact heisenberg_eq_self_of_disjoint_support
      (by decide) (timeTwoUnitary_unitary theta phi)
      (timeTwoUnitary_isSupportedOn theta phi) (zAt_isSupportedOn q4)

/-! ## Equation (25) -/

private theorem q3Rotation_fixes_q2 (phi : Real) (A : QubitMatrix) :
    heisenberg (rotationXAt q3 phi) (embedQubit q2 A) = embedQubit q2 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) (rotationXAt_unitary q3 phi)
    (rotationXAt_isSupportedOn q3 phi) (embedQubit_isSupportedOn q2 A)

private theorem q2Rotation_fixes_q3 (theta : Real) (A : QubitMatrix) :
    heisenberg (rotationXAt q2 theta) (embedQubit q3 A) = embedQubit q3 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) (rotationXAt_unitary q2 theta)
    (rotationXAt_isSupportedOn q2 theta) (embedQubit_isSupportedOn q3 A)

private theorem rotationLayer_heisenberg_q2_x (theta phi : Real) :
    heisenberg (rotationLayer theta phi) (xAt q2) = xAt q2 := by
  rw [rotationLayer, heisenberg_chronology]
  rw [show heisenberg (rotationXAt q3 phi) (xAt q2) = xAt q2 by
    simpa [xAt] using q3Rotation_fixes_q2 phi pauliX]
  exact rotationXAt_heisenberg_x q2 theta

private theorem rotationLayer_heisenberg_q2_y (theta phi : Real) :
    heisenberg (rotationLayer theta phi) (yAt q2) =
      (theta.cos : Complex) • yAt q2 - (theta.sin : Complex) • zAt q2 := by
  rw [rotationLayer, heisenberg_chronology]
  rw [show heisenberg (rotationXAt q3 phi) (yAt q2) = yAt q2 by
    simpa [yAt] using q3Rotation_fixes_q2 phi pauliY]
  exact rotationXAt_heisenberg_y q2 theta

private theorem rotationLayer_heisenberg_q2_z (theta phi : Real) :
    heisenberg (rotationLayer theta phi) (zAt q2) =
      (theta.sin : Complex) • yAt q2 + (theta.cos : Complex) • zAt q2 := by
  rw [rotationLayer, heisenberg_chronology]
  rw [show heisenberg (rotationXAt q3 phi) (zAt q2) = zAt q2 by
    simpa [zAt] using q3Rotation_fixes_q2 phi pauliZ]
  exact rotationXAt_heisenberg_z q2 theta

private theorem rotationLayer_heisenberg_q3_x (theta phi : Real) :
    heisenberg (rotationLayer theta phi) (xAt q3) = xAt q3 := by
  rw [rotationLayer, heisenberg_chronology, rotationXAt_heisenberg_x]
  simpa [xAt] using q2Rotation_fixes_q3 theta pauliX

private theorem rotationLayer_heisenberg_q3_y (theta phi : Real) :
    heisenberg (rotationLayer theta phi) (yAt q3) =
      (phi.cos : Complex) • yAt q3 - (phi.sin : Complex) • zAt q3 := by
  rw [rotationLayer, heisenberg_chronology, rotationXAt_heisenberg_y,
    heisenberg_sub, heisenberg_smul, heisenberg_smul]
  rw [show heisenberg (rotationXAt q2 theta) (yAt q3) = yAt q3 by
    simpa [yAt] using q2Rotation_fixes_q3 theta pauliY]
  rw [show heisenberg (rotationXAt q2 theta) (zAt q3) = zAt q3 by
    simpa [zAt] using q2Rotation_fixes_q3 theta pauliZ]

private theorem rotationLayer_heisenberg_q3_z (theta phi : Real) :
    heisenberg (rotationLayer theta phi) (zAt q3) =
      (phi.sin : Complex) • yAt q3 + (phi.cos : Complex) • zAt q3 := by
  rw [rotationLayer, heisenberg_chronology, rotationXAt_heisenberg_z,
    heisenberg_add, heisenberg_smul, heisenberg_smul]
  rw [show heisenberg (rotationXAt q2 theta) (yAt q3) = yAt q3 by
    simpa [yAt] using q2Rotation_fixes_q3 theta pauliY]
  rw [show heisenberg (rotationXAt q2 theta) (zAt q3) = zAt q3 by
    simpa [zAt] using q2Rotation_fixes_q3 theta pauliZ]

theorem timeTwo_q2_x (theta phi : Real) :
    (timeTwoDescriptors theta phi q2).x = xAt q2 := by
  change heisenberg (timeTwoUnitary theta phi) (xAt q2) = xAt q2
  rw [timeTwoUnitary, heisenberg_chronology,
    rotationLayer_heisenberg_q2_x, timeOneUnitary,
    bellInverseAt_conjugates_target_x]

theorem timeTwo_q2_y (theta phi : Real) :
    (timeTwoDescriptors theta phi q2).y =
      (theta.cos : Complex) • (-(yAt q2 * xAt q3)) -
        (theta.sin : Complex) • (-(zAt q2 * xAt q3)) := by
  change heisenberg (timeTwoUnitary theta phi) (yAt q2) = _
  rw [timeTwoUnitary, heisenberg_chronology,
    rotationLayer_heisenberg_q2_y, heisenberg_sub,
    heisenberg_smul, heisenberg_smul, timeOneUnitary,
    bellInverseAt_conjugates_target_y,
    bellInverseAt_conjugates_target_z]

theorem timeTwo_q2_z (theta phi : Real) :
    (timeTwoDescriptors theta phi q2).z =
      (theta.sin : Complex) • (-(yAt q2 * xAt q3)) +
        (theta.cos : Complex) • (-(zAt q2 * xAt q3)) := by
  change heisenberg (timeTwoUnitary theta phi) (zAt q2) = _
  rw [timeTwoUnitary, heisenberg_chronology,
    rotationLayer_heisenberg_q2_z, heisenberg_add,
    heisenberg_smul, heisenberg_smul, timeOneUnitary,
    bellInverseAt_conjugates_target_y,
    bellInverseAt_conjugates_target_z]

theorem timeTwo_q3_x (theta phi : Real) :
    (timeTwoDescriptors theta phi q3).x = xAt q2 * zAt q3 := by
  change heisenberg (timeTwoUnitary theta phi) (xAt q3) = _
  rw [timeTwoUnitary, heisenberg_chronology,
    rotationLayer_heisenberg_q3_x, timeOneUnitary,
    bellInverseAt_conjugates_control_x]

theorem timeTwo_q3_y (theta phi : Real) :
    (timeTwoDescriptors theta phi q3).y =
      (phi.cos : Complex) • (-(xAt q2 * yAt q3)) -
        (phi.sin : Complex) • xAt q3 := by
  change heisenberg (timeTwoUnitary theta phi) (yAt q3) = _
  rw [timeTwoUnitary, heisenberg_chronology,
    rotationLayer_heisenberg_q3_y, heisenberg_sub,
    heisenberg_smul, heisenberg_smul, timeOneUnitary,
    bellInverseAt_conjugates_control_y,
    bellInverseAt_conjugates_control_z]

theorem timeTwo_q3_z (theta phi : Real) :
    (timeTwoDescriptors theta phi q3).z =
      (phi.sin : Complex) • (-(xAt q2 * yAt q3)) +
        (phi.cos : Complex) • xAt q3 := by
  change heisenberg (timeTwoUnitary theta phi) (zAt q3) = _
  rw [timeTwoUnitary, heisenberg_chronology,
    rotationLayer_heisenberg_q3_z, heisenberg_add,
    heisenberg_smul, heisenberg_smul, timeOneUnitary,
    bellInverseAt_conjugates_control_y,
    bellInverseAt_conjugates_control_z]

theorem equation25_q2 (theta phi : Real) :
    timeTwoDescriptors theta phi q2 =
      { x := xAt q2
        y := (theta.cos : Complex) • (-(yAt q2 * xAt q3)) -
          (theta.sin : Complex) • (-(zAt q2 * xAt q3))
        z := (theta.sin : Complex) • (-(yAt q2 * xAt q3)) +
          (theta.cos : Complex) • (-(zAt q2 * xAt q3)) } := by
  apply Descriptor.ext_components
  · exact timeTwo_q2_x theta phi
  · exact timeTwo_q2_y theta phi
  · exact timeTwo_q2_z theta phi

theorem equation25_q3 (theta phi : Real) :
    timeTwoDescriptors theta phi q3 =
      { x := xAt q2 * zAt q3
        y := (phi.cos : Complex) • (-(xAt q2 * yAt q3)) -
          (phi.sin : Complex) • xAt q3
        z := (phi.sin : Complex) • (-(xAt q2 * yAt q3)) +
          (phi.cos : Complex) • xAt q3 } := by
  apply Descriptor.ext_components
  · exact timeTwo_q3_x theta phi
  · exact timeTwo_q3_y theta phi
  · exact timeTwo_q3_z theta phi

/-! ## Equation (27): coherent local records -/

private theorem rightRecording_fixes_q1 (A : QubitMatrix) :
    heisenberg rightRecordingGate (embedQubit q1 A) = embedQubit q1 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) rightRecordingGate_unitary rightRecordingGate_isSupportedOn
    (embedQubit_isSupportedOn q1 A)

private theorem rightRecording_fixes_q2 (A : QubitMatrix) :
    heisenberg rightRecordingGate (embedQubit q2 A) = embedQubit q2 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) rightRecordingGate_unitary rightRecordingGate_isSupportedOn
    (embedQubit_isSupportedOn q2 A)

private theorem leftRecording_fixes_q3 (A : QubitMatrix) :
    heisenberg leftRecordingGate (embedQubit q3 A) = embedQubit q3 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) leftRecordingGate_unitary leftRecordingGate_isSupportedOn
    (embedQubit_isSupportedOn q3 A)

private theorem leftRecording_fixes_q4 (A : QubitMatrix) :
    heisenberg leftRecordingGate (embedQubit q4 A) = embedQubit q4 A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) leftRecordingGate_unitary leftRecordingGate_isSupportedOn
    (embedQubit_isSupportedOn q4 A)

private theorem recordingLayer_heisenberg_q1_x :
    heisenberg recordingLayer (xAt q1) = xAt q1 := by
  rw [recordingLayer, heisenberg_chronology]
  rw [show heisenberg rightRecordingGate (xAt q1) = xAt q1 by
    simpa [xAt] using rightRecording_fixes_q1 pauliX]
  exact cnotAt_conjugates_target_x q1 q2 q1_ne_q2

private theorem recordingLayer_heisenberg_q1_y :
    heisenberg recordingLayer (yAt q1) = -(yAt q1 * zAt q2) := by
  rw [recordingLayer, heisenberg_chronology]
  rw [show heisenberg rightRecordingGate (yAt q1) = yAt q1 by
    simpa [yAt] using rightRecording_fixes_q1 pauliY]
  exact cnotAt_conjugates_target_y q1 q2 q1_ne_q2

private theorem recordingLayer_heisenberg_q1_z :
    heisenberg recordingLayer (zAt q1) = -(zAt q1 * zAt q2) := by
  rw [recordingLayer, heisenberg_chronology]
  rw [show heisenberg rightRecordingGate (zAt q1) = zAt q1 by
    simpa [zAt] using rightRecording_fixes_q1 pauliZ]
  exact cnotAt_conjugates_target_z q1 q2 q1_ne_q2

private theorem recordingLayer_heisenberg_q2_x :
    heisenberg recordingLayer (xAt q2) = xAt q1 * xAt q2 := by
  rw [recordingLayer, heisenberg_chronology]
  rw [show heisenberg rightRecordingGate (xAt q2) = xAt q2 by
    simpa [xAt] using rightRecording_fixes_q2 pauliX]
  exact cnotAt_conjugates_control_x q1 q2 q1_ne_q2

private theorem recordingLayer_heisenberg_q2_y :
    heisenberg recordingLayer (yAt q2) = xAt q1 * yAt q2 := by
  rw [recordingLayer, heisenberg_chronology]
  rw [show heisenberg rightRecordingGate (yAt q2) = yAt q2 by
    simpa [yAt] using rightRecording_fixes_q2 pauliY]
  exact cnotAt_conjugates_control_y q1 q2 q1_ne_q2

private theorem recordingLayer_heisenberg_q2_z :
    heisenberg recordingLayer (zAt q2) = zAt q2 := by
  rw [recordingLayer, heisenberg_chronology]
  rw [show heisenberg rightRecordingGate (zAt q2) = zAt q2 by
    simpa [zAt] using rightRecording_fixes_q2 pauliZ]
  exact cnotAt_conjugates_control_z q1 q2 q1_ne_q2

private theorem recordingLayer_heisenberg_q3_x :
    heisenberg recordingLayer (xAt q3) = xAt q4 * xAt q3 := by
  rw [recordingLayer, heisenberg_chronology, rightRecordingGate,
    cnotAt_conjugates_control_x,
    heisenberg_mul_of_unitary _ _ _ leftRecordingGate_unitary]
  rw [show heisenberg leftRecordingGate (xAt q4) = xAt q4 by
    simpa [xAt] using leftRecording_fixes_q4 pauliX]
  rw [show heisenberg leftRecordingGate (xAt q3) = xAt q3 by
    simpa [xAt] using leftRecording_fixes_q3 pauliX]

private theorem recordingLayer_heisenberg_q3_y :
    heisenberg recordingLayer (yAt q3) = xAt q4 * yAt q3 := by
  rw [recordingLayer, heisenberg_chronology, rightRecordingGate,
    cnotAt_conjugates_control_y,
    heisenberg_mul_of_unitary _ _ _ leftRecordingGate_unitary]
  rw [show heisenberg leftRecordingGate (xAt q4) = xAt q4 by
    simpa [xAt] using leftRecording_fixes_q4 pauliX]
  rw [show heisenberg leftRecordingGate (yAt q3) = yAt q3 by
    simpa [yAt] using leftRecording_fixes_q3 pauliY]

private theorem recordingLayer_heisenberg_q3_z :
    heisenberg recordingLayer (zAt q3) = zAt q3 := by
  rw [recordingLayer, heisenberg_chronology, rightRecordingGate,
    cnotAt_conjugates_control_z]
  simpa [zAt] using leftRecording_fixes_q3 pauliZ

private theorem recordingLayer_heisenberg_q4_x :
    heisenberg recordingLayer (xAt q4) = xAt q4 := by
  rw [recordingLayer, heisenberg_chronology, rightRecordingGate,
    cnotAt_conjugates_target_x]
  simpa [xAt] using leftRecording_fixes_q4 pauliX

private theorem recordingLayer_heisenberg_q4_y :
    heisenberg recordingLayer (yAt q4) = -(yAt q4 * zAt q3) := by
  rw [recordingLayer, heisenberg_chronology, rightRecordingGate,
    cnotAt_conjugates_target_y, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ leftRecordingGate_unitary]
  rw [show heisenberg leftRecordingGate (yAt q4) = yAt q4 by
    simpa [yAt] using leftRecording_fixes_q4 pauliY]
  rw [show heisenberg leftRecordingGate (zAt q3) = zAt q3 by
    simpa [zAt] using leftRecording_fixes_q3 pauliZ]

private theorem recordingLayer_heisenberg_q4_z :
    heisenberg recordingLayer (zAt q4) = -(zAt q4 * zAt q3) := by
  rw [recordingLayer, heisenberg_chronology, rightRecordingGate,
    cnotAt_conjugates_target_z, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ leftRecordingGate_unitary]
  rw [show heisenberg leftRecordingGate (zAt q4) = zAt q4 by
    simpa [zAt] using leftRecording_fixes_q4 pauliZ]
  rw [show heisenberg leftRecordingGate (zAt q3) = zAt q3 by
    simpa [zAt] using leftRecording_fixes_q3 pauliZ]

theorem timeThree_q1_x (theta phi : Real) :
    (timeThreeDescriptors theta phi q1).x =
      (timeTwoDescriptors theta phi q1).x := by
  change heisenberg (timeThreeUnitary theta phi) (xAt q1) =
    heisenberg (timeTwoUnitary theta phi) (xAt q1)
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q1_x]

theorem timeThree_q1_y (theta phi : Real) :
    (timeThreeDescriptors theta phi q1).y =
      -((timeTwoDescriptors theta phi q1).y *
        (timeTwoDescriptors theta phi q2).z) := by
  change heisenberg (timeThreeUnitary theta phi) (yAt q1) =
    -(heisenberg (timeTwoUnitary theta phi) (yAt q1) *
      heisenberg (timeTwoUnitary theta phi) (zAt q2))
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q1_y, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeTwoUnitary_unitary theta phi)]

theorem timeThree_q1_z (theta phi : Real) :
    (timeThreeDescriptors theta phi q1).z =
      -((timeTwoDescriptors theta phi q1).z *
        (timeTwoDescriptors theta phi q2).z) := by
  change heisenberg (timeThreeUnitary theta phi) (zAt q1) =
    -(heisenberg (timeTwoUnitary theta phi) (zAt q1) *
      heisenberg (timeTwoUnitary theta phi) (zAt q2))
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q1_z, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeTwoUnitary_unitary theta phi)]

theorem timeThree_q2_x (theta phi : Real) :
    (timeThreeDescriptors theta phi q2).x =
      (timeTwoDescriptors theta phi q1).x *
        (timeTwoDescriptors theta phi q2).x := by
  change heisenberg (timeThreeUnitary theta phi) (xAt q2) =
    heisenberg (timeTwoUnitary theta phi) (xAt q1) *
      heisenberg (timeTwoUnitary theta phi) (xAt q2)
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q2_x,
    heisenberg_mul_of_unitary _ _ _ (timeTwoUnitary_unitary theta phi)]

theorem timeThree_q2_y (theta phi : Real) :
    (timeThreeDescriptors theta phi q2).y =
      (timeTwoDescriptors theta phi q1).x *
        (timeTwoDescriptors theta phi q2).y := by
  change heisenberg (timeThreeUnitary theta phi) (yAt q2) =
    heisenberg (timeTwoUnitary theta phi) (xAt q1) *
      heisenberg (timeTwoUnitary theta phi) (yAt q2)
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q2_y,
    heisenberg_mul_of_unitary _ _ _ (timeTwoUnitary_unitary theta phi)]

theorem timeThree_q2_z (theta phi : Real) :
    (timeThreeDescriptors theta phi q2).z =
      (timeTwoDescriptors theta phi q2).z := by
  change heisenberg (timeThreeUnitary theta phi) (zAt q2) =
    heisenberg (timeTwoUnitary theta phi) (zAt q2)
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q2_z]

theorem timeThree_q3_x (theta phi : Real) :
    (timeThreeDescriptors theta phi q3).x =
      (timeTwoDescriptors theta phi q4).x *
        (timeTwoDescriptors theta phi q3).x := by
  change heisenberg (timeThreeUnitary theta phi) (xAt q3) =
    heisenberg (timeTwoUnitary theta phi) (xAt q4) *
      heisenberg (timeTwoUnitary theta phi) (xAt q3)
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q3_x,
    heisenberg_mul_of_unitary _ _ _ (timeTwoUnitary_unitary theta phi)]

theorem timeThree_q3_y (theta phi : Real) :
    (timeThreeDescriptors theta phi q3).y =
      (timeTwoDescriptors theta phi q4).x *
        (timeTwoDescriptors theta phi q3).y := by
  change heisenberg (timeThreeUnitary theta phi) (yAt q3) =
    heisenberg (timeTwoUnitary theta phi) (xAt q4) *
      heisenberg (timeTwoUnitary theta phi) (yAt q3)
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q3_y,
    heisenberg_mul_of_unitary _ _ _ (timeTwoUnitary_unitary theta phi)]

theorem timeThree_q3_z (theta phi : Real) :
    (timeThreeDescriptors theta phi q3).z =
      (timeTwoDescriptors theta phi q3).z := by
  change heisenberg (timeThreeUnitary theta phi) (zAt q3) =
    heisenberg (timeTwoUnitary theta phi) (zAt q3)
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q3_z]

theorem timeThree_q4_x (theta phi : Real) :
    (timeThreeDescriptors theta phi q4).x =
      (timeTwoDescriptors theta phi q4).x := by
  change heisenberg (timeThreeUnitary theta phi) (xAt q4) =
    heisenberg (timeTwoUnitary theta phi) (xAt q4)
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q4_x]

theorem timeThree_q4_y (theta phi : Real) :
    (timeThreeDescriptors theta phi q4).y =
      -((timeTwoDescriptors theta phi q4).y *
        (timeTwoDescriptors theta phi q3).z) := by
  change heisenberg (timeThreeUnitary theta phi) (yAt q4) =
    -(heisenberg (timeTwoUnitary theta phi) (yAt q4) *
      heisenberg (timeTwoUnitary theta phi) (zAt q3))
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q4_y, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeTwoUnitary_unitary theta phi)]

theorem timeThree_q4_z (theta phi : Real) :
    (timeThreeDescriptors theta phi q4).z =
      -((timeTwoDescriptors theta phi q4).z *
        (timeTwoDescriptors theta phi q3).z) := by
  change heisenberg (timeThreeUnitary theta phi) (zAt q4) =
    -(heisenberg (timeTwoUnitary theta phi) (zAt q4) *
      heisenberg (timeTwoUnitary theta phi) (zAt q3))
  rw [timeThreeUnitary, heisenberg_chronology,
    recordingLayer_heisenberg_q4_z, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (timeTwoUnitary_unitary theta phi)]

/-- Equation (27), left record, factored through the time-two descriptors. -/
theorem equation27_q1 (theta phi : Real) :
    timeThreeDescriptors theta phi q1 =
      { x := (timeTwoDescriptors theta phi q1).x
        y := -((timeTwoDescriptors theta phi q1).y *
          (timeTwoDescriptors theta phi q2).z)
        z := -((timeTwoDescriptors theta phi q1).z *
          (timeTwoDescriptors theta phi q2).z) } := by
  apply Descriptor.ext_components
  · exact timeThree_q1_x theta phi
  · exact timeThree_q1_y theta phi
  · exact timeThree_q1_z theta phi

/-- Equation (27), left EPR qubit after its record CNOT. -/
theorem equation27_q2 (theta phi : Real) :
    timeThreeDescriptors theta phi q2 =
      { x := (timeTwoDescriptors theta phi q1).x *
          (timeTwoDescriptors theta phi q2).x
        y := (timeTwoDescriptors theta phi q1).x *
          (timeTwoDescriptors theta phi q2).y
        z := (timeTwoDescriptors theta phi q2).z } := by
  apply Descriptor.ext_components
  · exact timeThree_q2_x theta phi
  · exact timeThree_q2_y theta phi
  · exact timeThree_q2_z theta phi

/-- Equation (27), right EPR qubit after its record CNOT. -/
theorem equation27_q3 (theta phi : Real) :
    timeThreeDescriptors theta phi q3 =
      { x := (timeTwoDescriptors theta phi q4).x *
          (timeTwoDescriptors theta phi q3).x
        y := (timeTwoDescriptors theta phi q4).x *
          (timeTwoDescriptors theta phi q3).y
        z := (timeTwoDescriptors theta phi q3).z } := by
  apply Descriptor.ext_components
  · exact timeThree_q3_x theta phi
  · exact timeThree_q3_y theta phi
  · exact timeThree_q3_z theta phi

/-- Equation (27), right record, factored through the time-two descriptors. -/
theorem equation27_q4 (theta phi : Real) :
    timeThreeDescriptors theta phi q4 =
      { x := (timeTwoDescriptors theta phi q4).x
        y := -((timeTwoDescriptors theta phi q4).y *
          (timeTwoDescriptors theta phi q3).z)
        z := -((timeTwoDescriptors theta phi q4).z *
          (timeTwoDescriptors theta phi q3).z) } := by
  apply Descriptor.ext_components
  · exact timeThree_q4_x theta phi
  · exact timeThree_q4_y theta phi
  · exact timeThree_q4_z theta phi

end
end EPR
end Deutsch
