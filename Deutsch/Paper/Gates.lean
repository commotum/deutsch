import Deutsch.Gates.Bell
import Deutsch.Gates.AxisRotationRegister
import Mathlib.Tactic.Module

/-!
# Paper façade: specific quantum gates

Source-shaped entries for Equations (9)--(21).
-/

namespace Deutsch
namespace Paper

open Foundations Gates Register NormedSpace
open scoped Matrix

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-! ## Transported computation-basis action -/

/-- An initial computation ket transported to the Heisenberg frame selected by `W`. -/
def computationKetInFrame
    (W : QubitMatrix) (psi : QubitIndex → ℂ) : QubitIndex → ℂ :=
  Wᴴ *ᵥ psi

/-- The NOT gate written in that same Heisenberg frame. -/
def notGateInFrame (W : QubitMatrix) : QubitMatrix :=
  Foundations.heisenberg W notGate

private theorem heisenbergGateAdjoint_mulVec_transport
    (W G : QubitMatrix) (psi : QubitIndex → ℂ)
    (hW : W ∈ Matrix.unitaryGroup QubitIndex ℂ) :
    (Foundations.heisenberg W G)ᴴ *ᵥ (Wᴴ *ᵥ psi) =
      Wᴴ *ᵥ (Gᴴ *ᵥ psi) := by
  have hWW : W * Wᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hW.2
  have hAdjoint :
      (Foundations.heisenberg W G)ᴴ = Wᴴ * Gᴴ * W := by
    unfold Foundations.heisenberg
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simp [Matrix.mul_assoc]
  rw [hAdjoint, Matrix.mulVec_mulVec]
  rw [show (Wᴴ * Gᴴ * W) * Wᴴ =
      Wᴴ * Gᴴ * (W * Wᴴ) by simp [Matrix.mul_assoc]]
  rw [hWW, Matrix.mul_one, ← Matrix.mulVec_mulVec]

/-- Equation (9): the current-frame NOT adjoint exchanges the transported computation kets. -/
theorem equation09
    (W : QubitMatrix)
    (hW : W ∈ Matrix.unitaryGroup QubitIndex ℂ) :
    (notGateInFrame W)ᴴ *ᵥ computationKetInFrame W ketOne =
        computationKetInFrame W ketZero ∧
      (notGateInFrame W)ᴴ *ᵥ computationKetInFrame W ketZero =
        computationKetInFrame W ketOne := by
  constructor
  · rw [notGateInFrame, computationKetInFrame,
      heisenbergGateAdjoint_mulVec_transport W notGate ketOne hW,
      pauliX_isHermitian, not_mulVec_ketOne]
    rfl
  · rw [notGateInFrame, computationKetInFrame,
      heisenbergGateAdjoint_mulVec_transport W notGate ketZero hW,
      pauliX_isHermitian, not_mulVec_ketZero]
    rfl

/-- Initial-frame specialization of Equation (9). -/
theorem equation09_initial :
    notGate.mulVec ketOne = ketZero ∧
      notGate.mulVec ketZero = ketOne :=
  ⟨not_mulVec_ketOne, not_mulVec_ketZero⟩

/-- Equation (10): the source-labelled NOT matrix entries. -/
theorem equation10 (r s : QubitIndex) :
    notGate r s = if r = 1 - s then 1 else 0 :=
  not_matrix_entry r s

/-- Equation (11): NOT is the Pauli `X` matrix. -/
theorem equation11 : notGate = pauliX :=
  rfl

/-- Equation (12): in a current descriptor, NOT is its `X` component. -/
theorem equation12 (d : Descriptor Q) :
    descriptorNot d = d.x :=
  rfl

private theorem descriptorNot_fixes_other
    {D : DescriptorFamily Q} (hD : D.Valid)
    {target other : Q} (hne : target ≠ other) :
    (D other).evolve (descriptorNot (D target)) = D other := by
  apply Descriptor.ext_components
  ·
    change Register.heisenberg (D target).x _ = _
    rw [Register.heisenberg, (hD.each target).x_isHermitian]
    have hcomm :
        (D target).x * (D other).x =
          (D other).x * (D target).x := by
      simpa using hD.cross target other hne .x .x
    calc
      (D target).x * (D other).x * (D target).x =
          (D other).x * ((D target).x * (D target).x) := by
            rw [hcomm, Matrix.mul_assoc]
      _ = (D other).x := by rw [(hD.each target).x_mul_x, Matrix.mul_one]
  ·
    change Register.heisenberg (D target).x _ = _
    rw [Register.heisenberg, (hD.each target).x_isHermitian]
    have hcomm :
        (D target).x * (D other).y =
          (D other).y * (D target).x := by
      simpa using hD.cross target other hne .x .y
    calc
      (D target).x * (D other).y * (D target).x =
          (D other).y * ((D target).x * (D target).x) := by
            rw [hcomm, Matrix.mul_assoc]
      _ = (D other).y := by rw [(hD.each target).x_mul_x, Matrix.mul_one]
  ·
    change Register.heisenberg (D target).x _ = _
    rw [Register.heisenberg, (hD.each target).x_isHermitian]
    have hcomm :
        (D target).x * (D other).z =
          (D other).z * (D target).x := by
      simpa using hD.cross target other hne .x .z
    calc
      (D target).x * (D other).z * (D target).x =
          (D other).z * ((D target).x * (D target).x) := by
            rw [hcomm, Matrix.mul_assoc]
      _ = (D other).z := by rw [(hD.each target).x_mul_x, Matrix.mul_one]

/--
Equation (13): NOT changes the selected current descriptor and leaves every other descriptor
unchanged.
-/
theorem equation13
    (D : DescriptorFamily Q) (hD : D.Valid) (target : Q) :
    (D target).evolve (descriptorNot (D target)) =
        { x := (D target).x, y := -(D target).y, z := -(D target).z } ∧
      ∀ other, target ≠ other →
        (D other).evolve (descriptorNot (D target)) = D other := by
  constructor
  · exact descriptorNot_evolve (hD.each target)
  · intro other hne
    exact descriptorNot_fixes_other hD hne

/-! ## Current-frame one-qubit gates -/

/-- A gate written in the same Heisenberg frame as the current descriptors. -/
def gateInFrame (W G : Operator Q) : Operator Q :=
  Register.heisenberg W G

/-- The descriptor at `q` in the frame selected by the unitary `W`. -/
def descriptorInFrame (W : Operator Q) (q : Q) : Descriptor Q :=
  (Descriptor.initial q).evolve W

/-- Equation (14): the source branch of square-root-of-NOT on a current descriptor. -/
theorem equation14
    (W : Operator Q) (hW : W ∈ Matrix.unitaryGroup (Basis Q) ℂ) (q : Q) :
    (descriptorInFrame W q).evolve (gateInFrame W (paperSqrtNotAt q)) =
      { x := (descriptorInFrame W q).x
        y := (descriptorInFrame W q).z
        z := -(descriptorInFrame W q).y } := by
  apply Descriptor.ext_components
  · change
      Register.heisenberg (Register.heisenberg W (paperSqrtNotAt q))
          (Register.heisenberg W (xAt q)) =
        Register.heisenberg W (xAt q)
    rw [heisenberg_covariance _ _ _ hW, paperSqrtNotAt_heisenberg_x]
  · change
      Register.heisenberg (Register.heisenberg W (paperSqrtNotAt q))
          (Register.heisenberg W (yAt q)) =
        Register.heisenberg W (zAt q)
    rw [heisenberg_covariance _ _ _ hW, paperSqrtNotAt_heisenberg_y]
  · change
      Register.heisenberg (Register.heisenberg W (paperSqrtNotAt q))
          (Register.heisenberg W (zAt q)) =
        -Register.heisenberg W (yAt q)
    rw [heisenberg_covariance _ _ _ hW, paperSqrtNotAt_heisenberg_z]
    simpa only [neg_one_smul] using heisenberg_smul W (yAt q) (-1)

/-- Equation (15): CNOT as the explicit projector polynomial in current descriptors. -/
def equation15 (D : DescriptorFamily Q) (target control : Q) : Operator Q :=
  ((2 : ℂ)⁻¹) • (1 - (D control).z) +
    (D target).x * (((2 : ℂ)⁻¹) • (1 + (D control).z))

theorem equation15_eq_cnotFromDescriptors
    (D : DescriptorFamily Q) (target control : Q) :
    equation15 D target control = cnotFromDescriptors D target control :=
  rfl

/-- Equation (16): the six current-descriptor components after CNOT. -/
theorem equation16
    (D : DescriptorFamily Q) (hD : D.Valid)
    (target control : Q) (hne : target ≠ control) :
    (D target).evolve (equation15 D target control) =
        { x := (D target).x
          y := -((D target).y * (D control).z)
          z := -((D target).z * (D control).z) } ∧
      (D control).evolve (equation15 D target control) =
        { x := (D target).x * (D control).x
          y := (D target).x * (D control).y
          z := (D control).z } := by
  constructor
  · apply Descriptor.ext_components
    · exact cnotFromDescriptors_conjugates_target_x hD hne
    · exact cnotFromDescriptors_conjugates_target_y hD hne
    · exact cnotFromDescriptors_conjugates_target_z hD hne
  · apply Descriptor.ext_components
    · exact cnotFromDescriptors_conjugates_control_x hD hne
    · exact cnotFromDescriptors_conjugates_control_y hD hne
    · exact cnotFromDescriptors_conjugates_control_z hD hne

/-- Equation (17): exponential conjugation about an arbitrary unit descriptor axis. -/
theorem equation17
    (W : Operator Q) (hW : W ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (q : Q) (n : UnitAxis) (theta : ℝ) (a : Axis) :
    Register.heisenberg
        (Register.heisenberg W (axisRotationAt q n theta))
        (((Descriptor.initial q).evolve W).component a) =
      exp ((Complex.I * (theta / 2 : ℂ)) • currentAxisPauli W q n) *
        ((Descriptor.initial q).evolve W).component a *
        exp ((-Complex.I * (theta / 2 : ℂ)) • currentAxisPauli W q n) :=
  axisRotationAt_heisenberg_current_component_exp W q n theta a hW

/-- Rodrigues form of the same arbitrary-axis current-frame transformation. -/
theorem equation17_rodrigues
    (W : Operator Q) (hW : W ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (q : Q) (n : UnitAxis) (theta : ℝ) (v : Vector3) :
    Register.heisenberg (currentAxisRotation W q n theta)
        (descriptorPauliVector ((Descriptor.initial q).evolve W) v) =
      descriptorPauliVector ((Descriptor.initial q).evolve W)
        (Vector3.heisenbergRotate n.1 theta v) :=
  currentAxisRotation_heisenberg W q n theta v hW

/-- Equation (18): an `X` rotation in an arbitrary current Heisenberg frame. -/
theorem equation18
    (W : Operator Q) (hW : W ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (q : Q) (theta : ℝ) :
    (descriptorInFrame W q).evolve
        (gateInFrame W (rotationXAt q theta)) =
      { x := (descriptorInFrame W q).x
        y := (theta.cos : ℂ) • (descriptorInFrame W q).y -
          (theta.sin : ℂ) • (descriptorInFrame W q).z
        z := (theta.sin : ℂ) • (descriptorInFrame W q).y +
          (theta.cos : ℂ) • (descriptorInFrame W q).z } := by
  apply Descriptor.ext_components
  · change
      Register.heisenberg (Register.heisenberg W (rotationXAt q theta))
          (Register.heisenberg W (xAt q)) =
        Register.heisenberg W (xAt q)
    rw [heisenberg_covariance _ _ _ hW, rotationXAt_heisenberg_x]
  · change
      Register.heisenberg (Register.heisenberg W (rotationXAt q theta))
          (Register.heisenberg W (yAt q)) =
        (theta.cos : ℂ) • Register.heisenberg W (yAt q) -
          (theta.sin : ℂ) • Register.heisenberg W (zAt q)
    rw [heisenberg_covariance _ _ _ hW, rotationXAt_heisenberg_y,
      heisenberg_sub, heisenberg_smul, heisenberg_smul]
  · change
      Register.heisenberg (Register.heisenberg W (rotationXAt q theta))
          (Register.heisenberg W (zAt q)) =
        (theta.sin : ℂ) • Register.heisenberg W (yAt q) +
          (theta.cos : ℂ) • Register.heisenberg W (zAt q)
    rw [heisenberg_covariance _ _ _ hW, rotationXAt_heisenberg_z,
      heisenberg_add, heisenberg_smul, heisenberg_smul]

/-- Equation (19): Hadamard in an arbitrary current Heisenberg frame. -/
theorem equation19
    (W : Operator Q) (hW : W ∈ Matrix.unitaryGroup (Basis Q) ℂ) (q : Q) :
    (descriptorInFrame W q).evolve (gateInFrame W (hadamardAt q)) =
      { x := (descriptorInFrame W q).z
        y := -(descriptorInFrame W q).y
        z := (descriptorInFrame W q).x } := by
  apply Descriptor.ext_components
  · change
      Register.heisenberg (Register.heisenberg W (hadamardAt q))
          (Register.heisenberg W (xAt q)) =
        Register.heisenberg W (zAt q)
    rw [heisenberg_covariance _ _ _ hW, hadamardAt_heisenberg_x]
  · change
      Register.heisenberg (Register.heisenberg W (hadamardAt q))
          (Register.heisenberg W (yAt q)) =
        -Register.heisenberg W (yAt q)
    rw [heisenberg_covariance _ _ _ hW, hadamardAt_heisenberg_y]
    simpa only [neg_one_smul] using heisenberg_smul W (yAt q) (-1)
  · change
      Register.heisenberg (Register.heisenberg W (hadamardAt q))
          (Register.heisenberg W (zAt q)) =
        Register.heisenberg W (xAt q)
    rw [heisenberg_covariance _ _ _ hW, hadamardAt_heisenberg_z]

/-- Equation (20): the six components of the Bell transformation in any current frame. -/
theorem equation20
    (W : Operator Q) (hW : W ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (target control : Q) (hne : target ≠ control) :
    (descriptorInFrame W target).evolve
        (gateInFrame W (bellAt target control hne)) =
        { x := (descriptorInFrame W target).x
          y := -((descriptorInFrame W target).y *
            (descriptorInFrame W control).z)
          z := -((descriptorInFrame W target).z *
            (descriptorInFrame W control).z) } ∧
      (descriptorInFrame W control).evolve
        (gateInFrame W (bellAt target control hne)) =
        { x := (descriptorInFrame W control).z
          y := -((descriptorInFrame W target).x *
            (descriptorInFrame W control).y)
          z := (descriptorInFrame W target).x *
            (descriptorInFrame W control).x } := by
  constructor
  · apply Descriptor.ext_components
    ·
      change
        Register.heisenberg (Register.heisenberg W (bellAt target control hne))
            (Register.heisenberg W (xAt target)) =
          Register.heisenberg W (xAt target)
      rw [Register.heisenberg_covariance _ _ _ hW,
        bellAt_conjugates_target_x]
    ·
      change
        Register.heisenberg (Register.heisenberg W (bellAt target control hne))
            (Register.heisenberg W (yAt target)) =
          -(Register.heisenberg W (yAt target) *
            Register.heisenberg W (zAt control))
      rw [Register.heisenberg_covariance _ _ _ hW,
        bellAt_conjugates_target_y, Gates.heisenberg_neg,
        Register.heisenberg_mul_of_unitary W _ _ hW]
    ·
      change
        Register.heisenberg (Register.heisenberg W (bellAt target control hne))
            (Register.heisenberg W (zAt target)) =
          -(Register.heisenberg W (zAt target) *
            Register.heisenberg W (zAt control))
      rw [Register.heisenberg_covariance _ _ _ hW,
        bellAt_conjugates_target_z, Gates.heisenberg_neg,
        Register.heisenberg_mul_of_unitary W _ _ hW]
  · apply Descriptor.ext_components
    ·
      change
        Register.heisenberg (Register.heisenberg W (bellAt target control hne))
            (Register.heisenberg W (xAt control)) =
          Register.heisenberg W (zAt control)
      rw [Register.heisenberg_covariance _ _ _ hW,
        bellAt_conjugates_control_x]
    ·
      change
        Register.heisenberg (Register.heisenberg W (bellAt target control hne))
            (Register.heisenberg W (yAt control)) =
          -(Register.heisenberg W (xAt target) *
            Register.heisenberg W (yAt control))
      rw [Register.heisenberg_covariance _ _ _ hW,
        bellAt_conjugates_control_y, Gates.heisenberg_neg,
        Register.heisenberg_mul_of_unitary W _ _ hW]
    ·
      change
        Register.heisenberg (Register.heisenberg W (bellAt target control hne))
            (Register.heisenberg W (zAt control)) =
          Register.heisenberg W (xAt target) *
            Register.heisenberg W (xAt control)
      rw [Register.heisenberg_covariance _ _ _ hW,
        bellAt_conjugates_control_z,
        Register.heisenberg_mul_of_unitary W _ _ hW]

/-- Equation (21): the six components of the inverse Bell transformation in any current frame. -/
theorem equation21
    (W : Operator Q) (hW : W ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (target control : Q) (hne : target ≠ control) :
    (descriptorInFrame W target).evolve
        (gateInFrame W (bellInverseAt target control hne)) =
        { x := (descriptorInFrame W target).x
          y := -((descriptorInFrame W target).y *
            (descriptorInFrame W control).x)
          z := -((descriptorInFrame W target).z *
            (descriptorInFrame W control).x) } ∧
      (descriptorInFrame W control).evolve
        (gateInFrame W (bellInverseAt target control hne)) =
        { x := (descriptorInFrame W target).x *
            (descriptorInFrame W control).z
          y := -((descriptorInFrame W target).x *
            (descriptorInFrame W control).y)
          z := (descriptorInFrame W control).x } := by
  constructor
  · apply Descriptor.ext_components
    ·
      change
        Register.heisenberg
            (Register.heisenberg W (bellInverseAt target control hne))
            (Register.heisenberg W (xAt target)) =
          Register.heisenberg W (xAt target)
      rw [Register.heisenberg_covariance _ _ _ hW,
        bellInverseAt_conjugates_target_x]
    ·
      change
        Register.heisenberg
            (Register.heisenberg W (bellInverseAt target control hne))
            (Register.heisenberg W (yAt target)) =
          -(Register.heisenberg W (yAt target) *
            Register.heisenberg W (xAt control))
      rw [Register.heisenberg_covariance _ _ _ hW,
        bellInverseAt_conjugates_target_y, Gates.heisenberg_neg,
        Register.heisenberg_mul_of_unitary W _ _ hW]
    ·
      change
        Register.heisenberg
            (Register.heisenberg W (bellInverseAt target control hne))
            (Register.heisenberg W (zAt target)) =
          -(Register.heisenberg W (zAt target) *
            Register.heisenberg W (xAt control))
      rw [Register.heisenberg_covariance _ _ _ hW,
        bellInverseAt_conjugates_target_z, Gates.heisenberg_neg,
        Register.heisenberg_mul_of_unitary W _ _ hW]
  · apply Descriptor.ext_components
    ·
      change
        Register.heisenberg
            (Register.heisenberg W (bellInverseAt target control hne))
            (Register.heisenberg W (xAt control)) =
          Register.heisenberg W (xAt target) *
            Register.heisenberg W (zAt control)
      rw [Register.heisenberg_covariance _ _ _ hW,
        bellInverseAt_conjugates_control_x,
        Register.heisenberg_mul_of_unitary W _ _ hW]
    ·
      change
        Register.heisenberg
            (Register.heisenberg W (bellInverseAt target control hne))
            (Register.heisenberg W (yAt control)) =
          -(Register.heisenberg W (xAt target) *
            Register.heisenberg W (yAt control))
      rw [Register.heisenberg_covariance _ _ _ hW,
        bellInverseAt_conjugates_control_y, Gates.heisenberg_neg,
        Register.heisenberg_mul_of_unitary W _ _ hW]
    ·
      change
        Register.heisenberg
            (Register.heisenberg W (bellInverseAt target control hne))
            (Register.heisenberg W (zAt control)) =
          Register.heisenberg W (xAt control)
      rw [Register.heisenberg_covariance _ _ _ hW,
        bellInverseAt_conjugates_control_z]

end
end Paper
end Deutsch
