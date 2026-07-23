import Deutsch.Gates.Bell
import Mathlib.Tactic.Module

/-!
# Paper façade: specific quantum gates

Source-shaped entries for Equations (9)--(16) and (18)--(21).  Equation (17) belongs to the
arbitrary-axis rotation module and is intentionally not represented here.
-/

namespace Deutsch
namespace Paper

open Foundations Gates Register
open scoped Matrix

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-! ## Transported computation-basis action -/

/--
Equation (9): a NOT truth table at one time transports to the corresponding Heisenberg-frame
basis at the next time.  The hypotheses state only the earlier truth table; the displayed
next-time action is derived by unitary conjugation.
-/
theorem equation09
    (U A : Operator Q)
    (zeroKet oneKet : Ket Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (hZero : act A zeroKet = oneKet)
    (hOne : act A oneKet = zeroKet) :
    act (Register.heisenberg U A) (act Uᴴ zeroKet) = act Uᴴ oneKet ∧
      act (Register.heisenberg U A) (act Uᴴ oneKet) = act Uᴴ zeroKet := by
  have hUU : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hU.2
  constructor
  · simp only [Register.heisenberg, act_mul]
    rw [← act_mul U Uᴴ zeroKet, hUU, act_one, hZero]
  · simp only [Register.heisenberg, act_mul]
    rw [← act_mul U Uᴴ oneKet, hUU, act_one, hOne]

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

/-- Equation (15): CNOT as a polynomial in the current target/control descriptors. -/
def equation15 (D : DescriptorFamily Q) (target control : Q) : Operator Q :=
  cnotFromDescriptors D target control

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

/-- Equation (20): the six components of the Bell transformation on named wires. -/
theorem equation20 (target control : Q) (hne : target ≠ control) :
    DescriptorFamily.evolve (bellAt target control hne)
        (DescriptorFamily.initial Q) target =
        { x := xAt target
          y := -(yAt target * zAt control)
          z := -(zAt target * zAt control) } ∧
      DescriptorFamily.evolve (bellAt target control hne)
        (DescriptorFamily.initial Q) control =
        { x := zAt control
          y := -(xAt target * yAt control)
          z := xAt target * xAt control } :=
  ⟨bellAt_evolves_target_descriptor target control hne,
    bellAt_evolves_control_descriptor target control hne⟩

/-- Equation (21): the six components of the inverse Bell transformation on named wires. -/
theorem equation21 (target control : Q) (hne : target ≠ control) :
    DescriptorFamily.evolve (bellInverseAt target control hne)
        (DescriptorFamily.initial Q) target =
        { x := xAt target
          y := -(yAt target * xAt control)
          z := -(zAt target * xAt control) } ∧
      DescriptorFamily.evolve (bellInverseAt target control hne)
        (DescriptorFamily.initial Q) control =
        { x := xAt target * zAt control
          y := -(xAt target * yAt control)
          z := xAt control } :=
  ⟨bellInverseAt_evolves_target_descriptor target control hne,
    bellInverseAt_evolves_control_descriptor target control hne⟩

end
end Paper
end Deutsch
