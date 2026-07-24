import Deutsch.Gates.Bell
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module

/-!
# The two-qubit EPR resource

This module isolates the phase-sensitive two-qubit core of the paper's EPR circuit.  Coordinates
`0` and `1` are respectively the target and control of the inverse Bell operation.  Paper logical
bits retain the project's reversed raw-index convention: paper zero is raw index `1`.
-/

namespace Deutsch
namespace EPR

open Foundations Gates Register
open scoped Matrix

noncomputable section

/-- A raw two-qubit basis assignment, with coordinate `0` written first. -/
def pairBits (left right : QubitIndex) : Basis (Fin 2) := ![left, right]

@[simp]
theorem pairBits_zero (left right : QubitIndex) : pairBits left right 0 = left := rfl

@[simp]
theorem pairBits_one (left right : QubitIndex) : pairBits left right 1 = right := rfl

/-- The source-labelled pair `|0,0⟩`, represented by raw indices `(1,1)`. -/
def paperZeroZero : Basis (Fin 2) := pairBits 1 1

/-- The source-labelled pair `|1,1⟩`, represented by raw indices `(0,0)`. -/
def paperOneOne : Basis (Fin 2) := pairBits 0 0

/-- The source-labelled pair `|1,0⟩`, represented by raw indices `(0,1)`. -/
def paperOneZero : Basis (Fin 2) := pairBits 0 1

/-- The source-labelled pair `|0,1⟩`, represented by raw indices `(1,0)`. -/
def paperZeroOne : Basis (Fin 2) := pairBits 1 0

theorem paperZeroZero_eq_reference :
    paperZeroZero = paperZeroAssignment (Fin 2) := by
  funext q
  fin_cases q <;> rfl

/-- The inverse Bell resource preparation, with the first qubit target and the second control. -/
def pairPreparation : Operator (Fin 2) :=
  bellInverseAt (0 : Fin 2) (1 : Fin 2) (by decide)

theorem pairPreparation_unitary :
    pairPreparation ∈ Matrix.unitaryGroup (Basis (Fin 2)) ℂ := by
  exact bellInverseAt_unitary (0 : Fin 2) (1 : Fin 2) (by decide)

/-- Independent local `X` rotations, applied after resource preparation. -/
def pairRotations (theta phi : ℝ) : Operator (Fin 2) :=
  rotationXAt (1 : Fin 2) phi * rotationXAt (0 : Fin 2) theta

theorem pairRotations_unitary (theta phi : ℝ) :
    pairRotations theta phi ∈ Matrix.unitaryGroup (Basis (Fin 2)) ℂ := by
  exact (Matrix.unitaryGroup (Basis (Fin 2)) ℂ).mul_mem
    (rotationXAt_unitary (1 : Fin 2) phi)
    (rotationXAt_unitary (0 : Fin 2) theta)

/-- The complete two-qubit preparation-and-rotation circuit through the paper's time `t=2`. -/
def pairCircuit (theta phi : ℝ) : Operator (Fin 2) :=
  pairRotations theta phi * pairPreparation

theorem pairCircuit_unitary (theta phi : ℝ) :
    pairCircuit theta phi ∈ Matrix.unitaryGroup (Basis (Fin 2)) ℂ := by
  exact (Matrix.unitaryGroup (Basis (Fin 2)) ℂ).mul_mem
    (pairRotations_unitary theta phi) pairPreparation_unitary

/-- The exact resource ket produced using the library's conventionally phased Hadamard. -/
def pairKet : Ket (Fin 2) := act pairPreparation (referenceKet (Fin 2))

/-- Equation (22), including the source's explicit global phase. -/
def equation22Ket : Ket (Fin 2) :=
  (Complex.I * invSqrtTwo) •
    (basisKet paperZeroZero - basisKet paperOneOne)

/-- The exact inverse-Bell output in the library phase convention. -/
theorem pairKet_eq :
    pairKet = invSqrtTwo •
      (basisKet paperOneOne - basisKet paperZeroZero) := by
  apply WithLp.ofLp_injective
  change pairPreparation *ᵥ Pi.single (paperZeroAssignment (Fin 2)) 1 =
    invSqrtTwo •
      (Pi.single paperOneOne 1 - Pi.single paperZeroZero 1)
  funext output
  have hout : output = pairBits (output 0) (output 1) := by
    funext q
    fin_cases q <;> rfl
  rw [hout]
  generalize output 0 = left
  generalize output 1 = right
  fin_cases left <;> fin_cases right <;>
    simp [pairPreparation, paperZeroZero, paperOneOne, pairBits,
      bellInverseAt_apply, hadamard, invSqrtTwo, targetControlPlacement,
      flipRaw]

/-- The Equation (22) ket differs from the exact library ket only by global phase `-i`. -/
theorem equation22Ket_eq_globalPhase :
    equation22Ket = (-Complex.I) • pairKet := by
  rw [pairKet_eq]
  simp only [equation22Ket]
  module

/-- The route that places angle `theta` on the first/target qubit. -/
def leftRotationRoute (theta : ℝ) : Operator (Fin 2) :=
  rotationXAt (0 : Fin 2) theta * pairPreparation

/-- The alternative Equation (39) route, placing angle `-theta` on the second/control qubit. -/
def rightRotationRoute (theta : ℝ) : Operator (Fin 2) :=
  rotationXAt (1 : Fin 2) (-theta) * pairPreparation

theorem leftRotationRoute_unitary (theta : ℝ) :
    leftRotationRoute theta ∈ Matrix.unitaryGroup (Basis (Fin 2)) ℂ := by
  exact (Matrix.unitaryGroup (Basis (Fin 2)) ℂ).mul_mem
    (rotationXAt_unitary (0 : Fin 2) theta) pairPreparation_unitary

theorem rightRotationRoute_unitary (theta : ℝ) :
    rightRotationRoute theta ∈ Matrix.unitaryGroup (Basis (Fin 2)) ℂ := by
  exact (Matrix.unitaryGroup (Basis (Fin 2)) ℂ).mul_mem
    (rotationXAt_unitary (1 : Fin 2) (-theta)) pairPreparation_unitary

private theorem act_add_ket (A : Operator (Fin 2)) (psi chi : Ket (Fin 2)) :
    act A (psi + chi) = act A psi + act A chi := by
  exact (matrixEndEquiv (Fin 2) A).map_add psi chi

private theorem act_sub_ket (A : Operator (Fin 2)) (psi chi : Ket (Fin 2)) :
    act A (psi - chi) = act A psi - act A chi := by
  exact (matrixEndEquiv (Fin 2) A).map_sub psi chi

private theorem rotationXAt_zero_act_pairBits (theta : ℝ)
    (left right : QubitIndex) :
    act (rotationXAt (0 : Fin 2) theta) (basisKet (pairBits left right)) =
      rotationCosHalf theta • basisKet (pairBits left right) -
        (Complex.I * rotationSinHalf theta) •
          basisKet (pairBits (flipRaw left) right) := by
  apply WithLp.ofLp_injective
  change rotationXAt (0 : Fin 2) theta *ᵥ Pi.single (pairBits left right) 1 =
    rotationCosHalf theta • Pi.single (pairBits left right) 1 -
      (Complex.I * rotationSinHalf theta) •
        Pi.single (pairBits (flipRaw left) right) 1
  rw [Matrix.mulVec_single_one]
  funext output
  have hout : output = pairBits (output 0) (output 1) := by
    funext q
    fin_cases q <;> rfl
  rw [hout]
  generalize output 0 = outLeft
  generalize output 1 = outRight
  change embedQubit (0 : Fin 2) (rotationX theta)
      (pairBits outLeft outRight) (pairBits left right) = _
  rw [embedQubit_apply_ite]
  fin_cases left <;> fin_cases right <;>
    fin_cases outLeft <;> fin_cases outRight <;>
    simp [rotationX, identity₂, pauliX, pairBits, flipRaw]

private theorem rotationXAt_one_act_pairBits (phi : ℝ)
    (left right : QubitIndex) :
    act (rotationXAt (1 : Fin 2) phi) (basisKet (pairBits left right)) =
      rotationCosHalf phi • basisKet (pairBits left right) -
        (Complex.I * rotationSinHalf phi) •
          basisKet (pairBits left (flipRaw right)) := by
  apply WithLp.ofLp_injective
  change rotationXAt (1 : Fin 2) phi *ᵥ Pi.single (pairBits left right) 1 =
    rotationCosHalf phi • Pi.single (pairBits left right) 1 -
      (Complex.I * rotationSinHalf phi) •
        Pi.single (pairBits left (flipRaw right)) 1
  rw [Matrix.mulVec_single_one]
  funext output
  have hout : output = pairBits (output 0) (output 1) := by
    funext q
    fin_cases q <;> rfl
  rw [hout]
  generalize output 0 = outLeft
  generalize output 1 = outRight
  change embedQubit (1 : Fin 2) (rotationX phi)
      (pairBits outLeft outRight) (pairBits left right) = _
  rw [embedQubit_apply_ite]
  fin_cases left <;> fin_cases right <;>
    fin_cases outLeft <;> fin_cases outRight <;>
    simp [rotationX, identity₂, pauliX, pairBits, flipRaw]

/-- The unnormalized correlated Bell direction `|1,1⟩ - |0,0⟩` in paper labels. -/
def samePairKet : Ket (Fin 2) :=
  basisKet paperOneOne - basisKet paperZeroZero

/-- The unnormalized complementary direction `|1,0⟩ - |0,1⟩` in paper labels. -/
def crossPairKet : Ket (Fin 2) :=
  basisKet paperOneZero - basisKet paperZeroOne

private theorem rotationXAt_zero_act_samePair (theta : ℝ) :
    act (rotationXAt (0 : Fin 2) theta) samePairKet =
      rotationCosHalf theta • samePairKet +
        (Complex.I * rotationSinHalf theta) • crossPairKet := by
  rw [samePairKet, crossPairKet, act_sub_ket,
    show paperOneOne = pairBits 0 0 by rfl,
    show paperZeroZero = pairBits 1 1 by rfl,
    show paperOneZero = pairBits 0 1 by rfl,
    show paperZeroOne = pairBits 1 0 by rfl,
    rotationXAt_zero_act_pairBits, rotationXAt_zero_act_pairBits,
    flipRaw_zero, flipRaw_one]
  module

private theorem rotationXAt_one_act_samePair (phi : ℝ) :
    act (rotationXAt (1 : Fin 2) phi) samePairKet =
      rotationCosHalf phi • samePairKet -
        (Complex.I * rotationSinHalf phi) • crossPairKet := by
  rw [samePairKet, crossPairKet, act_sub_ket,
    show paperOneOne = pairBits 0 0 by rfl,
    show paperZeroZero = pairBits 1 1 by rfl,
    show paperOneZero = pairBits 0 1 by rfl,
    show paperZeroOne = pairBits 1 0 by rfl,
    rotationXAt_one_act_pairBits, rotationXAt_one_act_pairBits,
    flipRaw_zero, flipRaw_one]
  module

private theorem rotationXAt_one_act_crossPair (phi : ℝ) :
    act (rotationXAt (1 : Fin 2) phi) crossPairKet =
      rotationCosHalf phi • crossPairKet -
        (Complex.I * rotationSinHalf phi) • samePairKet := by
  rw [samePairKet, crossPairKet, act_sub_ket,
    show paperOneOne = pairBits 0 0 by rfl,
    show paperZeroZero = pairBits 1 1 by rfl,
    show paperOneZero = pairBits 0 1 by rfl,
    show paperZeroOne = pairBits 1 0 by rfl,
    rotationXAt_one_act_pairBits, rotationXAt_one_act_pairBits,
    flipRaw_zero, flipRaw_one]
  module

/--
The general four-coordinate Schrödinger output after independent local rotations.  Coefficients
are kept in the half-angle form supplied by the gate API, avoiding any hidden rotation mnemonic.
-/
theorem pairCircuit_referenceKet_eq_four_coordinates (theta phi : ℝ) :
    act (pairCircuit theta phi) (referenceKet (Fin 2)) =
      invSqrtTwo •
        ((((rotationCosHalf theta * rotationCosHalf phi) -
              (Complex.I * rotationSinHalf theta) *
                (Complex.I * rotationSinHalf phi)) • samePairKet) +
          ((((Complex.I * rotationSinHalf theta) * rotationCosHalf phi) -
              rotationCosHalf theta * (Complex.I * rotationSinHalf phi)) •
            crossPairKet)) := by
  rw [pairCircuit, pairRotations, act_mul, act_mul]
  change act (rotationXAt (1 : Fin 2) phi)
      (act (rotationXAt (0 : Fin 2) theta) pairKet) = _
  rw [pairKet_eq]
  change act (rotationXAt (1 : Fin 2) phi)
      (act (rotationXAt (0 : Fin 2) theta) (invSqrtTwo • samePairKet)) = _
  rw [act_smul, rotationXAt_zero_act_samePair]
  rw [act_smul, act_add_ket]
  rw [act_smul, rotationXAt_one_act_samePair]
  rw [act_smul, rotationXAt_one_act_crossPair]
  module

/-- Equation (39): the two local preparation routes agree on this EPR resource ket. -/
theorem equation39_route_kets_eq (theta : ℝ) :
    act (leftRotationRoute theta) (referenceKet (Fin 2)) =
      act (rightRotationRoute theta) (referenceKet (Fin 2)) := by
  rw [leftRotationRoute, rightRotationRoute, act_mul, act_mul]
  change act (rotationXAt (0 : Fin 2) theta) pairKet =
    act (rotationXAt (1 : Fin 2) (-theta)) pairKet
  rw [pairKet_eq, act_smul, act_smul]
  change invSqrtTwo •
      act (rotationXAt (0 : Fin 2) theta) samePairKet =
    invSqrtTwo •
      act (rotationXAt (1 : Fin 2) (-theta)) samePairKet
  rw [rotationXAt_zero_act_samePair, rotationXAt_one_act_samePair]
  have hcos : rotationCosHalf (-theta) = rotationCosHalf theta := by
    change ((Real.cos ((-theta) / 2) : ℝ) : ℂ) =
      ((Real.cos (theta / 2) : ℝ) : ℂ)
    exact congrArg (fun r : ℝ ↦ (r : ℂ)) (by
      rw [neg_div, Real.cos_neg])
  have hsin : rotationSinHalf (-theta) = -rotationSinHalf theta := by
    change ((Real.sin ((-theta) / 2) : ℝ) : ℂ) =
      -((Real.sin (theta / 2) : ℝ) : ℂ)
    simpa only [Complex.ofReal_neg] using congrArg (fun r : ℝ ↦ (r : ℂ)) (by
      rw [neg_div, Real.sin_neg] :
        Real.sin ((-theta) / 2) = -Real.sin (theta / 2))
  rw [hcos, hsin]
  module


end
end EPR
end Deutsch
