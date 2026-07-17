import Deutsch.Descriptor.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# One-qubit gates

Concrete NOT, `X`-axis rotations, the square-root-of-NOT branch printed by
Deutsch--Hayden, and Hadamard.  The local matrix identities are lifted to arbitrary named
register coordinates through `Register.embedQubit`.

`rotationX theta` is the Schrödinger unitary
`cos (theta/2) I - i sin (theta/2) X`.  Under the project's Heisenberg convention `Uᴴ A U`,
this sends `Y` to `cos theta Y - sin theta Z` and `Z` to
`sin theta Y + cos theta Z`.  Those signs follow from the exponential in the paper's Equation
(17), but are opposite to the signs printed in Equation (18).  `paperSqrtNot` deliberately keeps
the branch printed in Equation (14), which is opposite to `rotationX (pi/2)`; its chosen global
phase makes its square exactly `X` rather than merely a phase multiple of `X`.
-/

namespace Deutsch
namespace Gates

open Foundations Register
open scoped Matrix

noncomputable section

/-! ## Local matrices -/

/-- NOT is definitionally the existing Pauli `X`; no second matrix convention is introduced. -/
abbrev notGate : QubitMatrix := pauliX

/-- The real cosine coefficient in the closed form for `rotationX`. -/
def rotationCosHalf (theta : Real) : Complex :=
  Real.cos (theta / 2)

/-- The real sine coefficient in the closed form for `rotationX`. -/
def rotationSinHalf (theta : Real) : Complex :=
  Real.sin (theta / 2)

/-- `X`-axis Schrödinger rotation `exp (-i theta X / 2)`, in closed Pauli form. -/
def rotationX (theta : Real) : QubitMatrix :=
  rotationCosHalf theta • identity₂ -
    (Complex.I * rotationSinHalf theta) • pauliX

/--
An exact square root of NOT whose Heisenberg map is the branch printed in Equation (14):
`(X,Y,Z) -> (X,Z,-Y)`.  The selected phase makes `paperSqrtNot * paperSqrtNot = X` exactly.
-/
def paperSqrtNot : QubitMatrix :=
  ((2 : Complex)⁻¹) •
    (((1 - Complex.I) : Complex) • identity₂ +
      ((1 + Complex.I) : Complex) • pauliX)

/-- The positive real normalization coefficient `1 / sqrt 2`, embedded in `Complex`. -/
def invSqrtTwo : Complex :=
  ((Real.sqrt 2 : Real) : Complex)⁻¹

/-- The conventional, exactly phased Hadamard matrix. -/
def hadamard : QubitMatrix :=
  invSqrtTwo • !![1, 1; 1, -1]

/-! ## NOT -/

theorem not_mulVec_ketOne : notGate.mulVec ketOne = ketZero := by
  funext i
  fin_cases i <;>
    norm_num [notGate, pauliX, ketOne, ketZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem not_mulVec_ketZero : notGate.mulVec ketZero = ketOne := by
  funext i
  fin_cases i <;>
    norm_num [notGate, pauliX, ketOne, ketZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

/-- Equation (10), with paper logical labels and their reversed raw matrix indices explicit. -/
theorem not_matrix_entry (r s : QubitIndex) :
    notGate r s = if r = 1 - s then 1 else 0 := by
  fin_cases r <;> fin_cases s <;> norm_num [notGate, pauliX]

theorem not_involution : notGate * notGate = identity₂ :=
  pauliX_mul_pauliX

theorem not_unitary : notGate ∈ Matrix.unitaryGroup QubitIndex Complex :=
  pauliX_unitary

theorem not_heisenberg_x : Foundations.heisenberg notGate pauliX = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Foundations.heisenberg, notGate, pauliX, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem not_heisenberg_y : Foundations.heisenberg notGate pauliY = -pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Foundations.heisenberg, notGate, pauliX, pauliY, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

theorem not_heisenberg_z : Foundations.heisenberg notGate pauliZ = -pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Foundations.heisenberg, notGate, pauliX, pauliZ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

/-! ## Symbolic `X` rotations -/

@[simp]
private theorem star_rotationCosHalf (theta : Real) :
    star (rotationCosHalf theta) = rotationCosHalf theta := by
  unfold rotationCosHalf
  rw [Complex.star_def, Complex.conj_ofReal]

@[simp]
private theorem star_rotationSinHalf (theta : Real) :
    star (rotationSinHalf theta) = rotationSinHalf theta := by
  unfold rotationSinHalf
  rw [Complex.star_def, Complex.conj_ofReal]

@[simp]
private theorem starRingEnd_rotationCosHalf (theta : Real) :
    (starRingEnd Complex) (rotationCosHalf theta) = rotationCosHalf theta := by
  simpa only [starRingEnd_apply] using star_rotationCosHalf theta

@[simp]
private theorem starRingEnd_rotationSinHalf (theta : Real) :
    (starRingEnd Complex) (rotationSinHalf theta) = rotationSinHalf theta := by
  simpa only [starRingEnd_apply] using star_rotationSinHalf theta

private theorem rotation_half_sq_sum (theta : Real) :
    rotationCosHalf theta * rotationCosHalf theta +
      rotationSinHalf theta * rotationSinHalf theta = 1 := by
  change ((Real.cos (theta / 2) : Real) : Complex) * Real.cos (theta / 2) +
    ((Real.sin (theta / 2) : Real) : Complex) * Real.sin (theta / 2) = 1
  norm_cast
  nlinarith [Real.sin_sq_add_cos_sq (theta / 2)]

private theorem rotation_cos_eq_half_sq_sub (theta : Real) :
    Complex.cos (theta : Complex) =
      rotationCosHalf theta * rotationCosHalf theta -
        rotationSinHalf theta * rotationSinHalf theta := by
  rw [← Complex.ofReal_cos]
  unfold rotationCosHalf rotationSinHalf
  norm_cast
  rw [show theta = theta / 2 + theta / 2 by ring_nf, Real.cos_add]
  ring_nf

private theorem rotation_sin_eq_two_half_mul (theta : Real) :
    Complex.sin (theta : Complex) =
      2 * rotationSinHalf theta * rotationCosHalf theta := by
  rw [← Complex.ofReal_sin]
  unfold rotationCosHalf rotationSinHalf
  norm_cast
  rw [show theta = theta / 2 + theta / 2 by ring_nf, Real.sin_add]
  ring_nf

theorem rotationX_unitary (theta : Real) :
    rotationX theta ∈ Matrix.unitaryGroup QubitIndex Complex := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (rotationX theta)ᴴ * rotationX theta = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotationX, identity₂, pauliX, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.one_apply] <;>
      ring_nf
  all_goals
    have h := rotation_half_sq_sum theta
    ring_nf at h ⊢
    simp only [show Complex.I ^ 2 = (-1 : Complex) by norm_num] at ⊢
    ring_nf at ⊢
    exact h

theorem rotationX_mulVec_ketOne (theta : Real) :
    (rotationX theta).mulVec ketOne =
      rotationCosHalf theta • ketOne -
        (Complex.I * rotationSinHalf theta) • ketZero := by
  funext i
  fin_cases i <;>
    simp [rotationX, identity₂, pauliX, ketOne, ketZero, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

theorem rotationX_mulVec_ketZero (theta : Real) :
    (rotationX theta).mulVec ketZero =
      rotationCosHalf theta • ketZero -
        (Complex.I * rotationSinHalf theta) • ketOne := by
  funext i
  fin_cases i <;>
    simp [rotationX, identity₂, pauliX, ketOne, ketZero, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

theorem rotationX_heisenberg_x (theta : Real) :
    Foundations.heisenberg (rotationX theta) pauliX = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Foundations.heisenberg, rotationX, identity₂, pauliX,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.one_apply] <;> ring_nf
  all_goals
    have h := rotation_half_sq_sum theta
    ring_nf at h ⊢
    simp only [show Complex.I ^ 2 = (-1 : Complex) by norm_num] at ⊢
    ring_nf at ⊢
    exact h

/-- Corrected `Y` component of Equation (18), forced by Equation (17) and `XY = iZ`. -/
theorem rotationX_heisenberg_y (theta : Real) :
    Foundations.heisenberg (rotationX theta) pauliY =
      (theta.cos : Complex) • pauliY - (theta.sin : Complex) • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Foundations.heisenberg, rotationX, identity₂, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.one_apply] <;> ring_nf
  all_goals
    simp only [rotation_cos_eq_half_sq_sub, rotation_sin_eq_two_half_mul,
      pow_two, Complex.I_mul_I]
    ring_nf <;> norm_num [Complex.ext_iff, sub_eq_add_neg]

/-- Corrected `Z` component of Equation (18), forced by Equation (17) and `XY = iZ`. -/
theorem rotationX_heisenberg_z (theta : Real) :
    Foundations.heisenberg (rotationX theta) pauliZ =
      (theta.sin : Complex) • pauliY + (theta.cos : Complex) • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Foundations.heisenberg, rotationX, identity₂, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.one_apply] <;> ring_nf
  all_goals
    simp only [rotation_cos_eq_half_sq_sub, rotation_sin_eq_two_half_mul,
      pow_two, Complex.I_mul_I]
    ring_nf

@[simp]
theorem rotationX_zero : rotationX 0 = identity₂ := by
  simp [rotationX, rotationCosHalf, rotationSinHalf]

theorem rotationX_heisenberg_y_pi_div_two :
    Foundations.heisenberg (rotationX (Real.pi / 2)) pauliY = -pauliZ := by
  simpa using rotationX_heisenberg_y (Real.pi / 2)

theorem rotationX_heisenberg_z_pi_div_two :
    Foundations.heisenberg (rotationX (Real.pi / 2)) pauliZ = pauliY := by
  simpa using rotationX_heisenberg_z (Real.pi / 2)

theorem rotationX_heisenberg_y_neg_pi_div_two :
    Foundations.heisenberg (rotationX (-Real.pi / 2)) pauliY = pauliZ := by
  rw [rotationX_heisenberg_y]
  simp [neg_div]

theorem rotationX_heisenberg_z_neg_pi_div_two :
    Foundations.heisenberg (rotationX (-Real.pi / 2)) pauliZ = -pauliY := by
  rw [rotationX_heisenberg_z]
  simp [neg_div]

/-- The positive sine sign printed for `Y` in Equation (18) fails at `theta = pi/2`. -/
theorem rotationX_heisenberg_y_pi_div_two_ne_printed :
    Foundations.heisenberg (rotationX (Real.pi / 2)) pauliY ≠ pauliZ := by
  rw [rotationX_heisenberg_y_pi_div_two]
  intro h
  have h00 := congrFun (congrFun h (0 : QubitIndex)) (0 : QubitIndex)
  norm_num [pauliZ] at h00

/-- The negative sine sign printed for `Z` in Equation (18) fails at `theta = pi/2`. -/
theorem rotationX_heisenberg_z_pi_div_two_ne_printed :
    Foundations.heisenberg (rotationX (Real.pi / 2)) pauliZ ≠ -pauliY := by
  rw [rotationX_heisenberg_z_pi_div_two]
  intro h
  have h01 := congrFun (congrFun h (0 : QubitIndex)) (1 : QubitIndex)
  have him := congrArg Complex.im h01
  norm_num [pauliY] at him

theorem rotationX_heisenberg_y_pi :
    Foundations.heisenberg (rotationX Real.pi) pauliY = -pauliY := by
  simpa using rotationX_heisenberg_y Real.pi

theorem rotationX_heisenberg_z_pi :
    Foundations.heisenberg (rotationX Real.pi) pauliZ = -pauliZ := by
  simpa using rotationX_heisenberg_z Real.pi

/-! ## The paper's square-root branch -/

theorem paperSqrtNot_unitary :
    paperSqrtNot ∈ Matrix.unitaryGroup QubitIndex Complex := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperSqrtNot, identity₂, pauliX, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.one_apply]
  all_goals simp only [map_ofNat]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

theorem paperSqrtNot_square : paperSqrtNot * paperSqrtNot = notGate := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [paperSqrtNot, notGate, identity₂, pauliX, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.one_apply]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

theorem paperSqrtNot_mulVec_ketOne :
    paperSqrtNot.mulVec ketOne =
      (((2 : Complex)⁻¹ * (1 - Complex.I)) • ketOne +
        ((2 : Complex)⁻¹ * (1 + Complex.I)) • ketZero) := by
  funext i
  fin_cases i <;>
    norm_num [paperSqrtNot, identity₂, pauliX, ketOne, ketZero, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

theorem paperSqrtNot_mulVec_ketZero :
    paperSqrtNot.mulVec ketZero =
      (((2 : Complex)⁻¹ * (1 + Complex.I)) • ketOne +
        ((2 : Complex)⁻¹ * (1 - Complex.I)) • ketZero) := by
  funext i
  fin_cases i <;>
    norm_num [paperSqrtNot, identity₂, pauliX, ketOne, ketZero, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, Matrix.one_apply]

theorem paperSqrtNot_heisenberg_x :
    Foundations.heisenberg paperSqrtNot pauliX = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Foundations.heisenberg, paperSqrtNot, identity₂, pauliX,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.one_apply]
  all_goals simp only [map_ofNat]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

theorem paperSqrtNot_heisenberg_y :
    Foundations.heisenberg paperSqrtNot pauliY = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Foundations.heisenberg, paperSqrtNot, identity₂, pauliX,
      pauliY, pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.one_apply]
  all_goals simp only [map_ofNat]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

theorem paperSqrtNot_heisenberg_z :
    Foundations.heisenberg paperSqrtNot pauliZ = -pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Foundations.heisenberg, paperSqrtNot, identity₂, pauliX,
      pauliY, pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Matrix.one_apply]
  all_goals simp only [map_ofNat]
  all_goals ring_nf

/-- Two applications of the paper branch give the exact NOT Heisenberg action, not just a ray. -/
theorem paperSqrtNot_heisenberg_twice (A : QubitMatrix) :
    Foundations.heisenberg paperSqrtNot
        (Foundations.heisenberg paperSqrtNot A) =
      Foundations.heisenberg notGate A := by
  rw [← paperSqrtNot_square]
  simp [Foundations.heisenberg, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-! ## Hadamard -/

private theorem invSqrtTwo_sq :
    invSqrtTwo * invSqrtTwo = (2 : Complex)⁻¹ := by
  have hs : (Real.sqrt 2 : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [invSqrtTwo]
  field_simp
  norm_cast
  nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]

private theorem invSqrtTwo_pow_two :
    invSqrtTwo ^ 2 = (2 : Complex)⁻¹ := by
  simpa [pow_two] using invSqrtTwo_sq

theorem hadamard_involution : hadamard * hadamard = identity₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, identity₂, Matrix.mul_apply, Fin.sum_univ_succ,
      invSqrtTwo_sq] <;> norm_num

theorem hadamard_isHermitian : hadamard.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, invSqrtTwo, Matrix.conjTranspose_apply]

/-- Hadamard is the normalized diagonal Pauli `X + Z`. -/
theorem hadamard_eq_pauli_sum :
    hadamard = invSqrtTwo • (pauliX + pauliZ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, invSqrtTwo, pauliX, pauliZ]

/-- Closed `pi` rotation about the axis bisecting `X` and `Z`. -/
def diagonalPiRotation : QubitMatrix :=
  (-Complex.I * invSqrtTwo) • (pauliX + pauliZ)

/-- The diagonal `pi` rotation is the usual Hadamard up to the global phase `-i`. -/
theorem diagonalPiRotation_eq_globalPhase_hadamard :
    diagonalPiRotation = (-Complex.I) • hadamard := by
  rw [diagonalPiRotation, hadamard_eq_pauli_sum, smul_smul]

theorem diagonalPiRotation_unitary :
    diagonalPiRotation ∈ Matrix.unitaryGroup QubitIndex Complex := by
  rw [Matrix.mem_unitaryGroup_iff']
  change diagonalPiRotationᴴ * diagonalPiRotation = 1
  rw [diagonalPiRotation_eq_globalPhase_hadamard,
    Matrix.conjTranspose_smul, hadamard_isHermitian]
  simp [smul_smul, hadamard_involution, identity₂]

/-- The global phase in the diagonal rotation cancels from every Heisenberg observable. -/
theorem diagonalPiRotation_heisenberg (A : QubitMatrix) :
    Foundations.heisenberg diagonalPiRotation A =
      Foundations.heisenberg hadamard A := by
  rw [diagonalPiRotation_eq_globalPhase_hadamard]
  simp [Foundations.heisenberg, Matrix.conjTranspose_smul, smul_smul,
    Matrix.mul_assoc]

theorem hadamard_unitary :
    hadamard ∈ Matrix.unitaryGroup QubitIndex Complex := by
  rw [Matrix.mem_unitaryGroup_iff']
  change hadamardᴴ * hadamard = 1
  rw [hadamard_isHermitian, hadamard_involution, identity₂]

theorem hadamard_mulVec_ketOne :
    hadamard.mulVec ketOne = invSqrtTwo • (ketOne + ketZero) := by
  funext i
  fin_cases i <;>
    simp [hadamard, ketOne, ketZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem hadamard_mulVec_ketZero :
    hadamard.mulVec ketZero = invSqrtTwo • (ketOne - ketZero) := by
  funext i
  fin_cases i <;>
    simp [hadamard, ketOne, ketZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem hadamard_heisenberg_x :
    Foundations.heisenberg hadamard pauliX = pauliZ := by
  rw [Foundations.heisenberg, hadamard_isHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ,
      invSqrtTwo_sq] <;> norm_num

theorem hadamard_heisenberg_y :
    Foundations.heisenberg hadamard pauliY = -pauliY := by
  rw [Foundations.heisenberg, hadamard_isHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, pauliY, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring_nf
  all_goals rw [invSqrtTwo_pow_two]
  all_goals norm_num
  all_goals ring_nf

theorem hadamard_heisenberg_z :
    Foundations.heisenberg hadamard pauliZ = pauliX := by
  rw [Foundations.heisenberg, hadamard_isHermitian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hadamard, pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ,
      invSqrtTwo_sq] <;> norm_num

/-! ## Generic current-descriptor NOT -/

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Equation (12): at a general time, NOT is the current descriptor's `X` component. -/
def descriptorNot (d : Descriptor Q) : Operator Q :=
  d.x

theorem descriptorNot_unitary {d : Descriptor Q} (hd : d.Valid) :
    descriptorNot d ∈ Matrix.unitaryGroup (Basis Q) Complex :=
  hd.component_unitary .x

theorem descriptorNot_heisenberg_x {d : Descriptor Q} (hd : d.Valid) :
    Register.heisenberg (descriptorNot d) d.x = d.x := by
  rw [Register.heisenberg, descriptorNot, hd.x_isHermitian]
  calc
    d.x * d.x * d.x = (d.x * d.x) * d.x := rfl
    _ = d.x := by rw [hd.x_mul_x, one_mul]

theorem descriptorNot_heisenberg_y {d : Descriptor Q} (hd : d.Valid) :
    Register.heisenberg (descriptorNot d) d.y = -d.y := by
  rw [Register.heisenberg, descriptorNot, hd.x_isHermitian, hd.mul_xy,
    Matrix.smul_mul, hd.mul_zx, smul_smul]
  norm_num

theorem descriptorNot_heisenberg_z {d : Descriptor Q} (hd : d.Valid) :
    Register.heisenberg (descriptorNot d) d.z = -d.z := by
  rw [Register.heisenberg, descriptorNot, hd.x_isHermitian, hd.mul_xz,
    Matrix.smul_mul, hd.mul_yx, smul_smul]
  norm_num

/-- Equation (13) as equality of a fully evolved, arbitrary valid descriptor. -/
theorem descriptorNot_evolve {d : Descriptor Q} (hd : d.Valid) :
    d.evolve (descriptorNot d) = { x := d.x, y := -d.y, z := -d.z } := by
  apply Descriptor.ext_components
  · exact descriptorNot_heisenberg_x hd
  · exact descriptorNot_heisenberg_y hd
  · exact descriptorNot_heisenberg_z hd

/-! ## Named-register embeddings -/

/-- A local matrix conjugation lifts exactly through a named one-qubit embedding. -/
theorem heisenberg_embedQubit (q : Q) (U A : QubitMatrix) :
    Register.heisenberg (embedQubit q U) (embedQubit q A) =
      embedQubit q (Foundations.heisenberg U A) := by
  rw [Register.heisenberg, Foundations.heisenberg, embedQubit_conjTranspose,
    ← embedQubit_mul, ← embedQubit_mul]

/-- Every embedded one-qubit gate carries an explicit singleton support witness. -/
theorem embedQubit_isSupportedOn (q : Q) (A : QubitMatrix) :
    IsSupportedOn {q} (embedQubit q A) := by
  exact embedSubsystem_isSupportedOn {q}
    (Matrix.reindexRingEquiv Complex (singletonBasisEquiv q) A)

/-- NOT at `q` reuses the existing embedded Pauli `X`. -/
theorem embed_notGate_eq_xAt (q : Q) : embedQubit q notGate = xAt q :=
  rfl

/-- Symbolic `X` rotation embedded at a named register coordinate. -/
def rotationXAt (q : Q) (theta : Real) : Operator Q :=
  embedQubit q (rotationX theta)

/-- The paper's square-root branch embedded at a named register coordinate. -/
def paperSqrtNotAt (q : Q) : Operator Q :=
  embedQubit q paperSqrtNot

/-- Hadamard embedded at a named register coordinate. -/
def hadamardAt (q : Q) : Operator Q :=
  embedQubit q hadamard

theorem hadamardAt_mul_self (q : Q) :
    hadamardAt q * hadamardAt q = 1 := by
  rw [hadamardAt, ← embedQubit_mul, hadamard_involution, identity₂,
    embedQubit_one]

theorem hadamardAt_isHermitian (q : Q) :
    (hadamardAt q).IsHermitian :=
  Register.embedQubit_isHermitian q hadamard hadamard_isHermitian

theorem rotationXAt_unitary (q : Q) (theta : Real) :
    rotationXAt q theta ∈ Matrix.unitaryGroup (Basis Q) Complex :=
  embedQubit_unitary q (rotationX theta) (rotationX_unitary theta)

theorem paperSqrtNotAt_unitary (q : Q) :
    paperSqrtNotAt q ∈ Matrix.unitaryGroup (Basis Q) Complex :=
  embedQubit_unitary q paperSqrtNot paperSqrtNot_unitary

theorem hadamardAt_unitary (q : Q) :
    hadamardAt q ∈ Matrix.unitaryGroup (Basis Q) Complex :=
  embedQubit_unitary q hadamard hadamard_unitary

theorem rotationXAt_isSupportedOn (q : Q) (theta : Real) :
    IsSupportedOn {q} (rotationXAt q theta) :=
  embedQubit_isSupportedOn q (rotationX theta)

theorem paperSqrtNotAt_isSupportedOn (q : Q) :
    IsSupportedOn {q} (paperSqrtNotAt q) :=
  embedQubit_isSupportedOn q paperSqrtNot

theorem hadamardAt_isSupportedOn (q : Q) :
    IsSupportedOn {q} (hadamardAt q) :=
  embedQubit_isSupportedOn q hadamard

theorem rotationXAt_heisenberg_x (q : Q) (theta : Real) :
    Register.heisenberg (rotationXAt q theta) (xAt q) = xAt q := by
  rw [rotationXAt, xAt, heisenberg_embedQubit, rotationX_heisenberg_x]

theorem rotationXAt_heisenberg_y (q : Q) (theta : Real) :
    Register.heisenberg (rotationXAt q theta) (yAt q) =
      (theta.cos : Complex) • yAt q - (theta.sin : Complex) • zAt q := by
  rw [rotationXAt, yAt, zAt, heisenberg_embedQubit, rotationX_heisenberg_y,
    embedQubit_sub, embedQubit_smul, embedQubit_smul]

theorem rotationXAt_heisenberg_z (q : Q) (theta : Real) :
    Register.heisenberg (rotationXAt q theta) (zAt q) =
      (theta.sin : Complex) • yAt q + (theta.cos : Complex) • zAt q := by
  rw [rotationXAt, yAt, zAt, heisenberg_embedQubit, rotationX_heisenberg_z,
    embedQubit_add, embedQubit_smul, embedQubit_smul]

theorem paperSqrtNotAt_heisenberg_x (q : Q) :
    Register.heisenberg (paperSqrtNotAt q) (xAt q) = xAt q := by
  rw [paperSqrtNotAt, xAt, heisenberg_embedQubit, paperSqrtNot_heisenberg_x]

theorem paperSqrtNotAt_heisenberg_y (q : Q) :
    Register.heisenberg (paperSqrtNotAt q) (yAt q) = zAt q := by
  rw [paperSqrtNotAt, yAt, heisenberg_embedQubit, paperSqrtNot_heisenberg_y, zAt]

theorem paperSqrtNotAt_heisenberg_z (q : Q) :
    Register.heisenberg (paperSqrtNotAt q) (zAt q) = -yAt q := by
  rw [paperSqrtNotAt, zAt, heisenberg_embedQubit, paperSqrtNot_heisenberg_z,
    yAt]
  simpa only [neg_smul, one_smul] using embedQubit_smul q (-1) pauliY

theorem hadamardAt_heisenberg_x (q : Q) :
    Register.heisenberg (hadamardAt q) (xAt q) = zAt q := by
  rw [hadamardAt, xAt, heisenberg_embedQubit, hadamard_heisenberg_x, zAt]

theorem hadamardAt_heisenberg_y (q : Q) :
    Register.heisenberg (hadamardAt q) (yAt q) = -yAt q := by
  rw [hadamardAt, yAt, heisenberg_embedQubit, hadamard_heisenberg_y]
  simpa only [neg_smul, one_smul] using embedQubit_smul q (-1) pauliY

theorem hadamardAt_heisenberg_z (q : Q) :
    Register.heisenberg (hadamardAt q) (zAt q) = xAt q := by
  rw [hadamardAt, zAt, heisenberg_embedQubit, hadamard_heisenberg_z, xAt]

end
end Gates
end Deutsch
