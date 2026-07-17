import Deutsch.Foundations.Concrete
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic

/-! Executable algebra probes for the concrete matrix layer. -/

namespace DeutschTests
namespace Foundations

open Deutsch Foundations
open scoped Matrix Kronecker

noncomputable section

theorem pauli_x_mul_y : pauliX * pauliY = Complex.I • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauli_y_mul_x : pauliY * pauliX = -Complex.I • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauli_squares :
    pauliX * pauliX = identity₂ ∧
      pauliY * pauliY = identity₂ ∧ pauliZ * pauliZ = identity₂ := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pauliX, identity₂, Matrix.mul_apply, Fin.sum_univ_succ]
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pauliY, identity₂, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [pauliZ, identity₂, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauli_hermitian :
    pauliX.IsHermitian ∧ pauliY.IsHermitian ∧ pauliZ.IsHermitian := by
  repeat' apply And.intro
  all_goals ext i j
  all_goals fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.IsHermitian, pauliX, pauliY, pauliZ,
      Matrix.conjTranspose_apply]

theorem pauli_traces :
    Matrix.trace pauliX = 0 ∧ Matrix.trace pauliY = 0 ∧
      Matrix.trace pauliZ = 0 := by
  norm_num [pauliX, pauliY, pauliZ, Matrix.trace_fin_two_of]

theorem pauli_unitary :
    pauliX ∈ Matrix.unitaryGroup QubitIndex ℂ ∧
      pauliY ∈ Matrix.unitaryGroup QubitIndex ℂ ∧
      pauliZ ∈ Matrix.unitaryGroup QubitIndex ℂ := by
  refine ⟨?_, ?_, ?_⟩
  all_goals rw [Matrix.mem_unitaryGroup_iff']
  all_goals ext i j
  all_goals fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliY, pauliZ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Matrix.one_apply]

theorem paper_bit_projectors :
    bitOneProjector = !![1, 0; 0, 0] ∧ bitZeroProjector = !![0, 0; 0, 1] := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [bitOneProjector, bitZeroProjector, identity₂, pauliZ]

theorem paper_bit_z_eigenvalues :
    pauliZ.mulVec ketOne = ketOne ∧ pauliZ.mulVec ketZero = -ketZero := by
  constructor <;> funext i <;> fin_cases i <;>
    norm_num [pauliZ, ketOne, ketZero, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ]

theorem phase_gate_pins_heisenberg_direction : heisenberg phaseS pauliX = -pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [heisenberg, phaseS, pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply]

theorem opposite_phase_conjugation_differs : phaseS * pauliX * phaseSᴴ = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [phaseS, pauliX, pauliY, Matrix.mul_apply, Fin.sum_univ_succ,
      Matrix.conjTranspose_apply]

theorem phase_gate_transforms_x_eigenvectors :
    let plus : QubitIndex → ℂ := ![1, 1]
    let minus : QubitIndex → ℂ := ![1, -1]
    let transformedPlus := phaseSᴴ.mulVec plus
    let transformedMinus := phaseSᴴ.mulVec minus
    (heisenberg phaseS pauliX).mulVec transformedPlus = transformedPlus ∧
      (heisenberg phaseS pauliX).mulVec transformedMinus = -transformedMinus := by
  dsimp
  constructor <;> funext i <;> fin_cases i <;>
    norm_num [heisenberg, phaseS, pauliX, Matrix.mul_apply,
      Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Fin.sum_univ_succ]

private noncomputable def invSqrtTwo : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

private theorem invSqrtTwo_sq : invSqrtTwo * invSqrtTwo = (2 : ℂ)⁻¹ := by
  have hs : (Real.sqrt 2 : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [invSqrtTwo]
  field_simp
  norm_cast
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

private theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

private theorem invSqrtTwo_pow_two : invSqrtTwo ^ 2 = (2 : ℂ)⁻¹ := by
  simpa [pow_two] using invSqrtTwo_sq

private noncomputable def rxPiDivTwo : QubitMatrix :=
  invSqrtTwo • (identity₂ - Complex.I • pauliX)

theorem rx_pi_div_two_pins_heisenberg_y :
    heisenberg rxPiDivTwo pauliY = -pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisenberg, rxPiDivTwo, identity₂, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.one_apply, star_invSqrtTwo, invSqrtTwo_sq] <;> ring_nf
  all_goals simp only [invSqrtTwo_pow_two, Complex.I_sq]
  all_goals norm_num

theorem rx_pi_div_two_pins_heisenberg_z :
    heisenberg rxPiDivTwo pauliZ = pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [heisenberg, rxPiDivTwo, identity₂, pauliX, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Matrix.one_apply, star_invSqrtTwo, invSqrtTwo_sq] <;> ring_nf
  all_goals simp only [invSqrtTwo_pow_two, Complex.I_sq]
  all_goals norm_num <;> ring

theorem fin_pair_basis_order :
    finProdFinEquiv ((0 : Fin 2), (0 : Fin 2)) = (0 : Fin 4) ∧
      finProdFinEquiv ((0 : Fin 2), (1 : Fin 2)) = (1 : Fin 4) ∧
      finProdFinEquiv ((1 : Fin 2), (0 : Fin 2)) = (2 : Fin 4) ∧
      finProdFinEquiv ((1 : Fin 2), (1 : Fin 2)) = (3 : Fin 4) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem kronecker_mulVec_tensorKet
    (A B : QubitMatrix) (v w : QubitIndex → ℂ) :
    (A ⊗ₖ B).mulVec (tensorKet v w) =
      tensorKet (A.mulVec v) (B.mulVec w) := by
  funext index
  rcases index with ⟨i, j⟩
  simp [Matrix.mulVec, tensorKet, dotProduct, Fintype.sum_prod_type,
    mul_assoc, mul_left_comm, mul_comm]
  ring

theorem x_left_factor_all_basis :
    (pauliX ⊗ₖ identity₂).mulVec (tensorKet ketZero ketZero) =
        tensorKet ketOne ketZero ∧
      (pauliX ⊗ₖ identity₂).mulVec (tensorKet ketZero ketOne) =
        tensorKet ketOne ketOne ∧
      (pauliX ⊗ₖ identity₂).mulVec (tensorKet ketOne ketZero) =
        tensorKet ketZero ketZero ∧
      (pauliX ⊗ₖ identity₂).mulVec (tensorKet ketOne ketOne) =
        tensorKet ketZero ketOne := by
  repeat' apply And.intro
  all_goals rw [kronecker_mulVec_tensorKet]
  all_goals funext index
  all_goals rcases index with ⟨i, j⟩
  all_goals fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mulVec, tensorKet, dotProduct, Fin.sum_univ_succ,
      pauliX, identity₂, ketZero, ketOne, Matrix.one_apply]

theorem x_right_factor_all_basis :
    (identity₂ ⊗ₖ pauliX).mulVec (tensorKet ketZero ketZero) =
        tensorKet ketZero ketOne ∧
      (identity₂ ⊗ₖ pauliX).mulVec (tensorKet ketZero ketOne) =
        tensorKet ketZero ketZero ∧
      (identity₂ ⊗ₖ pauliX).mulVec (tensorKet ketOne ketZero) =
        tensorKet ketOne ketOne ∧
      (identity₂ ⊗ₖ pauliX).mulVec (tensorKet ketOne ketOne) =
        tensorKet ketOne ketZero := by
  repeat' apply And.intro
  all_goals rw [kronecker_mulVec_tensorKet]
  all_goals funext index
  all_goals rcases index with ⟨i, j⟩
  all_goals fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mulVec, tensorKet, dotProduct, Fin.sum_univ_succ,
      pauliX, identity₂, ketZero, ketOne, Matrix.one_apply]

theorem kronecker_left_factor_first :
    (pauliX ⊗ₖ pauliZ) (0, 0) (1, 0) = 1 ∧
      (pauliX ⊗ₖ pauliZ) (0, 1) (1, 1) = -1 := by
  norm_num [pauliX, pauliZ]

theorem cnot_basis_00 :
    cnotTargetLeftControlRight.mulVec (tensorKet ketZero ketZero) =
      tensorKet ketZero ketZero := by
  simp only [cnotTargetLeftControlRight]
  rw [paper_bit_projectors.1, paper_bit_projectors.2]
  funext index
  rcases index with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [tensorKet, ketZero, identity₂, pauliX, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_basis_10 :
    cnotTargetLeftControlRight.mulVec (tensorKet ketOne ketZero) =
      tensorKet ketOne ketZero := by
  simp only [cnotTargetLeftControlRight]
  rw [paper_bit_projectors.1, paper_bit_projectors.2]
  funext index
  rcases index with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [tensorKet, ketZero, ketOne, identity₂, pauliX, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_basis_01 :
    cnotTargetLeftControlRight.mulVec (tensorKet ketZero ketOne) =
      tensorKet ketOne ketOne := by
  simp only [cnotTargetLeftControlRight]
  rw [paper_bit_projectors.1, paper_bit_projectors.2]
  funext index
  rcases index with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [tensorKet, ketZero, ketOne, identity₂, pauliX, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_basis_11 :
    cnotTargetLeftControlRight.mulVec (tensorKet ketOne ketOne) =
      tensorKet ketZero ketOne := by
  simp only [cnotTargetLeftControlRight]
  rw [paper_bit_projectors.1, paper_bit_projectors.2]
  funext index
  rcases index with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [tensorKet, ketZero, ketOne, identity₂, pauliX, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply]

private def flipIndex : QubitIndex → QubitIndex := ![1, 0]

private def cnotOutputIndex (input : QubitIndex × QubitIndex) :
    QubitIndex × QubitIndex :=
  (if input.2 = 0 then flipIndex input.1 else input.1, input.2)

private def cnotExplicit : TwoQubitMatrix :=
  fun output input => if output = cnotOutputIndex input then 1 else 0

theorem cnot_projector_formula_is_explicit_permutation :
    cnotTargetLeftControlRight = cnotExplicit := by
  ext row col
  rcases row with ⟨rt, rc⟩
  rcases col with ⟨ct, cc⟩
  fin_cases rt <;> fin_cases rc <;> fin_cases ct <;> fin_cases cc <;>
    norm_num [cnotTargetLeftControlRight, cnotExplicit, cnotOutputIndex, flipIndex,
      bitZeroProjector, bitOneProjector, identity₂, pauliX, pauliZ, Matrix.one_apply]

theorem cnot_conjugates_target_x :
    cnotTargetLeftControlRightᴴ * (pauliX ⊗ₖ identity₂) *
        cnotTargetLeftControlRight =
      pauliX ⊗ₖ identity₂ := by
  rw [cnot_projector_formula_is_explicit_permutation]
  ext row col
  rcases row with ⟨rt, rc⟩
  rcases col with ⟨ct, cc⟩
  fin_cases rt <;> fin_cases rc <;> fin_cases ct <;> fin_cases cc <;>
    norm_num [cnotExplicit, cnotOutputIndex, flipIndex, identity₂, pauliX,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_conjugates_target_y :
    cnotTargetLeftControlRightᴴ * (pauliY ⊗ₖ identity₂) *
        cnotTargetLeftControlRight =
      -(pauliY ⊗ₖ pauliZ) := by
  rw [cnot_projector_formula_is_explicit_permutation]
  ext row col
  rcases row with ⟨rt, rc⟩
  rcases col with ⟨ct, cc⟩
  fin_cases rt <;> fin_cases rc <;> fin_cases ct <;> fin_cases cc <;>
    norm_num [cnotExplicit, cnotOutputIndex, flipIndex, identity₂, pauliY, pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_conjugates_target_z :
    cnotTargetLeftControlRightᴴ * (pauliZ ⊗ₖ identity₂) *
        cnotTargetLeftControlRight =
      -(pauliZ ⊗ₖ pauliZ) := by
  rw [cnot_projector_formula_is_explicit_permutation]
  ext row col
  rcases row with ⟨rt, rc⟩
  rcases col with ⟨ct, cc⟩
  fin_cases rt <;> fin_cases rc <;> fin_cases ct <;> fin_cases cc <;>
    norm_num [cnotExplicit, cnotOutputIndex, flipIndex, identity₂, pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_conjugates_control_x :
    cnotTargetLeftControlRightᴴ * (identity₂ ⊗ₖ pauliX) *
        cnotTargetLeftControlRight =
      pauliX ⊗ₖ pauliX := by
  rw [cnot_projector_formula_is_explicit_permutation]
  ext row col
  rcases row with ⟨rt, rc⟩
  rcases col with ⟨ct, cc⟩
  fin_cases rt <;> fin_cases rc <;> fin_cases ct <;> fin_cases cc <;>
    norm_num [cnotExplicit, cnotOutputIndex, flipIndex, identity₂, pauliX,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_conjugates_control_y :
    cnotTargetLeftControlRightᴴ * (identity₂ ⊗ₖ pauliY) *
        cnotTargetLeftControlRight =
      pauliX ⊗ₖ pauliY := by
  rw [cnot_projector_formula_is_explicit_permutation]
  ext row col
  rcases row with ⟨rt, rc⟩
  rcases col with ⟨ct, cc⟩
  fin_cases rt <;> fin_cases rc <;> fin_cases ct <;> fin_cases cc <;>
    norm_num [cnotExplicit, cnotOutputIndex, flipIndex, identity₂, pauliX, pauliY,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_conjugates_control_z :
    cnotTargetLeftControlRightᴴ * (identity₂ ⊗ₖ pauliZ) *
        cnotTargetLeftControlRight =
      identity₂ ⊗ₖ pauliZ := by
  rw [cnot_projector_formula_is_explicit_permutation]
  ext row col
  rcases row with ⟨rt, rc⟩
  rcases col with ⟨ct, cc⟩
  fin_cases rt <;> fin_cases rc <;> fin_cases ct <;> fin_cases cc <;>
    norm_num [cnotExplicit, cnotOutputIndex, flipIndex, identity₂, pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.one_apply]

def paperHadamard : QubitMatrix :=
  invSqrtTwo • !![1, 1; 1, -1]

theorem paper_hadamard_involution :
    paperHadamard * paperHadamard = identity₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [paperHadamard, identity₂, Matrix.mul_apply, Fin.sum_univ_succ,
      invSqrtTwo_sq] <;> norm_num

theorem cnot_involution :
    cnotTargetLeftControlRight * cnotTargetLeftControlRight = 1 := by
  ext row col
  rcases row with ⟨rt, rc⟩
  rcases col with ⟨ct, cc⟩
  fin_cases rt <;> fin_cases rc <;> fin_cases ct <;> fin_cases cc <;>
    norm_num [cnotTargetLeftControlRight, bitZeroProjector, bitOneProjector,
      identity₂, pauliX, pauliZ, Matrix.mul_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.one_apply]

def hadamardOnRightControl : TwoQubitMatrix :=
  identity₂ ⊗ₖ paperHadamard

theorem hadamard_on_right_control_involution :
    hadamardOnRightControl * hadamardOnRightControl = 1 := by
  rw [hadamardOnRightControl, ← Matrix.mul_kronecker_mul,
    paper_hadamard_involution]
  simp [identity₂]

/-- Schrödinger chronology: CNOT acts first, then Hadamard on the right/control factor. -/
def paperBellTransform : TwoQubitMatrix :=
  hadamardOnRightControl * cnotTargetLeftControlRight

/-- Reverse chronology: Hadamard acts first, then CNOT. -/
def paperBellTransformInverse : TwoQubitMatrix :=
  cnotTargetLeftControlRight * hadamardOnRightControl

theorem paper_bell_chronology_inverse_left :
    paperBellTransformInverse * paperBellTransform = 1 := by
  simp only [paperBellTransformInverse, paperBellTransform, mul_assoc]
  rw [← mul_assoc hadamardOnRightControl hadamardOnRightControl
    cnotTargetLeftControlRight]
  rw [hadamard_on_right_control_involution]
  simpa using cnot_involution

theorem paper_bell_chronology_inverse_right :
    paperBellTransform * paperBellTransformInverse = 1 := by
  simp only [paperBellTransformInverse, paperBellTransform, mul_assoc]
  rw [← mul_assoc cnotTargetLeftControlRight cnotTargetLeftControlRight
    hadamardOnRightControl]
  rw [cnot_involution]
  simpa using hadamard_on_right_control_involution

end
end Foundations
end DeutschTests
