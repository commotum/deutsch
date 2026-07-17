import Deutsch.Foundations.Concrete
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Finite qubit registers

A register is named by an arbitrary finite decidable type `Q`. Its computational basis consists of
raw bit assignments `Q → Fin 2`; paper logical values retain the reversed raw-index convention fixed
in `Deutsch.Foundations.Concrete`.
-/

namespace Deutsch
namespace Register

open Foundations
open scoped Matrix

noncomputable section

/-- Computational-basis labels for a register whose qubits are named by `Q`. -/
abbrev Basis (Q : Type*) := Q → QubitIndex

/-- Coordinate vectors in the computational basis. -/
abbrev CoordinateVector (Q : Type*) := Basis Q → ℂ

/-- The finite Hilbert space associated with the computational basis. -/
abbrev Ket (Q : Type*) := EuclideanSpace ℂ (Basis Q)

/-- Concrete square operators on a named finite qubit register. -/
abbrev Operator (Q : Type*) := Matrix (Basis Q) (Basis Q) ℂ

/-- Bundled unitary register operators. -/
abbrev UnitaryOperator (Q : Type*) [Fintype Q] [DecidableEq Q] :=
  Matrix.unitaryGroup (Basis Q) ℂ

theorem card_basis (Q : Type*) [Fintype Q] [DecidableEq Q] :
    Fintype.card (Basis Q) = 2 ^ Fintype.card Q := by
  simp [Basis, QubitIndex]

/-- Matrix operators as endomorphisms of the corresponding finite Hilbert space. -/
def matrixEndEquiv (Q : Type*) [Fintype Q] [DecidableEq Q] :
    Operator Q ≃ₐ[ℂ] Module.End ℂ (Ket Q) :=
  Matrix.toLpLinAlgEquiv 2

@[simp]
theorem matrixEndEquiv_apply (Q : Type*) [Fintype Q] [DecidableEq Q]
    (A : Operator Q) (psi : Ket Q) :
    matrixEndEquiv Q A psi = WithLp.toLp 2 (A.mulVec (WithLp.ofLp psi)) := by
  rfl

theorem matrixEndEquiv_conjTranspose (Q : Type*) [Fintype Q] [DecidableEq Q]
    (A : Operator Q) :
    matrixEndEquiv Q Aᴴ = (matrixEndEquiv Q A).adjoint := by
  exact Matrix.toEuclideanLin_conjTranspose_eq_adjoint A

/-- Algebraic Heisenberg conjugation in the project direction `U† A U`. -/
def heisenberg {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U A : Operator Q) : Operator Q :=
  Uᴴ * A * U

@[simp]
theorem heisenberg_one_operator {Q : Type*} [Fintype Q] [DecidableEq Q]
    (A : Operator Q) : heisenberg 1 A = A := by
  simp [heisenberg]

theorem heisenberg_chronology {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U V A : Operator Q) :
    heisenberg (V * U) A = heisenberg U (heisenberg V A) := by
  simp [heisenberg, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem heisenberg_add {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U A B : Operator Q) :
    heisenberg U (A + B) = heisenberg U A + heisenberg U B := by
  simp [heisenberg, Matrix.mul_add, Matrix.add_mul]

theorem heisenberg_sub {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U A B : Operator Q) :
    heisenberg U (A - B) = heisenberg U A - heisenberg U B := by
  simp [heisenberg, Matrix.mul_sub, Matrix.sub_mul]

theorem heisenberg_smul {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U A : Operator Q) (c : ℂ) :
    heisenberg U (c • A) = c • heisenberg U A := by
  simp [heisenberg]

theorem heisenberg_conjTranspose {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U A : Operator Q) :
    (heisenberg U A)ᴴ = heisenberg U Aᴴ := by
  simp [heisenberg, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem heisenberg_isHermitian {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U A : Operator Q) (hA : A.IsHermitian) :
    (heisenberg U A).IsHermitian := by
  exact Matrix.isHermitian_conjTranspose_mul_mul U hA

@[simp]
theorem heisenberg_one_of_unitary {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U : Operator Q) (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) :
    heisenberg U 1 = 1 := by
  simp only [heisenberg, mul_one]
  change star U * U = 1
  exact hU.1

theorem heisenberg_mul_of_unitary {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U A B : Operator Q) (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) :
    heisenberg U (A * B) = heisenberg U A * heisenberg U B := by
  have hUU : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hU.2
  simp only [heisenberg]
  calc
    Uᴴ * (A * B) * U = Uᴴ * A * B * U := by simp [Matrix.mul_assoc]
    _ = Uᴴ * A * (U * Uᴴ) * B * U := by rw [hUU]; simp
    _ = (Uᴴ * A * U) * (Uᴴ * B * U) := by simp [Matrix.mul_assoc]

theorem heisenberg_unitary {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U A : Operator Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (hA : A ∈ Matrix.unitaryGroup (Basis Q) ℂ) :
    heisenberg U A ∈ Matrix.unitaryGroup (Basis Q) ℂ := by
  have hUstar : Uᴴ ∈ Matrix.unitaryGroup (Basis Q) ℂ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Unitary.star_mem hU
  exact (Matrix.unitaryGroup (Basis Q) ℂ).mul_mem
    ((Matrix.unitaryGroup (Basis Q) ℂ).mul_mem hUstar hA) hU

/--
Unitary conjugation is covariant under a shared change of Heisenberg frame.  This is the typed
bridge from a gate written in initial matrices to the same gate written in current descriptors.
-/
theorem heisenberg_covariance {Q : Type*} [Fintype Q] [DecidableEq Q]
    (W U A : Operator Q)
    (hW : W ∈ Matrix.unitaryGroup (Basis Q) ℂ) :
    heisenberg (heisenberg W U) (heisenberg W A) =
      heisenberg W (heisenberg U A) := by
  have hWWstar : W * Wᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hW.2
  simp only [heisenberg, Matrix.conjTranspose_mul]
  rw [Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc W Wᴴ, hWWstar, one_mul]

/-- Physical Heisenberg evolution by a bundled unitary operator. -/
def evolve {Q : Type*} [Fintype Q] [DecidableEq Q]
    (U : UnitaryOperator Q) (A : Operator Q) : Operator Q :=
  heisenberg U.1 A

end
end Register
end Deutsch
