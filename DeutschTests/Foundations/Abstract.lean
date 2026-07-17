import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Abstract finite-Hilbert API probe

This verification-only module demonstrates that the chosen mathlib pin supports a basis-independent
semantic layer. Stage 3 and Stage 7 will decide the final public wrappers.
-/

open scoped ComplexOrder InnerProductSpace Kronecker MatrixOrder TensorProduct

noncomputable section

namespace DeutschTests
namespace Foundations
namespace AbstractProbe

variable {H K : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [FiniteDimensional ℂ K]

abbrev Operator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  Module.End ℂ H

structure Density (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] where
  op : Operator H
  positive : op.IsPositive
  trace_one : op.trace ℂ H = 1

structure Effect (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] where
  op : Operator H
  nonneg : 0 ≤ op
  le_one : op ≤ 1

def probability (rho : Density H) (effect : Effect H) : ℝ :=
  ((rho.op * effect.op).trace ℂ H).re

def pureDensity (psi : H) (hpsi : ‖psi‖ = 1) : Density H where
  op := InnerProductSpace.rankOne ℂ psi psi
  positive := InnerProductSpace.isPositive_rankOne_self psi
  trace_one := by
    rw [InnerProductSpace.trace_rankOne, inner_self_eq_one_of_norm_eq_one hpsi]

omit [FiniteDimensional ℂ H] [FiniteDimensional ℂ K] in
theorem disjoint_binary_operators_commute (A : Operator H) (B : Operator K) :
    A.rTensor K * B.lTensor H = B.lTensor H * A.rTensor K := by
  simp only [Module.End.mul_eq_comp, LinearMap.rTensor_comp_lTensor,
    LinearMap.lTensor_comp_rTensor]

theorem tensor_adjoint (A : Operator H) (B : Operator K) :
    (TensorProduct.map A B).adjoint = TensorProduct.map A.adjoint B.adjoint := by
  exact TensorProduct.adjoint_map A B

theorem binary_locality_api_probe (U : Operator H) (B : Operator K)
    (hU : U ∈ unitary (Operator H)) :
    (U.rTensor K).adjoint * B.lTensor H * U.rTensor K = B.lTensor H := by
  have hcomm : U.rTensor K * B.lTensor H = B.lTensor H * U.rTensor K :=
    disjoint_binary_operators_commute U B
  have hU' : (U.rTensor K).adjoint * U.rTensor K = 1 := by
    rw [LinearMap.adjoint_rTensor, ← LinearMap.rTensor_mul, ← LinearMap.star_eq_adjoint,
      hU.1, Module.End.one_eq_id, LinearMap.rTensor_id, ← Module.End.one_eq_id]
  calc
    _ = (U.rTensor K).adjoint * (B.lTensor H * U.rTensor K) := mul_assoc ..
    _ = (U.rTensor K).adjoint * (U.rTensor K * B.lTensor H) := by rw [hcomm]
    _ = ((U.rTensor K).adjoint * U.rTensor K) * B.lTensor H := (mul_assoc ..).symm
    _ = _ := by rw [hU', one_mul]

/-- A finite family of effects whose operator sum is the identity. -/
structure FiniteMeasurement (Outcome : Type*) [Fintype Outcome] where
  effect : Outcome → Effect H
  complete : ∑ outcome, (effect outcome).op = 1

/-- The total trace-real Born weight of a complete finite effect family is one. -/
theorem sum_probability_eq_one {Outcome : Type*} [Fintype Outcome]
    (rho : Density H) (measurement : FiniteMeasurement (H := H) Outcome) :
    ∑ outcome, probability rho (measurement.effect outcome) = 1 := by
  classical
  calc
    ∑ outcome, probability rho (measurement.effect outcome) =
        ∑ outcome,
          (((rho.op * (measurement.effect outcome).op).trace ℂ H).re) := rfl
    _ = ((∑ outcome,
          (rho.op * (measurement.effect outcome).op).trace ℂ H)).re := by
      rw [Complex.re_sum]
    _ = (((∑ outcome, rho.op * (measurement.effect outcome).op).trace ℂ H)).re := by
      rw [map_sum]
    _ = ((rho.op * ∑ outcome, (measurement.effect outcome).op).trace ℂ H).re := by
      rw [Finset.mul_sum]
    _ = (rho.op.trace ℂ H).re := by rw [measurement.complete, mul_one]
    _ = 1 := by rw [rho.trace_one]; norm_num

section MatrixBridge

variable {i j : Type*} [Fintype i] [DecidableEq i] [Fintype j] [DecidableEq j]

theorem disjoint_matrix_operators_commute (A : Matrix i i ℂ) (B : Matrix j j ℂ) :
    (A ⊗ₖ (1 : Matrix j j ℂ)) * ((1 : Matrix i i ℂ) ⊗ₖ B) =
      ((1 : Matrix i i ℂ) ⊗ₖ B) * (A ⊗ₖ (1 : Matrix j j ℂ)) := by
  calc
    _ = (A * 1) ⊗ₖ (1 * B) := (Matrix.mul_kronecker_mul A 1 1 B).symm
    _ = A ⊗ₖ B := by simp
    _ = (1 * A) ⊗ₖ (B * 1) := by simp
    _ = _ := Matrix.mul_kronecker_mul 1 A B 1

end MatrixBridge

end AbstractProbe
end Foundations
end DeutschTests

end
