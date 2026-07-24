import Deutsch.EPR.Statistics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Product structure of the EPR resource

The two coordinates of `Fin 2` are treated explicitly as the left and right one-qubit registers.
Product kets and operators factor in those coordinates, while a product density requires two
genuine normalized one-qubit density factors.  The exact circuit state has a nonzero amplitude
determinant at every pair of local rotation settings, which rules out both a product ket and a
product-density decomposition.
-/

namespace Deutsch
namespace EPR

open Foundations Gates Information Register
open scoped Matrix

noncomputable section

/-! ## Explicit two-qubit product split -/

/-- The one-qubit basis assignment with raw bit `bit`. -/
def oneQubitBits (bit : QubitIndex) : Basis (Fin 1) :=
  fun _ => bit

/--
A two-qubit ket is a product ket when its coordinates factor across coordinates `0` and `1`.
The factors are ordinary one-qubit kets.
-/
def IsProductKet (psi : Ket (Fin 2)) : Prop :=
  ∃ left right : Ket (Fin 1),
    ∀ leftBit rightBit : QubitIndex,
      psi (pairBits leftBit rightBit) =
        left (oneQubitBits leftBit) * right (oneQubitBits rightBit)

/-- Pure-state entanglement in this split: the normalized ket has no product factorization. -/
def IsEntangledPureState (psi : PureState (Fin 2)) : Prop :=
  ¬ IsProductKet psi.ket

/-- Entrywise tensor product in the explicit coordinate-`0`/coordinate-`1` register split. -/
def twoQubitProductOperator
    (left right : Operator (Fin 1)) : Operator (Fin 2) :=
  fun row column =>
    left (oneQubitBits (row 0)) (oneQubitBits (column 0)) *
      right (oneQubitBits (row 1)) (oneQubitBits (column 1))

/-- A two-qubit operator that factors across coordinates `0` and `1`. -/
def IsProductOperator (A : Operator (Fin 2)) : Prop :=
  ∃ left right : Operator (Fin 1),
    A = twoQubitProductOperator left right

/--
A product density is the tensor product of two genuine one-qubit densities in the explicit
coordinate-`0`/coordinate-`1` split.
-/
def IsProductDensity (rho : Density (Fin 2)) : Prop :=
  ∃ left right : Density (Fin 1),
    rho.op = twoQubitProductOperator left.op right.op

theorem IsProductDensity.isProductOperator {rho : Density (Fin 2)}
    (hproduct : IsProductDensity rho) : IsProductOperator rho.op := by
  rcases hproduct with ⟨left, right, hproduct⟩
  exact ⟨left.op, right.op, hproduct⟩

/-- Every product ket has a rank-one two-by-two amplitude table. -/
theorem IsProductKet.amplitude_minor {psi : Ket (Fin 2)}
    (hproduct : IsProductKet psi) :
    psi (pairBits 0 0) * psi (pairBits 1 1) =
      psi (pairBits 0 1) * psi (pairBits 1 0) := by
  rcases hproduct with ⟨left, right, hproduct⟩
  rw [hproduct, hproduct, hproduct, hproduct]
  ring

/--
Every product operator has a vanishing row-amplitude minor at each fixed column.  This criterion
will be applied directly to the entries of the circuit-produced density.
-/
theorem IsProductOperator.row_minor {A : Operator (Fin 2)}
    (hproduct : IsProductOperator A) (columnLeft columnRight : QubitIndex) :
    A (pairBits 0 0) (pairBits columnLeft columnRight) *
        A (pairBits 1 1) (pairBits columnLeft columnRight) =
      A (pairBits 0 1) (pairBits columnLeft columnRight) *
        A (pairBits 1 0) (pairBits columnLeft columnRight) := by
  rcases hproduct with ⟨left, right, hproduct⟩
  rw [hproduct]
  simp only [twoQubitProductOperator, pairBits_zero, pairBits_one]
  ring

theorem IsProductDensity.row_minor {rho : Density (Fin 2)}
    (hproduct : IsProductDensity rho) (columnLeft columnRight : QubitIndex) :
    rho.op (pairBits 0 0) (pairBits columnLeft columnRight) *
        rho.op (pairBits 1 1) (pairBits columnLeft columnRight) =
      rho.op (pairBits 0 1) (pairBits columnLeft columnRight) *
        rho.op (pairBits 1 0) (pairBits columnLeft columnRight) :=
  hproduct.isProductOperator.row_minor columnLeft columnRight

/-! ## The circuit resource is not a product -/

private theorem invSqrtTwo_sq :
    invSqrtTwo ^ 2 = (2 : ℂ)⁻¹ := by
  have hs : (Real.sqrt 2 : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [pow_two, invSqrtTwo]
  field_simp
  norm_cast
  nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]

/--
The determinant of the exact circuit ket's two-by-two amplitude table is always `-1/2`.
Local rotation settings therefore cannot turn the resource into a product ket.
-/
theorem pairPureState_amplitude_determinant (theta phi : ℝ) :
    (invSqrtTwo * crossCoefficient theta phi) ^ 2 -
        (invSqrtTwo * sameCoefficient theta phi) ^ 2 =
      -(1 / 2 : ℂ) := by
  rw [sameCoefficient_eq_cos_sub_half,
    crossCoefficient_eq_I_mul_sin_sub_half]
  have htrig :
      (Real.sin ((theta - phi) / 2) : ℂ) ^ 2 +
        (Real.cos ((theta - phi) / 2) : ℂ) ^ 2 = 1 := by
    norm_cast
    exact Real.sin_sq_add_cos_sq ((theta - phi) / 2)
  simp only [mul_pow, invSqrtTwo_sq, Complex.I_sq]
  linear_combination -(2 : ℂ)⁻¹ * htrig

/-- The exact circuit ket is non-product for every pair of local rotation settings. -/
theorem pairPureState_not_product (theta phi : ℝ) :
    ¬ IsProductKet (pairPureState theta phi).ket := by
  intro hproduct
  have hminor := hproduct.amplitude_minor
  rw [pairPureState_ket_pairBits, pairPureState_ket_pairBits,
    pairPureState_ket_pairBits, pairPureState_ket_pairBits] at hminor
  have hzero :
      (invSqrtTwo * crossCoefficient theta phi) ^ 2 -
          (invSqrtTwo * sameCoefficient theta phi) ^ 2 = 0 := by
    calc
      (invSqrtTwo * crossCoefficient theta phi) ^ 2 -
            (invSqrtTwo * sameCoefficient theta phi) ^ 2 =
          (invSqrtTwo * sameCoefficient theta phi) *
              -(invSqrtTwo * sameCoefficient theta phi) -
            (invSqrtTwo * crossCoefficient theta phi) *
              -(invSqrtTwo * crossCoefficient theta phi) := by ring
      _ = 0 := sub_eq_zero.mpr hminor
  rw [pairPureState_amplitude_determinant] at hzero
  norm_num at hzero

/-- Every locally rotated circuit resource is entangled as a pure state. -/
theorem pairPureState_isEntangled (theta phi : ℝ) :
    IsEntangledPureState (pairPureState theta phi) :=
  pairPureState_not_product theta phi

/--
The density produced by the exact EPR circuit is not a tensor product of two one-qubit densities,
for any pair of local rotation settings.
-/
theorem pairDensity_not_product (theta phi : ℝ) :
    ¬ IsProductDensity (pairDensity theta phi) := by
  intro hproduct
  let a : ℂ := invSqrtTwo * sameCoefficient theta phi
  let b : ℂ := invSqrtTwo * crossCoefficient theta phi
  have hdet : b ^ 2 - a ^ 2 = -(1 / 2 : ℂ) :=
    pairPureState_amplitude_determinant theta phi
  by_cases ha : a = 0
  · have hb : b ≠ 0 := by
      intro hb
      rw [ha, hb] at hdet
      norm_num at hdet
    have hminor := hproduct.row_minor (0 : QubitIndex) (1 : QubitIndex)
    simp only [pairDensity, pureDensity, densityOfVector, Matrix.vecMulVec,
      Matrix.of_apply, Pi.star_apply, pairPureState_ket_pairBits] at hminor
    change
      (a * (starRingEnd ℂ) b) * (-a * (starRingEnd ℂ) b) =
        (b * (starRingEnd ℂ) b) * (-b * (starRingEnd ℂ) b) at hminor
    have hzero : ((starRingEnd ℂ) b) ^ 2 * (b ^ 2 - a ^ 2) = 0 := by
      calc
        ((starRingEnd ℂ) b) ^ 2 * (b ^ 2 - a ^ 2) =
            (a * (starRingEnd ℂ) b) * (-a * (starRingEnd ℂ) b) -
              (b * (starRingEnd ℂ) b) * (-b * (starRingEnd ℂ) b) := by ring
        _ = 0 := sub_eq_zero.mpr hminor
    have hstar : (starRingEnd ℂ) b ≠ 0 :=
      (map_ne_zero (starRingEnd ℂ)).2 hb
    exact (mul_ne_zero (pow_ne_zero 2 hstar) (by
      rw [hdet]
      norm_num)) hzero
  · have hminor := hproduct.row_minor (0 : QubitIndex) (0 : QubitIndex)
    simp only [pairDensity, pureDensity, densityOfVector, Matrix.vecMulVec,
      Matrix.of_apply, Pi.star_apply, pairPureState_ket_pairBits] at hminor
    change
      (a * (starRingEnd ℂ) a) * (-a * (starRingEnd ℂ) a) =
        (b * (starRingEnd ℂ) a) * (-b * (starRingEnd ℂ) a) at hminor
    have hzero : ((starRingEnd ℂ) a) ^ 2 * (b ^ 2 - a ^ 2) = 0 := by
      calc
        ((starRingEnd ℂ) a) ^ 2 * (b ^ 2 - a ^ 2) =
            (a * (starRingEnd ℂ) a) * (-a * (starRingEnd ℂ) a) -
              (b * (starRingEnd ℂ) a) * (-b * (starRingEnd ℂ) a) := by ring
        _ = 0 := sub_eq_zero.mpr hminor
    have hstar : (starRingEnd ℂ) a ≠ 0 :=
      (map_ne_zero (starRingEnd ℂ)).2 ha
    exact (mul_ne_zero (pow_ne_zero 2 hstar) (by
      rw [hdet]
      norm_num)) hzero

/-- In particular, the resource immediately after inverse-Bell preparation is non-product. -/
theorem pairDensity_resource_not_product :
    ¬ IsProductDensity (pairDensity 0 0) :=
  pairDensity_not_product 0 0

end
end EPR
end Deutsch
