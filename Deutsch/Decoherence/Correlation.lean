import Deutsch.EPR.Statistics
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Classical correlation is not an entanglement witness

The source points to zero one-qubit `Z` moments and a unit joint `ZZ` moment when motivating
entanglement as a teleportation "key".  Those moments do not by themselves witness
entanglement.  The density below is, constructively, the equal convex mixture of the two product
computational-basis densities at raw words `00` and `11` (paper words `11` and `00`), and it has
the same three moments.

The project does not currently expose a general separability predicate.  Accordingly, the
separable boundary is stated by the displayed convex decomposition rather than hidden behind an
unavailable abstract classification theorem.
-/

namespace Deutsch
namespace Decoherence

open Foundations Gates Information Register EPR
open scoped ComplexOrder Matrix MatrixOrder

noncomputable section

/-- An explicitly classically correlated, separable two-qubit density. -/
def classicallyCorrelatedDensity : Density (Fin 2) where
  op := (2 : ℂ)⁻¹ • (basisDensity paperOneOne).op +
    (2 : ℂ)⁻¹ • (basisDensity paperZeroZero).op
  positive := by
    apply Matrix.PosSemidef.add
    · exact (basisDensity paperOneOne).positive.smul (by
        norm_num [Complex.nonneg_iff])
    · exact (basisDensity paperZeroZero).positive.smul (by
        norm_num [Complex.nonneg_iff])
  trace_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      (basisDensity paperOneOne).trace_one,
      (basisDensity paperZeroZero).trace_one]
    norm_num

/-- The constructive convex decomposition used in place of a general separability predicate. -/
@[simp]
theorem classicallyCorrelatedDensity_op :
    classicallyCorrelatedDensity.op =
      (2 : ℂ)⁻¹ • (basisDensity paperOneOne).op +
        (2 : ℂ)⁻¹ • (basisDensity paperZeroZero).op := rfl

private theorem basisDensity_expectation (bits : Basis (Fin 2))
    (A : Operator (Fin 2)) :
    densityExpectation (basisDensity bits) A = A bits bits := by
  classical
  unfold densityExpectation
  rw [show (basisDensity bits).op = Matrix.single bits bits 1 by
    exact Matrix.diagonal_single bits 1]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single]
  rw [Fintype.sum_eq_single bits]
  · rw [Fintype.sum_eq_single bits]
    · simp
    · intro other hother
      simp [Ne.symm hother]
  · intro other hother
    simp [Ne.symm hother]

private theorem basisDensity_z_expectation (bits : Basis (Fin 2)) (q : Fin 2) :
    densityExpectation (basisDensity bits) (zAt q) =
      if bits q = 0 then 1 else -1 := by
  rw [basisDensity_expectation, zAt, embedQubit_apply_ite]
  generalize hbit : bits q = bit
  fin_cases bit <;> simp [pauliZ]

private theorem basisDensity_zz_expectation (bits : Basis (Fin 2)) :
    densityExpectation (basisDensity bits)
        (zAt (0 : Fin 2) * zAt (1 : Fin 2)) =
      (if bits 0 = 0 then 1 else -1) *
        (if bits 1 = 0 then 1 else -1) := by
  classical
  rw [basisDensity_expectation, Matrix.mul_apply]
  simp only [zAt, embedQubit_apply_ite]
  rw [Fintype.sum_eq_single bits]
  · generalize hzero : bits 0 = zeroBit
    generalize hone : bits 1 = oneBit
    fin_cases zeroBit <;> fin_cases oneBit <;> simp [pauliZ]
  · intro other hother
    by_cases houtsideZero : ∀ j, j ≠ (0 : Fin 2) → bits j = other j
    · have hzero : bits 0 ≠ other 0 := by
        intro h
        apply hother
        funext j
        fin_cases j
        · exact h.symm
        · exact (houtsideZero 1 (by decide)).symm
      generalize hbits : bits 0 = bitsZero
      generalize hotherBit : other 0 = otherZero
      fin_cases bitsZero <;> fin_cases otherZero <;> simp_all [pauliZ]
    · simp [houtsideZero]

/-- The left single-`Z` moment vanishes, exactly as for the Bell resource. -/
theorem classicallyCorrelatedDensity_left_z_expectation :
    densityExpectation classicallyCorrelatedDensity (zAt (0 : Fin 2)) = 0 := by
  simp only [densityExpectation, classicallyCorrelatedDensity_op,
    Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul]
  rw [← densityExpectation, ← densityExpectation,
    basisDensity_z_expectation, basisDensity_z_expectation]
  norm_num [paperOneOne, paperZeroZero, pairBits]

/-- The right single-`Z` moment also vanishes. -/
theorem classicallyCorrelatedDensity_right_z_expectation :
    densityExpectation classicallyCorrelatedDensity (zAt (1 : Fin 2)) = 0 := by
  simp only [densityExpectation, classicallyCorrelatedDensity_op,
    Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul]
  rw [← densityExpectation, ← densityExpectation,
    basisDensity_z_expectation, basisDensity_z_expectation]
  norm_num [paperOneOne, paperZeroZero, pairBits]

/-- The joint `ZZ` moment is one, despite the explicit classical convex decomposition. -/
theorem classicallyCorrelatedDensity_zz_expectation :
    densityExpectation classicallyCorrelatedDensity
        (zAt (0 : Fin 2) * zAt (1 : Fin 2)) = 1 := by
  simp only [densityExpectation, classicallyCorrelatedDensity_op,
    Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul]
  rw [← densityExpectation, ← densityExpectation,
    basisDensity_zz_expectation, basisDensity_zz_expectation]
  norm_num [paperOneOne, paperZeroZero, pairBits]

/-- The classical mixture and the pure Bell resource agree on all three moments used by U03. -/
theorem classicallyCorrelatedDensity_matches_pairDensity_zero_z_moments :
    densityExpectation classicallyCorrelatedDensity (zAt (0 : Fin 2)) =
        densityExpectation (pairDensity 0 0) (zAt (0 : Fin 2)) ∧
      densityExpectation classicallyCorrelatedDensity (zAt (1 : Fin 2)) =
        densityExpectation (pairDensity 0 0) (zAt (1 : Fin 2)) ∧
      densityExpectation classicallyCorrelatedDensity
          (zAt (0 : Fin 2) * zAt (1 : Fin 2)) =
        densityExpectation (pairDensity 0 0)
          (zAt (0 : Fin 2) * zAt (1 : Fin 2)) := by
  rw [classicallyCorrelatedDensity_left_z_expectation,
    classicallyCorrelatedDensity_right_z_expectation,
    classicallyCorrelatedDensity_zz_expectation,
    pairDensity_z_expectation, pairDensity_z_expectation,
    pairDensity_equal_settings_zz_expectation]
  norm_num

/-- The U03 nonfactorizing-correlation inequality therefore also holds classically. -/
theorem classicallyCorrelatedDensity_correlation :
    densityExpectation classicallyCorrelatedDensity
        (zAt (0 : Fin 2) * zAt (1 : Fin 2)) ≠
      densityExpectation classicallyCorrelatedDensity (zAt (0 : Fin 2)) *
        densityExpectation classicallyCorrelatedDensity (zAt (1 : Fin 2)) := by
  rw [classicallyCorrelatedDensity_zz_expectation,
    classicallyCorrelatedDensity_left_z_expectation,
    classicallyCorrelatedDensity_right_z_expectation]
  norm_num

/--
The classical mixture is not the pure Bell-pair density, even though the three `Z` moments above
agree.  An off-diagonal matrix entry distinguishes the states.
-/
theorem classicallyCorrelatedDensity_ne_pairDensity_zero :
    classicallyCorrelatedDensity ≠ pairDensity 0 0 := by
  intro h
  have hbits : paperOneOne ≠ paperZeroZero := by
    intro hbits
    have hentry := congrFun hbits 0
    norm_num [paperOneOne, paperZeroZero, pairBits] at hentry
  have hentry := congrArg
    (fun rho : Density (Fin 2) ↦ rho.op paperOneOne paperZeroZero) h
  simp [hbits, classicallyCorrelatedDensity, basisDensity,
    pairDensity, pureDensity, densityOfVector, Matrix.vecMulVec,
    pairPureState_paperOneOne, pairPureState_paperZeroZero,
    sameCoefficient, rotationCosHalf, rotationSinHalf] at hentry
  have hsqrt : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [invSqrtTwo] at hentry
  field_simp at hentry
  norm_num at hentry

end
end Decoherence
end Deutsch
