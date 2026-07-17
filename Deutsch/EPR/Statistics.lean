import Deutsch.EPR.Pair
import Deutsch.Information.OneTimePad
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Statistical semantics of the EPR pair

The state is the normalized pure output of the exact pair circuit.  Its one-qubit reductions are
proved maximally mixed for every pair of settings, while a joint parity effect detects the relative
setting.  The resulting joint formulas correct Equations (28) and (41) of the source.
-/

namespace Deutsch
namespace EPR

open Foundations Gates Information Register
open scoped ComplexOrder InnerProductSpace Matrix MatrixOrder

noncomputable section

/-- The normalized fixed reference state on the two-qubit EPR register. -/
def referencePairPureState : PureState (Fin 2) where
  ket := referenceKet (Fin 2)
  norm_eq_one := norm_referenceKet

/-- The normalized pure output of the pair circuit at settings `theta,phi`. -/
def pairPureState (theta phi : ℝ) : PureState (Fin 2) :=
  referencePairPureState.evolve (pairCircuit theta phi)
    (pairCircuit_unitary theta phi)

/-- Density-state form of the exact pure EPR output. -/
def pairDensity (theta phi : ℝ) : Density (Fin 2) :=
  pureDensity (pairPureState theta phi)

/-- The real correlated-sector coefficient before the common `1/sqrt 2` factor. -/
def sameCoefficient (theta phi : ℝ) : ℂ :=
  rotationCosHalf theta * rotationCosHalf phi -
    (Complex.I * rotationSinHalf theta) *
      (Complex.I * rotationSinHalf phi)

/-- The imaginary different-sector coefficient before the common `1/sqrt 2` factor. -/
def crossCoefficient (theta phi : ℝ) : ℂ :=
  (Complex.I * rotationSinHalf theta) * rotationCosHalf phi -
    rotationCosHalf theta * (Complex.I * rotationSinHalf phi)

/-- Equation (38) in the source's explicit paper-labelled phase convention. -/
def equation38Ket (theta : ℝ) : Ket (Fin 2) :=
  invSqrtTwo •
    ((Real.sin (theta / 2) : ℂ) • crossPairKet -
      (Complex.I * (Real.cos (theta / 2) : ℂ)) • samePairKet)

theorem pairPureState_ket_eq_four_coordinates (theta phi : ℝ) :
    (pairPureState theta phi).ket =
      invSqrtTwo •
        (sameCoefficient theta phi • samePairKet +
          crossCoefficient theta phi • crossPairKet) := by
  exact pairCircuit_referenceKet_eq_four_coordinates theta phi

theorem pairPureState_paperOneOne (theta phi : ℝ) :
    (pairPureState theta phi).ket paperOneOne =
      invSqrtTwo * sameCoefficient theta phi := by
  rw [pairPureState_ket_eq_four_coordinates]
  simp [samePairKet, crossPairKet, paperOneOne, paperZeroZero,
    paperOneZero, paperZeroOne, pairBits, basisKet, basisVector, Pi.single]

theorem pairPureState_paperZeroZero (theta phi : ℝ) :
    (pairPureState theta phi).ket paperZeroZero =
      -(invSqrtTwo * sameCoefficient theta phi) := by
  rw [pairPureState_ket_eq_four_coordinates]
  simp [samePairKet, crossPairKet, paperOneOne, paperZeroZero,
    paperOneZero, paperZeroOne, pairBits, basisKet, basisVector, Pi.single]

theorem pairPureState_paperOneZero (theta phi : ℝ) :
    (pairPureState theta phi).ket paperOneZero =
      invSqrtTwo * crossCoefficient theta phi := by
  rw [pairPureState_ket_eq_four_coordinates]
  simp [samePairKet, crossPairKet, paperOneOne, paperZeroZero,
    paperOneZero, paperZeroOne, pairBits, basisKet, basisVector, Pi.single]

theorem pairPureState_paperZeroOne (theta phi : ℝ) :
    (pairPureState theta phi).ket paperZeroOne =
      -(invSqrtTwo * crossCoefficient theta phi) := by
  rw [pairPureState_ket_eq_four_coordinates]
  simp [samePairKet, crossPairKet, paperOneOne, paperZeroZero,
    paperOneZero, paperZeroOne, pairBits, basisKet, basisVector, Pi.single]

private theorem invSqrtTwo_mul_self :
    invSqrtTwo * invSqrtTwo = (2 : ℂ)⁻¹ := by
  have hs : (Real.sqrt 2 : Real) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  rw [invSqrtTwo]
  field_simp
  norm_cast
  nlinarith [Real.sq_sqrt (by norm_num : (0 : Real) ≤ 2)]

private theorem star_invSqrtTwo : star invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

theorem sameCoefficient_eq_cos_sub_half (theta phi : ℝ) :
    sameCoefficient theta phi =
      (Real.cos ((theta - phi) / 2) : ℂ) := by
  have harg : (theta - phi) / 2 = theta / 2 - phi / 2 := by ring
  rw [harg, Real.cos_sub]
  simp [sameCoefficient, rotationCosHalf, rotationSinHalf]
  ring_nf
  norm_num [Complex.I_sq]

theorem crossCoefficient_eq_I_mul_sin_sub_half (theta phi : ℝ) :
    crossCoefficient theta phi =
      Complex.I * (Real.sin ((theta - phi) / 2) : ℂ) := by
  have harg : (theta - phi) / 2 = theta / 2 - phi / 2 := by ring
  rw [harg, Real.sin_sub]
  simp [crossCoefficient, rotationCosHalf, rotationSinHalf]
  ring

/-- The printed Equation (38) is the exact circuit ket with the source's global phase `-i`. -/
theorem equation38Ket_eq_globalPhase_pairPureState (theta : ℝ) :
    equation38Ket theta = (-Complex.I) • (pairPureState theta 0).ket := by
  rw [pairPureState_ket_eq_four_coordinates,
    sameCoefficient_eq_cos_sub_half,
    crossCoefficient_eq_I_mul_sin_sub_half]
  simp only [sub_zero]
  simp only [equation38Ket]
  match_scalars <;> ring_nf
  rw [Complex.I_sq]
  ring

private theorem star_same_amplitude (theta phi : ℝ) :
    star (invSqrtTwo * sameCoefficient theta phi) =
      invSqrtTwo * sameCoefficient theta phi := by
  have hinv : (starRingEnd ℂ) invSqrtTwo = invSqrtTwo := by
    simpa only [starRingEnd_apply] using star_invSqrtTwo
  have hcoefficient :
      (starRingEnd ℂ) (sameCoefficient theta phi) =
        sameCoefficient theta phi := by
    rw [sameCoefficient_eq_cos_sub_half]
    change star (Real.cos ((theta - phi) / 2) : ℂ) = _
    rw [Complex.star_def, Complex.conj_ofReal]
  change (starRingEnd ℂ) (invSqrtTwo * sameCoefficient theta phi) = _
  rw [map_mul]
  rw [hinv, hcoefficient]

private theorem star_cross_amplitude (theta phi : ℝ) :
    star (invSqrtTwo * crossCoefficient theta phi) =
      -(invSqrtTwo * crossCoefficient theta phi) := by
  have hinv : (starRingEnd ℂ) invSqrtTwo = invSqrtTwo := by
    simpa only [starRingEnd_apply] using star_invSqrtTwo
  have hcoefficient :
      (starRingEnd ℂ) (crossCoefficient theta phi) =
        -(crossCoefficient theta phi) := by
    rw [crossCoefficient_eq_I_mul_sin_sub_half]
    change star (Complex.I * (Real.sin ((theta - phi) / 2) : ℂ)) = _
    rw [Complex.star_def, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  change (starRingEnd ℂ) (invSqrtTwo * crossCoefficient theta phi) = _
  rw [map_mul]
  rw [hinv, hcoefficient]
  ring

private theorem pair_amplitudes_norm (theta phi : ℝ) :
    (invSqrtTwo * sameCoefficient theta phi) *
        star (invSqrtTwo * sameCoefficient theta phi) +
      (invSqrtTwo * crossCoefficient theta phi) *
        star (invSqrtTwo * crossCoefficient theta phi) = (2 : ℂ)⁻¹ := by
  rw [star_same_amplitude, star_cross_amplitude,
    sameCoefficient_eq_cos_sub_half,
    crossCoefficient_eq_I_mul_sin_sub_half]
  have htrig :
      (Real.sin ((theta - phi) / 2) : ℂ) ^ 2 +
        (Real.cos ((theta - phi) / 2) : ℂ) ^ 2 = 1 := by
    norm_cast
    exact Real.sin_sq_add_cos_sq ((theta - phi) / 2)
  calc
    invSqrtTwo * (Real.cos ((theta - phi) / 2) : ℂ) *
          (invSqrtTwo * (Real.cos ((theta - phi) / 2) : ℂ)) +
        invSqrtTwo *
            (Complex.I * (Real.sin ((theta - phi) / 2) : ℂ)) *
          -(invSqrtTwo *
            (Complex.I * (Real.sin ((theta - phi) / 2) : ℂ))) =
        (invSqrtTwo * invSqrtTwo) *
          ((Real.sin ((theta - phi) / 2) : ℂ) ^ 2 +
            (Real.cos ((theta - phi) / 2) : ℂ) ^ 2) := by
              ring_nf
              rw [Complex.I_sq]
              ring
    _ = (2 : ℂ)⁻¹ := by rw [htrig, mul_one, invSqrtTwo_mul_self]

theorem pairPureState_ket_pairBits (theta phi : ℝ)
    (left right : QubitIndex) :
    (pairPureState theta phi).ket (pairBits left right) =
      match left, right with
      | 0, 0 => invSqrtTwo * sameCoefficient theta phi
      | 0, 1 => invSqrtTwo * crossCoefficient theta phi
      | 1, 0 => -(invSqrtTwo * crossCoefficient theta phi)
      | 1, 1 => -(invSqrtTwo * sameCoefficient theta phi) := by
  fin_cases left <;> fin_cases right
  · exact pairPureState_paperOneOne theta phi
  · exact pairPureState_paperOneZero theta phi
  · exact pairPureState_paperZeroOne theta phi
  · exact pairPureState_paperZeroZero theta phi

private theorem pairPureState_ofLp_pairBits (theta phi : ℝ)
    (left right : QubitIndex) :
    (pairPureState theta phi).ket.ofLp (pairBits left right) =
      match left, right with
      | 0, 0 => invSqrtTwo * sameCoefficient theta phi
      | 0, 1 => invSqrtTwo * crossCoefficient theta phi
      | 1, 0 => -(invSqrtTwo * crossCoefficient theta phi)
      | 1, 1 => -(invSqrtTwo * sameCoefficient theta phi) := by
  exact pairPureState_ket_pairBits theta phi left right

private theorem flipRaw_ne_self (bit : QubitIndex) : flipRaw bit ≠ bit := by
  fin_cases bit <;> decide

/-- Canonical raw-bit coordinates for the complement of one coordinate in a two-qubit pair. -/
private def complementSingletonBasisEquiv (q : Fin 2) :
    QubitIndex ≃ ComplementBasis ({q} : Finset (Fin 2)) where
  toFun bit := fun _ ↦ bit
  invFun bits := bits ⟨flipRaw q, by simpa using flipRaw_ne_self q⟩
  left_inv _ := rfl
  right_inv bits := by
    funext r
    apply congrArg bits
    apply Subtype.ext
    have hne : r.1 ≠ q := by simpa using r.2
    generalize hx : r.1 = x
    fin_cases q <;> fin_cases x
    · exact (hne hx).elim
    · simp [flipRaw]
    · simp [flipRaw]
    · exact (hne hx).elim

private theorem splitBasis_symm_singleton (q : Fin 2)
    (selected rest : QubitIndex) :
    (splitBasis ({q} : Finset (Fin 2))).symm
        (singletonBasisEquiv q selected,
          complementSingletonBasisEquiv q rest) =
      if q = 0 then pairBits selected rest else pairBits rest selected := by
  funext r
  change (if h : r ∈ ({q} : Finset (Fin 2)) then selected else rest) = _
  fin_cases q <;> fin_cases r <;> simp [pairBits]

/-- Either one-qubit marginal of the rotated EPR pair is exactly maximally mixed. -/
theorem pairDensity_reduce_singleton (theta phi : ℝ) (q : Fin 2) :
    (pairDensity theta phi).reduce ({q} : Finset (Fin 2)) =
      singletonMaximallyMixed q := by
  apply Density.ext
  rw [Density.reduce_op]
  ext i j
  let e := singletonBasisEquiv q
  rw [← e.apply_symm_apply i, ← e.apply_symm_apply j]
  generalize hi : e.symm i = left
  generalize hj : e.symm j = right
  simp only [partialTrace, splitOperator_apply, pairDensity, pureDensity,
    densityOfVector, Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply,
    singletonMaximallyMixed, Matrix.diagonal_apply]
  rw [← (complementSingletonBasisEquiv q).sum_comp]
  simp only [e, splitBasis_symm_singleton]
  have hnorm := pair_amplitudes_norm theta phi
  rw [star_same_amplitude, star_cross_amplitude] at hnorm
  fin_cases q <;> fin_cases left <;> fin_cases right <;>
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] <;>
    norm_num <;>
    simp only [pairPureState_ofLp_pairBits, map_neg, starRingEnd_apply] <;>
    rw [star_same_amplitude, star_cross_amplitude] <;>
    first | linear_combination hnorm | ring

private theorem pureDensity_basisEffect_probability {Q : Type*}
    [Fintype Q] [DecidableEq Q] (psi : PureState Q) (bits : Basis Q) :
    bornProbability (pureDensity psi) (basisEffect bits) =
      (psi.ket.ofLp bits * star (psi.ket.ofLp bits)).re := by
  classical
  simp only [bornProbability, bornWeight, pureDensity, densityOfVector,
    basisEffect, basisDensity, Matrix.trace, Matrix.diag,
    Matrix.mul_diagonal, Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply]
  rw [Finset.sum_eq_single bits]
  · simp
  · intro other _ hne
    simp [hne]
  · simp

/-- Every local effect statistic on either qubit is independent of both rotation settings. -/
theorem pairDensity_locallyStatisticsIndependent (q : Fin 2) :
    LocallyStatisticsIndependent ({q} : Finset (Fin 2))
      (fun settings : ℝ × ℝ => pairDensity settings.1 settings.2) := by
  intro settings settings'
  apply effectStatisticallyEquivalent_of_eq
  rw [pairDensity_reduce_singleton, pairDensity_reduce_singleton]

private theorem sameAmplitude_probability (theta phi : ℝ) :
    ((invSqrtTwo * sameCoefficient theta phi) *
        star (invSqrtTwo * sameCoefficient theta phi)).re =
      (1 / 2 : ℝ) * Real.cos ((theta - phi) / 2) ^ 2 := by
  rw [star_same_amplitude, sameCoefficient_eq_cos_sub_half]
  have hproduct :
      (invSqrtTwo * (Real.cos ((theta - phi) / 2) : ℂ)) *
          (invSqrtTwo * (Real.cos ((theta - phi) / 2) : ℂ)) =
        (2 : ℂ)⁻¹ * (Real.cos ((theta - phi) / 2) : ℂ) ^ 2 := by
    rw [← invSqrtTwo_mul_self]
    ring
  rw [hproduct]
  rw [show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

private theorem crossAmplitude_probability (theta phi : ℝ) :
    ((invSqrtTwo * crossCoefficient theta phi) *
        star (invSqrtTwo * crossCoefficient theta phi)).re =
      (1 / 2 : ℝ) * Real.sin ((theta - phi) / 2) ^ 2 := by
  rw [star_cross_amplitude, crossCoefficient_eq_I_mul_sin_sub_half]
  have hproduct :
      (invSqrtTwo *
          (Complex.I * (Real.sin ((theta - phi) / 2) : ℂ))) *
          -(invSqrtTwo *
            (Complex.I * (Real.sin ((theta - phi) / 2) : ℂ))) =
        (2 : ℂ)⁻¹ * (Real.sin ((theta - phi) / 2) : ℂ) ^ 2 := by
    rw [← invSqrtTwo_mul_self]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hproduct]
  rw [show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]

/-- Joint paper outcome `(1,1)` has probability `1/2 cos²((theta-phi)/2)`. -/
theorem pairDensity_paperOneOne_probability (theta phi : ℝ) :
    bornProbability (pairDensity theta phi) (basisEffect paperOneOne) =
      (1 / 2 : ℝ) * Real.cos ((theta - phi) / 2) ^ 2 := by
  rw [pairDensity, pureDensity_basisEffect_probability,
    pairPureState_paperOneOne]
  exact sameAmplitude_probability theta phi

theorem pairDensity_paperZeroZero_probability (theta phi : ℝ) :
    bornProbability (pairDensity theta phi) (basisEffect paperZeroZero) =
      (1 / 2 : ℝ) * Real.cos ((theta - phi) / 2) ^ 2 := by
  rw [pairDensity, pureDensity_basisEffect_probability,
    pairPureState_paperZeroZero]
  simpa only [star_neg, neg_mul_neg] using
    sameAmplitude_probability theta phi

theorem pairDensity_paperOneZero_probability (theta phi : ℝ) :
    bornProbability (pairDensity theta phi) (basisEffect paperOneZero) =
      (1 / 2 : ℝ) * Real.sin ((theta - phi) / 2) ^ 2 := by
  rw [pairDensity, pureDensity_basisEffect_probability,
    pairPureState_paperOneZero]
  exact crossAmplitude_probability theta phi

theorem pairDensity_paperZeroOne_probability (theta phi : ℝ) :
    bornProbability (pairDensity theta phi) (basisEffect paperZeroOne) =
      (1 / 2 : ℝ) * Real.sin ((theta - phi) / 2) ^ 2 := by
  rw [pairDensity, pureDensity_basisEffect_probability,
    pairPureState_paperZeroOne]
  simpa only [star_neg, neg_mul_neg] using
    crossAmplitude_probability theta phi

/-- The joint effect selecting the two computational outcomes with different paper bits. -/
def differentEffect : Effect (Fin 2) :=
  parityEffect 1

private theorem differentEffect_op_eq_z_product :
    differentEffect.op =
      ((2 : ℂ)⁻¹) • (1 - zAt (0 : Fin 2) * zAt (1 : Fin 2)) := by
  ext row column
  generalize hrowZero : row 0 = rowZero
  generalize hrowOne : row 1 = rowOne
  generalize hcolumnZero : column 0 = columnZero
  generalize hcolumnOne : column 1 = columnOne
  have hrow : row = pairBits rowZero rowOne := by
    funext q
    fin_cases q
    · exact hrowZero
    · exact hrowOne
  have hcolumn : column = pairBits columnZero columnOne := by
    funext q
    fin_cases q
    · exact hcolumnZero
    · exact hcolumnOne
  rw [hrow, hcolumn]
  simp only [Matrix.smul_apply, Matrix.sub_apply]
  change _ = _ • (_ -
    (embedQubit (0 : Fin 2) pauliZ * embedQubit (1 : Fin 2) pauliZ)
      (pairBits rowZero rowOne) (pairBits columnZero columnOne))
  rw [embedQubit_mul_embedQubit_apply_of_ne (by decide : (0 : Fin 2) ≠ 1)]
  fin_cases rowZero <;> fin_cases rowOne <;>
    fin_cases columnZero <;> fin_cases columnOne <;>
    norm_num [differentEffect, parityEffect, twoQubitParity, zAt,
      pairBits, pauliZ, Fin.add_def, Matrix.one_apply]

private theorem differentEffect_op_eq_basis_sum :
    differentEffect.op =
      (basisEffect paperOneZero).op + (basisEffect paperZeroOne).op := by
  ext row column
  generalize hrowZero : row 0 = rowZero
  generalize hrowOne : row 1 = rowOne
  generalize hcolumnZero : column 0 = columnZero
  generalize hcolumnOne : column 1 = columnOne
  have hrow : row = pairBits rowZero rowOne := by
    funext q
    fin_cases q
    · exact hrowZero
    · exact hrowOne
  have hcolumn : column = pairBits columnZero columnOne := by
    funext q
    fin_cases q
    · exact hcolumnZero
    · exact hcolumnOne
  rw [hrow, hcolumn]
  fin_cases rowZero <;> fin_cases rowOne <;>
    fin_cases columnZero <;> fin_cases columnOne <;>
    norm_num [differentEffect, parityEffect, twoQubitParity,
      basisEffect, basisDensity, paperOneZero, paperZeroOne,
      pairBits, Matrix.diagonal, Pi.single, Fin.add_def] <;>
    simp [paperOneZero, paperZeroOne, pairBits]

/-- Corrected Equation (28): different outcomes occur with `sin²((theta-phi)/2)`. -/
theorem pairDensity_different_probability (theta phi : ℝ) :
    bornProbability (pairDensity theta phi) differentEffect =
      Real.sin ((theta - phi) / 2) ^ 2 := by
  simp only [bornProbability, bornWeight]
  rw [differentEffect_op_eq_basis_sum, Matrix.mul_add, Matrix.trace_add,
    Complex.add_re]
  change
    bornProbability (pairDensity theta phi) (basisEffect paperOneZero) +
        bornProbability (pairDensity theta phi) (basisEffect paperZeroOne) = _
  rw [pairDensity_paperOneZero_probability,
    pairDensity_paperZeroOne_probability]
  ring

/-- The joint effect for the paper-labelled outcome `(1,1)`. -/
def jointPaperOneEffect : Effect (Fin 2) :=
  basisEffect paperOneOne

/-- Corrected Equation (41): the joint paper-one probability is `1/2 cos²`. -/
theorem pairDensity_jointPaperOne_probability (theta phi : ℝ) :
    bornProbability (pairDensity theta phi) jointPaperOneEffect =
      (1 / 2 : ℝ) * Real.cos ((theta - phi) / 2) ^ 2 := by
  exact pairDensity_paperOneOne_probability theta phi

/-- The paper-labelled one outcome on a named singleton subsystem (raw index zero). -/
def singletonPaperOne (q : Fin 2) :
    Basis {r : Fin 2 // r ∈ ({q} : Finset (Fin 2))} :=
  fun _ => 0

/-- The globally embedded paper-one effect on one selected qubit. -/
def paperOneMarginalEffect (q : Fin 2) : Effect (Fin 2) :=
  (basisEffect (singletonPaperOne q)).embedSubsystem ({q} : Finset (Fin 2))

private theorem paperOneMarginalEffect_op_eq_projector (q : Fin 2) :
    (paperOneMarginalEffect q).op = paperBitOneProjectorAt q := by
  unfold paperOneMarginalEffect paperBitOneProjectorAt embedQubit
  rw [Effect.embedSubsystem_op]
  congr 1
  let e := singletonBasisEquiv q
  have hone : singletonPaperOne q = e 0 := rfl
  rw [hone]
  ext i j
  rw [← e.apply_symm_apply i, ← e.apply_symm_apply j]
  generalize hi : e.symm i = rawI
  generalize hj : e.symm j = rawJ
  fin_cases rawI <;> fin_cases rawJ <;>
    norm_num [basisEffect, basisDensity, bitOneProjector, identity₂,
      pauliZ, Pi.single, e]

private theorem singletonMaximallyMixed_basis_probability (q : Fin 2)
    (bits : Basis {r : Fin 2 // r ∈ ({q} : Finset (Fin 2))}) :
    bornProbability (singletonMaximallyMixed q) (basisEffect bits) =
      (1 / 2 : ℝ) := by
  classical
  simp [bornProbability, bornWeight, singletonMaximallyMixed,
    basisEffect, basisDensity, Matrix.trace,
    Matrix.diagonal_mul_diagonal, Pi.single_apply]

/-- Either paper-one marginal has probability exactly one half at every setting. -/
theorem pairDensity_paperOne_marginal_probability
    (theta phi : ℝ) (q : Fin 2) :
    bornProbability (pairDensity theta phi) (paperOneMarginalEffect q) =
      (1 / 2 : ℝ) := by
  change bornProbability (pairDensity theta phi)
      ((basisEffect (singletonPaperOne q)).embedSubsystem
        ({q} : Finset (Fin 2))) = _
  rw [← bornProbability_reduce]
  rw [pairDensity_reduce_singleton]
  exact singletonMaximallyMixed_basis_probability q (singletonPaperOne q)

theorem pairDensity_left_paperOne_probability (theta phi : ℝ) :
    bornProbability (pairDensity theta phi) (paperOneMarginalEffect 0) =
      (1 / 2 : ℝ) :=
  pairDensity_paperOne_marginal_probability theta phi 0

theorem pairDensity_right_paperOne_probability (theta phi : ℝ) :
    bornProbability (pairDensity theta phi) (paperOneMarginalEffect 1) =
      (1 / 2 : ℝ) :=
  pairDensity_paperOne_marginal_probability theta phi 1

/-- Every single-qubit `Z` expectation vanishes because each EPR marginal is maximally mixed. -/
theorem pairDensity_z_expectation (theta phi : ℝ) (q : Fin 2) :
    densityExpectation (pairDensity theta phi) (zAt q) = 0 := by
  have hw := bornWeight_eq_probability
    (pairDensity theta phi) (paperOneMarginalEffect q)
  rw [pairDensity_paperOne_marginal_probability] at hw
  simp only [bornWeight] at hw
  rw [paperOneMarginalEffect_op_eq_projector,
    paperBitOneProjectorAt_eq] at hw
  simp only [Matrix.mul_smul, Matrix.mul_add,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_add,
    (pairDensity theta phi).trace_one] at hw
  norm_num at hw
  unfold densityExpectation
  exact hw

/-- Equal settings force the two paper outcomes to agree. -/
theorem pairDensity_different_equal_settings (theta : ℝ) :
    bornProbability (pairDensity theta theta) differentEffect = 0 := by
  rw [pairDensity_different_probability]
  simp

/-- Equal EPR settings have perfect joint `Z` correlation. -/
theorem pairDensity_equal_settings_zz_expectation (theta : ℝ) :
    densityExpectation (pairDensity theta theta)
      (zAt (0 : Fin 2) * zAt (1 : Fin 2)) = 1 := by
  have hw := bornWeight_eq_probability
    (pairDensity theta theta) differentEffect
  rw [pairDensity_different_equal_settings] at hw
  simp only [bornWeight] at hw
  rw [differentEffect_op_eq_z_product] at hw
  simp only [Matrix.mul_smul, Matrix.mul_sub,
    Matrix.mul_one, Matrix.trace_smul, Matrix.trace_sub,
    (pairDensity theta theta).trace_one] at hw
  norm_num at hw
  unfold densityExpectation
  exact (sub_eq_zero.mp hw).symm

/-- At zero settings, the EPR resource has joint `Z` statistics that do not factor into marginals. -/
theorem pairDensity_zero_resource_correlation :
    densityExpectation (pairDensity 0 0)
        (zAt (0 : Fin 2) * zAt (1 : Fin 2)) ≠
      densityExpectation (pairDensity 0 0) (zAt (0 : Fin 2)) *
        densityExpectation (pairDensity 0 0) (zAt (1 : Fin 2)) := by
  rw [pairDensity_equal_settings_zz_expectation,
    pairDensity_z_expectation, pairDensity_z_expectation]
  norm_num

/-- At equal settings the joint paper-one outcome has probability one half. -/
theorem pairDensity_jointPaperOne_equal_settings (theta : ℝ) :
    bornProbability (pairDensity theta theta) jointPaperOneEffect =
      (1 / 2 : ℝ) := by
  rw [pairDensity_jointPaperOne_probability]
  norm_num

/-- Settings separated by `pi` force different paper outcomes. -/
theorem pairDensity_different_pi_zero :
    bornProbability (pairDensity Real.pi 0) differentEffect = 1 := by
  rw [pairDensity_different_probability]
  norm_num

/-- At equal angles, the printed cosine-square Equation (28) predicts the wrong value. -/
theorem equation28_printed_equal_angle_counterexample :
    bornProbability (pairDensity 0 0) differentEffect ≠
      Real.cos (((0 : ℝ) - 0) / 2) ^ 2 := by
  rw [pairDensity_different_equal_settings]
  norm_num

/-- At equal angles, the printed sine-square Equation (41) predicts the wrong value. -/
theorem equation41_printed_equal_angle_counterexample :
    bornProbability (pairDensity 0 0) jointPaperOneEffect ≠
      (1 / 2 : ℝ) * Real.sin (((0 : ℝ) - 0) / 2) ^ 2 := by
  rw [pairDensity_jointPaperOne_equal_settings]
  norm_num

/-- The finite setting family using the angle choices zero and `pi` with `phi = 0`. -/
def pairSettingFamily : Bool → Density (Fin 2)
  | false => pairDensity 0 0
  | true => pairDensity Real.pi 0

/-- Every singleton-local statistic is independent of the finite setting choice. -/
theorem pairSettingFamily_locallyStatisticsIndependent (q : Fin 2) :
    LocallyStatisticsIndependent ({q} : Finset (Fin 2)) pairSettingFamily := by
  intro setting setting'
  apply effectStatisticallyEquivalent_of_eq
  cases setting <;> cases setting' <;>
    simp only [pairSettingFamily] <;>
    rw [pairDensity_reduce_singleton, pairDensity_reduce_singleton]

/-- A joint finite-register effect distinguishes the two members of `pairSettingFamily`. -/
theorem pairSettingFamily_statisticallyDetectable :
    StatisticallyDetectable pairSettingFamily := by
  refine ⟨false, true, differentEffect, ?_⟩
  change bornProbability (pairDensity 0 0) differentEffect ≠
    bornProbability (pairDensity Real.pi 0) differentEffect
  rw [pairDensity_different_equal_settings, pairDensity_different_pi_zero]
  norm_num

end
end EPR
end Deutsch
