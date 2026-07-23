import Deutsch.Register.State
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef

/-!
# Finite density states, effects, and POVMs

The public statistical layer stays on the concrete finite-register matrices used throughout the
project. A density is positive semidefinite with trace one. An effect has both itself and its
complement positive semidefinite, and a finite POVM is a complete family of effects.

The general Born bounds are proved rather than built into the definitions. In particular,
positivity of `trace (rho * E)` is obtained by factoring `E = Cᴴ C`, cycling the trace, and using
positive-semidefiniteness of `C rho Cᴴ`.
-/

namespace Deutsch
namespace Information

open Foundations Register
open scoped ComplexOrder InnerProductSpace Matrix MatrixOrder

noncomputable section

variable {Q Outcome : Type*} [Fintype Q] [DecidableEq Q]

/-- A finite-register density operator: positive semidefinite with trace one. -/
structure Density (Q : Type*) [Fintype Q] [DecidableEq Q] where
  op : Operator Q
  positive : op.PosSemidef
  trace_one : op.trace = 1

@[ext]
theorem Density.ext {rho sigma : Density Q} (h : rho.op = sigma.op) : rho = sigma := by
  cases rho
  cases sigma
  simp_all

/-- A finite-register effect `E`, encoded by `0 ≤ E` and `0 ≤ I - E`. -/
structure Effect (Q : Type*) [Fintype Q] [DecidableEq Q] where
  op : Operator Q
  positive : op.PosSemidef
  complement_positive : (1 - op).PosSemidef

@[ext]
theorem Effect.ext {E F : Effect Q} (h : E.op = F.op) : E = F := by
  cases E
  cases F
  simp_all

/-- A trace-one positive semidefinite density operator is bounded above by the identity. -/
theorem density_le_one (rho : Density Q) : (1 - rho.op).PosSemidef := by
  classical
  let U : Matrix (Basis Q) (Basis Q) ℂ := rho.positive.isHermitian.eigenvectorUnitary
  let d : Basis Q → ℝ := rho.positive.isHermitian.eigenvalues
  have hd_nonneg (i : Basis Q) : 0 ≤ d i :=
    rho.positive.eigenvalues_nonneg i
  have hd_sum : ∑ i, d i = 1 := by
    have htrace := rho.positive.isHermitian.trace_eq_sum_eigenvalues
    rw [rho.trace_one] at htrace
    have hre := congrArg Complex.re htrace.symm
    simpa [d] using hre
  have hd_le_one (i : Basis Q) : d i ≤ 1 := by
    rw [← hd_sum]
    exact Finset.single_le_sum (fun j _ ↦ hd_nonneg j) (Finset.mem_univ i)
  have hdiag :
      (Matrix.diagonal (fun i ↦ Complex.ofReal (1 - d i))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    change (0 : ℂ) ≤ Complex.ofReal (1 - d i)
    exact RCLike.ofReal_nonneg.mpr (sub_nonneg.mpr (hd_le_one i))
  have hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ :=
    rho.positive.isHermitian.eigenvectorUnitary.property
  have hone : (1 : Operator Q) = U * (1 : Operator Q) * star U := by
    rw [Matrix.mul_one]
    exact hU.2.symm
  have hrho : rho.op =
      U * Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d) * star U := by
    simpa only [U, d, Unitary.conjStarAlgAut_apply] using
      rho.positive.isHermitian.spectral_theorem
  rw [hone, hrho, ← Matrix.sub_mul, ← Matrix.mul_sub]
  have hmiddle :
      (1 : Operator Q) -
          Matrix.diagonal ((RCLike.ofReal : ℝ → ℂ) ∘ d) =
        Matrix.diagonal (fun i ↦ Complex.ofReal (1 - d i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.diagonal]
    · simp [Matrix.diagonal, hij]
  rw [hmiddle]
  simpa only [← Matrix.star_eq_conjTranspose] using
    hdiag.mul_mul_conjTranspose_same U

/-- Regard a density operator as an effect; trace one forces every eigenvalue into `[0,1]`. -/
def Density.toEffect (rho : Density Q) : Effect Q where
  op := rho.op
  positive := rho.positive
  complement_positive := density_le_one rho

@[simp]
theorem Density.toEffect_op (rho : Density Q) : rho.toEffect.op = rho.op := rfl

/-- A finite-outcome POVM: a family of effects summing to the identity. -/
structure POVM (Q Outcome : Type*)
    [Fintype Q] [DecidableEq Q] [Fintype Outcome] where
  effect : Outcome → Effect Q
  complete : ∑ x, (effect x).op = 1

/-- The complex trace expression underlying the Born rule. -/
def bornWeight (rho : Density Q) (effect : Effect Q) : ℂ :=
  Matrix.trace (rho.op * effect.op)

/-- The real Born probability associated with an effect. -/
def bornProbability (rho : Density Q) (effect : Effect Q) : ℝ :=
  (bornWeight rho effect).re

/-- The trace of a product of two positive semidefinite complex matrices is nonnegative. -/
theorem trace_mul_nonneg_of_posSemidef {A B : Operator Q}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ Matrix.trace (A * B) := by
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle']
  simpa [Matrix.mul_assoc] using (hA.mul_mul_conjTranspose_same C).trace_nonneg

theorem bornWeight_nonneg (rho : Density Q) (effect : Effect Q) :
    0 ≤ bornWeight rho effect :=
  trace_mul_nonneg_of_posSemidef rho.positive effect.positive

theorem bornWeight_im (rho : Density Q) (effect : Effect Q) :
    (bornWeight rho effect).im = 0 :=
  (Complex.nonneg_iff.mp (bornWeight_nonneg rho effect)).2.symm

/-- The complex Born weight is exactly the coercion of its real probability. -/
theorem bornWeight_eq_probability (rho : Density Q) (effect : Effect Q) :
    bornWeight rho effect = (bornProbability rho effect : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa [bornProbability] using bornWeight_im rho effect

theorem bornProbability_nonneg (rho : Density Q) (effect : Effect Q) :
    0 ≤ bornProbability rho effect :=
  (Complex.nonneg_iff.mp (bornWeight_nonneg rho effect)).1

theorem bornProbability_le_one (rho : Density Q) (effect : Effect Q) :
    bornProbability rho effect ≤ 1 := by
  have h := trace_mul_nonneg_of_posSemidef rho.positive effect.complement_positive
  have hre := (Complex.nonneg_iff.mp h).1
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.trace_sub, rho.trace_one] at hre
  simpa [bornProbability, bornWeight] using hre

theorem bornProbability_mem_Icc (rho : Density Q) (effect : Effect Q) :
    bornProbability rho effect ∈ Set.Icc 0 1 :=
  ⟨bornProbability_nonneg rho effect, bornProbability_le_one rho effect⟩

/-- In every finite register, all effect probabilities determine the density operator. -/
theorem density_eq_iff_effect_probabilities (rho sigma : Density Q) :
    rho = sigma ↔
      ∀ effect : Effect Q,
        bornProbability rho effect = bornProbability sigma effect := by
  constructor
  · rintro rfl effect
    rfl
  · intro h
    apply Density.ext
    let A : Operator Q := rho.op - sigma.op
    have hAherm : A.IsHermitian :=
      rho.positive.isHermitian.sub sigma.positive.isHermitian
    apply sub_eq_zero.mp
    change A = 0
    apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
    rw [hAherm.eq]
    have hrho := h rho.toEffect
    have hsigma := h sigma.toEffect
    have hrhoC : bornWeight rho rho.toEffect = bornWeight sigma rho.toEffect := by
      calc
        bornWeight rho rho.toEffect = (bornProbability rho rho.toEffect : ℂ) :=
          bornWeight_eq_probability _ _
        _ = (bornProbability sigma rho.toEffect : ℂ) :=
          congrArg (fun x : ℝ ↦ (x : ℂ)) hrho
        _ = bornWeight sigma rho.toEffect :=
          (bornWeight_eq_probability _ _).symm
    have hsigmaC : bornWeight rho sigma.toEffect = bornWeight sigma sigma.toEffect := by
      calc
        bornWeight rho sigma.toEffect = (bornProbability rho sigma.toEffect : ℂ) :=
          bornWeight_eq_probability _ _
        _ = (bornProbability sigma sigma.toEffect : ℂ) :=
          congrArg (fun x : ℝ ↦ (x : ℂ)) hsigma
        _ = bornWeight sigma sigma.toEffect :=
          (bornWeight_eq_probability _ _).symm
    simp only [bornWeight, Density.toEffect_op] at hrhoC hsigmaC
    dsimp [A]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub, Matrix.trace_sub]
    rw [hrhoC, hsigmaC]
    rw [Matrix.mul_sub, Matrix.trace_sub]
    exact sub_self _

theorem bornWeights_normalize [Fintype Outcome] (rho : Density Q)
    (measurement : POVM Q Outcome) :
    ∑ x, bornWeight rho (measurement.effect x) = 1 := by
  classical
  simp only [bornWeight]
  rw [← Matrix.trace_sum, ← Finset.mul_sum, measurement.complete, mul_one, rho.trace_one]

theorem bornProbabilities_normalize [Fintype Outcome] (rho : Density Q)
    (measurement : POVM Q Outcome) :
    ∑ x, bornProbability rho (measurement.effect x) = 1 := by
  have h := congrArg Complex.re (bornWeights_normalize rho measurement)
  simpa [bornProbability] using h

/-- Density-matrix expectation of an arbitrary register operator. -/
def densityExpectation (rho : Density Q) (A : Operator Q) : ℂ :=
  Matrix.trace (rho.op * A)

theorem densityExpectation_one (rho : Density Q) :
    densityExpectation rho 1 = 1 := by
  simp [densityExpectation, rho.trace_one]

/-- The complementary outcome effect `I - E`. -/
def Effect.complement (effect : Effect Q) : Effect Q where
  op := 1 - effect.op
  positive := effect.complement_positive
  complement_positive := by simpa using effect.positive

@[simp]
theorem Effect.complement_op (effect : Effect Q) :
    effect.complement.op = 1 - effect.op := rfl

@[simp]
theorem Effect.complement_complement (effect : Effect Q) :
    effect.complement.complement = effect := by
  cases effect
  simp [Effect.complement]

/-- The two-outcome POVM consisting of an effect and its complement. -/
def Effect.binaryPOVM (effect : Effect Q) : POVM Q Bool where
  effect outcome := if outcome then effect.complement else effect
  complete := by
    simp [Effect.complement_op]

@[simp]
theorem Effect.binaryPOVM_false (effect : Effect Q) :
    (effect.binaryPOVM.effect false) = effect := rfl

@[simp]
theorem Effect.binaryPOVM_true (effect : Effect Q) :
    (effect.binaryPOVM.effect true) = effect.complement := rfl

/-- The impossible effect. -/
def zeroEffect (Q : Type*) [Fintype Q] [DecidableEq Q] : Effect Q where
  op := 0
  positive := Matrix.PosSemidef.zero
  complement_positive := by
    simpa using (Matrix.PosSemidef.one : (1 : Operator Q).PosSemidef)

/-- The certain effect. -/
def oneEffect (Q : Type*) [Fintype Q] [DecidableEq Q] : Effect Q where
  op := 1
  positive := Matrix.PosSemidef.one
  complement_positive := by
    simpa using (Matrix.PosSemidef.zero : (0 : Operator Q).PosSemidef)

@[simp]
theorem bornProbability_zeroEffect (rho : Density Q) :
    bornProbability rho (zeroEffect Q) = 0 := by
  simp [bornProbability, bornWeight, zeroEffect]

@[simp]
theorem bornProbability_oneEffect (rho : Density Q) :
    bornProbability rho (oneEffect Q) = 1 := by
  simp [bornProbability, bornWeight, oneEffect, rho.trace_one]

/-- Rank-one density built from a raw normalized coordinate vector. -/
def densityOfVector (psi : Basis Q → ℂ)
    (hnorm : psi ⬝ᵥ star psi = 1) : Density Q where
  op := Matrix.vecMulVec psi (star psi)
  positive := Matrix.posSemidef_vecMulVec_self_star psi
  trace_one := by simpa using hnorm

/-- Density operator associated with a normalized public pure state. -/
def pureDensity (psi : PureState Q) : Density Q :=
  densityOfVector (fun i => psi.ket i) (by
    have hinner : ⟪psi.ket, psi.ket⟫_ℂ = 1 :=
      inner_self_eq_one_of_norm_eq_one psi.norm_eq_one
    change ∑ i, psi.ket i * (starRingEnd ℂ) (psi.ket i) = 1
    simpa only [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using hinner)

/-- Trace expectation of a pure density agrees with the existing ket expectation. -/
theorem densityExpectation_pureDensity (psi : PureState Q) (A : Operator Q) :
    densityExpectation (pureDensity psi) A = Register.expectation psi.ket A := by
  simp only [densityExpectation, pureDensity, densityOfVector,
    Register.expectation, Register.act, matrixEndEquiv_apply]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.vecMulVec,
    Matrix.of_apply, Pi.star_apply, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.mulVec, dotProduct, ← starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The pure computational-basis density at `bits`. -/
def basisDensity (bits : Basis Q) : Density Q where
  op := Matrix.diagonal (Pi.single bits 1)
  positive := by
    apply Matrix.PosSemidef.diagonal
    intro i
    classical
    by_cases h : i = bits
    · subst i
      simp
    · simp [Pi.single, h]
  trace_one := by
    classical
    simp

/-- The density of a normalized computational-basis ket is its basis projector. -/
theorem pureDensity_basisState (bits : Basis Q) :
    pureDensity
        ({ ket := basisKet bits
           norm_eq_one := norm_basisKet bits } : PureState Q) =
      basisDensity bits := by
  apply Density.ext
  ext i j
  classical
  simp only [pureDensity, densityOfVector, basisDensity, basisKet, basisVector,
    Matrix.vecMulVec, Matrix.of_apply, Pi.star_apply, Matrix.diagonal_apply]
  by_cases hi : i = bits <;> by_cases hj : j = bits <;>
    subst_vars <;> simp_all [Pi.single, eq_comm]

/-- A computational-basis density reads off the matching diagonal matrix entry. -/
theorem basisDensity_expectation (bits : Basis Q) (A : Operator Q) :
    densityExpectation (basisDensity bits) A = A bits bits := by
  classical
  simp [densityExpectation, basisDensity, Matrix.trace,
    Matrix.diagonal_mul, Pi.single_apply]

/-- The rank-one computational-basis effect at `bits`. -/
def basisEffect (bits : Basis Q) : Effect Q where
  op := (basisDensity bits).op
  positive := (basisDensity bits).positive
  complement_positive := by
    classical
    rw [show 1 - (basisDensity bits).op =
        Matrix.diagonal (fun i => if i = bits then (0 : ℂ) else 1) by
      ext i j
      by_cases hij : i = j
      · subst j
        by_cases hi : i = bits
        · subst i
          simp [basisDensity]
        · simp [basisDensity, Matrix.diagonal, Pi.single, hi]
      · simp [basisDensity, Matrix.diagonal, hij]]
    apply Matrix.PosSemidef.diagonal
    intro i
    by_cases hi : i = bits <;> simp [hi]

@[simp]
theorem basisEffect_op (bits : Basis Q) :
    (basisEffect bits).op = (basisDensity bits).op := rfl

/-- Projective measurement in the full register computational basis. -/
def computationalBasisPOVM (Q : Type*) [Fintype Q] [DecidableEq Q] :
    POVM Q (Basis Q) where
  effect := basisEffect
  complete := by
    classical
    ext i j
    rw [Matrix.sum_apply]
    simp [basisEffect, basisDensity, Matrix.one_apply, Matrix.diagonal, Pi.single_apply]

theorem basisDensity_basisEffect_probability (prepared observed : Basis Q) :
    bornProbability (basisDensity prepared) (basisEffect observed) =
      if prepared = observed then 1 else 0 := by
  classical
  by_cases h : prepared = observed
  · subst observed
    simp [bornProbability, bornWeight, basisEffect, basisDensity,
      Matrix.trace, Matrix.diagonal_mul_diagonal, Pi.single_apply]
  · have h' : observed ≠ prepared := Ne.symm h
    simp [bornProbability, bornWeight, basisEffect, basisDensity,
      Matrix.trace, Matrix.diagonal_mul_diagonal, Pi.single_apply, h, h']

/-- Density form of the paper's all-zero reference state. -/
def referenceDensity (Q : Type*) [Fintype Q] [DecidableEq Q] : Density Q :=
  basisDensity (paperZeroAssignment Q)

/-- Density and ket expectations agree on the paper's all-zero reference state. -/
theorem referenceDensity_expectation (A : Operator Q) :
    densityExpectation (referenceDensity Q) A =
      Register.expectation (referenceKet Q) A := by
  rw [referenceDensity, basisDensity_expectation,
    referenceKet, Register.basisKet_expectation]

/-- Schrödinger unitary evolution of a density state. -/
def Density.evolve (rho : Density Q) (U : Operator Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) : Density Q where
  op := U * rho.op * Uᴴ
  positive := rho.positive.mul_mul_conjTranspose_same U
  trace_one := by
    rw [Matrix.trace_mul_cycle]
    have hUstar : Uᴴ * U = 1 := by
      rw [← Matrix.star_eq_conjTranspose]
      exact hU.1
    rw [hUstar, one_mul, rho.trace_one]

@[simp]
theorem Density.evolve_op (rho : Density Q) (U : Operator Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) :
    (rho.evolve U hU).op = U * rho.op * Uᴴ := rfl

/-- Schrödinger density evolution and Heisenberg operator evolution have equal expectations. -/
theorem densityExpectation_evolve (rho : Density Q) (U A : Operator Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) :
    densityExpectation (rho.evolve U hU) A =
      densityExpectation rho (Register.heisenberg U A) := by
  simp only [densityExpectation, Density.evolve_op, Register.heisenberg]
  calc
    Matrix.trace ((U * rho.op * Uᴴ) * A) =
        Matrix.trace (U * (rho.op * (Uᴴ * A))) := by
          congr 1
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace ((Uᴴ * A) * (U * rho.op)) :=
      Matrix.trace_mul_cycle' U rho.op (Uᴴ * A)
    _ = Matrix.trace ((Uᴴ * A * U) * rho.op) := by
      congr 1
      simp only [Matrix.mul_assoc]
    _ = Matrix.trace (rho.op * (Uᴴ * A * U)) :=
      Matrix.trace_mul_comm (Uᴴ * A * U) rho.op

/-- Evolving a pure-state density agrees exactly with evolving its underlying ket. -/
theorem pureDensity_evolve (psi : PureState Q) (U : Operator Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) :
    pureDensity (psi.evolve U hU) =
      (pureDensity psi).evolve U hU := by
  apply Density.ext
  simp only [pureDensity, densityOfVector, PureState.evolve,
    Density.evolve_op, Register.act, matrixEndEquiv_apply]
  change Matrix.vecMulVec (U *ᵥ psi.ket.ofLp)
      (star (U *ᵥ psi.ket.ofLp)) =
    U * Matrix.vecMulVec psi.ket.ofLp (star psi.ket.ofLp) * Uᴴ
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul,
    Matrix.vecMul_conjTranspose]
  simp

/-- Density-state purity `re (trace rho^2)`. -/
def purity (rho : Density Q) : ℝ :=
  (Matrix.trace (rho.op * rho.op)).re

/-- Purity is invariant under physical unitary evolution. -/
theorem purity_evolve (rho : Density Q) (U : Operator Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) :
    purity (rho.evolve U hU) = purity rho := by
  have hUstar : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hU.1
  apply congrArg Complex.re
  simp only [Density.evolve_op]
  calc
    Matrix.trace ((U * rho.op * Uᴴ) * (U * rho.op * Uᴴ)) =
        Matrix.trace (U * (rho.op * (Uᴴ * U) * rho.op) * Uᴴ) := by
          congr 1
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (U * (rho.op * rho.op) * Uᴴ) := by
      rw [hUstar, Matrix.mul_one]
    _ = Matrix.trace (Uᴴ * U * (rho.op * rho.op)) := by
      rw [Matrix.trace_mul_cycle]
    _ = Matrix.trace (rho.op * rho.op) := by rw [hUstar, one_mul]

end
end Information
end Deutsch
