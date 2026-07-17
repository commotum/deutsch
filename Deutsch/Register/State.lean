import Deutsch.Register.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Pure register states and predictions

The paper's standard ket is the all-paper-zero computational basis vector. Because paper bit zero
is raw matrix index `1`, its basis assignment is the constant raw index `1`. Expectations use the
finite Hilbert-space inner product, and state/operator prediction equivalence is proved through the
matrix-to-endomorphism bridge from `Deutsch.Register.Basic`.
-/

namespace Deutsch
namespace Register

open Foundations
open scoped ComplexConjugate InnerProductSpace Matrix

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The coordinate vector concentrated at one computational-basis assignment. -/
def basisVector (bits : Basis Q) : CoordinateVector Q := Pi.single bits 1

/-- A computational-basis ket in the finite register Hilbert space. -/
def basisKet (bits : Basis Q) : Ket Q := WithLp.toLp 2 (basisVector bits)

@[simp]
theorem norm_basisKet (bits : Basis Q) : ‖basisKet bits‖ = 1 := by
  simp [basisKet, basisVector]

/-- Raw basis assignment for the paper's `|0,…,0⟩`; paper zero is raw index `1`. -/
def paperZeroAssignment (Q : Type*) : Basis Q := fun _ ↦ 1

omit [Fintype Q] [DecidableEq Q] in
@[simp]
theorem paperZeroAssignment_apply (q : Q) : paperZeroAssignment Q q = 1 := rfl

/-- The paper's all-zero reference ket. -/
def referenceKet (Q : Type*) [Fintype Q] [DecidableEq Q] : Ket Q :=
  basisKet (paperZeroAssignment Q)

@[simp]
theorem norm_referenceKet : ‖referenceKet Q‖ = 1 := norm_basisKet _

/-- A normalized pure register state. -/
structure PureState (Q : Type*) [Fintype Q] [DecidableEq Q] where
  ket : Ket Q
  norm_eq_one : ‖ket‖ = 1

/-- Matrix action on the finite Hilbert-space representation. -/
def act (A : Operator Q) (psi : Ket Q) : Ket Q := matrixEndEquiv Q A psi

@[simp]
theorem act_one (psi : Ket Q) : act (1 : Operator Q) psi = psi := by
  simp [act]

theorem act_mul (A B : Operator Q) (psi : Ket Q) :
    act (A * B) psi = act A (act B psi) := by
  change matrixEndEquiv Q (A * B) psi = _
  rw [map_mul]
  rfl

theorem act_smul (A : Operator Q) (c : ℂ) (psi : Ket Q) :
    act A (c • psi) = c • act A psi := by
  exact (matrixEndEquiv Q A).map_smul c psi

theorem inner_act_unitary (U : Operator Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) (psi phi : Ket Q) :
    ⟪act U psi, act U phi⟫_ℂ = ⟪psi, phi⟫_ℂ := by
  unfold act
  rw [← LinearMap.adjoint_inner_right]
  rw [← matrixEndEquiv_conjTranspose]
  rw [← Module.End.mul_apply, ← map_mul]
  have hUstar : Uᴴ * U = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hU.1
  rw [hUstar]
  simp

theorem norm_act_unitary (U : Operator Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) (psi : Ket Q) :
    ‖act U psi‖ = ‖psi‖ := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  rw [inner_act_unitary U hU]

/-- A unitary maps a normalized pure state to another normalized pure state. -/
def PureState.evolve (U : Operator Q)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ) (psi : PureState Q) : PureState Q where
  ket := act U psi.ket
  norm_eq_one := by rw [norm_act_unitary U hU, psi.norm_eq_one]

/-- Pure-state expectation `⟨ψ|A|ψ⟩`. -/
def expectation (psi : Ket Q) (A : Operator Q) : ℂ := ⟪psi, act A psi⟫_ℂ

theorem star_expectation (psi : Ket Q) (A : Operator Q) :
    star (expectation psi A) = expectation psi Aᴴ := by
  unfold expectation
  calc
    star ⟪psi, act A psi⟫_ℂ = ⟪act A psi, psi⟫_ℂ := inner_conj_symm _ _
    _ = ⟪psi, act Aᴴ psi⟫_ℂ := by
      unfold act
      rw [matrixEndEquiv_conjTranspose, LinearMap.adjoint_inner_right]

theorem expectation_of_isHermitian (psi : Ket Q) (A : Operator Q)
    (hA : A.IsHermitian) : star (expectation psi A) = expectation psi A := by
  rw [star_expectation, hA.eq]

/-- Schrödinger state action and Heisenberg operator action give the same pure expectation. -/
theorem expectation_after_action (U A : Operator Q) (psi : Ket Q) :
    expectation (act U psi) A = expectation psi (heisenberg U A) := by
  unfold expectation act
  rw [← LinearMap.adjoint_inner_right]
  rw [← matrixEndEquiv_conjTranspose]
  simp only [heisenberg, map_mul, Module.End.mul_apply]

/-- The fixed-reference prediction equality for any matrix preparation `U`. -/
theorem fixed_reference_prediction (U A : Operator Q) :
    expectation (act U (referenceKet Q)) A =
      expectation (referenceKet Q) (heisenberg U A) :=
  expectation_after_action U A (referenceKet Q)

/-- Eigenvectors transport contravariantly under unitary Heisenberg evolution. -/
theorem heisenberg_eigenvector (U A : Operator Q) (v : Ket Q) (lambda : ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) ℂ)
    (hv : act A v = lambda • v) :
    act (heisenberg U A) (act Uᴴ v) = lambda • act Uᴴ v := by
  have hUU : U * Uᴴ = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact hU.2
  calc
    act (heisenberg U A) (act Uᴴ v) =
        act Uᴴ (act A (act U (act Uᴴ v))) := by
          simp only [heisenberg, act_mul]
    _ = act Uᴴ (act A (act (U * Uᴴ) v)) := by rw [act_mul]
    _ = act Uᴴ (act A v) := by rw [hUU, act_one]
    _ = act Uᴴ (lambda • v) := by rw [hv]
    _ = lambda • act Uᴴ v := act_smul Uᴴ lambda v

/-- Any unit vector is the image of a designated computational basis vector under a unitary. -/
theorem exists_unitary_matrix_mulVec_reference
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (reference : ι) (psi : EuclideanSpace ℂ ι) (hpsi : ‖psi‖ = 1) :
    ∃ U : Matrix ι ι ℂ,
      U ∈ Matrix.unitaryGroup ι ℂ ∧
      U *ᵥ Pi.single reference 1 = fun i ↦ psi i := by
  let selected : Set ι := {reference}
  let prescribed : ι → EuclideanSpace ℂ ι := fun _ ↦ psi
  have hprescribed : Orthonormal ℂ (selected.restrict prescribed) := by
    rw [orthonormal_subsingleton_iff]
    intro i
    simpa [selected, prescribed] using hpsi
  have hcard : Module.finrank ℂ (EuclideanSpace ℂ ι) = Fintype.card ι := by
    simp
  obtain ⟨b, hb⟩ :=
    hprescribed.exists_orthonormalBasis_extension_of_card_eq hcard
  let standard : OrthonormalBasis ι ℂ (EuclideanSpace ℂ ι) :=
    EuclideanSpace.basisFun ι ℂ
  let U : Matrix ι ι ℂ := standard.toBasis.toMatrix b
  refine ⟨U, standard.toMatrix_orthonormalBasis_mem_unitary b, ?_⟩
  rw [Matrix.mulVec_single_one]
  funext i
  change standard.toBasis.repr (b reference) i = psi i
  rw [hb reference (by simp [selected])]
  rfl

/-- Every normalized register ket is a unitary image of the paper's all-zero reference ket. -/
theorem exists_unitary_matrix_mulVec_paperZero (psi : Ket Q) (hpsi : ‖psi‖ = 1) :
    ∃ U : Operator Q,
      U ∈ Matrix.unitaryGroup (Basis Q) ℂ ∧
      U *ᵥ Pi.single (paperZeroAssignment Q) 1 = fun i ↦ psi i :=
  exists_unitary_matrix_mulVec_reference (paperZeroAssignment Q) psi hpsi

/-- Endomorphism-form standardization of an arbitrary normalized pure register ket. -/
theorem exists_unitary_act_reference (psi : Ket Q) (hpsi : ‖psi‖ = 1) :
    ∃ U : Operator Q,
      U ∈ Matrix.unitaryGroup (Basis Q) ℂ ∧ act U (referenceKet Q) = psi := by
  obtain ⟨U, hU, hpsiU⟩ := exists_unitary_matrix_mulVec_paperZero psi hpsi
  refine ⟨U, hU, ?_⟩
  rw [act, matrixEndEquiv_apply]
  apply WithLp.ofLp_injective
  change U *ᵥ Pi.single (paperZeroAssignment Q) 1 = fun i ↦ psi i
  exact hpsiU

/-- Pure-state standardization packaged for the public normalized-state type. -/
theorem PureState.exists_unitary_preparation (psi : PureState Q) :
    ∃ U : Operator Q,
      U ∈ Matrix.unitaryGroup (Basis Q) ℂ ∧ act U (referenceKet Q) = psi.ket :=
  exists_unitary_act_reference psi.ket psi.norm_eq_one

/-- Every pure-state prediction has an exactly equivalent fixed-reference Heisenberg form. -/
theorem PureState.exists_fixed_reference_representation (psi : PureState Q) :
    ∃ U : Operator Q,
      U ∈ Matrix.unitaryGroup (Basis Q) ℂ ∧
      psi.ket = act U (referenceKet Q) ∧
      ∀ A : Operator Q,
        expectation psi.ket A = expectation (referenceKet Q) (heisenberg U A) := by
  obtain ⟨U, hU, hprep⟩ := psi.exists_unitary_preparation
  refine ⟨U, hU, hprep.symm, ?_⟩
  intro A
  rw [← hprep]
  exact fixed_reference_prediction U A

end
end Register
end Deutsch
