import Deutsch.Locality.Heisenberg
import Deutsch.Register.Pauli
import Mathlib.Tactic

/-!
# Locality verification

Focused Stage 4 tests for disjoint finite supports, Heisenberg invariance, arbitrary-ket
predictions, empty support, and the hypotheses that cannot be dropped.
-/

namespace DeutschTests
namespace LocalityVerification

open Deutsch Deutsch.Foundations Deutsch.Locality Deutsch.Register
open scoped ComplexConjugate InnerProductSpace Matrix

noncomputable section

/-! ## Arbitrary nonadjacent multi-label supports -/

def evenSites : Finset (Fin 5) := {0, 2}

def remoteSites : Finset (Fin 5) := {1, 4}

theorem evenSites_disjoint_remoteSites : Disjoint evenSites remoteSites := by
  decide

theorem nonadjacent_multi_label_embeddings_commute
    (A : SubsystemOperator evenSites) (B : SubsystemOperator remoteSites) :
    embedSubsystem evenSites A * embedSubsystem remoteSites B =
      embedSubsystem remoteSites B * embedSubsystem evenSites A := by
  exact embedSubsystem_commute_of_disjoint evenSites_disjoint_remoteSites A B

theorem semantic_nonadjacent_supported_operators_commute
    {A B : Operator (Fin 5)}
    (hA : IsSupportedOn evenSites A) (hB : IsSupportedOn remoteSites B) :
    A * B = B * A := by
  exact supportedOperators_commute_of_disjoint
    evenSites_disjoint_remoteSites hA hB

/-! ## Heisenberg and prediction locality -/

theorem singleton_local_x_fixes_remote_z :
    Deutsch.Register.heisenberg (xAt (0 : Fin 3)) (zAt (2 : Fin 3)) =
      zAt (2 : Fin 3) := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) (xAt_unitary 0) (xAt_isSupportedOn 0) (zAt_isSupportedOn 2)

theorem arbitrary_ket_remote_z_expectation_is_invariant (psi : Ket (Fin 3)) :
    expectation (act (xAt (0 : Fin 3)) psi) (zAt (2 : Fin 3)) =
      expectation psi (zAt (2 : Fin 3)) := by
  exact expectation_after_local_unitary_eq
    (by decide) (xAt_unitary 0) (xAt_isSupportedOn 0) (zAt_isSupportedOn 2) psi

theorem arbitrary_ket_heisenberg_expectation_is_invariant (psi : Ket (Fin 3)) :
    expectation psi
        (Deutsch.Register.heisenberg (xAt (0 : Fin 3)) (zAt (2 : Fin 3))) =
      expectation psi (zAt (2 : Fin 3)) := by
  exact expectation_heisenberg_eq_of_disjoint_support
    (by decide) (xAt_unitary 0) (xAt_isSupportedOn 0) (zAt_isSupportedOn 2) psi

/-! ## A normalized, formally non-product regression state -/

def bits (a b : QubitIndex) : Basis (Fin 2) := ![a, b]

@[simp]
theorem bits_apply_zero (a b : QubitIndex) : bits a b 0 = a := rfl

@[simp]
theorem bits_apply_one (a b : QubitIndex) : bits a b 1 = b := rfl

def bellAmplitude : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

/-- The normalized raw-index Bell vector `( |00⟩ + |11⟩ ) / √2`. -/
def bellKet : Ket (Fin 2) :=
  bellAmplitude • (basisKet (bits 0 0) + basisKet (bits 1 1))

/-- Coordinate-factorization definition of a two-qubit product vector. -/
def IsProductKet (psi : Ket (Fin 2)) : Prop :=
  ∃ left right : QubitIndex → ℂ,
    ∀ x : Basis (Fin 2), psi x = left (x 0) * right (x 1)

theorem bellAmplitude_ne_zero : bellAmplitude ≠ 0 := by
  unfold bellAmplitude
  norm_num

@[simp]
theorem bellKet_apply_zero_zero : bellKet (bits 0 0) = bellAmplitude := by
  simp [bellKet, basisKet, basisVector, bits]

@[simp]
theorem bellKet_apply_zero_one : bellKet (bits 0 1) = 0 := by
  simp [bellKet, basisKet, basisVector, bits]

@[simp]
theorem bellKet_apply_one_zero : bellKet (bits 1 0) = 0 := by
  simp [bellKet, basisKet, basisVector, bits]

@[simp]
theorem bellKet_apply_one_one : bellKet (bits 1 1) = bellAmplitude := by
  simp [bellKet, basisKet, basisVector, bits]

theorem IsProductKet.cross_product_identity {psi : Ket (Fin 2)}
    (hpsi : IsProductKet psi) :
    psi (bits 0 0) * psi (bits 1 1) =
      psi (bits 0 1) * psi (bits 1 0) := by
  rcases hpsi with ⟨left, right, hfactor⟩
  rw [hfactor, hfactor, hfactor, hfactor]
  simp only [bits_apply_zero, bits_apply_one]
  ring

theorem bellKet_not_product : ¬ IsProductKet bellKet := by
  intro hproduct
  have hcross := hproduct.cross_product_identity
  simp only [bellKet_apply_zero_zero, bellKet_apply_zero_one,
    bellKet_apply_one_zero, bellKet_apply_one_one, mul_zero] at hcross
  exact (mul_ne_zero bellAmplitude_ne_zero bellAmplitude_ne_zero) hcross

theorem basisKet_zero_zero_orthogonal_one_one :
    ⟪basisKet (bits 0 0), basisKet (bits 1 1)⟫_ℂ = 0 := by
  simp [basisKet, basisVector, bits, PiLp.inner_apply]

theorem norm_bellKet : ‖bellKet‖ = 1 := by
  rw [bellKet, norm_smul]
  have hsqrt_nonneg : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrt_ne : Real.sqrt 2 ≠ 0 := by positivity
  have hsum_norm :
      ‖basisKet (bits 0 0) + basisKet (bits 1 1)‖ = Real.sqrt 2 := by
    apply (sq_eq_sq₀ (norm_nonneg _) hsqrt_nonneg).mp
    simp only [pow_two]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
      basisKet_zero_zero_orthogonal_one_one]
    simp only [norm_basisKet, one_mul]
    rw [Real.mul_self_sqrt (by norm_num)]
    norm_num
  rw [hsum_norm]
  rw [show ‖bellAmplitude‖ = (Real.sqrt 2)⁻¹ by
    simp [bellAmplitude, Complex.norm_real, abs_of_nonneg hsqrt_nonneg]]
  field_simp

def bellPureState : PureState (Fin 2) where
  ket := bellKet
  norm_eq_one := norm_bellKet

/-- Locality is instantiated on a ket proved normalized and outside the product-vector class. -/
theorem bellKet_remote_z_expectation_is_invariant :
    expectation (act (xAt (0 : Fin 2)) bellKet) (zAt (1 : Fin 2)) =
      expectation bellKet (zAt (1 : Fin 2)) := by
  exact expectation_after_local_unitary_eq
    (by decide) (xAt_unitary 0) (xAt_isSupportedOn 0) (zAt_isSupportedOn 1) bellKet

theorem bellKet_remote_z_heisenberg_expectation_is_invariant :
    expectation bellKet
        (Deutsch.Register.heisenberg (xAt (0 : Fin 2)) (zAt (1 : Fin 2))) =
      expectation bellKet (zAt (1 : Fin 2)) := by
  exact expectation_heisenberg_eq_of_disjoint_support
    (by decide) (xAt_unitary 0) (xAt_isSupportedOn 0) (zAt_isSupportedOn 1) bellKet

/-! ## Empty support -/

theorem empty_support_commutes_with_any_supported_operator
    {A B : Operator (Fin 5)}
    (hA : IsSupportedOn (∅ : Finset (Fin 5)) A)
    (hB : IsSupportedOn remoteSites B) :
    A * B = B * A := by
  exact supportedOperators_commute_of_disjoint (by simp) hA hB

theorem embedded_empty_subsystem_commutes
    (A : SubsystemOperator (∅ : Finset (Fin 5)))
    (B : SubsystemOperator evenSites) :
    embedSubsystem ∅ A * embedSubsystem evenSites B =
      embedSubsystem evenSites B * embedSubsystem ∅ A := by
  exact embedSubsystem_commute_of_disjoint (by simp) A B

theorem nonzero_scalar_has_empty_support :
    IsSupportedOn (∅ : Finset (Fin 5)) ((3 : ℂ) • (1 : Operator (Fin 5))) := by
  exact (isSupportedOn_one (∅ : Finset (Fin 5))).smul 3

/-! ## Overlap and nonunitarity are genuine boundaries -/

theorem same_coordinate_x_and_z_do_not_commute
    {Q : Type*} [Fintype Q] [DecidableEq Q] (q : Q) :
    xAt q * zAt q ≠ zAt q * xAt q := by
  rw [xAt, zAt, ← embedQubit_mul, ← embedQubit_mul]
  intro h
  have hlocal := embedQubit_injective q h
  have hentry := congrFun (congrFun hlocal (0 : QubitIndex)) (1 : QubitIndex)
  norm_num [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ] at hentry

theorem overlapping_x_changes_z :
    Deutsch.Register.heisenberg (xAt (0 : Fin 1)) (zAt (0 : Fin 1)) =
      -(zAt (0 : Fin 1)) := by
  rw [Deutsch.Register.heisenberg, xAt_isHermitian, xAt_mul_zAt,
    Matrix.smul_mul, yAt_mul_xAt, smul_smul]
  norm_num

theorem overlapping_supported_unitary_does_not_fix_z :
    IsSupportedOn ({0} : Finset (Fin 1)) (xAt (0 : Fin 1)) ∧
      IsSupportedOn ({0} : Finset (Fin 1)) (zAt (0 : Fin 1)) ∧
      ¬ Disjoint ({0} : Finset (Fin 1)) ({0} : Finset (Fin 1)) ∧
      xAt (0 : Fin 1) ∈ Matrix.unitaryGroup (Basis (Fin 1)) ℂ ∧
      Deutsch.Register.heisenberg (xAt (0 : Fin 1)) (zAt (0 : Fin 1)) ≠
        zAt (0 : Fin 1) := by
  refine ⟨xAt_isSupportedOn 0, zAt_isSupportedOn 0, by simp,
    xAt_unitary 0, ?_⟩
  rw [overlapping_x_changes_z]
  intro h
  let raw0 : Basis (Fin 1) := fun _ ↦ 0
  have hz : zAt (0 : Fin 1) raw0 raw0 = 1 := by
    rw [zAt, embedQubit_apply_ite]
    norm_num [raw0, pauliZ]
  have hentry := congrFun (congrFun h raw0) raw0
  simp only [Matrix.neg_apply] at hentry
  rw [hz] at hentry
  norm_num at hentry

/-- Exact support cannot be fabricated on a remote coordinate. -/
theorem xAt_zero_not_supported_on_one :
    ¬ IsSupportedOn ({1} : Finset (Fin 2)) (xAt (0 : Fin 2)) := by
  intro hwrong
  have hcomm := supportedOperators_commute_of_disjoint
    (s := ({1} : Finset (Fin 2))) (t := ({0} : Finset (Fin 2)))
    (by decide) hwrong (zAt_isSupportedOn 0)
  exact same_coordinate_x_and_z_do_not_commute (0 : Fin 2) hcomm

theorem remote_z_is_nonzero : zAt (2 : Fin 3) ≠ 0 := by
  intro h
  rw [zAt, ← embedQubit_zero] at h
  have hlocal := embedQubit_injective (2 : Fin 3) h
  have hentry := congrFun (congrFun hlocal (0 : QubitIndex)) (0 : QubitIndex)
  norm_num [pauliZ] at hentry

/-- Disjoint support without unitarity does not imply Heisenberg invariance. -/
theorem zero_has_disjoint_support_but_does_not_fix_remote_z :
    IsSupportedOn ({0} : Finset (Fin 3)) (0 : Operator (Fin 3)) ∧
      IsSupportedOn ({2} : Finset (Fin 3)) (zAt (2 : Fin 3)) ∧
      Deutsch.Register.heisenberg (0 : Operator (Fin 3)) (zAt (2 : Fin 3)) ≠
        zAt (2 : Fin 3) := by
  refine ⟨isSupportedOn_zero {0}, zAt_isSupportedOn 2, ?_⟩
  simpa [Deutsch.Register.heisenberg] using remote_z_is_nonzero.symm

end
end LocalityVerification
end DeutschTests
