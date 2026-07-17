import Deutsch.Descriptor
import Mathlib.Tactic

/-!
# Descriptor verification

Focused Stage 5 tests for initial and evolved validity, arbitrary-register reconstruction and
generation, invalid triples/families, empty and singleton boundaries, and the strict separation
between operator equality, unitary conjugacy, and fixed-reference component expectations.
-/

namespace DeutschTests
namespace DescriptorVerification

open Deutsch Deutsch.Foundations Deutsch.Register
open scoped Matrix

noncomputable section

/-! ## Initial and evolved validity -/

theorem initial_descriptor_one_valid :
    (Descriptor.initial (0 : Fin 1)).Valid :=
  Descriptor.initial_valid 0

theorem initial_family_two_valid :
    DescriptorFamily.Valid (DescriptorFamily.initial (Fin 2)) :=
  DescriptorFamily.initial_valid

theorem initial_family_three_valid :
    DescriptorFamily.Valid (DescriptorFamily.initial (Fin 3)) :=
  DescriptorFamily.initial_valid

theorem initial_family_three_all_cross_relations
    {q r : Fin 3} (hqr : q ≠ r) (a b : Axis) :
    ((DescriptorFamily.initial (Fin 3) q).component a) *
        ((DescriptorFamily.initial (Fin 3) r).component b) =
      ((DescriptorFamily.initial (Fin 3) r).component b) *
        ((DescriptorFamily.initial (Fin 3) q).component a) :=
  DescriptorFamily.initial_pairwiseCommutes q r hqr a b

def xUnitaryThree : UnitaryOperator (Fin 3) :=
  ⟨xAt (0 : Fin 3), xAt_unitary 0⟩

theorem x_evolved_three_family_valid :
    DescriptorFamily.Valid
      (DescriptorFamily.evolve xUnitaryThree (DescriptorFamily.initial (Fin 3))) :=
  DescriptorFamily.initial_valid.evolve xUnitaryThree.property

theorem x_evolved_three_family_preserves_every_cross_relation
    {q r : Fin 3} (hqr : q ≠ r) (a b : Axis) :
    let D := DescriptorFamily.evolve xUnitaryThree (DescriptorFamily.initial (Fin 3))
    (D q).component a * (D r).component b =
      (D r).component b * (D q).component a := by
  exact x_evolved_three_family_valid.cross q r hqr a b

/-! ## Exact completeness, reconstruction, and basis results -/

theorem initial_empty_family_generates_operator_algebra :
    DescriptorFamily.GeneratesOperatorAlgebra (DescriptorFamily.initial Empty) :=
  DescriptorFamily.initial_generates

theorem initial_three_family_generates_operator_algebra :
    DescriptorFamily.GeneratesOperatorAlgebra (DescriptorFamily.initial (Fin 3)) :=
  DescriptorFamily.initial_generates

theorem x_evolved_three_family_generates_operator_algebra :
    DescriptorFamily.GeneratesOperatorAlgebra
      (DescriptorFamily.evolve xUnitaryThree (DescriptorFamily.initial (Fin 3))) :=
  DescriptorFamily.evolved_initial_generates xUnitaryThree

theorem every_empty_register_operator_reconstructs (A : Operator Empty) :
    (∑ word : PauliWord Empty,
      PauliWord.coefficient A word • PauliWord.initialPauliString word) = A :=
  PauliWord.reconstruction A

theorem every_three_qubit_operator_reconstructs (A : Operator (Fin 3)) :
    (∑ word : PauliWord (Fin 3),
      PauliWord.coefficient A word • PauliWord.initialPauliString word) = A :=
  PauliWord.reconstruction A

theorem every_x_evolved_three_qubit_operator_reconstructs (A : Operator (Fin 3)) :
    (∑ word : PauliWord (Fin 3),
      PauliWord.evolvedCoefficient xUnitaryThree A word •
        PauliWord.evolvedPauliString xUnitaryThree word) = A :=
  PauliWord.evolvedReconstruction xUnitaryThree A

theorem one_site_pauli_word_is_initial_descriptor (q : Fin 3) (a : Axis) :
    PauliWord.initialPauliString (PauliWord.single q a) =
      (Descriptor.initial q).component a :=
  PauliWord.initialPauliString_single q a

theorem one_site_evolved_word_is_evolved_descriptor (q : Fin 3) (a : Axis) :
    PauliWord.evolvedPauliString xUnitaryThree (PauliWord.single q a) =
      ((DescriptorFamily.evolve xUnitaryThree
        (DescriptorFamily.initial (Fin 3)) q).component a) :=
  PauliWord.evolvedPauliString_single xUnitaryThree q a

theorem pauli_basis_is_exact_on_three_qubits (word : PauliWord (Fin 3)) :
    PauliWord.basis word = PauliWord.initialPauliString word :=
  PauliWord.basis_apply word

/-! ## Invalid triples and invalid families -/

def zeroDescriptor (Q : Type*) [Fintype Q] [DecidableEq Q] : Descriptor Q :=
  { x := 0, y := 0, z := 0 }

theorem zero_descriptor_is_hermitian :
    ∀ a, ((zeroDescriptor (Fin 1)).component a).IsHermitian := by
  intro a
  cases a <;> simp [zeroDescriptor, Descriptor.component, Matrix.IsHermitian]

theorem zero_descriptor_satisfies_one_cyclic_relation :
    (zeroDescriptor (Fin 1)).x * (zeroDescriptor (Fin 1)).y =
      Complex.I • (zeroDescriptor (Fin 1)).z := by
  simp [zeroDescriptor]

theorem zero_descriptor_not_valid : ¬ (zeroDescriptor (Fin 1)).Valid := by
  intro h
  have hs := h.square Axis.x
  have hzeroone : (0 : Operator (Fin 1)) = 1 := by
    simp [zeroDescriptor, Descriptor.component] at hs
  exact zero_ne_one hzeroone

def identityDescriptor (Q : Type*) [Fintype Q] [DecidableEq Q] : Descriptor Q :=
  { x := 1, y := 1, z := 1 }

theorem identity_descriptor_is_hermitian :
    ∀ a, ((identityDescriptor (Fin 1)).component a).IsHermitian := by
  intro a
  cases a <;> simp [identityDescriptor, Descriptor.component, Matrix.IsHermitian]

theorem identity_descriptor_squares :
    ∀ a, (identityDescriptor (Fin 1)).component a *
      (identityDescriptor (Fin 1)).component a = 1 := by
  intro a
  cases a <;> simp [identityDescriptor, Descriptor.component]

theorem identity_descriptor_not_valid : ¬ (identityDescriptor (Fin 1)).Valid := by
  intro h
  have hc := h.cyclic Axis.x
  let b : Basis (Fin 1) := fun _ => 0
  have hentry := congrFun (congrFun hc b) b
  have hre := congrArg Complex.re hentry
  norm_num [identityDescriptor, Descriptor.component, Matrix.one_apply] at hre

theorem zero_nonunitary_evolution_not_valid :
    ¬ ((Descriptor.initial (0 : Fin 1)).evolve 0).Valid := by
  intro h
  have hs := h.square Axis.x
  have hzeroone : (0 : Operator (Fin 1)) = 1 := by
    simp [Descriptor.evolve, Descriptor.component, Deutsch.Register.heisenberg] at hs
  exact zero_ne_one hzeroone

def repeatedInitialFamily : DescriptorFamily (Fin 2) :=
  fun _ => Descriptor.initial (0 : Fin 2)

theorem repeated_family_is_locally_valid :
    ∀ q, (repeatedInitialFamily q).Valid := by
  intro q
  exact Descriptor.initial_valid 0

theorem repeated_family_not_pairwise_commuting :
    ¬ DescriptorFamily.PairwiseCommutes repeatedInitialFamily := by
  intro h
  have hxy := h (0 : Fin 2) (1 : Fin 2) (by decide) Axis.x Axis.y
  change xAt 0 * yAt 0 = yAt 0 * xAt 0 at hxy
  rw [xAt_mul_yAt, yAt_mul_xAt] at hxy
  let b : Basis (Fin 2) := fun _ => 0
  have hentry := congrFun (congrFun hxy b) b
  simp only [Matrix.smul_apply] at hentry
  rw [zAt, embedQubit_apply_ite] at hentry
  norm_num [pauliZ, b] at hentry
  have him := congrArg Complex.im hentry
  norm_num at him

theorem empty_initial_family_valid :
    DescriptorFamily.Valid (DescriptorFamily.initial Empty) :=
  DescriptorFamily.initial_valid

theorem every_singleton_family_cross_condition_is_vacuous
    (D : DescriptorFamily (Fin 1)) : DescriptorFamily.PairwiseCommutes D := by
  intro q r hqr
  exact False.elim (hqr (Subsingleton.elim q r))

/-! ## Equality, conjugacy, and fixed-reference predictions are distinct -/

def referenceStabilizer : UnitaryOperator (Fin 1) :=
  ⟨-(zAt (0 : Fin 1)), by
    rw [Matrix.mem_unitaryGroup_iff']
    change (-(zAt (0 : Fin 1)))ᴴ * (-(zAt (0 : Fin 1))) = 1
    rw [Matrix.conjTranspose_neg, zAt_isHermitian]
    simp [zAt_mul_zAt]⟩

theorem reference_stabilizer_fixes_reference :
    act referenceStabilizer (referenceKet (Fin 1)) = referenceKet (Fin 1) := by
  rw [act, matrixEndEquiv_apply]
  apply WithLp.ofLp_injective
  change (-(zAt (0 : Fin 1))) *ᵥ
      (Pi.single (paperZeroAssignment (Fin 1)) (1 : ℂ) : Basis (Fin 1) → ℂ) =
    (Pi.single (paperZeroAssignment (Fin 1)) (1 : ℂ) : Basis (Fin 1) → ℂ)
  rw [Matrix.mulVec_single_one]
  funext b
  change -(zAt (0 : Fin 1) b (paperZeroAssignment (Fin 1))) =
    (Pi.single (paperZeroAssignment (Fin 1)) (1 : ℂ) : Basis (Fin 1) → ℂ) b
  by_cases hb : b = paperZeroAssignment (Fin 1)
  · subst b
    rw [Pi.single_eq_same]
    have houtside : ∀ j : Fin 1, j ≠ 0 →
        paperZeroAssignment (Fin 1) j = paperZeroAssignment (Fin 1) j := by
      intro j hj
      exact False.elim (hj (Subsingleton.elim j 0))
    rw [zAt, embedQubit_apply_ite, if_pos houtside]
    norm_num [pauliZ, paperZeroAssignment]
  · have hb0ne : b 0 ≠ 1 := by
      intro hb0
      apply hb
      funext j
      have hj : j = 0 := Subsingleton.elim j 0
      subst j
      exact hb0
    have hb0 : b 0 = 0 := by
      have hlt : (b 0).val < 2 := (b 0).isLt
      have hvalne : (b 0).val ≠ 1 := by
        intro hval
        apply hb0ne
        apply Fin.ext
        exact hval
      apply Fin.ext
      omega
    have houtside : ∀ j : Fin 1, j ≠ 0 → b j = paperZeroAssignment (Fin 1) j := by
      intro j hj
      exact False.elim (hj (Subsingleton.elim j 0))
    rw [zAt, embedQubit_apply_ite, if_pos houtside]
    simp [pauliZ, paperZeroAssignment, hb, hb0]

theorem conjugated_initial_is_unitarily_conjugate :
    DescriptorFamily.IsUnitaryConjugate
      (DescriptorFamily.initial (Fin 1))
      (DescriptorFamily.evolve referenceStabilizer
        (DescriptorFamily.initial (Fin 1))) :=
  DescriptorFamily.isUnitaryConjugate_evolve referenceStabilizer _

theorem conjugated_initial_is_reference_expectation_equivalent :
    DescriptorFamily.ReferenceExpectationEquivalent
      (DescriptorFamily.initial (Fin 1))
      (DescriptorFamily.evolve referenceStabilizer
        (DescriptorFamily.initial (Fin 1))) :=
  DescriptorFamily.referenceExpectationEquivalent_evolve_of_fixes_reference
    referenceStabilizer _ reference_stabilizer_fixes_reference

theorem conjugated_initial_x_changes :
    ((DescriptorFamily.evolve referenceStabilizer
      (DescriptorFamily.initial (Fin 1)) 0).component .x) =
      -(Descriptor.initial (0 : Fin 1)).component .x := by
  simp only [DescriptorFamily.evolve_apply, Descriptor.evolve_component]
  change Deutsch.Register.heisenberg (-(zAt 0)) (xAt 0) = -(xAt 0)
  calc
    Deutsch.Register.heisenberg (-(zAt (0 : Fin 1))) (xAt (0 : Fin 1)) =
        (-(zAt (0 : Fin 1))) * xAt (0 : Fin 1) * (-(zAt (0 : Fin 1))) := by
      rw [Deutsch.Register.heisenberg, Matrix.conjTranspose_neg, zAt_isHermitian]
    _ = zAt (0 : Fin 1) * xAt 0 * zAt 0 := by noncomm_ring
    _ = (Complex.I • yAt (0 : Fin 1)) * zAt 0 := by rw [zAt_mul_xAt]
    _ = Complex.I • (yAt (0 : Fin 1) * zAt 0) := by rw [Matrix.smul_mul]
    _ = Complex.I • (Complex.I • xAt (0 : Fin 1)) := by rw [yAt_mul_zAt]
    _ = -(xAt (0 : Fin 1)) := by
      ext i j
      change Complex.I * (Complex.I * xAt 0 i j) = -xAt 0 i j
      rw [← mul_assoc, Complex.I_mul_I]
      simp

theorem conjugated_initial_is_not_operator_equal :
    DescriptorFamily.evolve referenceStabilizer
      (DescriptorFamily.initial (Fin 1)) ≠ DescriptorFamily.initial (Fin 1) := by
  intro h
  have hx := congrArg
    (fun D : DescriptorFamily (Fin 1) => (D 0).component .x) h
  rw [conjugated_initial_x_changes] at hx
  have hne : -(xAt (0 : Fin 1)) ≠ xAt 0 := by
    intro heq
    have hm := congrArg (fun A : Operator (Fin 1) => A * xAt 0) heq
    simp only [neg_mul, xAt_mul_xAt] at hm
    let b : Basis (Fin 1) := fun _ => 0
    have hentry := congrFun (congrFun hm b) b
    norm_num [Matrix.one_apply] at hentry
  exact hne hx

end
end DescriptorVerification
end DeutschTests
