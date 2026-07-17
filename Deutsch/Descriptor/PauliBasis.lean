import Deutsch.Descriptor.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Pauli-word basis for finite registers

A `PauliWord Q` chooses `I`, `X`, `Y`, or `Z` independently at every named qubit.  Its concrete
matrix is defined entrywise as the product of the corresponding one-qubit entries.  The dual
entry formula below gives exact coefficients and proves reconstruction for every register operator;
in particular, completeness is not inferred from a cardinality calculation.
-/

namespace Deutsch

open Foundations Register
open scoped Matrix BigOperators

noncomputable section

/-- A choice of identity or one of the three Pauli axes at every named qubit. -/
abbrev PauliWord (Q : Type*) := Q → Option Axis

namespace PauliWord

/-- The one-qubit matrix selected by a Pauli-word letter; `none` denotes the identity. -/
def localMatrix : Option Axis → QubitMatrix
  | none => identity₂
  | some .x => pauliX
  | some .y => pauliY
  | some .z => pauliZ

/-- The entrywise dual to `localMatrix` for the Hilbert--Schmidt pairing. -/
def localDualEntry (letter : Option Axis) (i j : QubitIndex) : ℂ :=
  (2 : ℂ)⁻¹ * star (localMatrix letter i j)

private theorem sum_letters (f : Option Axis → ℂ) :
    ∑ letter, f letter =
      f none + f (some .x) + f (some .y) + f (some .z) := by
  rw [show Finset.univ = {none, some .x, some .y, some .z} by decide]
  simp [add_assoc]

/-- Entrywise completeness of the four one-qubit Pauli matrices. -/
theorem local_completeness (i j k l : QubitIndex) :
    (∑ letter : Option Axis,
      localDualEntry letter i j * localMatrix letter k l) =
        if i = k ∧ j = l then 1 else 0 := by
  rw [sum_letters]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [localDualEntry, localMatrix, identity₂, pauliX, pauliY, pauliZ,
      Complex.I_mul_I]
  all_goals rw [mul_assoc, Complex.I_mul_I]
  all_goals norm_num

/-- The dual entries pair the four one-qubit Pauli matrices orthonormally. -/
theorem local_orthogonality (a b : Option Axis) :
    (∑ i : QubitIndex, ∑ j : QubitIndex,
      localDualEntry a i j * localMatrix b i j) =
        if a = b then 1 else 0 := by
  fin_cases a <;> fin_cases b <;>
    norm_num [localDualEntry, localMatrix, identity₂, pauliX, pauliY, pauliZ,
      Fin.sum_univ_succ, Complex.I_mul_I]
  all_goals simp [mul_assoc, Complex.I_mul_I]
  all_goals norm_num

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- The concrete register matrix represented by a Pauli word. -/
def initialPauliString (word : PauliWord Q) : Operator Q :=
  fun x y ↦ ∏ q, localMatrix (word q) (x q) (y q)

/-- Exact coefficient of a register operator in the initial Pauli-word basis. -/
def coefficient (A : Operator Q) (word : PauliWord Q) : ℂ :=
  ∑ x : Basis Q, ∑ y : Basis Q,
    (∏ q, localDualEntry (word q) (x q) (y q)) * A x y

/-- Pointwise pairing of two bit assignments as an assignment of bit pairs. -/
def piPairEquiv (Q : Type*) :
    (Q → QubitIndex × QubitIndex) ≃
      ((Q → QubitIndex) × (Q → QubitIndex)) where
  toFun z := (fun q ↦ (z q).1, fun q ↦ (z q).2)
  invFun xy := fun q ↦ (xy.1 q, xy.2 q)
  left_inv z := by ext q <;> rfl
  right_inv xy := by ext q <;> rfl

private theorem sum_word_factor (x y u v : Basis Q) :
    (∑ word : PauliWord Q,
      (∏ q, localDualEntry (word q) (u q) (v q)) *
        (∏ q, localMatrix (word q) (x q) (y q))) =
      if u = x ∧ v = y then 1 else 0 := by
  let f : Q → Option Axis → ℂ := fun q letter ↦
    localDualEntry letter (u q) (v q) * localMatrix letter (x q) (y q)
  change (∑ word : Q → Option Axis,
    (∏ q : Q, localDualEntry (word q) (u q) (v q)) *
      (∏ q : Q, localMatrix (word q) (x q) (y q))) = _
  calc
    _ = ∑ word : Q → Option Axis, ∏ q : Q, f q (word q) := by
      apply Finset.sum_congr rfl
      intro word _
      exact (Finset.prod_mul_distrib).symm
    _ = ∏ q : Q, ∑ letter : Option Axis, f q letter :=
      (Fintype.prod_sum f).symm
    _ = _ := by
      simp only [f, local_completeness]
      rw [Fintype.prod_boole]
      apply if_congr
      · constructor
        · intro h
          exact ⟨funext fun q ↦ (h q).1, funext fun q ↦ (h q).2⟩
        · rintro ⟨rfl, rfl⟩ q
          exact ⟨rfl, rfl⟩
      · rfl
      · rfl

private theorem triple_sum_rotate {A B C : Type*}
    [Fintype A] [Fintype B] [Fintype C] (f : A → B → C → ℂ) :
    (∑ a, ∑ b, ∑ c, f a b c) = ∑ b, ∑ c, ∑ a, f a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

/-- Every register operator has the explicit Pauli-word expansion given by `coefficient`. -/
theorem reconstruction (A : Operator Q) :
    (∑ word : PauliWord Q, coefficient A word • initialPauliString word) = A := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  change (∑ word : Q → Option Axis,
    (∑ u : Q → QubitIndex, ∑ v : Q → QubitIndex,
      (∏ q : Q, localDualEntry (word q) (u q) (v q)) * A u v) *
      (∏ q : Q, localMatrix (word q) (x q) (y q))) = A x y
  simp_rw [Finset.sum_mul]
  rw [triple_sum_rotate]
  simp_rw [show ∀ (word : Q → Option Axis) (u v : Q → QubitIndex),
      ((∏ q : Q, localDualEntry (word q) (u q) (v q)) * A u v) *
          (∏ q : Q, localMatrix (word q) (x q) (y q)) =
        A u v * ((∏ q : Q, localDualEntry (word q) (u q) (v q)) *
          (∏ q : Q, localMatrix (word q) (x q) (y q))) by
      intros; ring]
  simp_rw [← Finset.mul_sum]
  simp_rw [sum_word_factor]
  rw [Fintype.sum_eq_single x]
  · rw [Fintype.sum_eq_single y]
    · simp
    · intro v hv
      simp [hv]
  · intro u hu
    simp [hu]

/-- The coefficient of one Pauli string against another is a Kronecker delta. -/
theorem coefficient_initialPauliString (word test : PauliWord Q) :
    coefficient (initialPauliString word) test =
      if test = word then 1 else 0 := by
  let f : Q → (QubitIndex × QubitIndex) → ℂ := fun q ij ↦
    localDualEntry (test q) ij.1 ij.2 * localMatrix (word q) ij.1 ij.2
  unfold coefficient initialPauliString
  simp_rw [← Finset.prod_mul_distrib]
  change (∑ x : Q → QubitIndex, ∑ y : Q → QubitIndex,
    ∏ q : Q, f q (x q, y q)) = _
  calc
    _ = ∑ xy : (Q → QubitIndex) × (Q → QubitIndex),
        ∏ q : Q, f q (xy.1 q, xy.2 q) :=
      (Fintype.sum_prod_type (fun xy : (Q → QubitIndex) × (Q → QubitIndex) ↦
        ∏ q : Q, f q (xy.1 q, xy.2 q))).symm
    _ = ∑ z : Q → QubitIndex × QubitIndex, ∏ q : Q, f q (z q) := by
      exact Equiv.sum_comp (piPairEquiv Q).symm (fun z ↦ ∏ q : Q, f q (z q))
    _ = ∏ q : Q, ∑ ij : QubitIndex × QubitIndex, f q ij :=
      (Fintype.prod_sum f).symm
    _ = ∏ q : Q, if test q = word q then 1 else 0 := by
      apply Finset.prod_congr rfl
      intro q _
      rw [Fintype.sum_prod_type]
      exact local_orthogonality (test q) (word q)
    _ = _ := by
      rw [Fintype.prod_boole]
      apply if_congr
      · exact funext_iff.symm
      · rfl
      · rfl

/-- Coordinate extraction as a linear map. -/
def analysis : Operator Q →ₗ[ℂ] (PauliWord Q → ℂ) where
  toFun A := coefficient A
  map_add' A B := by
    funext word
    change coefficient (A + B) word = coefficient A word + coefficient B word
    simp only [coefficient, Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c A := by
    funext word
    change coefficient (c • A) word = c * coefficient A word
    simp only [coefficient, Matrix.smul_apply, smul_eq_mul]
    simp_rw [show ∀ (d a : ℂ), d * (c * a) = c * (d * a) by intros; ring]
    simp only [Finset.mul_sum]

/-- Synthesis from arbitrary Pauli-word coordinates. -/
def synthesis (c : PauliWord Q → ℂ) : Operator Q :=
  ∑ word, c word • initialPauliString word

theorem synthesis_analysis (A : Operator Q) : synthesis (analysis A) = A :=
  reconstruction A

theorem analysis_synthesis (c : PauliWord Q → ℂ) : analysis (synthesis c) = c := by
  funext test
  change analysis (∑ word, c word • initialPauliString word) test = c test
  rw [map_sum]
  simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change (∑ word, c word * coefficient (initialPauliString word) test) = c test
  simp_rw [coefficient_initialPauliString]
  rw [Fintype.sum_eq_single test]
  · simp
  · intro word hword
    rw [if_neg (Ne.symm hword)]
    simp

/-- The explicit coefficient/synthesis equivalence. -/
def analysisEquiv : Operator Q ≃ₗ[ℂ] (PauliWord Q → ℂ) :=
  LinearEquiv.mk analysis synthesis synthesis_analysis analysis_synthesis

/-- Pauli strings form a genuine basis of the full register operator space. -/
def basis : Module.Basis (PauliWord Q) ℂ (Operator Q) :=
  Module.Basis.ofEquivFun analysisEquiv

@[simp]
theorem basis_apply (word : PauliWord Q) : basis word = initialPauliString word := by
  apply analysisEquiv.injective
  funext test
  change (basis.equivFun (basis word)) test = coefficient (initialPauliString word) test
  rw [Module.Basis.equivFun_self, coefficient_initialPauliString]
  exact if_congr eq_comm rfl rfl

/-! ## Initial-descriptor bridge -/

/-- The word containing one Pauli letter at `q` and identities everywhere else. -/
def single (q : Q) (a : Axis) : PauliWord Q :=
  fun r ↦ if r = q then some a else none

private theorem initial_component_eq_embedQubit (q : Q) (a : Axis) :
    (Descriptor.initial q).component a = Register.embedQubit q (localMatrix (some a)) := by
  cases a <;> rfl

/-- A one-site Pauli word is exactly the corresponding initial descriptor component. -/
theorem initialPauliString_single (q : Q) (a : Axis) :
    initialPauliString (single q a) = (Descriptor.initial q).component a := by
  rw [initial_component_eq_embedQubit]
  ext x y
  rw [Register.embedQubit_apply_ite]
  unfold initialPauliString single
  rw [Fintype.prod_eq_mul_prod_compl q]
  simp only [if_pos, ne_eq]
  by_cases hxy : ∀ r, r ≠ q → x r = y r
  · rw [if_pos hxy]
    have hrest :
        (∏ r ∈ ({q} : Finset Q)ᶜ,
          localMatrix (if r = q then some a else none) (x r) (y r)) = 1 := by
      apply Finset.prod_eq_one
      intro r hr
      have hrq : r ≠ q := by simpa using hr
      simp [hrq, localMatrix, identity₂, Matrix.one_apply, hxy r hrq]
    rw [hrest, mul_one]
  · rw [if_neg hxy]
    have hzero :
        (∏ r ∈ ({q} : Finset Q)ᶜ,
          localMatrix (if r = q then some a else none) (x r) (y r)) = 0 := by
      push Not at hxy
      obtain ⟨r, hrq, hrxy⟩ := hxy
      apply Finset.prod_eq_zero (i := r)
      · simpa using hrq
      · simp [hrq, localMatrix, identity₂, hrxy]
    rw [hzero, mul_zero]

/-! ## Completeness after unitary Heisenberg evolution -/

/-- Unitary Heisenberg conjugation as a star-algebra automorphism. -/
def heisenbergAut (U : UnitaryOperator Q) : Operator Q ≃⋆ₐ[ℂ] Operator Q :=
  Unitary.conjStarAlgAut ℂ (Operator Q) (star U)

@[simp]
theorem heisenbergAut_apply (U : UnitaryOperator Q) (A : Operator Q) :
    heisenbergAut U A = Register.heisenberg U A := by
  simp [heisenbergAut, Unitary.conjStarAlgAut_apply, Register.heisenberg,
    Matrix.star_eq_conjTranspose]

@[simp]
theorem heisenbergAut_symm_apply (U : UnitaryOperator Q) (A : Operator Q) :
    (heisenbergAut U).symm A =
      Register.heisenberg (star (U : Operator Q)) A := by
  simp [heisenbergAut, Register.heisenberg,
    Matrix.star_eq_conjTranspose]

/-- A Pauli string evolved by the shared unitary Heisenberg automorphism. -/
def evolvedPauliString (U : UnitaryOperator Q) (word : PauliWord Q) : Operator Q :=
  heisenbergAut U (initialPauliString word)

@[simp]
theorem evolvedPauliString_eq_heisenberg (U : UnitaryOperator Q) (word : PauliWord Q) :
    evolvedPauliString U word = Register.heisenberg U (initialPauliString word) := by
  simp [evolvedPauliString]

/-- One-site evolved strings are exactly the components of the evolved descriptor family. -/
theorem evolvedPauliString_single (U : UnitaryOperator Q) (q : Q) (a : Axis) :
    evolvedPauliString U (single q a) =
      ((DescriptorFamily.evolve U (DescriptorFamily.initial Q) q).component a) := by
  rw [evolvedPauliString_eq_heisenberg, initialPauliString_single,
    DescriptorFamily.evolve_apply, Descriptor.evolve_component]
  rfl

/-- Coordinates in the evolved basis are initial coordinates after inverse conjugation. -/
def evolvedCoefficient (U : UnitaryOperator Q) (A : Operator Q) (word : PauliWord Q) : ℂ :=
  coefficient ((heisenbergAut U).symm A) word

/-- Unitary Heisenberg evolution preserves exact Pauli-word completeness. -/
theorem evolvedReconstruction (U : UnitaryOperator Q) (A : Operator Q) :
    (∑ word : PauliWord Q,
      evolvedCoefficient U A word • evolvedPauliString U word) = A := by
  change (∑ word : PauliWord Q,
    coefficient ((heisenbergAut U).symm A) word •
      heisenbergAut U (initialPauliString word)) = A
  calc
    _ = heisenbergAut U
        (∑ word : PauliWord Q,
          coefficient ((heisenbergAut U).symm A) word • initialPauliString word) := by
      rw [map_sum]
      simp
    _ = heisenbergAut U ((heisenbergAut U).symm A) := by
      rw [reconstruction]
    _ = A := (heisenbergAut U).apply_symm_apply A

/-- The evolved Pauli strings, bundled as a basis. -/
def evolvedBasis (U : UnitaryOperator Q) :
    Module.Basis (PauliWord Q) ℂ (Operator Q) :=
  basis.map (heisenbergAut U).toAlgEquiv.toLinearEquiv

@[simp]
theorem evolvedBasis_apply (U : UnitaryOperator Q) (word : PauliWord Q) :
    evolvedBasis U word = evolvedPauliString U word := by
  rw [evolvedBasis, Module.Basis.map_apply, basis_apply]
  rfl

end PauliWord
end
end Deutsch
