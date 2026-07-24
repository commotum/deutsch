import Deutsch.Information.Reduction
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Explicit finite-register purification

Every density operator on a finite named qubit register is realized as the reduction of an
explicit normalized pure state on two labelled copies of that register.  The construction
vectorizes the positive square root of the density matrix.  It therefore complements, rather
than weakens, the same-register purity obstruction in `Deutsch.Information.Qubit`.
-/

namespace Deutsch
namespace Information

open Foundations Register
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Matrix MatrixOrder

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Transport a density operator across an equivalence of computational-basis labels. -/
def Density.reindex {R : Type*} [Fintype R] [DecidableEq R]
    (rho : Density Q) (e : Basis Q ≃ Basis R) : Density R where
  op := Matrix.reindexAlgEquiv ℂ ℂ e rho.op
  positive := by
    apply (Matrix.posSemidef_submatrix_equiv e).1
    simpa [Matrix.reindexAlgEquiv] using rho.positive
  trace_one := by
    change (∑ i : Basis R, rho.op (e.symm i) (e.symm i)) = 1
    rw [Equiv.sum_comp e.symm (fun i : Basis Q ↦ rho.op i i)]
    exact rho.trace_one

@[simp]
theorem Density.reindex_op {R : Type*} [Fintype R] [DecidableEq R]
    (rho : Density Q) (e : Basis Q ≃ Basis R) :
    (rho.reindex e).op = Matrix.reindexAlgEquiv ℂ ℂ e rho.op :=
  rfl

@[simp]
theorem Density.reindex_symm_reindex {R : Type*} [Fintype R] [DecidableEq R]
    (rho : Density Q) (e : Basis Q ≃ Basis R) :
    (rho.reindex e).reindex e.symm = rho := by
  apply Density.ext
  simp [Density.reindex]

/-- Reindexing both a density and an observable preserves their trace expectation. -/
theorem densityExpectation_reindex {R : Type*} [Fintype R] [DecidableEq R]
    (rho : Density Q) (e : Basis Q ≃ Basis R) (A : Operator Q) :
    densityExpectation (rho.reindex e)
        (Matrix.reindexAlgEquiv ℂ ℂ e A) =
      densityExpectation rho A := by
  simp only [densityExpectation, Density.reindex_op, ← map_mul]
  change (∑ i : Basis R, (rho.op * A) (e.symm i) (e.symm i)) =
    ∑ i : Basis Q, (rho.op * A) i i
  exact Equiv.sum_comp e.symm (fun i : Basis Q ↦ (rho.op * A) i i)

/-- Two labelled copies of a qubit-name type. -/
abbrev PurificationRegister (Q : Type*) := Sum Q Q

/-- Placement of the represented system in the first copy of the enlarged register. -/
def purificationOriginalPlacement (Q : Type*) : Q ↪ PurificationRegister Q :=
  ⟨Sum.inl, Sum.inl_injective⟩

/-- Placement of the purifying system in the second copy of the enlarged register. -/
def purificationCopyPlacement (Q : Type*) : Q ↪ PurificationRegister Q :=
  ⟨Sum.inr, Sum.inr_injective⟩

/-- The selected original-copy qubits in the enlarged register. -/
abbrev purificationOriginalQubits (Q : Type*) [Fintype Q] [DecidableEq Q] :
    Finset (PurificationRegister Q) :=
  placementFinset (purificationOriginalPlacement Q)

/-- A doubled-register basis assignment is a pair of basis assignments, one per copy. -/
def purificationBasisEquiv (Q : Type*) :
    Basis (PurificationRegister Q) ≃ Basis Q × Basis Q where
  toFun bits :=
    (fun q ↦ bits (Sum.inl q), fun q ↦ bits (Sum.inr q))
  invFun bits := Sum.elim bits.1 bits.2
  left_inv bits := by
    funext q
    cases q <;> rfl
  right_inv bits := rfl

theorem purificationCopy_not_mem_originalQubits (q : Q) :
    Sum.inr q ∉ purificationOriginalQubits Q := by
  rw [purificationOriginalQubits,
    mem_placementFinset_iff (purificationOriginalPlacement Q)]
  rintro ⟨q', h⟩
  change Sum.inl q' = Sum.inr q at h
  exact (Sum.inl_ne_inr : (Sum.inl q' : Sum Q Q) ≠ Sum.inr q) h

/-- The second copy is exactly the complement of the selected first copy. -/
def purificationCopyComplementEquiv (Q : Type*) [Fintype Q] [DecidableEq Q] :
    Q ≃ {q : PurificationRegister Q // q ∉ purificationOriginalQubits Q} :=
  Equiv.ofBijective
    (fun q ↦ ⟨Sum.inr q, purificationCopy_not_mem_originalQubits q⟩)
    ⟨by
      intro q q' h
      exact Sum.inr_injective (congrArg Subtype.val h),
     by
      intro q
      cases hq : q.1 with
      | inl x =>
          exfalso
          apply q.2
          rw [mem_placementFinset_iff (purificationOriginalPlacement Q)]
          exact ⟨x, hq.symm⟩
      | inr x =>
          refine ⟨x, ?_⟩
          apply Subtype.ext
          exact hq.symm⟩

/-- Basis labels on the purifying complement, retaining the second copy's original labels. -/
def purificationCopyBasisEquiv (Q : Type*) [Fintype Q] [DecidableEq Q] :
    Basis Q ≃ ComplementBasis (purificationOriginalQubits Q) :=
  Equiv.arrowCongr (purificationCopyComplementEquiv Q) (Equiv.refl QubitIndex)

/--
The supplied density with its qubit labels transported to the selected first-copy subsystem.
-/
def purificationOriginalDensity (rho : Density Q) :
    Density {q : PurificationRegister Q // q ∈ purificationOriginalQubits Q} :=
  rho.reindex (alongBasisEquiv (purificationOriginalPlacement Q))

@[simp]
theorem purificationOriginalDensity_op (rho : Density Q) :
    (purificationOriginalDensity rho).op =
      Matrix.reindexAlgEquiv ℂ ℂ
        (alongBasisEquiv (purificationOriginalPlacement Q)) rho.op :=
  rfl

/-- The positive square root used in the canonical purification. -/
def densitySquareRoot (rho : Density Q) : Operator Q :=
  CFC.sqrt rho.op

theorem densitySquareRoot_posSemidef (rho : Density Q) :
    (densitySquareRoot rho).PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg rho.op)

theorem densitySquareRoot_isHermitian (rho : Density Q) :
    (densitySquareRoot rho).IsHermitian :=
  (densitySquareRoot_posSemidef rho).isHermitian

theorem densitySquareRoot_mul_self (rho : Density Q) :
    densitySquareRoot rho * densitySquareRoot rho = rho.op := by
  exact CFC.sqrt_mul_sqrt_self rho.op rho.positive.nonneg

/-- Coordinate vector obtained by vectorizing the positive square root of `rho`. -/
def purificationCoordinates (rho : Density Q) :
    Basis (PurificationRegister Q) → ℂ :=
  fun bits ↦
    densitySquareRoot rho
      (purificationBasisEquiv Q bits).1
      (purificationBasisEquiv Q bits).2

theorem purificationCoordinates_dot_star (rho : Density Q) :
    purificationCoordinates rho ⬝ᵥ star (purificationCoordinates rho) = 1 := by
  classical
  rw [show purificationCoordinates rho ⬝ᵥ star (purificationCoordinates rho) =
      ∑ bits : Basis (PurificationRegister Q),
        purificationCoordinates rho bits * star (purificationCoordinates rho bits) by
      rfl]
  change (∑ bits : Basis (PurificationRegister Q),
      densitySquareRoot rho (purificationBasisEquiv Q bits).1
          (purificationBasisEquiv Q bits).2 *
        star (densitySquareRoot rho (purificationBasisEquiv Q bits).1
          (purificationBasisEquiv Q bits).2)) = 1
  rw [Equiv.sum_comp (purificationBasisEquiv Q)
    (fun bits : Basis Q × Basis Q ↦
      densitySquareRoot rho bits.1 bits.2 *
        star (densitySquareRoot rho bits.1 bits.2))]
  rw [Fintype.sum_prod_type]
  have hsqrt :
      (densitySquareRoot rho)ᴴ = densitySquareRoot rho :=
    (densitySquareRoot_isHermitian rho).eq
  calc
    (∑ i : Basis Q, ∑ j : Basis Q,
        densitySquareRoot rho i j * star (densitySquareRoot rho i j)) =
        Matrix.trace (densitySquareRoot rho * (densitySquareRoot rho)ᴴ) := by
          simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply,
            Matrix.conjTranspose_apply]
    _ = Matrix.trace (densitySquareRoot rho * densitySquareRoot rho) := by
          rw [hsqrt]
    _ = Matrix.trace rho.op := by rw [densitySquareRoot_mul_self]
    _ = 1 := rho.trace_one

/-- The canonical purification ket of a finite density operator. -/
def purificationKet (rho : Density Q) : Ket (PurificationRegister Q) :=
  WithLp.toLp 2 (purificationCoordinates rho)

theorem purificationKet_norm (rho : Density Q) :
    ‖purificationKet rho‖ = 1 := by
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ)]
  have hinner :
      ⟪purificationKet rho, purificationKet rho⟫_ℂ = 1 := by
    simp only [purificationKet, PiLp.inner_apply, RCLike.inner_apply]
    change purificationCoordinates rho ⬝ᵥ
      star (purificationCoordinates rho) = 1
    exact purificationCoordinates_dot_star rho
  rw [hinner]
  norm_num

/-- The explicit normalized pure state on the doubled register. -/
def purificationPureState (rho : Density Q) : PureState (PurificationRegister Q) where
  ket := purificationKet rho
  norm_eq_one := purificationKet_norm rho

private theorem purification_split_original
    (i : SubsystemBasis (purificationOriginalQubits Q))
    (k : ComplementBasis (purificationOriginalQubits Q)) :
    (purificationBasisEquiv Q
      ((splitBasis (purificationOriginalQubits Q)).symm (i, k))).1 =
      (alongBasisEquiv (purificationOriginalPlacement Q)).symm i := by
  funext q
  have hin : Sum.inl q ∈ purificationOriginalQubits Q := by
    rw [mem_placementFinset_iff (purificationOriginalPlacement Q)]
    exact ⟨q, rfl⟩
  dsimp [purificationBasisEquiv, splitBasis]
  rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos hin]
  simp only [alongBasisEquiv]
  change i ⟨Sum.inl q, hin⟩ =
    i ((placementEquiv (purificationOriginalPlacement Q)) q)
  congr 1

private theorem purification_split_copy
    (i : SubsystemBasis (purificationOriginalQubits Q))
    (k : ComplementBasis (purificationOriginalQubits Q)) :
    (purificationBasisEquiv Q
      ((splitBasis (purificationOriginalQubits Q)).symm (i, k))).2 =
      (purificationCopyBasisEquiv Q).symm k := by
  funext q
  have hnot : Sum.inr q ∉ purificationOriginalQubits Q :=
    purificationCopy_not_mem_originalQubits q
  dsimp [purificationBasisEquiv, splitBasis]
  rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_neg hnot]
  simp only [purificationCopyBasisEquiv]
  change k ⟨Sum.inr q, hnot⟩ =
    k ((purificationCopyComplementEquiv Q) q)
  congr 1

/--
Tracing out the explicit second copy returns exactly the supplied density, with the retained
qubits canonically relabelled by the first-copy placement.
-/
theorem purification_reduce_original (rho : Density Q) :
    (pureDensity (purificationPureState rho)).reduce
        (purificationOriginalQubits Q) =
      purificationOriginalDensity rho := by
  apply Density.ext
  ext i j
  change (∑ k : ComplementBasis (purificationOriginalQubits Q),
      purificationCoordinates rho
          ((splitBasis (purificationOriginalQubits Q)).symm (i, k)) *
        star (purificationCoordinates rho
          ((splitBasis (purificationOriginalQubits Q)).symm (j, k)))) =
    rho.op
      ((alongBasisEquiv (purificationOriginalPlacement Q)).symm i)
      ((alongBasisEquiv (purificationOriginalPlacement Q)).symm j)
  simp_rw [purificationCoordinates, purification_split_original,
    purification_split_copy]
  rw [Equiv.sum_comp (purificationCopyBasisEquiv Q).symm
    (fun k : Basis Q ↦
      densitySquareRoot rho
          ((alongBasisEquiv (purificationOriginalPlacement Q)).symm i) k *
        star (densitySquareRoot rho
          ((alongBasisEquiv (purificationOriginalPlacement Q)).symm j) k))]
  change (densitySquareRoot rho * (densitySquareRoot rho)ᴴ)
      ((alongBasisEquiv (purificationOriginalPlacement Q)).symm i)
      ((alongBasisEquiv (purificationOriginalPlacement Q)).symm j) =
    rho.op
      ((alongBasisEquiv (purificationOriginalPlacement Q)).symm i)
      ((alongBasisEquiv (purificationOriginalPlacement Q)).symm j)
  have hsqrt :
      (densitySquareRoot rho)ᴴ = densitySquareRoot rho :=
    (densitySquareRoot_isHermitian rho).eq
  rw [hsqrt, densitySquareRoot_mul_self]

/-- Reduce the purification and transport the retained first-copy labels back to `Q`. -/
def purificationReducedDensity (rho : Density Q) : Density Q :=
  ((pureDensity (purificationPureState rho)).reduce
      (purificationOriginalQubits Q)).reindex
    (alongBasisEquiv (purificationOriginalPlacement Q)).symm

/-- On the original labels, reduction of the explicit purification is literally `rho`. -/
theorem purificationReducedDensity_eq (rho : Density Q) :
    purificationReducedDensity rho = rho := by
  rw [purificationReducedDensity, purification_reduce_original]
  exact Density.reindex_symm_reindex rho
    (alongBasisEquiv (purificationOriginalPlacement Q))

/--
Every observable on the represented system has the same prediction in `rho` as its ordered
first-copy embedding has in the explicit enlarged pure state.
-/
theorem purification_embedded_expectation (rho : Density Q) (A : Operator Q) :
    Register.expectation (purificationPureState rho).ket
        (embedAlong (purificationOriginalPlacement Q) A) =
      densityExpectation rho A := by
  let global : Density (PurificationRegister Q) :=
    pureDensity (purificationPureState rho)
  let localA : SubsystemOperator (purificationOriginalQubits Q) :=
    Matrix.reindexAlgEquiv ℂ ℂ
      (alongBasisEquiv (purificationOriginalPlacement Q)) A
  calc
    Register.expectation (purificationPureState rho).ket
        (embedAlong (purificationOriginalPlacement Q) A) =
        densityExpectation global
          (embedAlong (purificationOriginalPlacement Q) A) := by
            exact (densityExpectation_pureDensity
              (purificationPureState rho)
              (embedAlong (purificationOriginalPlacement Q) A)).symm
    _ = densityExpectation (global.reduce (purificationOriginalQubits Q))
          localA := by
            exact (partialTrace_trace_mul
              (purificationOriginalQubits Q) global.op localA).symm
    _ = densityExpectation (purificationOriginalDensity rho) localA := by
          rw [show global.reduce (purificationOriginalQubits Q) =
              purificationOriginalDensity rho by
            exact purification_reduce_original rho]
    _ = densityExpectation rho A :=
      densityExpectation_reindex rho
        (alongBasisEquiv (purificationOriginalPlacement Q)) A

/-- The enlarged purification can be prepared unitarily from the enlarged all-zero reference. -/
theorem exists_unitary_preparation_purification (rho : Density Q) :
    ∃ U : Operator (PurificationRegister Q),
      U ∈ Matrix.unitaryGroup (Basis (PurificationRegister Q)) ℂ ∧
      act U (referenceKet (PurificationRegister Q)) =
        (purificationPureState rho).ket :=
  (purificationPureState rho).exists_unitary_preparation

/--
Every finite density has one enlarged-register preparation unitary for which all embedded
original-system predictions are exactly fixed-reference Heisenberg predictions.
-/
theorem exists_purification_fixed_reference_representation (rho : Density Q) :
    ∃ U : Operator (PurificationRegister Q),
      U ∈ Matrix.unitaryGroup (Basis (PurificationRegister Q)) ℂ ∧
      act U (referenceKet (PurificationRegister Q)) =
        (purificationPureState rho).ket ∧
      ∀ A : Operator Q,
        densityExpectation rho A =
          Register.expectation (referenceKet (PurificationRegister Q))
            (heisenberg U (embedAlong (purificationOriginalPlacement Q) A)) := by
  obtain ⟨U, hU, hprep⟩ := exists_unitary_preparation_purification rho
  refine ⟨U, hU, hprep, ?_⟩
  intro A
  calc
    densityExpectation rho A =
        Register.expectation (purificationPureState rho).ket
          (embedAlong (purificationOriginalPlacement Q) A) :=
      (purification_embedded_expectation rho A).symm
    _ = Register.expectation
          (act U (referenceKet (PurificationRegister Q)))
          (embedAlong (purificationOriginalPlacement Q) A) := by
            rw [hprep]
    _ = Register.expectation (referenceKet (PurificationRegister Q))
          (heisenberg U (embedAlong (purificationOriginalPlacement Q) A)) :=
      fixed_reference_prediction U
        (embedAlong (purificationOriginalPlacement Q) A)

end
end Information
end Deutsch
