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

private theorem purificationReindex_posSemidef
    (rho : Density Q) :
    (Matrix.reindexAlgEquiv ℂ ℂ
      (alongBasisEquiv (purificationOriginalPlacement Q)) rho.op).PosSemidef := by
  apply (Matrix.posSemidef_submatrix_equiv
    (alongBasisEquiv (purificationOriginalPlacement Q))).1
  simpa [Matrix.reindexAlgEquiv] using rho.positive

/--
The supplied density with its qubit labels transported to the selected first-copy subsystem.
-/
def purificationOriginalDensity (rho : Density Q) :
    Density {q : PurificationRegister Q // q ∈ purificationOriginalQubits Q} where
  op := Matrix.reindexAlgEquiv ℂ ℂ
    (alongBasisEquiv (purificationOriginalPlacement Q)) rho.op
  positive := purificationReindex_posSemidef rho
  trace_one := by
    change (∑ i : SubsystemBasis (purificationOriginalQubits Q),
      rho.op
        ((alongBasisEquiv (purificationOriginalPlacement Q)).symm i)
        ((alongBasisEquiv (purificationOriginalPlacement Q)).symm i)) = 1
    rw [Equiv.sum_comp
      (alongBasisEquiv (purificationOriginalPlacement Q)).symm
      (fun i : Basis Q ↦ rho.op i i)]
    exact rho.trace_one

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

end
end Information
end Deutsch
