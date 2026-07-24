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
def purificationOriginalQubits (Q : Type*) [Fintype Q] [DecidableEq Q] :
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

end
end Information
end Deutsch
