import Deutsch.Register.Embedding
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Pauli operators and paper-bit projectors on named register coordinates

The local matrices come from `Deutsch.Foundations.Concrete`.  This module proves their algebra and
lifts it through the exact single-coordinate embedding.  In the paper's convention, raw matrix
index `0` is logical bit `1`, so `(I + Z) / 2` is the bit-`1` projector.
-/

namespace Deutsch
namespace Register

open Foundations
open scoped Matrix

noncomputable section

/-! ## One-qubit Pauli algebra -/

theorem pauliX_mul_pauliX : pauliX * pauliX = identity₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, identity₂, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliY_mul_pauliY : pauliY * pauliY = identity₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliY, identity₂, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliZ_mul_pauliZ : pauliZ * pauliZ = identity₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliZ, identity₂, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliX_mul_pauliY : pauliX * pauliY = Complex.I • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliY_mul_pauliZ : pauliY * pauliZ = Complex.I • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliZ_mul_pauliX : pauliZ * pauliX = Complex.I • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliY_mul_pauliX : pauliY * pauliX = -Complex.I • pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliZ_mul_pauliY : pauliZ * pauliY = -Complex.I • pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliX_mul_pauliZ : pauliX * pauliZ = -Complex.I • pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliY, pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliX_isHermitian : pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.IsHermitian, pauliX, Matrix.conjTranspose_apply]

theorem pauliY_isHermitian : pauliY.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.IsHermitian, pauliY, Matrix.conjTranspose_apply]

theorem pauliZ_isHermitian : pauliZ.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.IsHermitian, pauliZ, Matrix.conjTranspose_apply]

theorem pauliX_unitary : pauliX ∈ Matrix.unitaryGroup QubitIndex ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change pauliXᴴ * pauliX = 1
  rw [pauliX_isHermitian, pauliX_mul_pauliX, identity₂]

theorem pauliY_unitary : pauliY ∈ Matrix.unitaryGroup QubitIndex ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change pauliYᴴ * pauliY = 1
  rw [pauliY_isHermitian, pauliY_mul_pauliY, identity₂]

theorem pauliZ_unitary : pauliZ ∈ Matrix.unitaryGroup QubitIndex ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change pauliZᴴ * pauliZ = 1
  rw [pauliZ_isHermitian, pauliZ_mul_pauliZ, identity₂]

theorem pauliX_anticommutes_pauliY : pauliX * pauliY + pauliY * pauliX = 0 := by
  rw [pauliX_mul_pauliY, pauliY_mul_pauliX]
  simp

theorem pauliY_anticommutes_pauliZ : pauliY * pauliZ + pauliZ * pauliY = 0 := by
  rw [pauliY_mul_pauliZ, pauliZ_mul_pauliY]
  simp

theorem pauliZ_anticommutes_pauliX : pauliZ * pauliX + pauliX * pauliZ = 0 := by
  rw [pauliZ_mul_pauliX, pauliX_mul_pauliZ]
  simp

/-! ## Paper-bit projectors -/

theorem bitOneProjector_explicit : bitOneProjector = !![1, 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bitOneProjector, identity₂, pauliZ]

theorem bitZeroProjector_explicit : bitZeroProjector = !![0, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bitZeroProjector, identity₂, pauliZ]

theorem bitOneProjector_isHermitian : bitOneProjector.IsHermitian := by
  rw [bitOneProjector_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.IsHermitian, Matrix.conjTranspose_apply]

theorem bitZeroProjector_isHermitian : bitZeroProjector.IsHermitian := by
  rw [bitZeroProjector_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.IsHermitian, Matrix.conjTranspose_apply]

@[simp]
theorem bitOneProjector_mul_self :
    bitOneProjector * bitOneProjector = bitOneProjector := by
  rw [bitOneProjector_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

@[simp]
theorem bitZeroProjector_mul_self :
    bitZeroProjector * bitZeroProjector = bitZeroProjector := by
  rw [bitZeroProjector_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

theorem bitOneProjector_add_bitZeroProjector :
    bitOneProjector + bitZeroProjector = identity₂ := by
  rw [bitOneProjector_explicit, bitZeroProjector_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [identity₂, Matrix.one_apply]

theorem bitZeroProjector_eq_one_sub_bitOneProjector :
    bitZeroProjector = identity₂ - bitOneProjector := by
  rw [bitOneProjector_explicit, bitZeroProjector_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [identity₂, Matrix.one_apply]

@[simp]
theorem bitOneProjector_mul_bitZeroProjector :
    bitOneProjector * bitZeroProjector = 0 := by
  rw [bitOneProjector_explicit, bitZeroProjector_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

@[simp]
theorem bitZeroProjector_mul_bitOneProjector :
    bitZeroProjector * bitOneProjector = 0 := by
  rw [bitOneProjector_explicit, bitZeroProjector_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliZ_mul_bitOneProjector : pauliZ * bitOneProjector = bitOneProjector := by
  rw [bitOneProjector_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

theorem pauliZ_mul_bitZeroProjector : pauliZ * bitZeroProjector = -bitZeroProjector := by
  rw [bitZeroProjector_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pauliZ, Matrix.mul_apply, Fin.sum_univ_succ]

/-! ## Embedded coordinate observables -/

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Embedded Pauli `X` on coordinate `q`. -/
def xAt (q : Q) : Operator Q := embedQubit q pauliX

/-- Embedded Pauli `Y` on coordinate `q`. -/
def yAt (q : Q) : Operator Q := embedQubit q pauliY

/-- Embedded Pauli `Z` on coordinate `q`. -/
def zAt (q : Q) : Operator Q := embedQubit q pauliZ

/-- Projector onto logical paper bit `1` (`Z = +1`) at coordinate `q`. -/
def paperBitOneProjectorAt (q : Q) : Operator Q :=
  embedQubit q bitOneProjector

/-- Projector onto logical paper bit `0` (`Z = -1`) at coordinate `q`. -/
def paperBitZeroProjectorAt (q : Q) : Operator Q :=
  embedQubit q bitZeroProjector

/-- Entry formula for a product of operators embedded at two distinct coordinates. -/
theorem embedQubit_mul_embedQubit_apply_of_ne {q r : Q} (hqr : q ≠ r)
    (A B : QubitMatrix) (x y : Basis Q) :
    (embedQubit q A * embedQubit r B) x y =
      if ∀ j, j ≠ q → j ≠ r → x j = y j then
        A (x q) (y q) * B (x r) (y r)
      else 0 := by
  rw [Matrix.mul_apply]
  by_cases hxy : ∀ j, j ≠ q → j ≠ r → x j = y j
  · rw [if_pos hxy, Finset.sum_eq_single (Function.update x q (y q))]
    · have hqUpdate :
          ∀ j, j ≠ q → x j = Function.update x q (y q) j := by
        intro j hj
        simp [Function.update_of_ne hj]
      have hrUpdate :
          ∀ j, j ≠ r → Function.update x q (y q) j = y j := by
        intro j hjr
        by_cases hjq : j = q
        · subst j
          simp
        · rw [Function.update_of_ne hjq]
          exact hxy j hjq hjr
      rw [embedQubit_apply_ite, embedQubit_apply_ite,
        if_pos hqUpdate, if_pos hrUpdate]
      simp [Function.update_self, Function.update_of_ne hqr.symm]
    · intro z _ hzne
      rw [embedQubit_apply_ite, embedQubit_apply_ite]
      by_cases hqz : ∀ j, j ≠ q → x j = z j
      · by_cases hzr : ∀ j, j ≠ r → z j = y j
        · exfalso
          apply hzne
          funext j
          by_cases hjq : j = q
          · subst j
            simpa using hzr q hqr
          · rw [Function.update_of_ne hjq]
            exact (hqz j hjq).symm
        · rw [if_neg hzr]
          simp
      · rw [if_neg hqz]
        simp
    · simp
  · rw [if_neg hxy]
    apply Finset.sum_eq_zero
    intro z _
    rw [embedQubit_apply_ite, embedQubit_apply_ite]
    by_cases hqz : ∀ j, j ≠ q → x j = z j
    · by_cases hzr : ∀ j, j ≠ r → z j = y j
      · exfalso
        apply hxy
        intro j hjq hjr
        exact (hqz j hjq).trans (hzr j hjr)
      · rw [if_neg hzr]
        simp
    · rw [if_neg hqz]
      simp

/-- Arbitrary one-qubit operators on distinct named coordinates commute. -/
theorem embedQubit_commute_of_ne {q r : Q} (hqr : q ≠ r) (A B : QubitMatrix) :
    embedQubit q A * embedQubit r B = embedQubit r B * embedQubit q A := by
  ext x y
  rw [embedQubit_mul_embedQubit_apply_of_ne hqr A B x y,
    embedQubit_mul_embedQubit_apply_of_ne hqr.symm B A x y]
  by_cases hxy : ∀ j, j ≠ q → j ≠ r → x j = y j
  · rw [if_pos hxy, if_pos (fun j hjr hjq ↦ hxy j hjq hjr)]
    exact mul_comm _ _
  · rw [if_neg hxy, if_neg]
    intro hreverse
    exact hxy fun j hjq hjr ↦ hreverse j hjr hjq

theorem xAt_mul_xAt (q : Q) : xAt q * xAt q = 1 := by
  rw [xAt, ← embedQubit_mul, pauliX_mul_pauliX, identity₂, embedQubit_one]

theorem yAt_mul_yAt (q : Q) : yAt q * yAt q = 1 := by
  rw [yAt, ← embedQubit_mul, pauliY_mul_pauliY, identity₂, embedQubit_one]

theorem zAt_mul_zAt (q : Q) : zAt q * zAt q = 1 := by
  rw [zAt, ← embedQubit_mul, pauliZ_mul_pauliZ, identity₂, embedQubit_one]

theorem xAt_mul_yAt (q : Q) : xAt q * yAt q = Complex.I • zAt q := by
  rw [xAt, yAt, zAt, ← embedQubit_mul, pauliX_mul_pauliY,
    embedQubit_smul]

theorem yAt_mul_zAt (q : Q) : yAt q * zAt q = Complex.I • xAt q := by
  rw [yAt, zAt, xAt, ← embedQubit_mul, pauliY_mul_pauliZ,
    embedQubit_smul]

theorem zAt_mul_xAt (q : Q) : zAt q * xAt q = Complex.I • yAt q := by
  rw [zAt, xAt, yAt, ← embedQubit_mul, pauliZ_mul_pauliX,
    embedQubit_smul]

theorem yAt_mul_xAt (q : Q) : yAt q * xAt q = -Complex.I • zAt q := by
  rw [yAt, xAt, zAt, ← embedQubit_mul, pauliY_mul_pauliX,
    embedQubit_smul]

theorem zAt_mul_yAt (q : Q) : zAt q * yAt q = -Complex.I • xAt q := by
  rw [zAt, yAt, xAt, ← embedQubit_mul, pauliZ_mul_pauliY,
    embedQubit_smul]

theorem xAt_mul_zAt (q : Q) : xAt q * zAt q = -Complex.I • yAt q := by
  rw [xAt, zAt, yAt, ← embedQubit_mul, pauliX_mul_pauliZ,
    embedQubit_smul]

theorem xAt_anticommutes_yAt (q : Q) : xAt q * yAt q + yAt q * xAt q = 0 := by
  rw [xAt_mul_yAt, yAt_mul_xAt]
  simp

theorem yAt_anticommutes_zAt (q : Q) : yAt q * zAt q + zAt q * yAt q = 0 := by
  rw [yAt_mul_zAt, zAt_mul_yAt]
  simp

theorem zAt_anticommutes_xAt (q : Q) : zAt q * xAt q + xAt q * zAt q = 0 := by
  rw [zAt_mul_xAt, xAt_mul_zAt]
  simp

theorem xAt_isHermitian (q : Q) : (xAt q).IsHermitian :=
  embedQubit_isHermitian q pauliX pauliX_isHermitian

theorem yAt_isHermitian (q : Q) : (yAt q).IsHermitian :=
  embedQubit_isHermitian q pauliY pauliY_isHermitian

theorem zAt_isHermitian (q : Q) : (zAt q).IsHermitian :=
  embedQubit_isHermitian q pauliZ pauliZ_isHermitian

theorem xAt_unitary (q : Q) : xAt q ∈ Matrix.unitaryGroup (Basis Q) ℂ :=
  embedQubit_unitary q pauliX pauliX_unitary

theorem yAt_unitary (q : Q) : yAt q ∈ Matrix.unitaryGroup (Basis Q) ℂ :=
  embedQubit_unitary q pauliY pauliY_unitary

theorem zAt_unitary (q : Q) : zAt q ∈ Matrix.unitaryGroup (Basis Q) ℂ :=
  embedQubit_unitary q pauliZ pauliZ_unitary

theorem paperBitOneProjectorAt_isHermitian (q : Q) :
    (paperBitOneProjectorAt q).IsHermitian :=
  embedQubit_isHermitian q bitOneProjector bitOneProjector_isHermitian

theorem paperBitZeroProjectorAt_isHermitian (q : Q) :
    (paperBitZeroProjectorAt q).IsHermitian :=
  embedQubit_isHermitian q bitZeroProjector bitZeroProjector_isHermitian

@[simp]
theorem paperBitOneProjectorAt_mul_self (q : Q) :
    paperBitOneProjectorAt q * paperBitOneProjectorAt q =
      paperBitOneProjectorAt q := by
  rw [paperBitOneProjectorAt, ← embedQubit_mul, bitOneProjector_mul_self]

@[simp]
theorem paperBitZeroProjectorAt_mul_self (q : Q) :
    paperBitZeroProjectorAt q * paperBitZeroProjectorAt q =
      paperBitZeroProjectorAt q := by
  rw [paperBitZeroProjectorAt, ← embedQubit_mul, bitZeroProjector_mul_self]

/-- Register form of Equation (4), with logical paper bit `1` in the `Z = +1` sector. -/
theorem paperBitOneProjectorAt_eq (q : Q) :
    paperBitOneProjectorAt q = ((2 : ℂ)⁻¹) • (1 + zAt q) := by
  rw [paperBitOneProjectorAt, bitOneProjector, embedQubit_smul,
    embedQubit_add, identity₂, embedQubit_one, zAt]

/-- The complementary paper-bit projector is the `Z = -1` sector. -/
theorem paperBitZeroProjectorAt_eq (q : Q) :
    paperBitZeroProjectorAt q = ((2 : ℂ)⁻¹) • (1 - zAt q) := by
  rw [paperBitZeroProjectorAt, bitZeroProjector, embedQubit_smul,
    embedQubit_sub, identity₂, embedQubit_one, zAt]

theorem paperBitProjectorAt_sum (q : Q) :
    paperBitOneProjectorAt q + paperBitZeroProjectorAt q = 1 := by
  rw [paperBitOneProjectorAt, paperBitZeroProjectorAt,
    ← embedQubit_add, bitOneProjector_add_bitZeroProjector, identity₂,
    embedQubit_one]

theorem paperBitZeroProjectorAt_eq_one_sub_paperBitOneProjectorAt (q : Q) :
    paperBitZeroProjectorAt q = 1 - paperBitOneProjectorAt q := by
  rw [paperBitZeroProjectorAt, bitZeroProjector_eq_one_sub_bitOneProjector,
    embedQubit_sub, identity₂, embedQubit_one, paperBitOneProjectorAt]

@[simp]
theorem paperBitOneProjectorAt_mul_paperBitZeroProjectorAt (q : Q) :
    paperBitOneProjectorAt q * paperBitZeroProjectorAt q = 0 := by
  rw [paperBitOneProjectorAt, paperBitZeroProjectorAt,
    ← embedQubit_mul, bitOneProjector_mul_bitZeroProjector]
  exact map_zero (embedSubsystemAlgHom ({q} : Finset Q))

@[simp]
theorem paperBitZeroProjectorAt_mul_paperBitOneProjectorAt (q : Q) :
    paperBitZeroProjectorAt q * paperBitOneProjectorAt q = 0 := by
  rw [paperBitZeroProjectorAt, paperBitOneProjectorAt,
    ← embedQubit_mul, bitZeroProjector_mul_bitOneProjector]
  exact map_zero (embedSubsystemAlgHom ({q} : Finset Q))

theorem zAt_mul_paperBitOneProjectorAt (q : Q) :
    zAt q * paperBitOneProjectorAt q = paperBitOneProjectorAt q := by
  rw [zAt, paperBitOneProjectorAt, ← embedQubit_mul,
    pauliZ_mul_bitOneProjector]

theorem zAt_mul_paperBitZeroProjectorAt (q : Q) :
    zAt q * paperBitZeroProjectorAt q = -paperBitZeroProjectorAt q := by
  rw [zAt, paperBitZeroProjectorAt, ← embedQubit_mul,
    pauliZ_mul_bitZeroProjector]
  simpa only [neg_smul, one_smul] using embedQubit_smul q (-1) bitZeroProjector

theorem xAt_isSupportedOn (q : Q) : IsSupportedOn {q} (xAt q) := by
  exact embedSubsystem_isSupportedOn {q}
    (Matrix.reindexRingEquiv ℂ (singletonBasisEquiv q) pauliX)

theorem yAt_isSupportedOn (q : Q) : IsSupportedOn {q} (yAt q) := by
  exact embedSubsystem_isSupportedOn {q}
    (Matrix.reindexRingEquiv ℂ (singletonBasisEquiv q) pauliY)

theorem zAt_isSupportedOn (q : Q) : IsSupportedOn {q} (zAt q) := by
  exact embedSubsystem_isSupportedOn {q}
    (Matrix.reindexRingEquiv ℂ (singletonBasisEquiv q) pauliZ)

end
end Register
end Deutsch
