import Deutsch.Descriptor.Basic
import Deutsch.Register.Pauli
import Deutsch.Register.State
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Paper-convention controlled NOT on named registers

The local coordinate order is `(target, control)`. The paper's logical bit `1` is raw matrix
index `0`, so the target is toggled exactly when the control coordinate is raw `0`. The arbitrary
register gate is placed along an injection from `Fin 2`, keeping target/control roles in the type.
-/

namespace Deutsch
namespace Gates

open Foundations Register
open scoped Matrix Kronecker

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Raw matrix-index flip. Paper logical `1` is raw index `0`. -/
def flipRaw : QubitIndex → QubitIndex := ![1, 0]

@[simp] theorem flipRaw_zero : flipRaw 0 = 1 := rfl

@[simp] theorem flipRaw_one : flipRaw 1 = 0 := rfl

/-- Local two-qubit CNOT reindexed from `(target, control)` pairs to `Fin 2` assignments. -/
def cnotLocal : Operator (Fin 2) :=
  Matrix.reindexRingEquiv Complex twoQubitBasisEquiv.symm
    cnotTargetLeftControlRight

/-- Ordered placement whose local coordinate `0` is target and `1` is control. -/
def targetControlPlacement (target control : Q) (h : target ≠ control) : Fin 2 ↪ Q where
  toFun i := ![target, control] i
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

omit [Fintype Q] [DecidableEq Q] in
@[simp] theorem targetControlPlacement_zero (target control : Q) (h : target ≠ control) :
    targetControlPlacement target control h 0 = target := rfl

omit [Fintype Q] [DecidableEq Q] in
@[simp] theorem targetControlPlacement_one (target control : Q) (h : target ≠ control) :
    targetControlPlacement target control h 1 = control := rfl

/-- Arbitrary named-register CNOT, with target/control inequality enforced by its type. -/
def cnotAt (target control : Q) (h : target ≠ control) : Operator Q :=
  embedAlong (targetControlPlacement target control h) cnotLocal

/-- Local raw basis permutation: toggle coordinate `0` exactly when coordinate `1` is raw `0`. -/
def cnotLocalOutput (input : Basis (Fin 2)) : Basis (Fin 2) := fun i ↦
  if i = 0 then
    if input 1 = 0 then flipRaw (input 0) else input 0
  else input 1

@[simp] theorem cnotLocalOutput_zero (input : Basis (Fin 2)) :
    cnotLocalOutput input 0 =
      if input 1 = 0 then flipRaw (input 0) else input 0 := by
  simp [cnotLocalOutput]

@[simp] theorem cnotLocalOutput_one (input : Basis (Fin 2)) :
    cnotLocalOutput input 1 = input 1 := by
  simp [cnotLocalOutput]

/-- Named-register version of the same raw basis permutation. -/
def cnotOutput (target control : Q) (input : Basis Q) : Basis Q :=
  Function.update input target
    (if input control = 0 then flipRaw (input target) else input target)

omit [Fintype Q] in
@[simp] theorem cnotOutput_target (target control : Q) (input : Basis Q) :
    cnotOutput target control input target =
      if input control = 0 then flipRaw (input target) else input target := by
  simp [cnotOutput]

omit [Fintype Q] in
@[simp] theorem cnotOutput_control {target control : Q} (h : target ≠ control)
    (input : Basis Q) : cnotOutput target control input control = input control := by
  simp [cnotOutput, h.symm]

omit [Fintype Q] in
theorem cnotOutput_other {target control : Q} (input : Basis Q)
    {q : Q} (hqt : q ≠ target) :
    cnotOutput target control input q = input q := by
  simp [cnotOutput, hqt]

/-- The local CNOT is exactly its raw-index permutation matrix. -/
theorem cnotLocal_apply (output input : Basis (Fin 2)) :
    cnotLocal output input = if output = cnotLocalOutput input then 1 else 0 := by
  classical
  generalize ho0 : output 0 = o0
  generalize ho1 : output 1 = o1
  generalize hi0 : input 0 = i0
  generalize hi1 : input 1 = i1
  have hout : output = ![o0, o1] := by
    funext i
    fin_cases i <;> simp [ho0, ho1]
  have hin : input = ![i0, i1] := by
    funext i
    fin_cases i <;> simp [hi0, hi1]
  rw [hout, hin]
  fin_cases o0 <;> fin_cases o1 <;>
    fin_cases i0 <;> fin_cases i1 <;>
    norm_num [cnotLocal, cnotLocalOutput, flipRaw, cnotTargetLeftControlRight,
      bitZeroProjector, bitOneProjector, identity₂, pauliX, pauliZ,
      twoQubitBasisEquiv, Matrix.one_apply]
  all_goals decide

theorem cnotAt_isSupportedOn (target control : Q) (h : target ≠ control) :
    IsSupportedOn (placementFinset (targetControlPlacement target control h))
      (cnotAt target control h) :=
  embedAlong_isSupportedOn _ _

/-- Exact global permutation-matrix entries, including identity off target/control. -/
theorem cnotAt_apply (target control : Q) (h : target ≠ control)
    (output input : Basis Q) :
    cnotAt target control h output input =
      if output = cnotOutput target control input then 1 else 0 := by
  rw [cnotAt, embedAlong_apply_ite]
  let p := targetControlPlacement target control h
  change (if ∀ q, q ∉ Set.range p → output q = input q then
      cnotLocal (fun k ↦ output (p k)) (fun k ↦ input (p k)) else 0) = _
  rw [cnotLocal_apply]
  by_cases hEq : output = cnotOutput target control input
  · rw [if_pos hEq]
    subst output
    have houtside : ∀ q, q ∉ Set.range p →
        cnotOutput target control input q = input q := by
      intro q hq
      apply cnotOutput_other input
      intro hqt
      subst q
      exact hq ⟨0, rfl⟩
    rw [if_pos houtside]
    have hlocal :
        (fun k ↦ cnotOutput target control input (p k)) =
          cnotLocalOutput (fun k ↦ input (p k)) := by
      funext k
      fin_cases k <;> simp [p, cnotLocalOutput, h]
    rw [if_pos hlocal]
  · rw [if_neg hEq]
    by_cases houtside : ∀ q, q ∉ Set.range p → output q = input q
    · rw [if_pos houtside]
      by_cases hlocal :
          (fun k ↦ output (p k)) = cnotLocalOutput (fun k ↦ input (p k))
      · rw [if_pos hlocal]
        exfalso
        apply hEq
        funext q
        by_cases hqt : q = target
        · subst q
          have h0 := congrFun hlocal 0
          simpa [p, cnotLocalOutput, cnotOutput] using h0
        · by_cases hqc : q = control
          · subst q
            have h1 := congrFun hlocal 1
            simpa [p, cnotLocalOutput, cnotOutput, h.symm] using h1
          · rw [cnotOutput_other input hqt]
            apply houtside q
            intro hrange
            rcases hrange with ⟨k, hk⟩
            fin_cases k <;> simp [p] at hk
            · exact hqt hk.symm
            · exact hqc hk.symm
      · rw [if_neg hlocal]
    · rw [if_neg houtside]

/-- CNOT acts on computational basis kets by the exact raw-index permutation above. -/
theorem cnotAt_act_basisKet (target control : Q) (h : target ≠ control)
    (input : Basis Q) :
    act (cnotAt target control h) (basisKet input) =
      basisKet (cnotOutput target control input) := by
  rw [act, matrixEndEquiv_apply]
  simp only [basisKet]
  apply congrArg (WithLp.toLp 2)
  change cnotAt target control h *ᵥ Pi.single input 1 =
    Pi.single (cnotOutput target control input) 1
  rw [Matrix.mulVec_single_one]
  funext output
  change cnotAt target control h output input = _
  rw [cnotAt_apply]
  simp [Pi.single_apply]

def cnotPairOutput (input : QubitIndex × QubitIndex) :
    QubitIndex × QubitIndex :=
  (if input.2 = 0 then flipRaw input.1 else input.1, input.2)

def cnotPairPermutation : TwoQubitMatrix :=
  fun output input ↦ if output = cnotPairOutput input then 1 else 0

theorem cnot_pair_eq_permutation :
    cnotTargetLeftControlRight = cnotPairPermutation := by
  ext output input
  rcases output with ⟨ot, oc⟩
  rcases input with ⟨it, ic⟩
  fin_cases ot <;> fin_cases oc <;> fin_cases it <;> fin_cases ic <;>
    norm_num [cnotTargetLeftControlRight, cnotPairPermutation, cnotPairOutput,
      flipRaw, bitZeroProjector, bitOneProjector, identity₂, pauliX, pauliZ,
      Matrix.one_apply]

theorem cnot_pair_isHermitian : cnotTargetLeftControlRight.IsHermitian := by
  rw [cnot_pair_eq_permutation]
  ext output input
  rcases output with ⟨ot, oc⟩
  rcases input with ⟨it, ic⟩
  fin_cases ot <;> fin_cases oc <;> fin_cases it <;> fin_cases ic <;>
    norm_num [Matrix.IsHermitian, Matrix.conjTranspose_apply,
      cnotPairPermutation, cnotPairOutput, flipRaw]

theorem cnot_pair_mul_self :
    cnotTargetLeftControlRight * cnotTargetLeftControlRight = 1 := by
  rw [cnot_pair_eq_permutation]
  ext output input
  rcases output with ⟨ot, oc⟩
  rcases input with ⟨it, ic⟩
  fin_cases ot <;> fin_cases oc <;> fin_cases it <;> fin_cases ic <;>
    norm_num [cnotPairPermutation, cnotPairOutput, flipRaw, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply]

theorem cnotLocal_isHermitian : cnotLocal.IsHermitian := by
  rw [Matrix.IsHermitian, cnotLocal, reindexRingEquiv_conjTranspose,
    cnot_pair_isHermitian]

theorem cnotLocal_mul_self : cnotLocal * cnotLocal = 1 := by
  rw [cnotLocal, ← map_mul, cnot_pair_mul_self, map_one]

theorem cnotLocal_unitary :
    cnotLocal ∈ Matrix.unitaryGroup (Basis (Fin 2)) Complex := by
  rw [Matrix.mem_unitaryGroup_iff']
  change cnotLocalᴴ * cnotLocal = 1
  rw [cnotLocal_isHermitian, cnotLocal_mul_self]

theorem cnotAt_isHermitian (target control : Q) (h : target ≠ control) :
    (cnotAt target control h).IsHermitian :=
  embedAlong_isHermitian _ _ cnotLocal_isHermitian

theorem cnotAt_mul_self (target control : Q) (h : target ≠ control) :
    cnotAt target control h * cnotAt target control h = 1 := by
  rw [cnotAt, ← embedAlong_mul, cnotLocal_mul_self, embedAlong_one]

theorem cnotAt_unitary (target control : Q) (h : target ≠ control) :
    cnotAt target control h ∈ Matrix.unitaryGroup (Basis Q) Complex :=
  embedAlong_unitary _ _ cnotLocal_unitary

omit [Fintype Q] in
theorem placementFinset_targetControl (target control : Q) (h : target ≠ control) :
    placementFinset (targetControlPlacement target control h) = {target, control} := by
  ext q
  simp only [mem_placementFinset_iff, Set.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨k, rfl⟩
    fin_cases k <;> simp
  · intro hq
    rcases hq with hq | hq
    · exact ⟨0, hq.symm⟩
    · exact ⟨1, hq.symm⟩

theorem cnotAt_isSupportedOn_pair (target control : Q) (h : target ≠ control) :
    IsSupportedOn {target, control} (cnotAt target control h) := by
  rw [← placementFinset_targetControl target control h]
  exact cnotAt_isSupportedOn target control h

theorem reindex_pair_left_eq_embedQubit (A : QubitMatrix) :
    Matrix.reindexRingEquiv Complex twoQubitBasisEquiv.symm
        (A ⊗ₖ identity₂) =
      embedQubit (0 : Fin 2) A := by
  ext x y
  rw [embedQubit_apply_ite]
  change A (x 0) (y 0) * (1 : QubitMatrix) (x 1) (y 1) = _
  by_cases hxy : x 1 = y 1
  · rw [if_pos]
    · simp [Matrix.one_apply, hxy]
    · intro j hj
      fin_cases j
      · exact False.elim (hj rfl)
      · exact hxy
  · rw [if_neg]
    · simp [hxy]
    · intro hall
      exact hxy (hall 1 (by decide))

theorem reindex_pair_right_eq_embedQubit (A : QubitMatrix) :
    Matrix.reindexRingEquiv Complex twoQubitBasisEquiv.symm
        (identity₂ ⊗ₖ A) =
      embedQubit (1 : Fin 2) A := by
  ext x y
  rw [embedQubit_apply_ite]
  change (1 : QubitMatrix) (x 0) (y 0) * A (x 1) (y 1) = _
  by_cases hxy : x 0 = y 0
  · rw [if_pos]
    · simp [Matrix.one_apply, hxy]
    · intro j hj
      fin_cases j
      · exact hxy
      · exact False.elim (hj rfl)
  · rw [if_neg]
    · simp [hxy]
    · intro hall
      exact hxy (hall 0 (by decide))

theorem pair_kronecker_eq_factor_product (A B : QubitMatrix) :
    A ⊗ₖ B = (A ⊗ₖ identity₂) * (identity₂ ⊗ₖ B) := by
  rw [← Matrix.mul_kronecker_mul]
  simp [identity₂]

/-- Typed realization of Equation (15) on the local `Fin 2` register. -/
theorem cnotLocal_eq_global_formula :
    cnotLocal = paperBitZeroProjectorAt (1 : Fin 2) +
      xAt (0 : Fin 2) * paperBitOneProjectorAt (1 : Fin 2) := by
  rw [cnotLocal, cnotTargetLeftControlRight, map_add]
  rw [reindex_pair_right_eq_embedQubit]
  rw [pair_kronecker_eq_factor_product, map_mul,
    reindex_pair_left_eq_embedQubit, reindex_pair_right_eq_embedQubit]
  rfl

/--
Typed arbitrary-register form of Equation (15). Every factor here is already a global operator;
there is no second tensor embedding around the products.
-/
theorem cnotAt_eq_global_formula (target control : Q) (h : target ≠ control) :
    cnotAt target control h = paperBitZeroProjectorAt control +
      xAt target * paperBitOneProjectorAt control := by
  let p := targetControlPlacement target control h
  calc
    cnotAt target control h = embedAlong p cnotLocal := rfl
    _ = embedAlong p (paperBitZeroProjectorAt (1 : Fin 2) +
        xAt (0 : Fin 2) * paperBitOneProjectorAt (1 : Fin 2)) := by
      rw [cnotLocal_eq_global_formula]
    _ = embedAlong p (paperBitZeroProjectorAt (1 : Fin 2)) +
        embedAlong p (xAt (0 : Fin 2)) *
          embedAlong p (paperBitOneProjectorAt (1 : Fin 2)) := by
      rw [embedAlong_add, embedAlong_mul]
    _ = paperBitZeroProjectorAt control +
        xAt target * paperBitOneProjectorAt control := by
      unfold paperBitZeroProjectorAt paperBitOneProjectorAt xAt
      rw [embedAlong_embedQubit, embedAlong_embedQubit, embedAlong_embedQubit]
      rfl

/-! Six independently enumerated pair-basis Heisenberg checks. -/

theorem cnot_pair_conjugates_target_x :
    cnotTargetLeftControlRightᴴ * (pauliX ⊗ₖ identity₂) *
        cnotTargetLeftControlRight = pauliX ⊗ₖ identity₂ := by
  rw [cnot_pair_eq_permutation]
  ext output input
  rcases output with ⟨ot, oc⟩
  rcases input with ⟨it, ic⟩
  fin_cases ot <;> fin_cases oc <;> fin_cases it <;> fin_cases ic <;>
    norm_num [cnotPairPermutation, cnotPairOutput, flipRaw, identity₂, pauliX,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_pair_conjugates_target_y :
    cnotTargetLeftControlRightᴴ * (pauliY ⊗ₖ identity₂) *
        cnotTargetLeftControlRight = -(pauliY ⊗ₖ pauliZ) := by
  rw [cnot_pair_eq_permutation]
  ext output input
  rcases output with ⟨ot, oc⟩
  rcases input with ⟨it, ic⟩
  fin_cases ot <;> fin_cases oc <;> fin_cases it <;> fin_cases ic <;>
    norm_num [cnotPairPermutation, cnotPairOutput, flipRaw, identity₂, pauliY,
      pauliZ, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_pair_conjugates_target_z :
    cnotTargetLeftControlRightᴴ * (pauliZ ⊗ₖ identity₂) *
        cnotTargetLeftControlRight = -(pauliZ ⊗ₖ pauliZ) := by
  rw [cnot_pair_eq_permutation]
  ext output input
  rcases output with ⟨ot, oc⟩
  rcases input with ⟨it, ic⟩
  fin_cases ot <;> fin_cases oc <;> fin_cases it <;> fin_cases ic <;>
    norm_num [cnotPairPermutation, cnotPairOutput, flipRaw, identity₂, pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_pair_conjugates_control_x :
    cnotTargetLeftControlRightᴴ * (identity₂ ⊗ₖ pauliX) *
        cnotTargetLeftControlRight = pauliX ⊗ₖ pauliX := by
  rw [cnot_pair_eq_permutation]
  ext output input
  rcases output with ⟨ot, oc⟩
  rcases input with ⟨it, ic⟩
  fin_cases ot <;> fin_cases oc <;> fin_cases it <;> fin_cases ic <;>
    norm_num [cnotPairPermutation, cnotPairOutput, flipRaw, identity₂, pauliX,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_pair_conjugates_control_y :
    cnotTargetLeftControlRightᴴ * (identity₂ ⊗ₖ pauliY) *
        cnotTargetLeftControlRight = pauliX ⊗ₖ pauliY := by
  rw [cnot_pair_eq_permutation]
  ext output input
  rcases output with ⟨ot, oc⟩
  rcases input with ⟨it, ic⟩
  fin_cases ot <;> fin_cases oc <;> fin_cases it <;> fin_cases ic <;>
    norm_num [cnotPairPermutation, cnotPairOutput, flipRaw, identity₂, pauliX,
      pauliY, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fintype.sum_prod_type, Fin.sum_univ_succ, Matrix.one_apply]

theorem cnot_pair_conjugates_control_z :
    cnotTargetLeftControlRightᴴ * (identity₂ ⊗ₖ pauliZ) *
        cnotTargetLeftControlRight = identity₂ ⊗ₖ pauliZ := by
  rw [cnot_pair_eq_permutation]
  ext output input
  rcases output with ⟨ot, oc⟩
  rcases input with ⟨it, ic⟩
  fin_cases ot <;> fin_cases oc <;> fin_cases it <;> fin_cases ic <;>
    norm_num [cnotPairPermutation, cnotPairOutput, flipRaw, identity₂, pauliZ,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type,
      Fin.sum_univ_succ, Matrix.one_apply]

theorem reindex_pair_heisenberg (U A : TwoQubitMatrix) :
    Register.heisenberg
        (Matrix.reindexRingEquiv Complex twoQubitBasisEquiv.symm U)
        (Matrix.reindexRingEquiv Complex twoQubitBasisEquiv.symm A) =
      Matrix.reindexRingEquiv Complex twoQubitBasisEquiv.symm (Uᴴ * A * U) := by
  simp only [Register.heisenberg, reindexRingEquiv_conjTranspose]
  rw [map_mul, map_mul]

/-! Local `Fin 2` forms of Equation (16). -/

theorem cnotLocal_conjugates_target_x :
    heisenberg cnotLocal (xAt (0 : Fin 2)) = xAt 0 := by
  rw [xAt, ← reindex_pair_left_eq_embedQubit pauliX, cnotLocal,
    reindex_pair_heisenberg, cnot_pair_conjugates_target_x,
    reindex_pair_left_eq_embedQubit]

theorem cnotLocal_conjugates_target_y :
    heisenberg cnotLocal (yAt (0 : Fin 2)) = -(yAt 0 * zAt 1) := by
  rw [yAt, ← reindex_pair_left_eq_embedQubit pauliY, cnotLocal,
    reindex_pair_heisenberg, cnot_pair_conjugates_target_y, map_neg,
    pair_kronecker_eq_factor_product, map_mul,
    reindex_pair_left_eq_embedQubit, reindex_pair_right_eq_embedQubit]
  rfl

theorem cnotLocal_conjugates_target_z :
    heisenberg cnotLocal (zAt (0 : Fin 2)) = -(zAt 0 * zAt 1) := by
  rw [zAt, ← reindex_pair_left_eq_embedQubit pauliZ, cnotLocal,
    reindex_pair_heisenberg, cnot_pair_conjugates_target_z, map_neg,
    pair_kronecker_eq_factor_product, map_mul,
    reindex_pair_left_eq_embedQubit, reindex_pair_right_eq_embedQubit]
  rfl

theorem cnotLocal_conjugates_control_x :
    heisenberg cnotLocal (xAt (1 : Fin 2)) = xAt 0 * xAt 1 := by
  rw [xAt, ← reindex_pair_right_eq_embedQubit pauliX, cnotLocal,
    reindex_pair_heisenberg, cnot_pair_conjugates_control_x,
    pair_kronecker_eq_factor_product, map_mul,
    reindex_pair_left_eq_embedQubit, reindex_pair_right_eq_embedQubit]
  rfl

theorem cnotLocal_conjugates_control_y :
    heisenberg cnotLocal (yAt (1 : Fin 2)) = xAt 0 * yAt 1 := by
  rw [yAt, ← reindex_pair_right_eq_embedQubit pauliY, cnotLocal,
    reindex_pair_heisenberg, cnot_pair_conjugates_control_y,
    pair_kronecker_eq_factor_product, map_mul,
    reindex_pair_left_eq_embedQubit, reindex_pair_right_eq_embedQubit]
  rfl

theorem cnotLocal_conjugates_control_z :
    heisenberg cnotLocal (zAt (1 : Fin 2)) = zAt 1 := by
  rw [zAt, ← reindex_pair_right_eq_embedQubit pauliZ, cnotLocal,
    reindex_pair_heisenberg, cnot_pair_conjugates_control_z,
    reindex_pair_right_eq_embedQubit]

/-! Arbitrary named-register forms, with no local/global tensor ambiguity. -/

@[simp] private theorem embedAlong_xAt {K : Type*} [Fintype K] [DecidableEq K]
    (p : K ↪ Q) (k : K) : embedAlong p (xAt k) = xAt (p k) := by
  exact embedAlong_embedQubit p k pauliX

@[simp] private theorem embedAlong_yAt {K : Type*} [Fintype K] [DecidableEq K]
    (p : K ↪ Q) (k : K) : embedAlong p (yAt k) = yAt (p k) := by
  exact embedAlong_embedQubit p k pauliY

@[simp] private theorem embedAlong_zAt {K : Type*} [Fintype K] [DecidableEq K]
    (p : K ↪ Q) (k : K) : embedAlong p (zAt k) = zAt (p k) := by
  exact embedAlong_embedQubit p k pauliZ

private theorem embedAlong_neg {K : Type*} [Fintype K] [DecidableEq K]
    (p : K ↪ Q) (A : Operator K) : embedAlong p (-A) = -embedAlong p A := by
  exact map_neg (embedAlongAlgHom p) A

theorem cnotAt_conjugates_target_x (target control : Q) (h : target ≠ control) :
    heisenberg (cnotAt target control h) (xAt target) = xAt target := by
  let p := targetControlPlacement target control h
  calc
    heisenberg (cnotAt target control h) (xAt target) =
        embedAlong p (heisenberg cnotLocal (xAt (0 : Fin 2))) := by
      simpa [cnotAt, p] using
        (embedAlong_heisenberg p cnotLocal (xAt (0 : Fin 2)))
    _ = xAt target := by
      rw [cnotLocal_conjugates_target_x, embedAlong_xAt]
      rfl

theorem cnotAt_conjugates_target_y (target control : Q) (h : target ≠ control) :
    heisenberg (cnotAt target control h) (yAt target) =
      -(yAt target * zAt control) := by
  let p := targetControlPlacement target control h
  calc
    heisenberg (cnotAt target control h) (yAt target) =
        embedAlong p (heisenberg cnotLocal (yAt (0 : Fin 2))) := by
      simpa [cnotAt, p] using
        (embedAlong_heisenberg p cnotLocal (yAt (0 : Fin 2)))
    _ = embedAlong p (-(yAt (0 : Fin 2) * zAt (1 : Fin 2))) := by
      rw [cnotLocal_conjugates_target_y]
    _ = -(yAt target * zAt control) := by
      rw [embedAlong_neg, embedAlong_mul, embedAlong_yAt, embedAlong_zAt]
      rfl

theorem cnotAt_conjugates_target_z (target control : Q) (h : target ≠ control) :
    heisenberg (cnotAt target control h) (zAt target) =
      -(zAt target * zAt control) := by
  let p := targetControlPlacement target control h
  calc
    heisenberg (cnotAt target control h) (zAt target) =
        embedAlong p (heisenberg cnotLocal (zAt (0 : Fin 2))) := by
      simpa [cnotAt, p] using
        (embedAlong_heisenberg p cnotLocal (zAt (0 : Fin 2)))
    _ = embedAlong p (-(zAt (0 : Fin 2) * zAt (1 : Fin 2))) := by
      rw [cnotLocal_conjugates_target_z]
    _ = -(zAt target * zAt control) := by
      rw [embedAlong_neg, embedAlong_mul, embedAlong_zAt, embedAlong_zAt]
      rfl

theorem cnotAt_conjugates_control_x (target control : Q) (h : target ≠ control) :
    heisenberg (cnotAt target control h) (xAt control) =
      xAt target * xAt control := by
  let p := targetControlPlacement target control h
  calc
    heisenberg (cnotAt target control h) (xAt control) =
        embedAlong p (heisenberg cnotLocal (xAt (1 : Fin 2))) := by
      simpa [cnotAt, p] using
        (embedAlong_heisenberg p cnotLocal (xAt (1 : Fin 2)))
    _ = embedAlong p (xAt (0 : Fin 2) * xAt (1 : Fin 2)) := by
      rw [cnotLocal_conjugates_control_x]
    _ = xAt target * xAt control := by
      rw [embedAlong_mul, embedAlong_xAt, embedAlong_xAt]
      rfl

theorem cnotAt_conjugates_control_y (target control : Q) (h : target ≠ control) :
    heisenberg (cnotAt target control h) (yAt control) =
      xAt target * yAt control := by
  let p := targetControlPlacement target control h
  calc
    heisenberg (cnotAt target control h) (yAt control) =
        embedAlong p (heisenberg cnotLocal (yAt (1 : Fin 2))) := by
      simpa [cnotAt, p] using
        (embedAlong_heisenberg p cnotLocal (yAt (1 : Fin 2)))
    _ = embedAlong p (xAt (0 : Fin 2) * yAt (1 : Fin 2)) := by
      rw [cnotLocal_conjugates_control_y]
    _ = xAt target * yAt control := by
      rw [embedAlong_mul, embedAlong_xAt, embedAlong_yAt]
      rfl

theorem cnotAt_conjugates_control_z (target control : Q) (h : target ≠ control) :
    heisenberg (cnotAt target control h) (zAt control) = zAt control := by
  let p := targetControlPlacement target control h
  calc
    heisenberg (cnotAt target control h) (zAt control) =
        embedAlong p (heisenberg cnotLocal (zAt (1 : Fin 2))) := by
      simpa [cnotAt, p] using
        (embedAlong_heisenberg p cnotLocal (zAt (1 : Fin 2)))
    _ = zAt control := by
      rw [cnotLocal_conjugates_control_z, embedAlong_zAt]
      rfl

/-! Descriptor-dependent gate expression from Equation (15). -/

/-- The paper-bit-zero projector polynomial for a descriptor `Z` component. -/
def descriptorBitZeroProjector (Z : Operator Q) : Operator Q :=
  ((2 : Complex)⁻¹) • (1 - Z)

/-- The paper-bit-one projector polynomial for a descriptor `Z` component. -/
def descriptorBitOneProjector (Z : Operator Q) : Operator Q :=
  ((2 : Complex)⁻¹) • (1 + Z)

omit [DecidableEq Q] in
theorem descriptorBitProjector_sum (Z : Operator Q) : descriptorBitZeroProjector Z + descriptorBitOneProjector Z = 1 := by
  unfold descriptorBitZeroProjector descriptorBitOneProjector
  module

theorem descriptorBitZeroProjector_square {Z : Operator Q} (hZ : Z * Z = 1) :
    descriptorBitZeroProjector Z * descriptorBitZeroProjector Z = descriptorBitZeroProjector Z := by
  unfold descriptorBitZeroProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hpoly : (1 - Z) * (1 - Z) = (1 - Z) + (1 - Z) := by
    noncomm_ring [hZ]
  rw [hpoly, smul_add, ← add_smul]
  congr 1
  norm_num

theorem descriptorBitOneProjector_square {Z : Operator Q} (hZ : Z * Z = 1) :
    descriptorBitOneProjector Z * descriptorBitOneProjector Z = descriptorBitOneProjector Z := by
  unfold descriptorBitOneProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hpoly : (1 + Z) * (1 + Z) = (1 + Z) + (1 + Z) := by
    noncomm_ring [hZ]
  rw [hpoly, smul_add, ← add_smul]
  congr 1
  norm_num

theorem descriptorBitZeroProjector_mul_one {Z : Operator Q} (hZ : Z * Z = 1) :
    descriptorBitZeroProjector Z * descriptorBitOneProjector Z = 0 := by
  unfold descriptorBitZeroProjector descriptorBitOneProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hpoly : (1 - Z) * (1 + Z) = 0 := by noncomm_ring [hZ]
  rw [hpoly, smul_zero]

theorem descriptorBitOneProjector_mul_zero {Z : Operator Q} (hZ : Z * Z = 1) :
    descriptorBitOneProjector Z * descriptorBitZeroProjector Z = 0 := by
  unfold descriptorBitZeroProjector descriptorBitOneProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  have hpoly : (1 + Z) * (1 - Z) = 0 := by noncomm_ring [hZ]
  rw [hpoly, smul_zero]

omit [DecidableEq Q] in
theorem descriptorBitZeroProjector_isHermitian {Z : Operator Q} (hZ : Z.IsHermitian) :
    (descriptorBitZeroProjector Z).IsHermitian := by
  rw [Matrix.IsHermitian]
  unfold descriptorBitZeroProjector
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, hZ]
  simp

omit [DecidableEq Q] in
theorem descriptorBitOneProjector_isHermitian {Z : Operator Q} (hZ : Z.IsHermitian) :
    (descriptorBitOneProjector Z).IsHermitian := by
  rw [Matrix.IsHermitian]
  unfold descriptorBitOneProjector
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_add, hZ]
  simp

/-- Equation (15) evaluated on already-global current descriptor components. -/
def cnotFromDescriptors (D : DescriptorFamily Q) (target control : Q) : Operator Q :=
  descriptorBitZeroProjector (D control).z +
    (D target).x * descriptorBitOneProjector (D control).z

private theorem commutes_descriptorBitZeroProjector {X Z : Operator Q} (h : X * Z = Z * X) :
    X * descriptorBitZeroProjector Z = descriptorBitZeroProjector Z * X := by
  unfold descriptorBitZeroProjector
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  noncomm_ring [h]

private theorem commutes_descriptorBitOneProjector {X Z : Operator Q} (h : X * Z = Z * X) :
    X * descriptorBitOneProjector Z = descriptorBitOneProjector Z * X := by
  unfold descriptorBitOneProjector
  simp only [Matrix.mul_smul, Matrix.smul_mul]
  noncomm_ring [h]

omit [DecidableEq Q] in
theorem descriptorBitProjector_difference (Z : Operator Q) : descriptorBitZeroProjector Z - descriptorBitOneProjector Z = -Z := by
  unfold descriptorBitZeroProjector descriptorBitOneProjector
  module

private theorem descriptorBitZeroProjector_mul_of_anticommutes {Z A : Operator Q}
    (hZA : Z * A = -(A * Z)) : descriptorBitZeroProjector Z * A = A * descriptorBitOneProjector Z := by
  unfold descriptorBitZeroProjector descriptorBitOneProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  noncomm_ring [hZA]

private theorem descriptorBitOneProjector_mul_of_anticommutes {Z A : Operator Q}
    (hZA : Z * A = -(A * Z)) : descriptorBitOneProjector Z * A = A * descriptorBitZeroProjector Z := by
  unfold descriptorBitZeroProjector descriptorBitOneProjector
  simp only [Matrix.smul_mul, Matrix.mul_smul]
  noncomm_ring [hZA]

private theorem conjugate_control_of_anticommutes {X Z B : Operator Q}
    (hZ2 : Z * Z = 1)
    (hXZ : X * Z = Z * X) (hXB : X * B = B * X)
    (hZB : Z * B = -(B * Z)) :
    (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * B * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) = X * B := by
  have hXP0 : X * descriptorBitZeroProjector Z = descriptorBitZeroProjector Z * X := commutes_descriptorBitZeroProjector hXZ
  have hXP1 : X * descriptorBitOneProjector Z = descriptorBitOneProjector Z * X := commutes_descriptorBitOneProjector hXZ
  have hP0B : descriptorBitZeroProjector Z * B = B * descriptorBitOneProjector Z := descriptorBitZeroProjector_mul_of_anticommutes hZB
  have hP1B : descriptorBitOneProjector Z * B = B * descriptorBitZeroProjector Z := descriptorBitOneProjector_mul_of_anticommutes hZB
  have h00 : descriptorBitZeroProjector Z * (B * descriptorBitZeroProjector Z) = 0 := by
    calc
      descriptorBitZeroProjector Z * (B * descriptorBitZeroProjector Z) = (descriptorBitZeroProjector Z * B) * descriptorBitZeroProjector Z := by
        rw [Matrix.mul_assoc]
      _ = (B * descriptorBitOneProjector Z) * descriptorBitZeroProjector Z := by rw [hP0B]
      _ = B * (descriptorBitOneProjector Z * descriptorBitZeroProjector Z) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [descriptorBitOneProjector_mul_zero hZ2, mul_zero]
  have h01 : descriptorBitZeroProjector Z * (B * (X * descriptorBitOneProjector Z)) = (X * B) * descriptorBitOneProjector Z := by
    calc
      descriptorBitZeroProjector Z * (B * (X * descriptorBitOneProjector Z)) = (descriptorBitZeroProjector Z * B) * (X * descriptorBitOneProjector Z) := by
        rw [Matrix.mul_assoc]
      _ = (B * descriptorBitOneProjector Z) * (X * descriptorBitOneProjector Z) := by rw [hP0B]
      _ = B * ((descriptorBitOneProjector Z * X) * descriptorBitOneProjector Z) := by simp [Matrix.mul_assoc]
      _ = B * ((X * descriptorBitOneProjector Z) * descriptorBitOneProjector Z) := by rw [← hXP1]
      _ = B * (X * (descriptorBitOneProjector Z * descriptorBitOneProjector Z)) := by rw [Matrix.mul_assoc]
      _ = B * (X * descriptorBitOneProjector Z) := by rw [descriptorBitOneProjector_square hZ2]
      _ = (X * B) * descriptorBitOneProjector Z := by rw [← Matrix.mul_assoc, hXB]
  have h10 : descriptorBitOneProjector Z * (B * descriptorBitZeroProjector Z) = B * descriptorBitZeroProjector Z := by
    calc
      descriptorBitOneProjector Z * (B * descriptorBitZeroProjector Z) = (descriptorBitOneProjector Z * B) * descriptorBitZeroProjector Z := by
        rw [Matrix.mul_assoc]
      _ = (B * descriptorBitZeroProjector Z) * descriptorBitZeroProjector Z := by rw [hP1B]
      _ = B * (descriptorBitZeroProjector Z * descriptorBitZeroProjector Z) := by rw [Matrix.mul_assoc]
      _ = B * descriptorBitZeroProjector Z := by rw [descriptorBitZeroProjector_square hZ2]
  have h11 : descriptorBitOneProjector Z * (B * (X * descriptorBitOneProjector Z)) = 0 := by
    calc
      descriptorBitOneProjector Z * (B * (X * descriptorBitOneProjector Z)) = (descriptorBitOneProjector Z * B) * (X * descriptorBitOneProjector Z) := by
        rw [Matrix.mul_assoc]
      _ = (B * descriptorBitZeroProjector Z) * (X * descriptorBitOneProjector Z) := by rw [hP1B]
      _ = B * ((descriptorBitZeroProjector Z * X) * descriptorBitOneProjector Z) := by simp [Matrix.mul_assoc]
      _ = B * ((X * descriptorBitZeroProjector Z) * descriptorBitOneProjector Z) := by rw [← hXP0]
      _ = B * (X * (descriptorBitZeroProjector Z * descriptorBitOneProjector Z)) := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [descriptorBitZeroProjector_mul_one hZ2, mul_zero, mul_zero]
  calc
    (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * B * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) =
        descriptorBitZeroProjector Z * (B * descriptorBitZeroProjector Z) + descriptorBitZeroProjector Z * (B * (X * descriptorBitOneProjector Z)) +
          X * (descriptorBitOneProjector Z * (B * descriptorBitZeroProjector Z)) +
            X * (descriptorBitOneProjector Z * (B * (X * descriptorBitOneProjector Z))) := by noncomm_ring
    _ = (X * B) * descriptorBitOneProjector Z + (X * B) * descriptorBitZeroProjector Z := by
      rw [h00, h01, h10, h11]
      simp [Matrix.mul_assoc]
    _ = (X * B) * (descriptorBitOneProjector Z + descriptorBitZeroProjector Z) := by rw [Matrix.mul_add]
    _ = X * B := by rw [add_comm, descriptorBitProjector_sum, mul_one]

private theorem conjugate_target_of_anticommutes {X Z A : Operator Q}
    (hX2 : X * X = 1) (hZ2 : Z * Z = 1)
    (hXZ : X * Z = Z * X) (hAZ : A * Z = Z * A)
    (hXA : X * A = -(A * X)) :
    (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * A * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) = -(A * Z) := by
  have hXP0 : X * descriptorBitZeroProjector Z = descriptorBitZeroProjector Z * X := commutes_descriptorBitZeroProjector hXZ
  have hXP1 : X * descriptorBitOneProjector Z = descriptorBitOneProjector Z * X := commutes_descriptorBitOneProjector hXZ
  have hAP0 : A * descriptorBitZeroProjector Z = descriptorBitZeroProjector Z * A := commutes_descriptorBitZeroProjector hAZ
  have hAP1 : A * descriptorBitOneProjector Z = descriptorBitOneProjector Z * A := commutes_descriptorBitOneProjector hAZ
  have hpp : descriptorBitZeroProjector Z * (descriptorBitZeroProjector Z * A) = descriptorBitZeroProjector Z * A := by
    rw [← Matrix.mul_assoc, descriptorBitZeroProjector_square hZ2]
  have hcross₀ : descriptorBitOneProjector Z * (A * (descriptorBitZeroProjector Z * X)) = 0 := by
    calc
      descriptorBitOneProjector Z * (A * (descriptorBitZeroProjector Z * X)) =
          descriptorBitOneProjector Z * ((A * descriptorBitZeroProjector Z) * X) := by
            rw [Matrix.mul_assoc A (descriptorBitZeroProjector Z) X]
      _ = descriptorBitOneProjector Z * ((descriptorBitZeroProjector Z * A) * X) := by rw [hAP0]
      _ = (descriptorBitOneProjector Z * descriptorBitZeroProjector Z) * (A * X) := by simp [Matrix.mul_assoc]
      _ = 0 := by rw [descriptorBitOneProjector_mul_zero hZ2, zero_mul]
  have hcross₁ : descriptorBitZeroProjector Z * (A * (descriptorBitOneProjector Z * X)) = 0 := by
    calc
      descriptorBitZeroProjector Z * (A * (descriptorBitOneProjector Z * X)) =
          descriptorBitZeroProjector Z * ((A * descriptorBitOneProjector Z) * X) := by
            rw [Matrix.mul_assoc A (descriptorBitOneProjector Z) X]
      _ = descriptorBitZeroProjector Z * ((descriptorBitOneProjector Z * A) * X) := by rw [hAP1]
      _ = (descriptorBitZeroProjector Z * descriptorBitOneProjector Z) * (A * X) := by simp [Matrix.mul_assoc]
      _ = 0 := by rw [descriptorBitZeroProjector_mul_one hZ2, zero_mul]
  have hqq : descriptorBitOneProjector Z * (A * (X * (descriptorBitOneProjector Z * X))) = descriptorBitOneProjector Z * A := by
    calc
      descriptorBitOneProjector Z * (A * (X * (descriptorBitOneProjector Z * X))) =
          descriptorBitOneProjector Z * (A * ((X * descriptorBitOneProjector Z) * X)) := by
            rw [Matrix.mul_assoc X (descriptorBitOneProjector Z) X]
      _ = descriptorBitOneProjector Z * (A * ((descriptorBitOneProjector Z * X) * X)) := by rw [hXP1]
      _ = descriptorBitOneProjector Z * (A * (descriptorBitOneProjector Z * (X * X))) := by
        rw [Matrix.mul_assoc (descriptorBitOneProjector Z) X X]
      _ = descriptorBitOneProjector Z * (A * descriptorBitOneProjector Z) := by rw [hX2, mul_one]
      _ = descriptorBitOneProjector Z * (descriptorBitOneProjector Z * A) := by rw [hAP1]
      _ = descriptorBitOneProjector Z * A := by rw [← Matrix.mul_assoc, descriptorBitOneProjector_square hZ2]
  have hmain :
      (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * A * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) =
        A * (descriptorBitZeroProjector Z - descriptorBitOneProjector Z) := by
    noncomm_ring [hX2, hXP0, hXP1, hAP0, hAP1, hXA,
      descriptorBitZeroProjector_square hZ2, descriptorBitOneProjector_square hZ2, descriptorBitZeroProjector_mul_one hZ2,
      descriptorBitOneProjector_mul_zero hZ2, hpp, hcross₀, hcross₁, hqq]
  rw [hmain, descriptorBitProjector_difference]
  noncomm_ring

theorem cnotFromDescriptors_mul_self {D : DescriptorFamily Q} {target control : Q}
    (hD : D.Valid) (hne : target ≠ control) :
    cnotFromDescriptors D target control * cnotFromDescriptors D target control = 1 := by
  let X := (D target).x
  let Z := (D control).z
  have hX2 : X * X = 1 := (hD.each target).x_mul_x
  have hZ2 : Z * Z = 1 := (hD.each control).z_mul_z
  have hXZ : X * Z = Z * X := hD.cross target control hne .x .z
  have hXP0 : X * descriptorBitZeroProjector Z = descriptorBitZeroProjector Z * X := commutes_descriptorBitZeroProjector hXZ
  have hXP1 : X * descriptorBitOneProjector Z = descriptorBitOneProjector Z * X := commutes_descriptorBitOneProjector hXZ
  have hcross₁ : descriptorBitOneProjector Z * (descriptorBitZeroProjector Z * X) = 0 := by
    rw [← Matrix.mul_assoc, descriptorBitOneProjector_mul_zero hZ2, zero_mul]
  have hcross₂ : descriptorBitZeroProjector Z * (descriptorBitOneProjector Z * X) = 0 := by
    rw [← Matrix.mul_assoc, descriptorBitZeroProjector_mul_one hZ2, zero_mul]
  have hlast : descriptorBitOneProjector Z * (X * (descriptorBitOneProjector Z * X)) = descriptorBitOneProjector Z := by
    calc
      descriptorBitOneProjector Z * (X * (descriptorBitOneProjector Z * X)) =
          (descriptorBitOneProjector Z * X) * (descriptorBitOneProjector Z * X) := by rw [Matrix.mul_assoc]
      _ = (X * descriptorBitOneProjector Z) * (X * descriptorBitOneProjector Z) := by rw [← hXP1]
      _ = (X * (descriptorBitOneProjector Z * X)) * descriptorBitOneProjector Z := by simp [Matrix.mul_assoc]
      _ = (X * (X * descriptorBitOneProjector Z)) * descriptorBitOneProjector Z := by rw [← hXP1]
      _ = X * X * (descriptorBitOneProjector Z * descriptorBitOneProjector Z) := by simp [Matrix.mul_assoc]
      _ = descriptorBitOneProjector Z := by rw [hX2, one_mul, descriptorBitOneProjector_square hZ2]
  change (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) = 1
  noncomm_ring [descriptorBitZeroProjector_square hZ2, descriptorBitOneProjector_square hZ2, descriptorBitZeroProjector_mul_one hZ2,
    descriptorBitOneProjector_mul_zero hZ2, hX2, hXP0, hXP1, hcross₁, hcross₂, hlast,
    descriptorBitProjector_sum Z]

theorem cnotFromDescriptors_isHermitian {D : DescriptorFamily Q} {target control : Q}
    (hD : D.Valid) (hne : target ≠ control) :
    (cnotFromDescriptors D target control).IsHermitian := by
  let X := (D target).x
  let Z := (D control).z
  have hX : X.IsHermitian := (hD.each target).x_isHermitian
  have hZ : Z.IsHermitian := (hD.each control).z_isHermitian
  have hXZ : X * Z = Z * X := hD.cross target control hne .x .z
  have hXP1 : X * descriptorBitOneProjector Z = descriptorBitOneProjector Z * X := commutes_descriptorBitOneProjector hXZ
  rw [Matrix.IsHermitian]
  change (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z)ᴴ = descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    (descriptorBitZeroProjector_isHermitian hZ).eq, (descriptorBitOneProjector_isHermitian hZ).eq, hX]
  rw [← hXP1]

theorem cnotFromDescriptors_unitary {D : DescriptorFamily Q} {target control : Q}
    (hD : D.Valid) (hne : target ≠ control) :
    cnotFromDescriptors D target control ∈ Matrix.unitaryGroup (Basis Q) Complex := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (cnotFromDescriptors D target control)ᴴ * cnotFromDescriptors D target control = 1
  rw [(cnotFromDescriptors_isHermitian hD hne).eq, cnotFromDescriptors_mul_self hD hne]

theorem cnotFromDescriptors_conjugates_target_y {D : DescriptorFamily Q} {target control : Q}
    (hD : D.Valid) (hne : target ≠ control) :
    heisenberg (cnotFromDescriptors D target control) (D target).y =
      -((D target).y * (D control).z) := by
  let X := (D target).x
  let Y := (D target).y
  let Z := (D control).z
  have hX2 : X * X = 1 := (hD.each target).x_mul_x
  have hZ2 : Z * Z = 1 := (hD.each control).z_mul_z
  have hXY : X * Y = -(Y * X) := by
    have hanti := (hD.each target).anticommutes_xy
    change X * Y + Y * X = 0 at hanti
    exact eq_neg_of_add_eq_zero_left hanti
  have hXZ : X * Z = Z * X := hD.cross target control hne .x .z
  have hYZ : Y * Z = Z * Y := hD.cross target control hne .y .z
  rw [Register.heisenberg, (cnotFromDescriptors_isHermitian hD hne).eq]
  change (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * Y * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) = -(Y * Z)
  exact conjugate_target_of_anticommutes hX2 hZ2 hXZ hYZ hXY

theorem cnotFromDescriptors_conjugates_target_x {D : DescriptorFamily Q} {target control : Q}
    (hD : D.Valid) (hne : target ≠ control) :
    heisenberg (cnotFromDescriptors D target control) (D target).x = (D target).x := by
  let X := (D target).x
  let Z := (D control).z
  have hXZ : X * Z = Z * X := hD.cross target control hne .x .z
  have hXP0 : X * descriptorBitZeroProjector Z = descriptorBitZeroProjector Z * X := commutes_descriptorBitZeroProjector hXZ
  have hXP1 : X * descriptorBitOneProjector Z = descriptorBitOneProjector Z * X := commutes_descriptorBitOneProjector hXZ
  have hcomm : (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * X = X * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) := by
    noncomm_ring [← hXP0, ← hXP1]
  rw [Register.heisenberg, (cnotFromDescriptors_isHermitian hD hne).eq]
  change (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * X * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) = X
  calc
    (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * X * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) =
        X * ((descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z)) := by
      rw [hcomm, Matrix.mul_assoc]
    _ = X := by
      have hsq := cnotFromDescriptors_mul_self hD hne
      change (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) = 1 at hsq
      rw [hsq, mul_one]

theorem cnotFromDescriptors_conjugates_target_z {D : DescriptorFamily Q} {target control : Q}
    (hD : D.Valid) (hne : target ≠ control) :
    heisenberg (cnotFromDescriptors D target control) (D target).z =
      -((D target).z * (D control).z) := by
  let X := (D target).x
  let A := (D target).z
  let Z := (D control).z
  have hX2 : X * X = 1 := (hD.each target).x_mul_x
  have hZ2 : Z * Z = 1 := (hD.each control).z_mul_z
  have hXA : X * A = -(A * X) := by
    have hanti := (hD.each target).anticommutes_zx
    change A * X + X * A = 0 at hanti
    exact eq_neg_of_add_eq_zero_right hanti
  have hXZ : X * Z = Z * X := hD.cross target control hne .x .z
  have hAZ : A * Z = Z * A := hD.cross target control hne .z .z
  rw [Register.heisenberg, (cnotFromDescriptors_isHermitian hD hne).eq]
  change (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * A * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) = -(A * Z)
  exact conjugate_target_of_anticommutes hX2 hZ2 hXZ hAZ hXA

theorem cnotFromDescriptors_conjugates_control_z {D : DescriptorFamily Q} {target control : Q}
    (hD : D.Valid) (hne : target ≠ control) :
    heisenberg (cnotFromDescriptors D target control) (D control).z = (D control).z := by
  let X := (D target).x
  let Z := (D control).z
  have hXZ : X * Z = Z * X := hD.cross target control hne .x .z
  have hZP0 : Z * descriptorBitZeroProjector Z = descriptorBitZeroProjector Z * Z := commutes_descriptorBitZeroProjector rfl
  have hZP1 : Z * descriptorBitOneProjector Z = descriptorBitOneProjector Z * Z := commutes_descriptorBitOneProjector rfl
  have hterm : X * (Z * descriptorBitOneProjector Z) = Z * (X * descriptorBitOneProjector Z) := by
    rw [← Matrix.mul_assoc, hXZ, Matrix.mul_assoc]
  have hcomm : (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * Z = Z * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) := by
    noncomm_ring [← hZP0, ← hZP1, hterm]
  rw [Register.heisenberg, (cnotFromDescriptors_isHermitian hD hne).eq]
  change (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * Z * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) = Z
  calc
    (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * Z * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) =
        Z * ((descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z)) := by
      rw [hcomm, Matrix.mul_assoc]
    _ = Z := by
      have hsq := cnotFromDescriptors_mul_self hD hne
      change (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) = 1 at hsq
      rw [hsq, mul_one]

theorem cnotFromDescriptors_conjugates_control_x {D : DescriptorFamily Q} {target control : Q}
    (hD : D.Valid) (hne : target ≠ control) :
    heisenberg (cnotFromDescriptors D target control) (D control).x =
      (D target).x * (D control).x := by
  let X := (D target).x
  let Z := (D control).z
  let B := (D control).x
  have hZ2 : Z * Z = 1 := (hD.each control).z_mul_z
  have hXZ : X * Z = Z * X := hD.cross target control hne .x .z
  have hXB : X * B = B * X := hD.cross target control hne .x .x
  have hZB : Z * B = -(B * Z) := by
    have hanti := (hD.each control).anticommutes_zx
    change Z * B + B * Z = 0 at hanti
    exact eq_neg_of_add_eq_zero_left hanti
  rw [Register.heisenberg, (cnotFromDescriptors_isHermitian hD hne).eq]
  change (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * B * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) = X * B
  exact conjugate_control_of_anticommutes hZ2 hXZ hXB hZB

theorem cnotFromDescriptors_conjugates_control_y {D : DescriptorFamily Q} {target control : Q}
    (hD : D.Valid) (hne : target ≠ control) :
    heisenberg (cnotFromDescriptors D target control) (D control).y =
      (D target).x * (D control).y := by
  let X := (D target).x
  let Z := (D control).z
  let B := (D control).y
  have hZ2 : Z * Z = 1 := (hD.each control).z_mul_z
  have hXZ : X * Z = Z * X := hD.cross target control hne .x .z
  have hXB : X * B = B * X := hD.cross target control hne .x .y
  have hZB : Z * B = -(B * Z) := by
    have hanti := (hD.each control).anticommutes_yz
    change B * Z + Z * B = 0 at hanti
    exact eq_neg_of_add_eq_zero_right hanti
  rw [Register.heisenberg, (cnotFromDescriptors_isHermitian hD hne).eq]
  change (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) * B * (descriptorBitZeroProjector Z + X * descriptorBitOneProjector Z) = X * B
  exact conjugate_control_of_anticommutes hZ2 hXZ hXB hZB

/-- The descriptor-dependent expression at the initial family is the named embedded CNOT. -/
theorem cnotFromDescriptors_initial_eq_cnotAt
    (target control : Q) (h : target ≠ control) :
    cnotFromDescriptors (DescriptorFamily.initial Q) target control =
      cnotAt target control h := by
  rw [cnotAt_eq_global_formula]
  change ((2 : Complex)⁻¹) • (1 - zAt control) +
      xAt target * (((2 : Complex)⁻¹) • (1 + zAt control)) =
    paperBitZeroProjectorAt control + xAt target * paperBitOneProjectorAt control
  rw [← paperBitZeroProjectorAt_eq, ← paperBitOneProjectorAt_eq]

/-- Descriptor-polynomial CNOT is equivariant under a shared unitary descriptor evolution. -/
theorem cnotFromDescriptors_evolve (D : DescriptorFamily Q)
    (U : Operator Q) (hU : U ∈ Matrix.unitaryGroup (Basis Q) Complex)
    (target control : Q) :
    cnotFromDescriptors (DescriptorFamily.evolve U D) target control =
      heisenberg U (cnotFromDescriptors D target control) := by
  unfold cnotFromDescriptors descriptorBitZeroProjector descriptorBitOneProjector
  simp only [DescriptorFamily.evolve_apply, Descriptor.evolve]
  rw [heisenberg_add, heisenberg_mul_of_unitary U _ _ hU,
    heisenberg_smul, heisenberg_sub, heisenberg_one_of_unitary U hU,
    heisenberg_smul, heisenberg_add, heisenberg_one_of_unitary U hU]

end
end Gates
end Deutsch
