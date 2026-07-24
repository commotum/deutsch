import Deutsch.Gates.Bell
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum

/-!
# Three-qubit teleportation correction

This module gives an explicit Clifford circuit for the transformation in Equation (33).
The paper's reversed raw-bit convention makes the two terminal `Z` factors necessary for the
displayed signs.  The three named coordinates remain generic, with pairwise distinctness supplied
explicitly.
-/

namespace Deutsch
namespace Teleportation

open Foundations Gates Locality Register
open scoped Matrix

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Controlled `Z` synthesized as `H_m CNOT(m,l) H_m` in Schrödinger product order. -/
def controlledZAt (l m : Q) (hlm : l ≠ m) : Operator Q :=
  hadamardAt m * cnotAt m l hlm.symm * hadamardAt m

theorem controlledZAt_unitary (l m : Q) (hlm : l ≠ m) :
    controlledZAt l m hlm ∈ Matrix.unitaryGroup (Basis Q) ℂ := by
  exact (Matrix.unitaryGroup (Basis Q) ℂ).mul_mem
    ((Matrix.unitaryGroup (Basis Q) ℂ).mul_mem
      (hadamardAt_unitary m) (cnotAt_unitary m l hlm.symm))
    (hadamardAt_unitary m)

theorem controlledZAt_isSupportedOn_pair (l m : Q) (hlm : l ≠ m) :
    IsSupportedOn {l, m} (controlledZAt l m hlm) := by
  have hH : IsSupportedOn {l, m} (hadamardAt m) :=
    hadamardAt_isSupportedOn_pair l m hlm
  have hC : IsSupportedOn {l, m} (cnotAt m l hlm.symm) := by
    simpa [Finset.pair_comm] using cnotAt_isSupportedOn_pair m l hlm.symm
  exact (hH.mul hC).mul hH

/-- Projector form of the controlled `Z`, exposing its computational-basis branches. -/
theorem controlledZAt_eq_global_formula (l m : Q) (hlm : l ≠ m) :
    controlledZAt l m hlm = paperBitZeroProjectorAt l +
      zAt m * paperBitOneProjectorAt l := by
  have hH2 : hadamardAt m * hadamardAt m = 1 :=
    hadamardAt_mul_self m
  have hHP0 : hadamardAt m * paperBitZeroProjectorAt l =
      paperBitZeroProjectorAt l * hadamardAt m := by
    exact embedQubit_commute_of_ne hlm.symm hadamard bitZeroProjector
  have hP1H : paperBitOneProjectorAt l * hadamardAt m =
      hadamardAt m * paperBitOneProjectorAt l := by
    exact embedQubit_commute_of_ne hlm bitOneProjector hadamard
  have hHXH : hadamardAt m * xAt m * hadamardAt m = zAt m := by
    have h := hadamardAt_heisenberg_x (Q := Q) m
    rw [Register.heisenberg, (hadamardAt_isHermitian m).eq] at h
    exact h
  rw [controlledZAt, cnotAt_eq_global_formula]
  rw [Matrix.mul_add, Matrix.add_mul]
  congr 1
  · calc
      hadamardAt m * paperBitZeroProjectorAt l * hadamardAt m =
          paperBitZeroProjectorAt l * hadamardAt m * hadamardAt m := by
            rw [hHP0]
      _ = paperBitZeroProjectorAt l := by
        rw [Matrix.mul_assoc, hH2, mul_one]
  · calc
      hadamardAt m * (xAt m * paperBitOneProjectorAt l) * hadamardAt m =
          (hadamardAt m * xAt m) *
            (paperBitOneProjectorAt l * hadamardAt m) := by
              simp only [Matrix.mul_assoc]
      _ = (hadamardAt m * xAt m) *
          (hadamardAt m * paperBitOneProjectorAt l) := by rw [hP1H]
      _ = (hadamardAt m * xAt m * hadamardAt m) *
          paperBitOneProjectorAt l := by simp only [Matrix.mul_assoc]
      _ = zAt m * paperBitOneProjectorAt l := by rw [hHXH]

/-- The `Z` eigenvalue of a raw basis index; raw `0` is paper bit `1`. -/
def rawZPhase (bit : QubitIndex) : ℂ :=
  if bit = 0 then 1 else -1

/-- The diagonal phase of `controlledZAt` on raw control/target indices. -/
def controlledZPhase (control target : QubitIndex) : ℂ :=
  if control = 0 then rawZPhase target else 1

private theorem embedQubit_act_basisKet_of_diagonal
    (q : Q) (A : QubitMatrix) (phase : QubitIndex → ℂ)
    (hA : ∀ i j, A i j = if i = j then phase j else 0)
    (input : Basis Q) :
    act (embedQubit q A) (basisKet input) =
      phase (input q) • basisKet input := by
  apply WithLp.ofLp_injective
  change embedQubit q A *ᵥ Pi.single input 1 =
    phase (input q) • Pi.single input 1
  rw [Matrix.mulVec_single_one]
  funext output
  change embedQubit q A output input =
    (phase (input q) • Pi.single input 1) output
  rw [embedQubit_apply_ite, hA]
  by_cases hout : output = input
  · subst output
    simp
  · have hsingle :
        (Pi.single input (1 : ℂ) : CoordinateVector Q) output = 0 := by
      simp [hout]
    change (if ∀ j, j ≠ q → output j = input j then
        if output q = input q then phase (input q) else 0 else 0) =
      phase (input q) *
        (Pi.single input (1 : ℂ) : CoordinateVector Q) output
    rw [hsingle, mul_zero]
    by_cases houtside : ∀ j, j ≠ q → output j = input j
    · rw [if_pos houtside]
      have hlocal : output q ≠ input q := by
        intro hq
        apply hout
        funext j
        by_cases hj : j = q
        · simpa [hj] using hq
        · exact houtside j hj
      rw [if_neg hlocal]
    · rw [if_neg houtside]

private theorem zAt_act_basisKet (q : Q) (input : Basis Q) :
    act (zAt q) (basisKet input) =
      rawZPhase (input q) • basisKet input := by
  apply embedQubit_act_basisKet_of_diagonal q pauliZ rawZPhase
  intro i j
  fin_cases i <;> fin_cases j <;> norm_num [pauliZ, rawZPhase]

private theorem paperBitZeroProjectorAt_act_basisKet
    (q : Q) (input : Basis Q) :
    act (paperBitZeroProjectorAt q) (basisKet input) =
      (if input q = 1 then (1 : ℂ) else 0) • basisKet input := by
  apply embedQubit_act_basisKet_of_diagonal q bitZeroProjector
    (fun bit ↦ if bit = 1 then 1 else 0)
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bitZeroProjector, identity₂, pauliZ]

private theorem paperBitOneProjectorAt_act_basisKet
    (q : Q) (input : Basis Q) :
    act (paperBitOneProjectorAt q) (basisKet input) =
      (if input q = 0 then (1 : ℂ) else 0) • basisKet input := by
  apply embedQubit_act_basisKet_of_diagonal q bitOneProjector
    (fun bit ↦ if bit = 0 then 1 else 0)
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [bitOneProjector, identity₂, pauliZ]

private theorem act_add_operator (A B : Operator Q) (psi : Ket Q) :
    act (A + B) psi = act A psi + act B psi := by
  change matrixEndEquiv Q (A + B) psi = _
  rw [map_add]
  rfl

/-- Direct computational-basis action of the synthesized controlled `Z`. -/
theorem controlledZAt_act_basisKet (l m : Q) (hlm : l ≠ m)
    (input : Basis Q) :
    act (controlledZAt l m hlm) (basisKet input) =
      controlledZPhase (input l) (input m) • basisKet input := by
  rw [controlledZAt_eq_global_formula, act_add_operator, act_mul,
    paperBitZeroProjectorAt_act_basisKet,
    paperBitOneProjectorAt_act_basisKet, act_smul,
    zAt_act_basisKet]
  generalize input l = left
  generalize input m = receiver
  fin_cases left <;> fin_cases receiver <;>
    simp [controlledZPhase, rawZPhase]

/--
An exact representative of Equation (33), determined by its Pauli action up to global phase.
Products are in Schrödinger order; the rightmost `Z_l` acts first.
-/
def correctionGate (k l m : Q) (_hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    Operator Q :=
  controlledZAt l m hlm * cnotAt m k hkm.symm * zAt k * zAt l

theorem correctionGate_unitary (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    correctionGate k l m hkl hkm hlm ∈
      Matrix.unitaryGroup (Basis Q) ℂ := by
  exact (Matrix.unitaryGroup (Basis Q) ℂ).mul_mem
    ((Matrix.unitaryGroup (Basis Q) ℂ).mul_mem
      ((Matrix.unitaryGroup (Basis Q) ℂ).mul_mem
        (controlledZAt_unitary l m hlm)
        (cnotAt_unitary m k hkm.symm))
      (zAt_unitary k))
    (zAt_unitary l)

/-- The complete correction circuit acts only on its two record qubits and receiver. -/
theorem correctionGate_isSupportedOn_triple (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    IsSupportedOn {k, l, m} (correctionGate k l m hkl hkm hlm) := by
  have hCZ : IsSupportedOn {k, l, m} (controlledZAt l m hlm) :=
    Register.IsSupportedOn.mono (controlledZAt_isSupportedOn_pair l m hlm) (by simp)
  have hCNOT : IsSupportedOn {k, l, m} (cnotAt m k hkm.symm) :=
    Register.IsSupportedOn.mono (cnotAt_isSupportedOn_pair m k hkm.symm) (by
      intro q hq
      rcases Finset.mem_insert.mp hq with hqm | hqk
      · subst q
        simp
      · have : q = k := Finset.mem_singleton.mp hqk
        subst q
        simp)
  have hZk : IsSupportedOn {k, l, m} (zAt k) :=
    Register.IsSupportedOn.mono (zAt_isSupportedOn k) (by simp)
  have hZl : IsSupportedOn {k, l, m} (zAt l) :=
    Register.IsSupportedOn.mono (zAt_isSupportedOn l) (by simp)
  exact ((hCZ.mul hCNOT).mul hZk).mul hZl

/-- Raw basis assignment after the record bit at `k` conditionally flips receiver `m`. -/
def correctionBasisOutput (k m : Q) (input : Basis Q) : Basis Q :=
  cnotOutput m k input

/--
Exact branch phase.  The first two factors are the terminal `Z_k Z_l` phase; the final
factor is the eigenvalue of the conditional receiver `Z^l` after the receiver `X^k`.
Here a raw record index `0` means paper/logical bit `1`.
-/
def correctionBasisPhase (k l m : Q) (input : Basis Q) : ℂ :=
  rawZPhase (input k) * rawZPhase (input l) *
    controlledZPhase (input l) (correctionBasisOutput k m input m)

omit [Fintype Q] in
@[simp] theorem correctionBasisOutput_control (k m : Q) (hkm : k ≠ m)
    (input : Basis Q) :
    correctionBasisOutput k m input k = input k := by
  exact cnotOutput_control hkm.symm input

omit [Fintype Q] in
@[simp] theorem correctionBasisOutput_remote (k l m : Q) (hlm : l ≠ m)
    (input : Basis Q) :
    correctionBasisOutput k m input l = input l := by
  exact cnotOutput_other input hlm

omit [Fintype Q] in
@[simp] theorem correctionBasisOutput_receiver (k m : Q) (input : Basis Q) :
    correctionBasisOutput k m input m =
      if input k = 0 then flipRaw (input m) else input m := by
  exact cnotOutput_target m k input

/--
Direct computational-basis semantics of Equation (33).  Both record coordinates are preserved;
on the receiver this is, up to the displayed `Z_k Z_l` basis phase, exactly `Z^l X^k`, where
the exponents are paper bits (raw index `0` means exponent `1`).
-/
theorem correctionGate_act_basisKet (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (input : Basis Q) :
    act (correctionGate k l m hkl hkm hlm) (basisKet input) =
      correctionBasisPhase k l m input •
        basisKet (correctionBasisOutput k m input) := by
  simp only [correctionGate, act_mul, zAt_act_basisKet, act_smul,
    cnotAt_act_basisKet, controlledZAt_act_basisKet, smul_smul,
    correctionBasisPhase, correctionBasisOutput]
  rw [cnotOutput_other input hlm]
  have hphase :
      rawZPhase (input l) *
          (rawZPhase (input k) *
            controlledZPhase (input l) (cnotOutput m k input m)) =
        (rawZPhase (input k) * rawZPhase (input l)) *
          controlledZPhase (input l) (cnotOutput m k input m) := by
    rw [← mul_assoc, mul_comm (rawZPhase (input l)) (rawZPhase (input k))]
  rw [hphase]

/-- Flip only receiver coordinate `m` in a raw computational-basis assignment. -/
def flipBasisAt (m : Q) (input : Basis Q) : Basis Q :=
  Function.update input m (flipRaw (input m))

/-- Paper record pair `(0,0)` is raw pair `(1,1)`: the receiver operation is `I`. -/
theorem correctionGate_branch_paper00 (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (input : Basis Q) (hk : input k = 1) (hl : input l = 1) :
    act (correctionGate k l m hkl hkm hlm) (basisKet input) =
      basisKet input := by
  rw [correctionGate_act_basisKet]
  simp [correctionBasisPhase, correctionBasisOutput, cnotOutput,
    rawZPhase, controlledZPhase, hk, hl]

/-- Paper record pair `(0,1)` is raw pair `(1,0)`: the receiver operation is `Z`. -/
theorem correctionGate_branch_paper01 (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (input : Basis Q) (hk : input k = 1) (hl : input l = 0) :
    act (correctionGate k l m hkl hkm hlm) (basisKet input) =
      (-rawZPhase (input m)) • basisKet input := by
  rw [correctionGate_act_basisKet]
  simp [correctionBasisPhase, correctionBasisOutput, cnotOutput,
    rawZPhase, controlledZPhase, hk, hl]
  generalize input m = receiver
  fin_cases receiver <;> simp

/-- Paper record pair `(1,0)` is raw pair `(0,1)`: the receiver operation is `X`. -/
theorem correctionGate_branch_paper10 (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (input : Basis Q) (hk : input k = 0) (hl : input l = 1) :
    act (correctionGate k l m hkl hkm hlm) (basisKet input) =
      (-1 : ℂ) • basisKet (flipBasisAt m input) := by
  rw [correctionGate_act_basisKet]
  simp [correctionBasisPhase, correctionBasisOutput, cnotOutput,
    flipBasisAt, rawZPhase, controlledZPhase, hk, hl]

/-- Paper record pair `(1,1)` is raw pair `(0,0)`: the receiver operation is `Z X`. -/
theorem correctionGate_branch_paper11 (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m)
    (input : Basis Q) (hk : input k = 0) (hl : input l = 0) :
    act (correctionGate k l m hkl hkm hlm) (basisKet input) =
      rawZPhase (flipRaw (input m)) •
        basisKet (flipBasisAt m input) := by
  rw [correctionGate_act_basisKet]
  simp [correctionBasisPhase, correctionBasisOutput, cnotOutput,
    flipBasisAt, rawZPhase, controlledZPhase, hk, hl]

private theorem pauliZ_heisenberg_x :
    Foundations.heisenberg pauliZ pauliX = -pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Foundations.heisenberg, pauliX, pauliZ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

private theorem pauliZ_heisenberg_y :
    Foundations.heisenberg pauliZ pauliY = -pauliY := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Foundations.heisenberg, pauliY, pauliZ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

private theorem pauliZ_heisenberg_z :
    Foundations.heisenberg pauliZ pauliZ = pauliZ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Foundations.heisenberg, pauliZ, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ]

private theorem zAt_heisenberg_x (q : Q) :
    heisenberg (zAt q) (xAt q) = -xAt q := by
  rw [zAt, xAt, heisenberg_embedQubit, pauliZ_heisenberg_x]
  simpa only [neg_smul, one_smul] using embedQubit_smul q (-1) pauliX

private theorem zAt_heisenberg_y (q : Q) :
    heisenberg (zAt q) (yAt q) = -yAt q := by
  rw [zAt, yAt, heisenberg_embedQubit, pauliZ_heisenberg_y]
  simpa only [neg_smul, one_smul] using embedQubit_smul q (-1) pauliY

private theorem zAt_heisenberg_z (q : Q) :
    heisenberg (zAt q) (zAt q) = zAt q := by
  rw [zAt, heisenberg_embedQubit, pauliZ_heisenberg_z]

private theorem zAt_heisenberg_remote (q r : Q) (hqr : q ≠ r)
    (A : QubitMatrix) :
    heisenberg (zAt q) (embedQubit r A) = embedQubit r A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by simp [hqr]) (zAt_unitary q) (zAt_isSupportedOn q)
    (embedQubit_isSupportedOn r A)

private theorem cnotAt_heisenberg_remote
    (target control remote : Q) (htc : target ≠ control)
    (hrt : remote ≠ target) (hrc : remote ≠ control) (A : QubitMatrix) :
    heisenberg (cnotAt target control htc) (embedQubit remote A) =
      embedQubit remote A := by
  exact heisenberg_eq_self_of_disjoint_support
    (by simp [hrt, hrc])
    (cnotAt_unitary target control htc)
    (cnotAt_isSupportedOn_pair target control htc)
    (embedQubit_isSupportedOn remote A)

theorem controlledZAt_heisenberg_remote (l m q : Q)
    (hlm : l ≠ m) (hql : q ≠ l) (hqm : q ≠ m) (A : QubitMatrix) :
    heisenberg (controlledZAt l m hlm) (embedQubit q A) =
      embedQubit q A := by
  rw [controlledZAt, heisenberg_chronology, heisenberg_chronology,
    hadamardAt_heisenberg_remote q m hqm,
    cnotAt_heisenberg_remote m l q hlm.symm hqm hql,
    hadamardAt_heisenberg_remote q m hqm]

private theorem zAt_heisenberg_remote_x (q r : Q) (hqr : q ≠ r) :
    heisenberg (zAt q) (xAt r) = xAt r :=
  zAt_heisenberg_remote q r hqr pauliX

private theorem zAt_heisenberg_remote_y (q r : Q) (hqr : q ≠ r) :
    heisenberg (zAt q) (yAt r) = yAt r :=
  zAt_heisenberg_remote q r hqr pauliY

private theorem zAt_heisenberg_remote_z (q r : Q) (hqr : q ≠ r) :
    heisenberg (zAt q) (zAt r) = zAt r :=
  zAt_heisenberg_remote q r hqr pauliZ

private theorem cnotAt_heisenberg_remote_x
    (target control remote : Q) (htc : target ≠ control)
    (hrt : remote ≠ target) (hrc : remote ≠ control) :
    heisenberg (cnotAt target control htc) (xAt remote) = xAt remote :=
  cnotAt_heisenberg_remote target control remote htc hrt hrc pauliX

private theorem cnotAt_heisenberg_remote_y
    (target control remote : Q) (htc : target ≠ control)
    (hrt : remote ≠ target) (hrc : remote ≠ control) :
    heisenberg (cnotAt target control htc) (yAt remote) = yAt remote :=
  cnotAt_heisenberg_remote target control remote htc hrt hrc pauliY

private theorem cnotAt_heisenberg_remote_z
    (target control remote : Q) (htc : target ≠ control)
    (hrt : remote ≠ target) (hrc : remote ≠ control) :
    heisenberg (cnotAt target control htc) (zAt remote) = zAt remote :=
  cnotAt_heisenberg_remote target control remote htc hrt hrc pauliZ

private theorem controlledZAt_heisenberg_remote_x (l m q : Q)
    (hlm : l ≠ m) (hql : q ≠ l) (hqm : q ≠ m) :
    heisenberg (controlledZAt l m hlm) (xAt q) = xAt q :=
  controlledZAt_heisenberg_remote l m q hlm hql hqm pauliX

private theorem controlledZAt_heisenberg_remote_y (l m q : Q)
    (hlm : l ≠ m) (hql : q ≠ l) (hqm : q ≠ m) :
    heisenberg (controlledZAt l m hlm) (yAt q) = yAt q :=
  controlledZAt_heisenberg_remote l m q hlm hql hqm pauliY

private theorem controlledZAt_heisenberg_remote_z (l m q : Q)
    (hlm : l ≠ m) (hql : q ≠ l) (hqm : q ≠ m) :
    heisenberg (controlledZAt l m hlm) (zAt q) = zAt q :=
  controlledZAt_heisenberg_remote l m q hlm hql hqm pauliZ

theorem controlledZAt_conjugates_left_x (l m : Q) (hlm : l ≠ m) :
    heisenberg (controlledZAt l m hlm) (xAt l) = xAt l * zAt m := by
  rw [controlledZAt, heisenberg_chronology, heisenberg_chronology,
    hadamardAt_heisenberg_remote_x l m hlm,
    cnotAt_conjugates_control_x,
    heisenberg_mul_of_unitary _ _ _ (hadamardAt_unitary m),
    hadamardAt_heisenberg_x,
    hadamardAt_heisenberg_remote_x l m hlm]
  exact embedQubit_commute_of_ne hlm.symm pauliZ pauliX

theorem controlledZAt_conjugates_left_y (l m : Q) (hlm : l ≠ m) :
    heisenberg (controlledZAt l m hlm) (yAt l) = yAt l * zAt m := by
  rw [controlledZAt, heisenberg_chronology, heisenberg_chronology,
    hadamardAt_heisenberg_remote_y l m hlm,
    cnotAt_conjugates_control_y,
    heisenberg_mul_of_unitary _ _ _ (hadamardAt_unitary m),
    hadamardAt_heisenberg_x,
    hadamardAt_heisenberg_remote_y l m hlm]
  exact embedQubit_commute_of_ne hlm.symm pauliZ pauliY

theorem controlledZAt_conjugates_left_z (l m : Q) (hlm : l ≠ m) :
    heisenberg (controlledZAt l m hlm) (zAt l) = zAt l := by
  rw [controlledZAt, heisenberg_chronology, heisenberg_chronology,
    hadamardAt_heisenberg_remote_z l m hlm,
    cnotAt_conjugates_control_z,
    hadamardAt_heisenberg_remote_z l m hlm]

theorem controlledZAt_conjugates_right_x (l m : Q) (hlm : l ≠ m) :
    heisenberg (controlledZAt l m hlm) (xAt m) = -(zAt l * xAt m) := by
  rw [controlledZAt, heisenberg_chronology, heisenberg_chronology,
    hadamardAt_heisenberg_x, cnotAt_conjugates_target_z,
    heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (hadamardAt_unitary m),
    hadamardAt_heisenberg_z,
    hadamardAt_heisenberg_remote_z l m hlm]
  congr 1
  exact embedQubit_commute_of_ne hlm.symm pauliX pauliZ

theorem controlledZAt_conjugates_right_y (l m : Q) (hlm : l ≠ m) :
    heisenberg (controlledZAt l m hlm) (yAt m) = -(zAt l * yAt m) := by
  rw [controlledZAt, heisenberg_chronology, heisenberg_chronology,
    hadamardAt_heisenberg_y, heisenberg_neg,
    cnotAt_conjugates_target_y]
  simp only [neg_neg]
  rw [heisenberg_mul_of_unitary _ _ _ (hadamardAt_unitary m),
    hadamardAt_heisenberg_y,
    hadamardAt_heisenberg_remote_z l m hlm, neg_mul]
  congr 1
  exact embedQubit_commute_of_ne hlm.symm pauliY pauliZ

theorem controlledZAt_conjugates_right_z (l m : Q) (hlm : l ≠ m) :
    heisenberg (controlledZAt l m hlm) (zAt m) = zAt m := by
  rw [controlledZAt, heisenberg_chronology, heisenberg_chronology,
    hadamardAt_heisenberg_z, cnotAt_conjugates_target_x,
    hadamardAt_heisenberg_x]

/-! ## Equation (33): all nine Pauli generators -/

theorem equation33_k_x (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    heisenberg (correctionGate k l m hkl hkm hlm) (xAt k) =
      -(xAt k * xAt m) := by
  rw [correctionGate, heisenberg_chronology, heisenberg_chronology,
    heisenberg_chronology,
    controlledZAt_heisenberg_remote_x l m k hlm hkl hkm,
    cnotAt_conjugates_control_x,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary k),
    zAt_heisenberg_remote_x k m hkm, zAt_heisenberg_x,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary l),
    zAt_heisenberg_remote_x l m hlm, heisenberg_neg,
    zAt_heisenberg_remote_x l k hkl.symm]
  have hcomm : xAt m * xAt k = xAt k * xAt m :=
    embedQubit_commute_of_ne hkm.symm pauliX pauliX
  noncomm_ring [hcomm]

theorem equation33_k_y (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    heisenberg (correctionGate k l m hkl hkm hlm) (yAt k) =
      -(yAt k * xAt m) := by
  rw [correctionGate, heisenberg_chronology, heisenberg_chronology,
    heisenberg_chronology,
    controlledZAt_heisenberg_remote_y l m k hlm hkl hkm,
    cnotAt_conjugates_control_y,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary k),
    zAt_heisenberg_remote_x k m hkm, zAt_heisenberg_y,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary l),
    zAt_heisenberg_remote_x l m hlm, heisenberg_neg,
    zAt_heisenberg_remote_y l k hkl.symm]
  have hcomm : xAt m * yAt k = yAt k * xAt m :=
    embedQubit_commute_of_ne hkm.symm pauliX pauliY
  noncomm_ring [hcomm]

theorem equation33_k_z (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    heisenberg (correctionGate k l m hkl hkm hlm) (zAt k) = zAt k := by
  rw [correctionGate, heisenberg_chronology, heisenberg_chronology,
    heisenberg_chronology,
    controlledZAt_heisenberg_remote_z l m k hlm hkl hkm,
    cnotAt_conjugates_control_z, zAt_heisenberg_z,
    zAt_heisenberg_remote_z l k hkl.symm]

theorem equation33_l_x (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    heisenberg (correctionGate k l m hkl hkm hlm) (xAt l) =
      zAt k * xAt l * zAt m := by
  rw [correctionGate, heisenberg_chronology, heisenberg_chronology,
    heisenberg_chronology, controlledZAt_conjugates_left_x,
    heisenberg_mul_of_unitary _ _ _ (cnotAt_unitary m k hkm.symm),
    cnotAt_heisenberg_remote_x m k l hkm.symm hlm hkl.symm,
    cnotAt_conjugates_target_z,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary k),
    zAt_heisenberg_remote_x k l hkl, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary k),
    zAt_heisenberg_remote_z k m hkm, zAt_heisenberg_z,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary l),
    zAt_heisenberg_x, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary l),
    zAt_heisenberg_remote_z l m hlm,
    zAt_heisenberg_remote_z l k hkl.symm]
  have h_lk : xAt l * zAt k = zAt k * xAt l :=
    embedQubit_commute_of_ne hkl.symm pauliX pauliZ
  have h_mk : zAt m * zAt k = zAt k * zAt m :=
    embedQubit_commute_of_ne hkm.symm pauliZ pauliZ
  simp only [neg_mul, mul_neg, neg_neg]
  rw [Matrix.mul_assoc, h_mk, ← Matrix.mul_assoc, h_lk]
  exact Matrix.mul_assoc _ _ _

theorem equation33_l_y (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    heisenberg (correctionGate k l m hkl hkm hlm) (yAt l) =
      zAt k * yAt l * zAt m := by
  rw [correctionGate, heisenberg_chronology, heisenberg_chronology,
    heisenberg_chronology, controlledZAt_conjugates_left_y,
    heisenberg_mul_of_unitary _ _ _ (cnotAt_unitary m k hkm.symm),
    cnotAt_heisenberg_remote_y m k l hkm.symm hlm hkl.symm,
    cnotAt_conjugates_target_z,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary k),
    zAt_heisenberg_remote_y k l hkl, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary k),
    zAt_heisenberg_remote_z k m hkm, zAt_heisenberg_z,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary l),
    zAt_heisenberg_y, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary l),
    zAt_heisenberg_remote_z l m hlm,
    zAt_heisenberg_remote_z l k hkl.symm]
  have h_lk : yAt l * zAt k = zAt k * yAt l :=
    embedQubit_commute_of_ne hkl.symm pauliY pauliZ
  have h_mk : zAt m * zAt k = zAt k * zAt m :=
    embedQubit_commute_of_ne hkm.symm pauliZ pauliZ
  simp only [neg_mul, mul_neg, neg_neg]
  rw [Matrix.mul_assoc, h_mk, ← Matrix.mul_assoc, h_lk]
  exact Matrix.mul_assoc _ _ _

theorem equation33_l_z (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    heisenberg (correctionGate k l m hkl hkm hlm) (zAt l) = zAt l := by
  rw [correctionGate, heisenberg_chronology, heisenberg_chronology,
    heisenberg_chronology, controlledZAt_conjugates_left_z,
    cnotAt_heisenberg_remote_z m k l hkm.symm hlm hkl.symm,
    zAt_heisenberg_remote_z k l hkl, zAt_heisenberg_z]

theorem equation33_m_x (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    heisenberg (correctionGate k l m hkl hkm hlm) (xAt m) =
      -(zAt l * xAt m) := by
  rw [correctionGate, heisenberg_chronology, heisenberg_chronology,
    heisenberg_chronology, controlledZAt_conjugates_right_x,
    heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (cnotAt_unitary m k hkm.symm),
    cnotAt_heisenberg_remote_z m k l hkm.symm hlm hkl.symm,
    cnotAt_conjugates_target_x, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary k),
    zAt_heisenberg_remote_z k l hkl,
    zAt_heisenberg_remote_x k m hkm, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary l),
    zAt_heisenberg_z, zAt_heisenberg_remote_x l m hlm]

theorem equation33_m_y (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    heisenberg (correctionGate k l m hkl hkm hlm) (yAt m) =
      zAt k * zAt l * yAt m := by
  rw [correctionGate, heisenberg_chronology, heisenberg_chronology,
    heisenberg_chronology, controlledZAt_conjugates_right_y,
    heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (cnotAt_unitary m k hkm.symm),
    cnotAt_heisenberg_remote_z m k l hkm.symm hlm hkl.symm,
    cnotAt_conjugates_target_y]
  simp only [mul_neg, neg_neg]
  rw [heisenberg_mul_of_unitary _ _ _ (zAt_unitary k),
    zAt_heisenberg_remote_z k l hkl,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary k),
    zAt_heisenberg_remote_y k m hkm, zAt_heisenberg_z,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary l),
    zAt_heisenberg_z,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary l),
    zAt_heisenberg_remote_y l m hlm,
    zAt_heisenberg_remote_z l k hkl.symm]
  have h_mk : yAt m * zAt k = zAt k * yAt m :=
    embedQubit_commute_of_ne hkm.symm pauliY pauliZ
  have h_lk : zAt l * zAt k = zAt k * zAt l :=
    embedQubit_commute_of_ne hkl.symm pauliZ pauliZ
  rw [h_mk, ← Matrix.mul_assoc, h_lk]

theorem equation33_m_z (k l m : Q)
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) :
    heisenberg (correctionGate k l m hkl hkm hlm) (zAt m) =
      -(zAt k * zAt m) := by
  rw [correctionGate, heisenberg_chronology, heisenberg_chronology,
    heisenberg_chronology, controlledZAt_conjugates_right_z,
    cnotAt_conjugates_target_z, heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary k),
    zAt_heisenberg_remote_z k m hkm, zAt_heisenberg_z,
    heisenberg_neg,
    heisenberg_mul_of_unitary _ _ _ (zAt_unitary l),
    zAt_heisenberg_remote_z l m hlm,
    zAt_heisenberg_remote_z l k hkl.symm]
  congr 1
  exact embedQubit_commute_of_ne hkm.symm pauliZ pauliZ

end
end Teleportation
end Deutsch
