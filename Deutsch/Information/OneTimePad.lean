import Deutsch.Information.Dependence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Classical one-time-pad information boundary

This two-qubit density family separates four notions that the source prose can blur. Either
single-qubit marginal is independent of the secret, a joint parity effect detects it, a finite
Kraus channel recovers it exactly, and explicitly supplied preparation histories can differ while
realizing the same final density family.
-/

namespace Deutsch
namespace Information

open Foundations Register
open scoped ComplexOrder Matrix MatrixOrder BigOperators

noncomputable section

/-- The classical one-time-pad basis word `(key, key + secret)` on two qubits. -/
def oneTimePadBasis (secret key : QubitIndex) : Basis (Fin 2) :=
  ![key, key + secret]

/-- The encoded secret, uniformly mixed over the two possible keys. -/
def oneTimePadDensity (secret : QubitIndex) : Density (Fin 2) where
  op := (2 : ℂ)⁻¹ • (basisDensity (oneTimePadBasis secret 0)).op +
    (2 : ℂ)⁻¹ • (basisDensity (oneTimePadBasis secret 1)).op
  positive := by
    apply Matrix.PosSemidef.add
    · exact (basisDensity (oneTimePadBasis secret 0)).positive.smul (by
        norm_num [Complex.nonneg_iff])
    · exact (basisDensity (oneTimePadBasis secret 1)).positive.smul (by
        norm_num [Complex.nonneg_iff])
  trace_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      (basisDensity (oneTimePadBasis secret 0)).trace_one,
      (basisDensity (oneTimePadBasis secret 1)).trace_one]
    norm_num

@[simp]
theorem oneTimePadDensity_op (secret : QubitIndex) :
    (oneTimePadDensity secret).op =
      (2 : ℂ)⁻¹ • (basisDensity (oneTimePadBasis secret 0)).op +
        (2 : ℂ)⁻¹ • (basisDensity (oneTimePadBasis secret 1)).op := rfl

/-- The symmetric construction with ciphertext and key coordinates exchanged. -/
def swappedOneTimePadBasis (secret key : QubitIndex) : Basis (Fin 2) :=
  ![key + secret, key]

/-- The uniform mixture obtained from the swapped construction route. -/
def swappedOneTimePadDensity (secret : QubitIndex) : Density (Fin 2) where
  op := (2 : ℂ)⁻¹ • (basisDensity (swappedOneTimePadBasis secret 0)).op +
    (2 : ℂ)⁻¹ • (basisDensity (swappedOneTimePadBasis secret 1)).op
  positive := by
    apply Matrix.PosSemidef.add
    · exact (basisDensity (swappedOneTimePadBasis secret 0)).positive.smul (by
        norm_num [Complex.nonneg_iff])
    · exact (basisDensity (swappedOneTimePadBasis secret 1)).positive.smul (by
        norm_num [Complex.nonneg_iff])
  trace_one := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul,
      (basisDensity (swappedOneTimePadBasis secret 0)).trace_one,
      (basisDensity (swappedOneTimePadBasis secret 1)).trace_one]
    norm_num

/-- Exchanging the key/ciphertext construction order leaves the final density family unchanged. -/
theorem swappedOneTimePadDensity_eq (secret : QubitIndex) :
    swappedOneTimePadDensity secret = oneTimePadDensity secret := by
  apply Density.ext
  fin_cases secret
  · rfl
  · change
      (2 : ℂ)⁻¹ • (basisDensity ![1, 0]).op +
          (2 : ℂ)⁻¹ • (basisDensity ![0, 1]).op =
        (2 : ℂ)⁻¹ • (basisDensity ![0, 1]).op +
          (2 : ℂ)⁻¹ • (basisDensity ![1, 0]).op
    exact add_comm _ _

/-- The maximally mixed density on a named singleton subsystem. -/
def singletonMaximallyMixed (q : Fin 2) :
    Density {r : Fin 2 // r ∈ ({q} : Finset (Fin 2))} where
  op := Matrix.diagonal (fun _ ↦ (2 : ℂ)⁻¹)
  positive := by
    apply Matrix.PosSemidef.diagonal
    intro i
    norm_num [Complex.nonneg_iff]
  trace_one := by
    simp [Matrix.trace]

/-- Either individual ciphertext qubit is exactly maximally mixed. -/
theorem oneTimePadDensity_reduce_singleton (secret : QubitIndex) (q : Fin 2) :
    (oneTimePadDensity secret).reduce ({q} : Finset (Fin 2)) =
      singletonMaximallyMixed q := by
  apply Density.ext
  rw [Density.reduce_op, oneTimePadDensity_op, partialTrace_add,
    partialTrace_smul, partialTrace_smul,
    partialTrace_basisDensity, partialTrace_basisDensity]
  let e := singletonBasisEquiv q
  have hrestrict (key : QubitIndex) :
      (fun r : {r : Fin 2 // r ∈ ({q} : Finset (Fin 2))} ↦
        oneTimePadBasis secret key r.1) =
        e (oneTimePadBasis secret key q) := by
    funext r
    have hr : r.1 = q := Finset.mem_singleton.mp r.2
    change oneTimePadBasis secret key r.1 = oneTimePadBasis secret key q
    rw [hr]
  rw [hrestrict 0, hrestrict 1]
  ext i j
  rw [← e.apply_symm_apply i, ← e.apply_symm_apply j]
  generalize e.symm i = a
  generalize e.symm j = b
  fin_cases q <;> fin_cases secret <;> fin_cases a <;> fin_cases b <;>
    norm_num [singletonMaximallyMixed, oneTimePadBasis, Pi.single, Fin.add_def]

/-- Every local effect statistic on either single qubit is secret-independent. -/
theorem oneTimePad_locallyStatisticsIndependent (q : Fin 2) :
    LocallyStatisticsIndependent ({q} : Finset (Fin 2)) oneTimePadDensity := by
  intro secret secret'
  apply effectStatisticallyEquivalent_of_eq
  rw [oneTimePadDensity_reduce_singleton, oneTimePadDensity_reduce_singleton]

/-- Raw mod-two parity of a two-qubit computational basis word. -/
def twoQubitParity (bits : Basis (Fin 2)) : QubitIndex :=
  bits 0 + bits 1

@[simp]
theorem oneTimePadBasis_parity (secret key : QubitIndex) :
    twoQubitParity (oneTimePadBasis secret key) = secret := by
  fin_cases secret <;> fin_cases key <;>
    norm_num [twoQubitParity, oneTimePadBasis, Fin.add_def]

/-- The joint computational effect selecting a specified parity sector. -/
def parityEffect (observed : QubitIndex) : Effect (Fin 2) where
  op := Matrix.diagonal (fun bits ↦
    if twoQubitParity bits = observed then (1 : ℂ) else 0)
  positive := by
    apply Matrix.PosSemidef.diagonal
    intro bits
    change 0 ≤ (if twoQubitParity bits = observed then (1 : ℂ) else 0)
    split_ifs <;> norm_num [Complex.nonneg_iff]
  complement_positive := by
    rw [show 1 - Matrix.diagonal (fun bits ↦
          if twoQubitParity bits = observed then (1 : ℂ) else 0) =
        Matrix.diagonal (fun bits ↦
          if twoQubitParity bits = observed then (0 : ℂ) else 1) by
      ext i j
      by_cases hij : i = j
      · subst j
        by_cases h : twoQubitParity i = observed <;> simp [h]
      · simp [Matrix.diagonal, hij]]
    apply Matrix.PosSemidef.diagonal
    intro bits
    change 0 ≤ (if twoQubitParity bits = observed then (0 : ℂ) else 1)
    split_ifs <;> norm_num [Complex.nonneg_iff]

@[simp]
theorem parityEffect_op (observed : QubitIndex) :
    (parityEffect observed).op = Matrix.diagonal (fun bits ↦
      if twoQubitParity bits = observed then (1 : ℂ) else 0) := rfl

private theorem trace_basisDensity_mul_parityEffect
    (prepared : Basis (Fin 2)) (observed : QubitIndex) :
    Matrix.trace ((basisDensity prepared).op * (parityEffect observed).op) =
      if twoQubitParity prepared = observed then 1 else 0 := by
  classical
  simp only [basisDensity, parityEffect, Matrix.trace,
    Matrix.diagonal_mul_diagonal, Matrix.diag, Pi.single_apply]
  by_cases h : twoQubitParity prepared = observed
  · rw [Fintype.sum_eq_single prepared]
    · simp [h]
    · intro i hi
      simp [hi]
  · rw [Finset.sum_eq_zero]
    · simp [h]
    · intro i hi
      by_cases hip : i = prepared
      · subst i
        simp [h]
      · simp [hip]

/-- The parity measurement recovers the encoded secret with probability one. -/
theorem oneTimePadDensity_parity_probability (secret observed : QubitIndex) :
    bornProbability (oneTimePadDensity secret) (parityEffect observed) =
      if secret = observed then 1 else 0 := by
  simp only [bornProbability, bornWeight, oneTimePadDensity_op,
    Matrix.add_mul, Matrix.smul_mul, Matrix.trace_add, Matrix.trace_smul]
  rw [trace_basisDensity_mul_parityEffect,
    trace_basisDensity_mul_parityEffect,
    oneTimePadBasis_parity, oneTimePadBasis_parity]
  by_cases h : secret = observed
  · simp [h]
    norm_num [Complex.inv_def]
  · simp [h]

/-- The two encoded density operators are jointly weakly distinguishable. -/
theorem oneTimePadDensity_weaklyDistinguishable :
    WeaklyDistinguishable (oneTimePadDensity 0) (oneTimePadDensity 1) := by
  refine ⟨parityEffect 0, ?_⟩
  rw [oneTimePadDensity_parity_probability,
    oneTimePadDensity_parity_probability]
  norm_num

/-- The secret-indexed family is detectable by a joint measurement. -/
theorem oneTimePad_statisticallyDetectable :
    StatisticallyDetectable oneTimePadDensity :=
  ⟨0, 1, oneTimePadDensity_weaklyDistinguishable⟩

/-- The one-qubit basis word carrying a decoded raw bit. -/
def oneTimePadDecodedBasis (secret : QubitIndex) : Basis (Fin 1) :=
  fun _ ↦ secret

/-- One rank-one Kraus operator for each input computational basis word. -/
def parityDecoderKraus (word : Basis (Fin 2)) :
    Matrix (Basis (Fin 1)) (Basis (Fin 2)) ℂ :=
  Matrix.single (oneTimePadDecodedBasis (twoQubitParity word)) word 1

private theorem parityDecoderKraus_star_mul (word : Basis (Fin 2)) :
    (parityDecoderKraus word)ᴴ * parityDecoderKraus word =
      Matrix.single word word 1 := by
  classical
  ext i j
  simp only [parityDecoderKraus, Matrix.conjTranspose_apply,
    Matrix.mul_apply, Matrix.single]
  by_cases hi : word = i <;> by_cases hj : word = j
  · subst i
    subst j
    simp
  · have hij : i ≠ j := fun h ↦ hj (hi.trans h)
    simp [hi, hij]
  · have hij : i ≠ j := fun h ↦ hi (hj.trans h.symm)
    simp [hj]
  · simp [hi, hj]

/-- Computational-basis parity measurement followed by preparation of its one-qubit value. -/
def parityDecoder : KrausChannel (Fin 2) (Fin 1) (Basis (Fin 2)) where
  kraus := parityDecoderKraus
  complete := by
    classical
    simp_rw [parityDecoderKraus_star_mul]
    exact Matrix.sum_single_one

private theorem parityDecoderKraus_mul_basisDensity
    (word prepared : Basis (Fin 2)) :
    parityDecoderKraus word * (basisDensity prepared).op *
        (parityDecoderKraus word)ᴴ =
      if word = prepared then
        (basisDensity (oneTimePadDecodedBasis (twoQubitParity prepared))).op
      else 0 := by
  classical
  rw [show (basisDensity prepared).op = Matrix.single prepared prepared 1 by
    exact Matrix.diagonal_single prepared 1]
  rw [show (basisDensity (oneTimePadDecodedBasis (twoQubitParity prepared))).op =
      Matrix.single (oneTimePadDecodedBasis (twoQubitParity prepared))
        (oneTimePadDecodedBasis (twoQubitParity prepared)) 1 by
    exact Matrix.diagonal_single (oneTimePadDecodedBasis (twoQubitParity prepared)) 1]
  by_cases h : word = prepared
  · subst word
    simp [parityDecoderKraus]
  · simp [parityDecoderKraus, h]

private theorem parityDecoder_map_basisDensity (prepared : Basis (Fin 2)) :
    parityDecoder.mapDensity (basisDensity prepared) =
      basisDensity (oneTimePadDecodedBasis (twoQubitParity prepared)) := by
  apply Density.ext
  classical
  change (∑ word : Basis (Fin 2),
      parityDecoderKraus word * (basisDensity prepared).op *
        (parityDecoderKraus word)ᴴ) =
    (basisDensity (oneTimePadDecodedBasis (twoQubitParity prepared))).op
  simp_rw [parityDecoderKraus_mul_basisDensity]
  simp

/-- The finite Kraus decoder exactly recovers the encoded secret bit. -/
theorem parityDecoder_recovers_density (secret : QubitIndex) :
    parityDecoder.mapDensity (oneTimePadDensity secret) =
      basisDensity (oneTimePadDecodedBasis secret) := by
  apply Density.ext
  change parityDecoder.mapOperator (oneTimePadDensity secret).op =
    (basisDensity (oneTimePadDecodedBasis secret)).op
  rw [oneTimePadDensity_op, parityDecoder.mapOperator_add,
    parityDecoder.mapOperator_smul, parityDecoder.mapOperator_smul]
  have h0 := congrArg Density.op
    (parityDecoder_map_basisDensity (oneTimePadBasis secret 0))
  have h1 := congrArg Density.op
    (parityDecoder_map_basisDensity (oneTimePadBasis secret 1))
  change parityDecoder.mapOperator (basisDensity (oneTimePadBasis secret 0)).op =
    (basisDensity (oneTimePadDecodedBasis
      (twoQubitParity (oneTimePadBasis secret 0)))).op at h0
  change parityDecoder.mapOperator (basisDensity (oneTimePadBasis secret 1)).op =
    (basisDensity (oneTimePadDecodedBasis
      (twoQubitParity (oneTimePadBasis secret 1)))).op at h1
  rw [h0, h1, oneTimePadBasis_parity, oneTimePadBasis_parity]
  rw [← add_smul]
  norm_num

/-- Recovery in the semantic `Recovers` API. -/
theorem parityDecoder_recovers :
    Recovers parityDecoder.mapDensity oneTimePadDensity
      (fun secret ↦ basisDensity (oneTimePadDecodedBasis secret)) := by
  intro secret
  exact parityDecoder_recovers_density secret

/-- Explicit provenance for two construction routes to the same encoded family. -/
structure OneTimePadHistory where
  route : Bool
  secret : QubitIndex
  deriving DecidableEq

/-- Interpret the route bit as the original or coordinate-swapped construction formula. -/
def oneTimePadHistoryDensity (history : OneTimePadHistory) : Density (Fin 2) :=
  if history.route then swappedOneTimePadDensity history.secret
  else oneTimePadDensity history.secret

/-- The first explicit preparation history for the encoded family. -/
def oneTimePadPreparationLeft :
    Preparation oneTimePadDensity OneTimePadHistory where
  history secret := ⟨false, secret⟩
  realize := oneTimePadHistoryDensity
  realizes _secret := by simp [oneTimePadHistoryDensity]

/-- A distinct explicit preparation history with the same realized density family. -/
def oneTimePadPreparationRight :
    Preparation oneTimePadDensity OneTimePadHistory where
  history secret := ⟨true, secret⟩
  realize := oneTimePadHistoryDensity
  realizes secret := by simp [oneTimePadHistoryDensity, swappedOneTimePadDensity_eq]

/-- The two supplied histories differ, even though their realized final density agrees. -/
theorem oneTimePad_preparation_histories_distinct (secret : QubitIndex) :
    oneTimePadPreparationLeft.history secret ≠
      oneTimePadPreparationRight.history secret := by
  intro h
  have hroute := congrArg OneTimePadHistory.route h
  simp [oneTimePadPreparationLeft, oneTimePadPreparationRight] at hroute

/-- Both explicit histories realize exactly the same member of the final family. -/
theorem oneTimePad_preparations_same_final_density (secret : QubitIndex) :
    oneTimePadPreparationLeft.realize
        (oneTimePadPreparationLeft.history secret) =
      oneTimePadPreparationRight.realize
        (oneTimePadPreparationRight.history secret) := by
  simp [oneTimePadPreparationLeft, oneTimePadPreparationRight,
    oneTimePadHistoryDensity, swappedOneTimePadDensity_eq]

theorem oneTimePadPreparationLeft_provenanceNonconstant :
    oneTimePadPreparationLeft.ProvenanceNonconstant := by
  refine ⟨0, 1, ?_⟩
  intro h
  have hsecret := congrArg OneTimePadHistory.secret h
  norm_num [oneTimePadPreparationLeft] at hsecret

theorem oneTimePadPreparationRight_provenanceNonconstant :
    oneTimePadPreparationRight.ProvenanceNonconstant := by
  refine ⟨0, 1, ?_⟩
  intro h
  have hsecret := congrArg OneTimePadHistory.secret h
  norm_num [oneTimePadPreparationRight] at hsecret

end
end Information
end Deutsch
