import Deutsch.Register.Basic
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Equiv.Prod

/-!
# Selected-subsystem embeddings and exact tensor support

For `s : Finset Q`, the global basis is split into assignments on `s` and its complement.
Embedding is reindexed `A ⊗ I`, bundled as an algebra homomorphism. Support is membership in the
image of this map, relative to the chosen register tensor factorization.
-/

namespace Deutsch
namespace Register

open Foundations
open scoped Matrix Kronecker

noncomputable section

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Basis labels on a selected finite set of named qubits. -/
abbrev SubsystemBasis (s : Finset Q) := {q : Q // q ∈ s} → QubitIndex

/-- Basis labels on the complement of a selected set. -/
abbrev ComplementBasis (s : Finset Q) := {q : Q // q ∉ s} → QubitIndex

/-- Operators intrinsic to a selected subsystem. -/
abbrev SubsystemOperator (s : Finset Q) :=
  Matrix (SubsystemBasis s) (SubsystemBasis s) ℂ

/-- Split a register basis assignment into selected and complementary coordinates. -/
def splitBasis (s : Finset Q) :
    Basis Q ≃ SubsystemBasis s × ComplementBasis s :=
  Equiv.piEquivPiSubtypeProd (fun q ↦ q ∈ s) (fun _ ↦ QubitIndex)

/-- The Stage 2 two-factor product order is coordinate `0` followed by coordinate `1`. -/
def twoQubitBasisEquiv : Basis (Fin 2) ≃ QubitIndex × QubitIndex :=
  finTwoArrowEquiv QubitIndex

/-- Tensoring on the right with an identity, as an algebra homomorphism. -/
def kroneckerRightOneAlgHom (m n : Type*) [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] :
    Matrix m m ℂ →ₐ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix n n ℂ)
  map_zero' := by simp
  map_one' := by simp
  map_add' A B := by rw [Matrix.add_kronecker]
  map_mul' A B := by
    rw [← Matrix.mul_kronecker_mul]
    simp
  commutes' r := by
    ext i j
    rcases i with ⟨i, k⟩
    rcases j with ⟨j, l⟩
    by_cases hi : i = j
    · subst j
      by_cases hk : k = l
      · subst l
        simp [Matrix.algebraMap_matrix_apply]
      · simp [Matrix.algebraMap_matrix_apply, hk]
    · simp [Matrix.algebraMap_matrix_apply, hi]

/-- Bundled embedding of operators on `s`, with identity action on the complement. -/
def embedSubsystemAlgHom (s : Finset Q) :
    SubsystemOperator s →ₐ[ℂ] Operator Q :=
  (Matrix.reindexAlgEquiv ℂ ℂ (splitBasis s).symm).toAlgHom.comp
    (kroneckerRightOneAlgHom (SubsystemBasis s) (ComplementBasis s))

/-- Embed `A` on `s`, tensored with the identity on the complement. -/
def embedSubsystem (s : Finset Q) (A : SubsystemOperator s) : Operator Q :=
  Matrix.reindexRingEquiv ℂ (splitBasis s).symm
    (A ⊗ₖ (1 : Matrix (ComplementBasis s) (ComplementBasis s) ℂ))

@[simp]
theorem embedSubsystem_eq_algHom (s : Finset Q) (A : SubsystemOperator s) :
    embedSubsystem s A = embedSubsystemAlgHom s A := rfl

theorem embedSubsystem_apply (s : Finset Q) (A : SubsystemOperator s)
    (x y : Basis Q) :
    embedSubsystem s A x y =
      A (fun q ↦ x q.1) (fun q ↦ y q.1) *
        (1 : Matrix (ComplementBasis s) (ComplementBasis s) ℂ)
          (fun q ↦ x q.1) (fun q ↦ y q.1) := by
  rfl

omit [Fintype Q] [DecidableEq Q] in
theorem complementBasis_eq_iff (s : Finset Q) (x y : Basis Q) :
    (fun q : {q : Q // q ∉ s} ↦ x q.1) =
        (fun q : {q : Q // q ∉ s} ↦ y q.1) ↔
      ∀ q, q ∉ s → x q = y q := by
  constructor
  · intro h q hq
    exact congrFun h ⟨q, hq⟩
  · intro h
    funext q
    exact h q.1 q.2

/-- Exact entry behavior: an embedded operator is diagonal off its selected subsystem. -/
theorem embedSubsystem_apply_ite (s : Finset Q) (A : SubsystemOperator s)
    (x y : Basis Q) :
    embedSubsystem s A x y =
      if ∀ q, q ∉ s → x q = y q
      then A (fun q ↦ x q.1) (fun q ↦ y q.1)
      else 0 := by
  rw [embedSubsystem_apply]
  simp only [Matrix.one_apply]
  rw [if_congr (complementBasis_eq_iff s x y) rfl rfl]
  simp

@[simp]
theorem embedSubsystem_zero (s : Finset Q) :
    embedSubsystem s (0 : SubsystemOperator s) = 0 := by
  exact map_zero (embedSubsystemAlgHom s)

@[simp]
theorem embedSubsystem_one (s : Finset Q) :
    embedSubsystem s (1 : SubsystemOperator s) = 1 := by
  exact map_one (embedSubsystemAlgHom s)

theorem embedSubsystem_add (s : Finset Q) (A B : SubsystemOperator s) :
    embedSubsystem s (A + B) = embedSubsystem s A + embedSubsystem s B := by
  exact map_add (embedSubsystemAlgHom s) A B

theorem embedSubsystem_smul (s : Finset Q) (c : ℂ) (A : SubsystemOperator s) :
    embedSubsystem s (c • A) = c • embedSubsystem s A := by
  exact map_smul (embedSubsystemAlgHom s) c A

theorem embedSubsystem_mul (s : Finset Q) (A B : SubsystemOperator s) :
    embedSubsystem s (A * B) = embedSubsystem s A * embedSubsystem s B := by
  exact map_mul (embedSubsystemAlgHom s) A B

/-- Same-index matrix reindexing commutes with conjugate transpose. -/
theorem reindexRingEquiv_conjTranspose {m k : Type*} [Fintype m] [Fintype k]
    [DecidableEq m] [DecidableEq k] (e : m ≃ k) (A : Matrix m m ℂ) :
    (Matrix.reindexRingEquiv ℂ e A)ᴴ = Matrix.reindexRingEquiv ℂ e Aᴴ := by
  ext i j
  rfl

theorem embedSubsystem_conjTranspose (s : Finset Q) (A : SubsystemOperator s) :
    (embedSubsystem s A)ᴴ = embedSubsystem s Aᴴ := by
  unfold embedSubsystem
  rw [reindexRingEquiv_conjTranspose, Matrix.conjTranspose_kronecker]
  simp

theorem embedSubsystem_injective (s : Finset Q) :
    Function.Injective (embedSubsystem s) := by
  intro A B h
  unfold embedSubsystem at h
  have hK := (Matrix.reindexRingEquiv ℂ (splitBasis s).symm).injective h
  let complementZero : ComplementBasis s := fun _ ↦ 0
  ext i j
  have hij := congrFun (congrFun hK (i, complementZero)) (j, complementZero)
  simpa [complementZero] using hij

theorem embedSubsystem_isHermitian (s : Finset Q) (A : SubsystemOperator s)
    (hA : A.IsHermitian) : (embedSubsystem s A).IsHermitian := by
  rw [Matrix.IsHermitian] at hA ⊢
  rw [embedSubsystem_conjTranspose, hA]

theorem embedSubsystem_unitary (s : Finset Q) (U : SubsystemOperator s)
    (hU : U ∈ Matrix.unitaryGroup (SubsystemBasis s) ℂ) :
    embedSubsystem s U ∈ Matrix.unitaryGroup (Basis Q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hU ⊢
  change Uᴴ * U = 1 at hU
  change (embedSubsystem s U)ᴴ * embedSubsystem s U = 1
  rw [embedSubsystem_conjTranspose, ← embedSubsystem_mul, hU, embedSubsystem_one]

theorem embedSubsystem_heisenberg (s : Finset Q) (U A : SubsystemOperator s) :
    heisenberg (embedSubsystem s U) (embedSubsystem s A) =
      embedSubsystem s (Uᴴ * A * U) := by
  rw [heisenberg, embedSubsystem_conjTranspose,
    ← embedSubsystem_mul, ← embedSubsystem_mul]

/-- Exact tensor-factor support relative to the chosen register factorization. -/
def IsSupportedOn (s : Finset Q) (A : Operator Q) : Prop :=
  ∃ localOp : SubsystemOperator s, A = embedSubsystem s localOp

theorem embedSubsystem_isSupportedOn (s : Finset Q) (A : SubsystemOperator s) :
    IsSupportedOn s (embedSubsystem s A) := ⟨A, rfl⟩

/-- Exact tensor support is monotone: an operator supported on `s` is also supported on
any larger selected subsystem `t`.  The extra coordinates carry an identity factor. -/
theorem IsSupportedOn.mono {s t : Finset Q} {A : Operator Q}
    (hA : IsSupportedOn s A) (hst : s ⊆ t) : IsSupportedOn t A := by
  rcases hA with ⟨a, rfl⟩
  let restrictBasis : SubsystemBasis t → SubsystemBasis s :=
    fun x q ↦ x ⟨q.1, hst q.2⟩
  let enlarged : SubsystemOperator t := fun x y ↦
    if ∀ q : {q : Q // q ∈ t}, q.1 ∉ s → x q = y q
    then a (restrictBasis x) (restrictBasis y)
    else 0
  refine ⟨enlarged, ?_⟩
  ext x y
  rw [embedSubsystem_apply_ite, embedSubsystem_apply_ite]
  by_cases hs : ∀ q, q ∉ s → x q = y q
  · rw [if_pos hs]
    have ht : ∀ q, q ∉ t → x q = y q := fun q hqt ↦
      hs q (fun hqs ↦ hqt (hst hqs))
    rw [if_pos ht]
    have hnew : ∀ q : {q : Q // q ∈ t}, q.1 ∉ s →
        (fun r : {r : Q // r ∈ t} ↦ x r.1) q =
          (fun r : {r : Q // r ∈ t} ↦ y r.1) q := by
      intro q hqs
      exact hs q.1 hqs
    simp only [enlarged, if_pos hnew, restrictBasis]
  · rw [if_neg hs]
    by_cases ht : ∀ q, q ∉ t → x q = y q
    · rw [if_pos ht]
      have hnew : ¬ ∀ q : {q : Q // q ∈ t}, q.1 ∉ s →
          (fun r : {r : Q // r ∈ t} ↦ x r.1) q =
            (fun r : {r : Q // r ∈ t} ↦ y r.1) q := by
        intro hinside
        apply hs
        intro q hqs
        by_cases hqt : q ∈ t
        · exact hinside ⟨q, hqt⟩ hqs
        · exact ht q hqt
      simp only [enlarged, if_neg hnew]
    · rw [if_neg ht]

@[simp]
theorem isSupportedOn_zero (s : Finset Q) : IsSupportedOn s (0 : Operator Q) :=
  ⟨0, (embedSubsystem_zero s).symm⟩

@[simp]
theorem isSupportedOn_one (s : Finset Q) : IsSupportedOn s (1 : Operator Q) :=
  ⟨1, (embedSubsystem_one s).symm⟩

theorem IsSupportedOn.add {s : Finset Q} {A B : Operator Q}
    (hA : IsSupportedOn s A) (hB : IsSupportedOn s B) :
    IsSupportedOn s (A + B) := by
  rcases hA with ⟨a, rfl⟩
  rcases hB with ⟨b, rfl⟩
  exact ⟨a + b, (embedSubsystem_add s a b).symm⟩

theorem IsSupportedOn.smul {s : Finset Q} {A : Operator Q}
    (hA : IsSupportedOn s A) (c : ℂ) : IsSupportedOn s (c • A) := by
  rcases hA with ⟨a, rfl⟩
  exact ⟨c • a, (embedSubsystem_smul s c a).symm⟩

theorem IsSupportedOn.mul {s : Finset Q} {A B : Operator Q}
    (hA : IsSupportedOn s A) (hB : IsSupportedOn s B) :
    IsSupportedOn s (A * B) := by
  rcases hA with ⟨a, rfl⟩
  rcases hB with ⟨b, rfl⟩
  exact ⟨a * b, (embedSubsystem_mul s a b).symm⟩

theorem IsSupportedOn.conjTranspose {s : Finset Q} {A : Operator Q}
    (hA : IsSupportedOn s A) : IsSupportedOn s Aᴴ := by
  rcases hA with ⟨a, rfl⟩
  exact ⟨aᴴ, embedSubsystem_conjTranspose s a⟩

theorem IsSupportedOn.heisenberg {s : Finset Q} {U A : Operator Q}
    (hU : IsSupportedOn s U) (hA : IsSupportedOn s A) :
    IsSupportedOn s (heisenberg U A) := by
  rcases hU with ⟨u, rfl⟩
  rcases hA with ⟨a, rfl⟩
  exact ⟨uᴴ * a * u, embedSubsystem_heisenberg s u a⟩

/-- The basis of a singleton selected subsystem is canonically one qubit. -/
def singletonBasisEquiv (q : Q) :
    QubitIndex ≃ SubsystemBasis ({q} : Finset Q) where
  toFun bit := fun _ ↦ bit
  invFun x := x ⟨q, Finset.mem_singleton_self q⟩
  left_inv _ := rfl
  right_inv x := by
    funext j
    have hj : j.1 = q := Finset.mem_singleton.mp j.2
    have heq : (⟨q, Finset.mem_singleton_self q⟩ :
        {k : Q // k ∈ ({q} : Finset Q)}) = j := by
      apply Subtype.ext
      exact hj.symm
    exact congrArg x heq

/-- Embed a one-qubit operator at any named register coordinate. -/
def embedQubit (q : Q) (A : QubitMatrix) : Operator Q :=
  embedSubsystem {q} (Matrix.reindexRingEquiv ℂ (singletonBasisEquiv q) A)

/-- The single-qubit embedding bundled as an algebra homomorphism. -/
def embedQubitAlgHom (q : Q) : QubitMatrix →ₐ[ℂ] Operator Q :=
  (embedSubsystemAlgHom ({q} : Finset Q)).comp
    (Matrix.reindexAlgEquiv ℂ ℂ (singletonBasisEquiv q)).toAlgHom

@[simp]
theorem embedQubit_eq_algHom (q : Q) (A : QubitMatrix) :
    embedQubit q A = embedQubitAlgHom q A := rfl

theorem embedQubit_apply (q : Q) (A : QubitMatrix) (x y : Basis Q) :
    embedQubit q A x y = A (x q) (y q) *
      (1 : Matrix (ComplementBasis ({q} : Finset Q))
        (ComplementBasis ({q} : Finset Q)) ℂ)
        (fun j ↦ x j.1) (fun j ↦ y j.1) := by
  rfl

omit [Fintype Q] [DecidableEq Q] in
theorem complement_singleton_eq_iff (q : Q) (x y : Basis Q) :
    (fun j : {k : Q // k ∉ ({q} : Finset Q)} ↦ x j.1) =
        (fun j : {k : Q // k ∉ ({q} : Finset Q)} ↦ y j.1) ↔
      ∀ j, j ≠ q → x j = y j := by
  constructor
  · intro h j hj
    have hmem : j ∉ ({q} : Finset Q) := by simpa using hj
    exact congrFun h ⟨j, hmem⟩
  · intro h
    funext j
    exact h j.1 (by simpa using j.2)

/-- Fully explicit matrix-entry behavior for a selected qubit. -/
theorem embedQubit_apply_ite (q : Q) (A : QubitMatrix) (x y : Basis Q) :
    embedQubit q A x y =
      if ∀ j, j ≠ q → x j = y j then A (x q) (y q) else 0 := by
  rw [embedQubit_apply]
  simp only [Matrix.one_apply]
  rw [if_congr (complement_singleton_eq_iff q x y) rfl rfl]
  simp

@[simp]
theorem embedQubit_one (q : Q) : embedQubit q (1 : QubitMatrix) = 1 := by
  simp [embedQubit]

@[simp]
theorem embedQubit_zero (q : Q) : embedQubit q (0 : QubitMatrix) = 0 := by
  exact map_zero (embedQubitAlgHom q)

theorem embedQubit_add (q : Q) (A B : QubitMatrix) :
    embedQubit q (A + B) = embedQubit q A + embedQubit q B := by
  exact map_add (embedQubitAlgHom q) A B

theorem embedQubit_sub (q : Q) (A B : QubitMatrix) :
    embedQubit q (A - B) = embedQubit q A - embedQubit q B := by
  exact map_sub (embedQubitAlgHom q) A B

theorem embedQubit_smul (q : Q) (c : ℂ) (A : QubitMatrix) :
    embedQubit q (c • A) = c • embedQubit q A := by
  exact map_smul (embedQubitAlgHom q) c A

theorem embedQubit_mul (q : Q) (A B : QubitMatrix) :
    embedQubit q (A * B) = embedQubit q A * embedQubit q B := by
  unfold embedQubit
  rw [map_mul, embedSubsystem_mul]

theorem embedQubit_conjTranspose (q : Q) (A : QubitMatrix) :
    (embedQubit q A)ᴴ = embedQubit q Aᴴ := by
  rw [embedQubit, embedSubsystem_conjTranspose, embedQubit]
  congr 1

theorem embedQubit_injective (q : Q) : Function.Injective (embedQubit q) := by
  intro A B h
  unfold embedQubit at h
  have hs := embedSubsystem_injective ({q} : Finset Q) h
  exact (Matrix.reindexRingEquiv ℂ (singletonBasisEquiv q)).injective hs

theorem embedQubit_isHermitian (q : Q) (A : QubitMatrix)
    (hA : A.IsHermitian) : (embedQubit q A).IsHermitian := by
  rw [Matrix.IsHermitian] at hA ⊢
  rw [embedQubit_conjTranspose, hA]

theorem embedQubit_unitary (q : Q) (U : QubitMatrix)
    (hU : U ∈ Matrix.unitaryGroup QubitIndex ℂ) :
    embedQubit q U ∈ Matrix.unitaryGroup (Basis Q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hU ⊢
  change Uᴴ * U = 1 at hU
  change (embedQubit q U)ᴴ * embedQubit q U = 1
  rw [embedQubit_conjTranspose, ← embedQubit_mul, hU, embedQubit_one]

section OrderedPlacement

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- The selected ambient qubits underlying an ordered injection. -/
def placementFinset (p : K ↪ Q) : Finset Q := Finset.univ.map p

omit [Fintype Q] [DecidableEq Q] [DecidableEq K] in
theorem mem_placementFinset_iff (p : K ↪ Q) (q : Q) :
    q ∈ placementFinset p ↔ q ∈ Set.range p := by
  simp [placementFinset]

/-- The injection identifies its domain with its selected range without forgetting domain labels. -/
def placementEquiv (p : K ↪ Q) : K ≃ {q : Q // q ∈ placementFinset p} where
  toFun k := ⟨p k, by simp [placementFinset]⟩
  invFun q := p.toEquivRange.symm
    ⟨q.1, (mem_placementFinset_iff p q.1).mp q.2⟩
  left_inv k := by
    change p.toEquivRange.symm ⟨p k, _⟩ = k
    simp
  right_inv q := by
    apply Subtype.ext
    change p (p.toEquivRange.symm ⟨q.1, _⟩) = q.1
    have h := congrArg Subtype.val
      (p.toEquivRange.apply_symm_apply
        ⟨q.1, (mem_placementFinset_iff p q.1).mp q.2⟩)
    exact h

/-- Reindex domain-labelled bit strings as bit strings on the injection's range. -/
def alongBasisEquiv (p : K ↪ Q) :
    Basis K ≃ SubsystemBasis (placementFinset p) :=
  Equiv.arrowCongr (placementEquiv p) (Equiv.refl QubitIndex)

/-- Ordered subsystem placement as a bundled algebra homomorphism. -/
def embedAlongAlgHom (p : K ↪ Q) : Operator K →ₐ[ℂ] Operator Q :=
  (embedSubsystemAlgHom (placementFinset p)).comp
    (Matrix.reindexAlgEquiv ℂ ℂ (alongBasisEquiv p)).toAlgHom

/-- Place an operator along an injection, preserving the injection domain's order and labels. -/
def embedAlong (p : K ↪ Q) (A : Operator K) : Operator Q :=
  embedAlongAlgHom p A

@[simp]
theorem embedAlong_zero (p : K ↪ Q) : embedAlong p (0 : Operator K) = 0 := by
  exact map_zero (embedAlongAlgHom p)

@[simp]
theorem embedAlong_one (p : K ↪ Q) : embedAlong p (1 : Operator K) = 1 := by
  exact map_one (embedAlongAlgHom p)

theorem embedAlong_add (p : K ↪ Q) (A B : Operator K) :
    embedAlong p (A + B) = embedAlong p A + embedAlong p B := by
  exact map_add (embedAlongAlgHom p) A B

theorem embedAlong_smul (p : K ↪ Q) (c : ℂ) (A : Operator K) :
    embedAlong p (c • A) = c • embedAlong p A := by
  exact map_smul (embedAlongAlgHom p) c A

theorem embedAlong_mul (p : K ↪ Q) (A B : Operator K) :
    embedAlong p (A * B) = embedAlong p A * embedAlong p B := by
  exact map_mul (embedAlongAlgHom p) A B

theorem embedAlong_injective (p : K ↪ Q) : Function.Injective (embedAlong p) := by
  intro A B h
  change embedSubsystem (placementFinset p)
      (Matrix.reindexAlgEquiv ℂ ℂ (alongBasisEquiv p) A) =
    embedSubsystem (placementFinset p)
      (Matrix.reindexAlgEquiv ℂ ℂ (alongBasisEquiv p) B) at h
  have hs := embedSubsystem_injective (placementFinset p) h
  exact (Matrix.reindexAlgEquiv ℂ ℂ (alongBasisEquiv p)).injective hs

/-- Exact ordered-placement entries before simplifying the complementary identity. -/
theorem embedAlong_apply (p : K ↪ Q) (A : Operator K) (x y : Basis Q) :
    embedAlong p A x y =
      A (fun k ↦ x (p k)) (fun k ↦ y (p k)) *
        (1 : Matrix (ComplementBasis (placementFinset p))
          (ComplementBasis (placementFinset p)) ℂ)
          (fun q ↦ x q.1) (fun q ↦ y q.1) := by
  rfl

omit [Fintype Q] [DecidableEq Q] [DecidableEq K] in
theorem placementComplement_eq_iff (p : K ↪ Q) (x y : Basis Q) :
    (fun q : {q : Q // q ∉ placementFinset p} ↦ x q.1) =
        (fun q : {q : Q // q ∉ placementFinset p} ↦ y q.1) ↔
      ∀ q, q ∉ Set.range p → x q = y q := by
  constructor
  · intro h q hq
    have hmem : q ∉ placementFinset p := fun hmem ↦
      hq ((mem_placementFinset_iff p q).mp hmem)
    exact congrFun h ⟨q, hmem⟩
  · intro h
    funext q
    exact h q.1 (fun hrange ↦ q.2 ((mem_placementFinset_iff p q.1).mpr hrange))

/-- An entry is local exactly when source and target agree outside the injection range. -/
theorem embedAlong_apply_ite (p : K ↪ Q) (A : Operator K) (x y : Basis Q) :
    embedAlong p A x y =
      if ∀ q, q ∉ Set.range p → x q = y q
      then A (fun k ↦ x (p k)) (fun k ↦ y (p k))
      else 0 := by
  rw [embedAlong_apply]
  simp only [Matrix.one_apply]
  rw [if_congr (placementComplement_eq_iff p x y) rfl rfl]
  simp

theorem embedAlong_conjTranspose (p : K ↪ Q) (A : Operator K) :
    (embedAlong p A)ᴴ = embedAlong p Aᴴ := by
  change (embedSubsystem (placementFinset p)
    (Matrix.reindexAlgEquiv ℂ ℂ (alongBasisEquiv p) A))ᴴ = _
  rw [embedSubsystem_conjTranspose]
  change embedSubsystem (placementFinset p)
      (Matrix.reindexAlgEquiv ℂ ℂ (alongBasisEquiv p) A)ᴴ =
    embedSubsystem (placementFinset p)
      (Matrix.reindexAlgEquiv ℂ ℂ (alongBasisEquiv p) Aᴴ)
  congr 1

theorem embedAlong_isHermitian (p : K ↪ Q) (A : Operator K)
    (hA : A.IsHermitian) : (embedAlong p A).IsHermitian := by
  rw [Matrix.IsHermitian] at hA ⊢
  rw [embedAlong_conjTranspose, hA]

theorem embedAlong_unitary (p : K ↪ Q) (U : Operator K)
    (hU : U ∈ Matrix.unitaryGroup (Basis K) ℂ) :
    embedAlong p U ∈ Matrix.unitaryGroup (Basis Q) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff'] at hU ⊢
  change Uᴴ * U = 1 at hU
  change (embedAlong p U)ᴴ * embedAlong p U = 1
  rw [embedAlong_conjTranspose, ← embedAlong_mul, hU, embedAlong_one]

theorem embedAlong_heisenberg (p : K ↪ Q) (U A : Operator K) :
    heisenberg (embedAlong p U) (embedAlong p A) =
      embedAlong p (heisenberg U A) := by
  rw [heisenberg, heisenberg, embedAlong_conjTranspose,
    ← embedAlong_mul, ← embedAlong_mul]

/-- Ordered subsystem placement composes exactly with a one-qubit coordinate embedding. -/
theorem embedAlong_embedQubit (p : K ↪ Q) (k : K) (A : QubitMatrix) :
    embedAlong p (embedQubit k A) = embedQubit (p k) A := by
  ext x y
  rw [embedAlong_apply_ite, embedQubit_apply_ite, embedQubit_apply_ite]
  by_cases hglobal : ∀ q, q ≠ p k → x q = y q
  · rw [if_pos hglobal]
    have houtside : ∀ q, q ∉ Set.range p → x q = y q := by
      intro q hq
      exact hglobal q (fun hpk ↦ hq ⟨k, hpk.symm⟩)
    rw [if_pos houtside]
    have hinside : ∀ j, j ≠ k → x (p j) = y (p j) := by
      intro j hj
      exact hglobal (p j) (fun hp ↦ hj (p.injective hp))
    rw [if_pos hinside]
  · rw [if_neg hglobal]
    by_cases houtside : ∀ q, q ∉ Set.range p → x q = y q
    · rw [if_pos houtside]
      by_cases hinside : ∀ j, j ≠ k → x (p j) = y (p j)
      · rw [if_pos hinside]
        exfalso
        apply hglobal
        intro q hq
        by_cases hqrange : q ∈ Set.range p
        · rcases hqrange with ⟨j, rfl⟩
          exact hinside j (fun hjk ↦ hq (congrArg p hjk))
        · exact houtside q hqrange
      · rw [if_neg hinside]
    · rw [if_neg houtside]

theorem embedAlong_isSupportedOn (p : K ↪ Q) (A : Operator K) :
    IsSupportedOn (placementFinset p) (embedAlong p A) := by
  exact ⟨Matrix.reindexAlgEquiv ℂ ℂ (alongBasisEquiv p) A, rfl⟩

end OrderedPlacement

end
end Register
end Deutsch
