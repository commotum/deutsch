import Deutsch.Register.Pauli

/-!
# Deutsch--Hayden descriptor triples

A descriptor is a triple of global register operators indexed by the three Pauli axes.  Its
validity structure stores only the independent forms used throughout the project: Hermiticity,
involution, and the positively oriented cyclic Pauli products.  Reverse products and
anticommutation are derived rather than duplicated as proof fields.

Descriptor families attach one triple to every named qubit.  Their cross-label condition
quantifies all pairs of axes, and simultaneous evolution always conjugates every component by the
same explicitly unitary global operator.
-/

namespace Deutsch

open Register
open scoped Matrix

noncomputable section

/-! ## Pauli axes -/

/-- The three Pauli components of a Deutsch--Hayden descriptor. -/
inductive Axis
  | x
  | y
  | z
  deriving DecidableEq, Fintype, Repr

namespace Axis

/-- The positive cyclic successor `X -> Y -> Z -> X`. -/
def next : Axis -> Axis
  | x => y
  | y => z
  | z => x

@[simp]
theorem next_x : x.next = y := rfl

@[simp]
theorem next_y : y.next = z := rfl

@[simp]
theorem next_z : z.next = x := rfl

@[simp]
theorem next_next_next (a : Axis) : a.next.next.next = a := by
  cases a <;> rfl

end Axis

/-! ## Individual descriptor triples -/

/-- A readable triple of global operators on the register named by `Q`. -/
structure Descriptor (Q : Type*) [Fintype Q] [DecidableEq Q] where
  x : Operator Q
  y : Operator Q
  z : Operator Q

namespace Descriptor

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

@[ext]
theorem ext_components {d e : Descriptor Q}
    (hx : d.x = e.x) (hy : d.y = e.y) (hz : d.z = e.z) : d = e := by
  cases d
  cases e
  simp_all

/-- Select a descriptor component by its Pauli axis. -/
def component (d : Descriptor Q) : Axis -> Operator Q
  | .x => d.x
  | .y => d.y
  | .z => d.z

@[simp]
theorem component_x (d : Descriptor Q) : d.component .x = d.x := rfl

@[simp]
theorem component_y (d : Descriptor Q) : d.component .y = d.y := rfl

@[simp]
theorem component_z (d : Descriptor Q) : d.component .z = d.z := rfl

/--
The same-factor Pauli obligations used to validate a descriptor.  Reverse signed products and
anticommutation follow from these fields and are exported below as theorems.
-/
structure Valid (d : Descriptor Q) : Prop where
  hermitian : forall a, (d.component a).IsHermitian
  square : forall a, d.component a * d.component a = 1
  cyclic : forall a,
    d.component a * d.component a.next =
      Complex.I • d.component a.next.next

namespace Valid

variable {d : Descriptor Q}

theorem x_isHermitian (h : d.Valid) : d.x.IsHermitian :=
  h.hermitian .x

theorem y_isHermitian (h : d.Valid) : d.y.IsHermitian :=
  h.hermitian .y

theorem z_isHermitian (h : d.Valid) : d.z.IsHermitian :=
  h.hermitian .z

theorem x_mul_x (h : d.Valid) : d.x * d.x = 1 :=
  h.square .x

theorem y_mul_y (h : d.Valid) : d.y * d.y = 1 :=
  h.square .y

theorem z_mul_z (h : d.Valid) : d.z * d.z = 1 :=
  h.square .z

/-- Every valid component is unitary; this is derived rather than stored as a validity field. -/
theorem component_unitary (h : d.Valid) (a : Axis) :
    d.component a ∈ Matrix.unitaryGroup (Basis Q) Complex := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (d.component a)ᴴ * d.component a = 1
  rw [h.hermitian a, h.square a]

theorem mul_xy (h : d.Valid) : d.x * d.y = Complex.I • d.z :=
  h.cyclic .x

theorem mul_yz (h : d.Valid) : d.y * d.z = Complex.I • d.x :=
  h.cyclic .y

theorem mul_zx (h : d.Valid) : d.z * d.x = Complex.I • d.y :=
  h.cyclic .z

theorem mul_yx (h : d.Valid) : d.y * d.x = -Complex.I • d.z := by
  have hadj := congrArg Matrix.conjTranspose h.mul_xy
  rw [Matrix.conjTranspose_mul, h.y_isHermitian, h.x_isHermitian,
    Matrix.conjTranspose_smul, h.z_isHermitian] at hadj
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  rw [hI] at hadj
  simpa only [neg_smul] using hadj

theorem mul_zy (h : d.Valid) : d.z * d.y = -Complex.I • d.x := by
  have hadj := congrArg Matrix.conjTranspose h.mul_yz
  rw [Matrix.conjTranspose_mul, h.z_isHermitian, h.y_isHermitian,
    Matrix.conjTranspose_smul, h.x_isHermitian] at hadj
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  rw [hI] at hadj
  simpa only [neg_smul] using hadj

theorem mul_xz (h : d.Valid) : d.x * d.z = -Complex.I • d.y := by
  have hadj := congrArg Matrix.conjTranspose h.mul_zx
  rw [Matrix.conjTranspose_mul, h.x_isHermitian, h.z_isHermitian,
    Matrix.conjTranspose_smul, h.y_isHermitian] at hadj
  have hI : star Complex.I = -Complex.I := Complex.conj_I
  rw [hI] at hadj
  simpa only [neg_smul] using hadj

/-- Adjacent components in the positive axis cycle anticommute. -/
theorem anticommutes_next (h : d.Valid) (a : Axis) :
    d.component a * d.component a.next +
      d.component a.next * d.component a = 0 := by
  cases a with
  | x =>
      change d.x * d.y + d.y * d.x = 0
      rw [h.mul_xy, h.mul_yx]
      simp
  | y =>
      change d.y * d.z + d.z * d.y = 0
      rw [h.mul_yz, h.mul_zy]
      simp
  | z =>
      change d.z * d.x + d.x * d.z = 0
      rw [h.mul_zx, h.mul_xz]
      simp

theorem anticommutes_xy (h : d.Valid) : d.x * d.y + d.y * d.x = 0 :=
  h.anticommutes_next .x

theorem anticommutes_yz (h : d.Valid) : d.y * d.z + d.z * d.y = 0 :=
  h.anticommutes_next .y

theorem anticommutes_zx (h : d.Valid) : d.z * d.x + d.x * d.z = 0 :=
  h.anticommutes_next .z

end Valid

/-! ## Initial descriptors -/

/-- The initial descriptor attached to the named register coordinate `q`. -/
def initial (q : Q) : Descriptor Q where
  x := xAt q
  y := yAt q
  z := zAt q

@[simp]
theorem initial_component (q : Q) : (initial q).component = fun
    | .x => xAt q
    | .y => yAt q
    | .z => zAt q := by
  funext a
  cases a <;> rfl

/-- Every component of an initial descriptor has exact singleton support at its label. -/
theorem initial_component_isSupportedOn (q : Q) (a : Axis) :
    IsSupportedOn {q} ((initial q).component a) := by
  cases a with
  | x => exact xAt_isSupportedOn q
  | y => exact yAt_isSupportedOn q
  | z => exact zAt_isSupportedOn q

theorem initial_valid (q : Q) : (initial q).Valid := by
  refine {
    hermitian := ?_
    square := ?_
    cyclic := ?_
  }
  · intro a
    cases a with
    | x => exact xAt_isHermitian q
    | y => exact yAt_isHermitian q
    | z => exact zAt_isHermitian q
  · intro a
    cases a with
    | x => exact xAt_mul_xAt q
    | y => exact yAt_mul_yAt q
    | z => exact zAt_mul_zAt q
  · intro a
    cases a with
    | x => exact xAt_mul_yAt q
    | y => exact yAt_mul_zAt q
    | z => exact zAt_mul_xAt q

/-! ## Simultaneous Heisenberg evolution -/

/-- Conjugate every component by the same global operator. -/
def evolve (U : Operator Q) (d : Descriptor Q) : Descriptor Q where
  x := Register.heisenberg U d.x
  y := Register.heisenberg U d.y
  z := Register.heisenberg U d.z

@[simp]
theorem evolve_component (U : Operator Q) (d : Descriptor Q) (a : Axis) :
    (d.evolve U).component a = Register.heisenberg U (d.component a) := by
  cases a <;> rfl

@[simp]
theorem evolve_one (d : Descriptor Q) : d.evolve 1 = d := by
  apply ext_components
  · exact Register.heisenberg_one_operator d.x
  · exact Register.heisenberg_one_operator d.y
  · exact Register.heisenberg_one_operator d.z

/-- Descriptor evolution follows the register's chronological product convention. -/
theorem evolve_chronology (U V : Operator Q) (d : Descriptor Q) :
    d.evolve (V * U) = (d.evolve V).evolve U := by
  apply ext_components
  · exact Register.heisenberg_chronology U V d.x
  · exact Register.heisenberg_chronology U V d.y
  · exact Register.heisenberg_chronology U V d.z

private theorem heisenberg_smul (U A : Operator Q) (c : Complex) :
    Register.heisenberg U (c • A) = c • Register.heisenberg U A := by
  simp [Register.heisenberg]

/-- A unitary simultaneous conjugation preserves every descriptor validity obligation. -/
theorem Valid.evolve {U : Operator Q} {d : Descriptor Q} (hd : d.Valid)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) Complex) : (d.evolve U).Valid := by
  refine {
    hermitian := ?_
    square := ?_
    cyclic := ?_
  }
  · intro a
    rw [evolve_component]
    exact Register.heisenberg_isHermitian U (d.component a) (hd.hermitian a)
  · intro a
    simp only [evolve_component]
    calc
      Register.heisenberg U (d.component a) *
          Register.heisenberg U (d.component a) =
          Register.heisenberg U (d.component a * d.component a) :=
        (Register.heisenberg_mul_of_unitary U _ _ hU).symm
      _ = Register.heisenberg U 1 := by rw [hd.square a]
      _ = 1 := Register.heisenberg_one_of_unitary U hU
  · intro a
    simp only [evolve_component]
    calc
      Register.heisenberg U (d.component a) *
          Register.heisenberg U (d.component a.next) =
          Register.heisenberg U (d.component a * d.component a.next) :=
        (Register.heisenberg_mul_of_unitary U _ _ hU).symm
      _ = Register.heisenberg U (Complex.I • d.component a.next.next) := by
        rw [hd.cyclic a]
      _ = Complex.I • Register.heisenberg U (d.component a.next.next) :=
        heisenberg_smul U _ _

end Descriptor

/-! ## Descriptor families -/

/-- One global descriptor triple for each named qubit in a register. -/
abbrev DescriptorFamily (Q : Type*) [Fintype Q] [DecidableEq Q] :=
  Q -> Descriptor Q

namespace DescriptorFamily

variable {Q : Type*} [Fintype Q] [DecidableEq Q]

/-- Every pair of components belonging to distinct labels commutes. -/
def PairwiseCommutes (D : DescriptorFamily Q) : Prop :=
  forall q r, q ≠ r -> forall a b,
    (D q).component a * (D r).component b =
      (D r).component b * (D q).component a

/-- Per-label Pauli validity together with all arbitrary cross-label commutators. -/
structure Valid (D : DescriptorFamily Q) : Prop where
  each : forall q, (D q).Valid
  cross : PairwiseCommutes D

/-- The family of initial embedded descriptors on a named register. -/
def initial (Q : Type*) [Fintype Q] [DecidableEq Q] : DescriptorFamily Q :=
  Descriptor.initial

theorem initial_pairwiseCommutes : PairwiseCommutes (initial Q) := by
  intro q r hqr a b
  cases a <;> cases b <;>
    exact Register.embedQubit_commute_of_ne hqr _ _

theorem initial_valid : Valid (initial Q) where
  each := Descriptor.initial_valid
  cross := initial_pairwiseCommutes

/-- Simultaneously evolve a whole family by one global operator. -/
def evolve (U : Operator Q) (D : DescriptorFamily Q) : DescriptorFamily Q :=
  fun q => (D q).evolve U

@[simp]
theorem evolve_apply (U : Operator Q) (D : DescriptorFamily Q) (q : Q) :
    evolve U D q = (D q).evolve U := rfl

@[simp]
theorem evolve_one (D : DescriptorFamily Q) : evolve 1 D = D := by
  funext q
  exact Descriptor.evolve_one (D q)

/-- Family evolution uses the same chronological product as every component. -/
theorem evolve_chronology (U V : Operator Q) (D : DescriptorFamily Q) :
    evolve (V * U) D = evolve U (evolve V D) := by
  funext q
  exact Descriptor.evolve_chronology U V (D q)

/-- One shared unitary conjugation preserves every cross-label component commutator. -/
theorem PairwiseCommutes.evolve {U : Operator Q} {D : DescriptorFamily Q}
    (hD : PairwiseCommutes D)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) Complex) :
    PairwiseCommutes (evolve U D) := by
  intro q r hqr a b
  simp only [evolve_apply, Descriptor.evolve_component]
  calc
    Register.heisenberg U ((D q).component a) *
        Register.heisenberg U ((D r).component b) =
        Register.heisenberg U ((D q).component a * (D r).component b) :=
      (Register.heisenberg_mul_of_unitary U _ _ hU).symm
    _ = Register.heisenberg U ((D r).component b * (D q).component a) := by
      rw [hD q r hqr a b]
    _ = Register.heisenberg U ((D r).component b) *
        Register.heisenberg U ((D q).component a) :=
      Register.heisenberg_mul_of_unitary U _ _ hU

/-- One shared unitary conjugation preserves complete descriptor-family validity. -/
theorem Valid.evolve {U : Operator Q} {D : DescriptorFamily Q} (hD : Valid D)
    (hU : U ∈ Matrix.unitaryGroup (Basis Q) Complex) : Valid (evolve U D) where
  each q := (hD.each q).evolve hU
  cross := hD.cross.evolve hU

end DescriptorFamily

end
end Deutsch
