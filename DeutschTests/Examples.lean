import Deutsch

/-!
# Compiled public-root reuse examples

These thin wrappers demonstrate representative downstream use of the library through its public
root.  They intentionally introduce no new mathematical assumptions.
-/

namespace DeutschTests
namespace Examples

open Deutsch Deutsch.Bell Deutsch.Foundations Deutsch.Gates Deutsch.Information Deutsch.Locality
  Deutsch.Register
open scoped BigOperators

noncomputable section

/-! ## Named registers and gates -/

/-- A Pauli operator on coordinate `1` is the corresponding one-qubit matrix embedding. -/
theorem named_pauli_is_embedded :
    xAt (1 : Fin 3) = embedQubit (1 : Fin 3) pauliX :=
  rfl

/-- A named `X` rotation fixes the `X` descriptor on the same coordinate. -/
theorem named_rotation_preserves_its_x_axis (theta : ℝ) :
    Register.heisenberg (rotationXAt (1 : Fin 3) theta) (xAt (1 : Fin 3)) =
      xAt (1 : Fin 3) :=
  rotationXAt_heisenberg_x 1 theta

/-- A named CNOT is the local `(target, control)` gate placed along the ordered injection. -/
theorem named_cnot_uses_target_control_placement :
    cnotAt (0 : Fin 3) (2 : Fin 3) (by decide) =
      embedAlong
        (targetControlPlacement (0 : Fin 3) (2 : Fin 3) (by decide))
        cnotLocal :=
  rfl

/-! ## Disjoint-support locality -/

/-- A unitary `X` on coordinate `0` fixes a `Z` observable supported on coordinate `2`. -/
theorem local_x_fixes_remote_z :
    Register.heisenberg (xAt (0 : Fin 3)) (zAt (2 : Fin 3)) =
      zAt (2 : Fin 3) := by
  exact heisenberg_eq_self_of_disjoint_support
    (by decide) (xAt_unitary 0) (xAt_isSupportedOn 0) (zAt_isSupportedOn 2)

/-! ## Operational information semantics -/

/-- Either singleton ciphertext subsystem is statistically independent of the secret bit. -/
theorem one_time_pad_hides_secret_locally (q : Fin 2) :
    LocallyStatisticsIndependent ({q} : Finset (Fin 2)) oneTimePadDensity :=
  oneTimePad_locallyStatisticsIndependent q

/-! ## Corrected finite Bell API -/

/-- Every two distinct members of the corrected three-angle family agree with probability `1/4`. -/
theorem corrected_three_setting_quantum_probability
    (i j : Setting) (hij : i ≠ j) :
    sameOutcomeProbability (threeSettingAngle i) (threeSettingAngle j) =
      (1 / 4 : ℝ) :=
  threeSetting_sameOutcomeProbability_of_ne i j hij

/-- No normalized nonnegative distribution over the explicit local response tables reproduces
the complete corrected three-setting quantum agreement table. -/
theorem corrected_quantum_table_refutes_normalized_local_model
    (weight : LocalAssignment → ℝ)
    (weight_nonnegative : ∀ assignment, 0 ≤ weight assignment)
    (weight_normalized : ∑ assignment, weight assignment = 1) :
    ¬ ReproducesThreeSettingQuantumAgreements weight :=
  no_normalized_local_model_reproduces_corrected_epr_three_settings
    weight weight_nonnegative weight_normalized

end

end Examples
end DeutschTests
