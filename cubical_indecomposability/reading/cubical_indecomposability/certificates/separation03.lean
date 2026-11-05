import cubical_indecomposability.separating_witness
import Mathlib.Tactic.FinCases

/-! Exact integer arithmetic and finite incidences, checked by Lean's kernel.
`decide +kernel` below proves closed propositions by reduction.  It invokes no native
oracle and introduces no mathematical assumptions.  Row lemmas keep the
kernel reduction and subsequent rebuilds small.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability

theorem separatingRow036 : ∀ w : Fin 144, 36 ≠ w →
    incident (separatingWitness 36 w) 36 ∧ ¬incident (separatingWitness 36 w) w := by decide +kernel

theorem separatingRow037 : ∀ w : Fin 144, 37 ≠ w →
    incident (separatingWitness 37 w) 37 ∧ ¬incident (separatingWitness 37 w) w := by decide +kernel

theorem separatingRow038 : ∀ w : Fin 144, 38 ≠ w →
    incident (separatingWitness 38 w) 38 ∧ ¬incident (separatingWitness 38 w) w := by decide +kernel

theorem separatingRow039 : ∀ w : Fin 144, 39 ≠ w →
    incident (separatingWitness 39 w) 39 ∧ ¬incident (separatingWitness 39 w) w := by decide +kernel

theorem separatingRow040 : ∀ w : Fin 144, 40 ≠ w →
    incident (separatingWitness 40 w) 40 ∧ ¬incident (separatingWitness 40 w) w := by decide +kernel

theorem separatingRow041 : ∀ w : Fin 144, 41 ≠ w →
    incident (separatingWitness 41 w) 41 ∧ ¬incident (separatingWitness 41 w) w := by decide +kernel

theorem separatingRow042 : ∀ w : Fin 144, 42 ≠ w →
    incident (separatingWitness 42 w) 42 ∧ ¬incident (separatingWitness 42 w) w := by decide +kernel

theorem separatingRow043 : ∀ w : Fin 144, 43 ≠ w →
    incident (separatingWitness 43 w) 43 ∧ ¬incident (separatingWitness 43 w) w := by decide +kernel

theorem separatingRow044 : ∀ w : Fin 144, 44 ≠ w →
    incident (separatingWitness 44 w) 44 ∧ ¬incident (separatingWitness 44 w) w := by decide +kernel

theorem separatingRow045 : ∀ w : Fin 144, 45 ≠ w →
    incident (separatingWitness 45 w) 45 ∧ ¬incident (separatingWitness 45 w) w := by decide +kernel

theorem separatingRow046 : ∀ w : Fin 144, 46 ≠ w →
    incident (separatingWitness 46 w) 46 ∧ ¬incident (separatingWitness 46 w) w := by decide +kernel

theorem separatingRow047 : ∀ w : Fin 144, 47 ≠ w →
    incident (separatingWitness 47 w) 47 ∧ ¬incident (separatingWitness 47 w) w := by decide +kernel

end CubicalIndecomposability
