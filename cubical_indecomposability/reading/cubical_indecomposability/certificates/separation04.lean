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

theorem separatingRow048 : ∀ w : Fin 144, 48 ≠ w →
    incident (separatingWitness 48 w) 48 ∧ ¬incident (separatingWitness 48 w) w := by decide +kernel

theorem separatingRow049 : ∀ w : Fin 144, 49 ≠ w →
    incident (separatingWitness 49 w) 49 ∧ ¬incident (separatingWitness 49 w) w := by decide +kernel

theorem separatingRow050 : ∀ w : Fin 144, 50 ≠ w →
    incident (separatingWitness 50 w) 50 ∧ ¬incident (separatingWitness 50 w) w := by decide +kernel

theorem separatingRow051 : ∀ w : Fin 144, 51 ≠ w →
    incident (separatingWitness 51 w) 51 ∧ ¬incident (separatingWitness 51 w) w := by decide +kernel

theorem separatingRow052 : ∀ w : Fin 144, 52 ≠ w →
    incident (separatingWitness 52 w) 52 ∧ ¬incident (separatingWitness 52 w) w := by decide +kernel

theorem separatingRow053 : ∀ w : Fin 144, 53 ≠ w →
    incident (separatingWitness 53 w) 53 ∧ ¬incident (separatingWitness 53 w) w := by decide +kernel

theorem separatingRow054 : ∀ w : Fin 144, 54 ≠ w →
    incident (separatingWitness 54 w) 54 ∧ ¬incident (separatingWitness 54 w) w := by decide +kernel

theorem separatingRow055 : ∀ w : Fin 144, 55 ≠ w →
    incident (separatingWitness 55 w) 55 ∧ ¬incident (separatingWitness 55 w) w := by decide +kernel

theorem separatingRow056 : ∀ w : Fin 144, 56 ≠ w →
    incident (separatingWitness 56 w) 56 ∧ ¬incident (separatingWitness 56 w) w := by decide +kernel

theorem separatingRow057 : ∀ w : Fin 144, 57 ≠ w →
    incident (separatingWitness 57 w) 57 ∧ ¬incident (separatingWitness 57 w) w := by decide +kernel

theorem separatingRow058 : ∀ w : Fin 144, 58 ≠ w →
    incident (separatingWitness 58 w) 58 ∧ ¬incident (separatingWitness 58 w) w := by decide +kernel

theorem separatingRow059 : ∀ w : Fin 144, 59 ≠ w →
    incident (separatingWitness 59 w) 59 ∧ ¬incident (separatingWitness 59 w) w := by decide +kernel

end CubicalIndecomposability
