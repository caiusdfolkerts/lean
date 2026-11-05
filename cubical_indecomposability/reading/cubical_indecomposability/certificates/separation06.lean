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

theorem separatingRow072 : ∀ w : Fin 144, 72 ≠ w →
    incident (separatingWitness 72 w) 72 ∧ ¬incident (separatingWitness 72 w) w := by decide +kernel

theorem separatingRow073 : ∀ w : Fin 144, 73 ≠ w →
    incident (separatingWitness 73 w) 73 ∧ ¬incident (separatingWitness 73 w) w := by decide +kernel

theorem separatingRow074 : ∀ w : Fin 144, 74 ≠ w →
    incident (separatingWitness 74 w) 74 ∧ ¬incident (separatingWitness 74 w) w := by decide +kernel

theorem separatingRow075 : ∀ w : Fin 144, 75 ≠ w →
    incident (separatingWitness 75 w) 75 ∧ ¬incident (separatingWitness 75 w) w := by decide +kernel

theorem separatingRow076 : ∀ w : Fin 144, 76 ≠ w →
    incident (separatingWitness 76 w) 76 ∧ ¬incident (separatingWitness 76 w) w := by decide +kernel

theorem separatingRow077 : ∀ w : Fin 144, 77 ≠ w →
    incident (separatingWitness 77 w) 77 ∧ ¬incident (separatingWitness 77 w) w := by decide +kernel

theorem separatingRow078 : ∀ w : Fin 144, 78 ≠ w →
    incident (separatingWitness 78 w) 78 ∧ ¬incident (separatingWitness 78 w) w := by decide +kernel

theorem separatingRow079 : ∀ w : Fin 144, 79 ≠ w →
    incident (separatingWitness 79 w) 79 ∧ ¬incident (separatingWitness 79 w) w := by decide +kernel

theorem separatingRow080 : ∀ w : Fin 144, 80 ≠ w →
    incident (separatingWitness 80 w) 80 ∧ ¬incident (separatingWitness 80 w) w := by decide +kernel

theorem separatingRow081 : ∀ w : Fin 144, 81 ≠ w →
    incident (separatingWitness 81 w) 81 ∧ ¬incident (separatingWitness 81 w) w := by decide +kernel

theorem separatingRow082 : ∀ w : Fin 144, 82 ≠ w →
    incident (separatingWitness 82 w) 82 ∧ ¬incident (separatingWitness 82 w) w := by decide +kernel

theorem separatingRow083 : ∀ w : Fin 144, 83 ≠ w →
    incident (separatingWitness 83 w) 83 ∧ ¬incident (separatingWitness 83 w) w := by decide +kernel

end CubicalIndecomposability
