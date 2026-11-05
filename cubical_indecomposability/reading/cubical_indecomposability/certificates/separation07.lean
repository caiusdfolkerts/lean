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

theorem separatingRow084 : ∀ w : Fin 144, 84 ≠ w →
    incident (separatingWitness 84 w) 84 ∧ ¬incident (separatingWitness 84 w) w := by decide +kernel

theorem separatingRow085 : ∀ w : Fin 144, 85 ≠ w →
    incident (separatingWitness 85 w) 85 ∧ ¬incident (separatingWitness 85 w) w := by decide +kernel

theorem separatingRow086 : ∀ w : Fin 144, 86 ≠ w →
    incident (separatingWitness 86 w) 86 ∧ ¬incident (separatingWitness 86 w) w := by decide +kernel

theorem separatingRow087 : ∀ w : Fin 144, 87 ≠ w →
    incident (separatingWitness 87 w) 87 ∧ ¬incident (separatingWitness 87 w) w := by decide +kernel

theorem separatingRow088 : ∀ w : Fin 144, 88 ≠ w →
    incident (separatingWitness 88 w) 88 ∧ ¬incident (separatingWitness 88 w) w := by decide +kernel

theorem separatingRow089 : ∀ w : Fin 144, 89 ≠ w →
    incident (separatingWitness 89 w) 89 ∧ ¬incident (separatingWitness 89 w) w := by decide +kernel

theorem separatingRow090 : ∀ w : Fin 144, 90 ≠ w →
    incident (separatingWitness 90 w) 90 ∧ ¬incident (separatingWitness 90 w) w := by decide +kernel

theorem separatingRow091 : ∀ w : Fin 144, 91 ≠ w →
    incident (separatingWitness 91 w) 91 ∧ ¬incident (separatingWitness 91 w) w := by decide +kernel

theorem separatingRow092 : ∀ w : Fin 144, 92 ≠ w →
    incident (separatingWitness 92 w) 92 ∧ ¬incident (separatingWitness 92 w) w := by decide +kernel

theorem separatingRow093 : ∀ w : Fin 144, 93 ≠ w →
    incident (separatingWitness 93 w) 93 ∧ ¬incident (separatingWitness 93 w) w := by decide +kernel

theorem separatingRow094 : ∀ w : Fin 144, 94 ≠ w →
    incident (separatingWitness 94 w) 94 ∧ ¬incident (separatingWitness 94 w) w := by decide +kernel

theorem separatingRow095 : ∀ w : Fin 144, 95 ≠ w →
    incident (separatingWitness 95 w) 95 ∧ ¬incident (separatingWitness 95 w) w := by decide +kernel

end CubicalIndecomposability
