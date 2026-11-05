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

theorem separatingRow108 : ∀ w : Fin 144, 108 ≠ w →
    incident (separatingWitness 108 w) 108 ∧ ¬incident (separatingWitness 108 w) w := by decide +kernel

theorem separatingRow109 : ∀ w : Fin 144, 109 ≠ w →
    incident (separatingWitness 109 w) 109 ∧ ¬incident (separatingWitness 109 w) w := by decide +kernel

theorem separatingRow110 : ∀ w : Fin 144, 110 ≠ w →
    incident (separatingWitness 110 w) 110 ∧ ¬incident (separatingWitness 110 w) w := by decide +kernel

theorem separatingRow111 : ∀ w : Fin 144, 111 ≠ w →
    incident (separatingWitness 111 w) 111 ∧ ¬incident (separatingWitness 111 w) w := by decide +kernel

theorem separatingRow112 : ∀ w : Fin 144, 112 ≠ w →
    incident (separatingWitness 112 w) 112 ∧ ¬incident (separatingWitness 112 w) w := by decide +kernel

theorem separatingRow113 : ∀ w : Fin 144, 113 ≠ w →
    incident (separatingWitness 113 w) 113 ∧ ¬incident (separatingWitness 113 w) w := by decide +kernel

theorem separatingRow114 : ∀ w : Fin 144, 114 ≠ w →
    incident (separatingWitness 114 w) 114 ∧ ¬incident (separatingWitness 114 w) w := by decide +kernel

theorem separatingRow115 : ∀ w : Fin 144, 115 ≠ w →
    incident (separatingWitness 115 w) 115 ∧ ¬incident (separatingWitness 115 w) w := by decide +kernel

theorem separatingRow116 : ∀ w : Fin 144, 116 ≠ w →
    incident (separatingWitness 116 w) 116 ∧ ¬incident (separatingWitness 116 w) w := by decide +kernel

theorem separatingRow117 : ∀ w : Fin 144, 117 ≠ w →
    incident (separatingWitness 117 w) 117 ∧ ¬incident (separatingWitness 117 w) w := by decide +kernel

theorem separatingRow118 : ∀ w : Fin 144, 118 ≠ w →
    incident (separatingWitness 118 w) 118 ∧ ¬incident (separatingWitness 118 w) w := by decide +kernel

theorem separatingRow119 : ∀ w : Fin 144, 119 ≠ w →
    incident (separatingWitness 119 w) 119 ∧ ¬incident (separatingWitness 119 w) w := by decide +kernel

end CubicalIndecomposability
