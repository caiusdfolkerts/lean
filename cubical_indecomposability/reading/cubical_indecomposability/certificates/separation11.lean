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

theorem separatingRow132 : ∀ w : Fin 144, 132 ≠ w →
    incident (separatingWitness 132 w) 132 ∧ ¬incident (separatingWitness 132 w) w := by decide +kernel

theorem separatingRow133 : ∀ w : Fin 144, 133 ≠ w →
    incident (separatingWitness 133 w) 133 ∧ ¬incident (separatingWitness 133 w) w := by decide +kernel

theorem separatingRow134 : ∀ w : Fin 144, 134 ≠ w →
    incident (separatingWitness 134 w) 134 ∧ ¬incident (separatingWitness 134 w) w := by decide +kernel

theorem separatingRow135 : ∀ w : Fin 144, 135 ≠ w →
    incident (separatingWitness 135 w) 135 ∧ ¬incident (separatingWitness 135 w) w := by decide +kernel

theorem separatingRow136 : ∀ w : Fin 144, 136 ≠ w →
    incident (separatingWitness 136 w) 136 ∧ ¬incident (separatingWitness 136 w) w := by decide +kernel

theorem separatingRow137 : ∀ w : Fin 144, 137 ≠ w →
    incident (separatingWitness 137 w) 137 ∧ ¬incident (separatingWitness 137 w) w := by decide +kernel

theorem separatingRow138 : ∀ w : Fin 144, 138 ≠ w →
    incident (separatingWitness 138 w) 138 ∧ ¬incident (separatingWitness 138 w) w := by decide +kernel

theorem separatingRow139 : ∀ w : Fin 144, 139 ≠ w →
    incident (separatingWitness 139 w) 139 ∧ ¬incident (separatingWitness 139 w) w := by decide +kernel

theorem separatingRow140 : ∀ w : Fin 144, 140 ≠ w →
    incident (separatingWitness 140 w) 140 ∧ ¬incident (separatingWitness 140 w) w := by decide +kernel

theorem separatingRow141 : ∀ w : Fin 144, 141 ≠ w →
    incident (separatingWitness 141 w) 141 ∧ ¬incident (separatingWitness 141 w) w := by decide +kernel

theorem separatingRow142 : ∀ w : Fin 144, 142 ≠ w →
    incident (separatingWitness 142 w) 142 ∧ ¬incident (separatingWitness 142 w) w := by decide +kernel

theorem separatingRow143 : ∀ w : Fin 144, 143 ≠ w →
    incident (separatingWitness 143 w) 143 ∧ ¬incident (separatingWitness 143 w) w := by decide +kernel

end CubicalIndecomposability
