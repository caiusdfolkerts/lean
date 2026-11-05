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

theorem separatingRow120 : ∀ w : Fin 144, 120 ≠ w →
    incident (separatingWitness 120 w) 120 ∧ ¬incident (separatingWitness 120 w) w := by decide +kernel

theorem separatingRow121 : ∀ w : Fin 144, 121 ≠ w →
    incident (separatingWitness 121 w) 121 ∧ ¬incident (separatingWitness 121 w) w := by decide +kernel

theorem separatingRow122 : ∀ w : Fin 144, 122 ≠ w →
    incident (separatingWitness 122 w) 122 ∧ ¬incident (separatingWitness 122 w) w := by decide +kernel

theorem separatingRow123 : ∀ w : Fin 144, 123 ≠ w →
    incident (separatingWitness 123 w) 123 ∧ ¬incident (separatingWitness 123 w) w := by decide +kernel

theorem separatingRow124 : ∀ w : Fin 144, 124 ≠ w →
    incident (separatingWitness 124 w) 124 ∧ ¬incident (separatingWitness 124 w) w := by decide +kernel

theorem separatingRow125 : ∀ w : Fin 144, 125 ≠ w →
    incident (separatingWitness 125 w) 125 ∧ ¬incident (separatingWitness 125 w) w := by decide +kernel

theorem separatingRow126 : ∀ w : Fin 144, 126 ≠ w →
    incident (separatingWitness 126 w) 126 ∧ ¬incident (separatingWitness 126 w) w := by decide +kernel

theorem separatingRow127 : ∀ w : Fin 144, 127 ≠ w →
    incident (separatingWitness 127 w) 127 ∧ ¬incident (separatingWitness 127 w) w := by decide +kernel

theorem separatingRow128 : ∀ w : Fin 144, 128 ≠ w →
    incident (separatingWitness 128 w) 128 ∧ ¬incident (separatingWitness 128 w) w := by decide +kernel

theorem separatingRow129 : ∀ w : Fin 144, 129 ≠ w →
    incident (separatingWitness 129 w) 129 ∧ ¬incident (separatingWitness 129 w) w := by decide +kernel

theorem separatingRow130 : ∀ w : Fin 144, 130 ≠ w →
    incident (separatingWitness 130 w) 130 ∧ ¬incident (separatingWitness 130 w) w := by decide +kernel

theorem separatingRow131 : ∀ w : Fin 144, 131 ≠ w →
    incident (separatingWitness 131 w) 131 ∧ ¬incident (separatingWitness 131 w) w := by decide +kernel

end CubicalIndecomposability
