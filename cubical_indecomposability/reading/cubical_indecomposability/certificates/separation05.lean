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

theorem separatingRow060 : ∀ w : Fin 144, 60 ≠ w →
    incident (separatingWitness 60 w) 60 ∧ ¬incident (separatingWitness 60 w) w := by decide +kernel

theorem separatingRow061 : ∀ w : Fin 144, 61 ≠ w →
    incident (separatingWitness 61 w) 61 ∧ ¬incident (separatingWitness 61 w) w := by decide +kernel

theorem separatingRow062 : ∀ w : Fin 144, 62 ≠ w →
    incident (separatingWitness 62 w) 62 ∧ ¬incident (separatingWitness 62 w) w := by decide +kernel

theorem separatingRow063 : ∀ w : Fin 144, 63 ≠ w →
    incident (separatingWitness 63 w) 63 ∧ ¬incident (separatingWitness 63 w) w := by decide +kernel

theorem separatingRow064 : ∀ w : Fin 144, 64 ≠ w →
    incident (separatingWitness 64 w) 64 ∧ ¬incident (separatingWitness 64 w) w := by decide +kernel

theorem separatingRow065 : ∀ w : Fin 144, 65 ≠ w →
    incident (separatingWitness 65 w) 65 ∧ ¬incident (separatingWitness 65 w) w := by decide +kernel

theorem separatingRow066 : ∀ w : Fin 144, 66 ≠ w →
    incident (separatingWitness 66 w) 66 ∧ ¬incident (separatingWitness 66 w) w := by decide +kernel

theorem separatingRow067 : ∀ w : Fin 144, 67 ≠ w →
    incident (separatingWitness 67 w) 67 ∧ ¬incident (separatingWitness 67 w) w := by decide +kernel

theorem separatingRow068 : ∀ w : Fin 144, 68 ≠ w →
    incident (separatingWitness 68 w) 68 ∧ ¬incident (separatingWitness 68 w) w := by decide +kernel

theorem separatingRow069 : ∀ w : Fin 144, 69 ≠ w →
    incident (separatingWitness 69 w) 69 ∧ ¬incident (separatingWitness 69 w) w := by decide +kernel

theorem separatingRow070 : ∀ w : Fin 144, 70 ≠ w →
    incident (separatingWitness 70 w) 70 ∧ ¬incident (separatingWitness 70 w) w := by decide +kernel

theorem separatingRow071 : ∀ w : Fin 144, 71 ≠ w →
    incident (separatingWitness 71 w) 71 ∧ ¬incident (separatingWitness 71 w) w := by decide +kernel

end CubicalIndecomposability
