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

theorem separatingRow024 : ∀ w : Fin 144, 24 ≠ w →
    incident (separatingWitness 24 w) 24 ∧ ¬incident (separatingWitness 24 w) w := by decide +kernel

theorem separatingRow025 : ∀ w : Fin 144, 25 ≠ w →
    incident (separatingWitness 25 w) 25 ∧ ¬incident (separatingWitness 25 w) w := by decide +kernel

theorem separatingRow026 : ∀ w : Fin 144, 26 ≠ w →
    incident (separatingWitness 26 w) 26 ∧ ¬incident (separatingWitness 26 w) w := by decide +kernel

theorem separatingRow027 : ∀ w : Fin 144, 27 ≠ w →
    incident (separatingWitness 27 w) 27 ∧ ¬incident (separatingWitness 27 w) w := by decide +kernel

theorem separatingRow028 : ∀ w : Fin 144, 28 ≠ w →
    incident (separatingWitness 28 w) 28 ∧ ¬incident (separatingWitness 28 w) w := by decide +kernel

theorem separatingRow029 : ∀ w : Fin 144, 29 ≠ w →
    incident (separatingWitness 29 w) 29 ∧ ¬incident (separatingWitness 29 w) w := by decide +kernel

theorem separatingRow030 : ∀ w : Fin 144, 30 ≠ w →
    incident (separatingWitness 30 w) 30 ∧ ¬incident (separatingWitness 30 w) w := by decide +kernel

theorem separatingRow031 : ∀ w : Fin 144, 31 ≠ w →
    incident (separatingWitness 31 w) 31 ∧ ¬incident (separatingWitness 31 w) w := by decide +kernel

theorem separatingRow032 : ∀ w : Fin 144, 32 ≠ w →
    incident (separatingWitness 32 w) 32 ∧ ¬incident (separatingWitness 32 w) w := by decide +kernel

theorem separatingRow033 : ∀ w : Fin 144, 33 ≠ w →
    incident (separatingWitness 33 w) 33 ∧ ¬incident (separatingWitness 33 w) w := by decide +kernel

theorem separatingRow034 : ∀ w : Fin 144, 34 ≠ w →
    incident (separatingWitness 34 w) 34 ∧ ¬incident (separatingWitness 34 w) w := by decide +kernel

theorem separatingRow035 : ∀ w : Fin 144, 35 ≠ w →
    incident (separatingWitness 35 w) 35 ∧ ¬incident (separatingWitness 35 w) w := by decide +kernel

end CubicalIndecomposability
