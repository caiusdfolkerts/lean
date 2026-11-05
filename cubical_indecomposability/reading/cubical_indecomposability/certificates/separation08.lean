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

theorem separatingRow096 : ∀ w : Fin 144, 96 ≠ w →
    incident (separatingWitness 96 w) 96 ∧ ¬incident (separatingWitness 96 w) w := by decide +kernel

theorem separatingRow097 : ∀ w : Fin 144, 97 ≠ w →
    incident (separatingWitness 97 w) 97 ∧ ¬incident (separatingWitness 97 w) w := by decide +kernel

theorem separatingRow098 : ∀ w : Fin 144, 98 ≠ w →
    incident (separatingWitness 98 w) 98 ∧ ¬incident (separatingWitness 98 w) w := by decide +kernel

theorem separatingRow099 : ∀ w : Fin 144, 99 ≠ w →
    incident (separatingWitness 99 w) 99 ∧ ¬incident (separatingWitness 99 w) w := by decide +kernel

theorem separatingRow100 : ∀ w : Fin 144, 100 ≠ w →
    incident (separatingWitness 100 w) 100 ∧ ¬incident (separatingWitness 100 w) w := by decide +kernel

theorem separatingRow101 : ∀ w : Fin 144, 101 ≠ w →
    incident (separatingWitness 101 w) 101 ∧ ¬incident (separatingWitness 101 w) w := by decide +kernel

theorem separatingRow102 : ∀ w : Fin 144, 102 ≠ w →
    incident (separatingWitness 102 w) 102 ∧ ¬incident (separatingWitness 102 w) w := by decide +kernel

theorem separatingRow103 : ∀ w : Fin 144, 103 ≠ w →
    incident (separatingWitness 103 w) 103 ∧ ¬incident (separatingWitness 103 w) w := by decide +kernel

theorem separatingRow104 : ∀ w : Fin 144, 104 ≠ w →
    incident (separatingWitness 104 w) 104 ∧ ¬incident (separatingWitness 104 w) w := by decide +kernel

theorem separatingRow105 : ∀ w : Fin 144, 105 ≠ w →
    incident (separatingWitness 105 w) 105 ∧ ¬incident (separatingWitness 105 w) w := by decide +kernel

theorem separatingRow106 : ∀ w : Fin 144, 106 ≠ w →
    incident (separatingWitness 106 w) 106 ∧ ¬incident (separatingWitness 106 w) w := by decide +kernel

theorem separatingRow107 : ∀ w : Fin 144, 107 ≠ w →
    incident (separatingWitness 107 w) 107 ∧ ¬incident (separatingWitness 107 w) w := by decide +kernel

end CubicalIndecomposability
