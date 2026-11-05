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

theorem separatingRow012 : ∀ w : Fin 144, 12 ≠ w →
    incident (separatingWitness 12 w) 12 ∧ ¬incident (separatingWitness 12 w) w := by decide +kernel

theorem separatingRow013 : ∀ w : Fin 144, 13 ≠ w →
    incident (separatingWitness 13 w) 13 ∧ ¬incident (separatingWitness 13 w) w := by decide +kernel

theorem separatingRow014 : ∀ w : Fin 144, 14 ≠ w →
    incident (separatingWitness 14 w) 14 ∧ ¬incident (separatingWitness 14 w) w := by decide +kernel

theorem separatingRow015 : ∀ w : Fin 144, 15 ≠ w →
    incident (separatingWitness 15 w) 15 ∧ ¬incident (separatingWitness 15 w) w := by decide +kernel

theorem separatingRow016 : ∀ w : Fin 144, 16 ≠ w →
    incident (separatingWitness 16 w) 16 ∧ ¬incident (separatingWitness 16 w) w := by decide +kernel

theorem separatingRow017 : ∀ w : Fin 144, 17 ≠ w →
    incident (separatingWitness 17 w) 17 ∧ ¬incident (separatingWitness 17 w) w := by decide +kernel

theorem separatingRow018 : ∀ w : Fin 144, 18 ≠ w →
    incident (separatingWitness 18 w) 18 ∧ ¬incident (separatingWitness 18 w) w := by decide +kernel

theorem separatingRow019 : ∀ w : Fin 144, 19 ≠ w →
    incident (separatingWitness 19 w) 19 ∧ ¬incident (separatingWitness 19 w) w := by decide +kernel

theorem separatingRow020 : ∀ w : Fin 144, 20 ≠ w →
    incident (separatingWitness 20 w) 20 ∧ ¬incident (separatingWitness 20 w) w := by decide +kernel

theorem separatingRow021 : ∀ w : Fin 144, 21 ≠ w →
    incident (separatingWitness 21 w) 21 ∧ ¬incident (separatingWitness 21 w) w := by decide +kernel

theorem separatingRow022 : ∀ w : Fin 144, 22 ≠ w →
    incident (separatingWitness 22 w) 22 ∧ ¬incident (separatingWitness 22 w) w := by decide +kernel

theorem separatingRow023 : ∀ w : Fin 144, 23 ≠ w →
    incident (separatingWitness 23 w) 23 ∧ ¬incident (separatingWitness 23 w) w := by decide +kernel

end CubicalIndecomposability
