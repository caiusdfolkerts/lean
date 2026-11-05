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

theorem separatingRow000 : ∀ w : Fin 144, 0 ≠ w →
    incident (separatingWitness 0 w) 0 ∧ ¬incident (separatingWitness 0 w) w := by decide +kernel

theorem separatingRow001 : ∀ w : Fin 144, 1 ≠ w →
    incident (separatingWitness 1 w) 1 ∧ ¬incident (separatingWitness 1 w) w := by decide +kernel

theorem separatingRow002 : ∀ w : Fin 144, 2 ≠ w →
    incident (separatingWitness 2 w) 2 ∧ ¬incident (separatingWitness 2 w) w := by decide +kernel

theorem separatingRow003 : ∀ w : Fin 144, 3 ≠ w →
    incident (separatingWitness 3 w) 3 ∧ ¬incident (separatingWitness 3 w) w := by decide +kernel

theorem separatingRow004 : ∀ w : Fin 144, 4 ≠ w →
    incident (separatingWitness 4 w) 4 ∧ ¬incident (separatingWitness 4 w) w := by decide +kernel

theorem separatingRow005 : ∀ w : Fin 144, 5 ≠ w →
    incident (separatingWitness 5 w) 5 ∧ ¬incident (separatingWitness 5 w) w := by decide +kernel

theorem separatingRow006 : ∀ w : Fin 144, 6 ≠ w →
    incident (separatingWitness 6 w) 6 ∧ ¬incident (separatingWitness 6 w) w := by decide +kernel

theorem separatingRow007 : ∀ w : Fin 144, 7 ≠ w →
    incident (separatingWitness 7 w) 7 ∧ ¬incident (separatingWitness 7 w) w := by decide +kernel

theorem separatingRow008 : ∀ w : Fin 144, 8 ≠ w →
    incident (separatingWitness 8 w) 8 ∧ ¬incident (separatingWitness 8 w) w := by decide +kernel

theorem separatingRow009 : ∀ w : Fin 144, 9 ≠ w →
    incident (separatingWitness 9 w) 9 ∧ ¬incident (separatingWitness 9 w) w := by decide +kernel

theorem separatingRow010 : ∀ w : Fin 144, 10 ≠ w →
    incident (separatingWitness 10 w) 10 ∧ ¬incident (separatingWitness 10 w) w := by decide +kernel

theorem separatingRow011 : ∀ w : Fin 144, 11 ≠ w →
    incident (separatingWitness 11 w) 11 ∧ ¬incident (separatingWitness 11 w) w := by decide +kernel

end CubicalIndecomposability
