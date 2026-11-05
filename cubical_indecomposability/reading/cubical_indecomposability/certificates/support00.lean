import cubical_indecomposability.data
import Mathlib.Tactic.FinCases

/-! Exact integer arithmetic and finite incidences, checked by Lean's kernel.
`decide +kernel` below proves closed propositions by reduction.  It invokes no native
oracle and introduces no mathematical assumptions.  Row lemmas keep the
kernel reduction and subsequent rebuilds small.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace CubicalIndecomposability

theorem supportRow000 : ∀ v : Fin 144,
    0 ≤ slackNumerator 0 v ∧ (slackNumerator 0 v = 0 ↔ incident 0 v) := by decide +kernel

theorem supportRow001 : ∀ v : Fin 144,
    0 ≤ slackNumerator 1 v ∧ (slackNumerator 1 v = 0 ↔ incident 1 v) := by decide +kernel

theorem supportRow002 : ∀ v : Fin 144,
    0 ≤ slackNumerator 2 v ∧ (slackNumerator 2 v = 0 ↔ incident 2 v) := by decide +kernel

theorem supportRow003 : ∀ v : Fin 144,
    0 ≤ slackNumerator 3 v ∧ (slackNumerator 3 v = 0 ↔ incident 3 v) := by decide +kernel

theorem supportRow004 : ∀ v : Fin 144,
    0 ≤ slackNumerator 4 v ∧ (slackNumerator 4 v = 0 ↔ incident 4 v) := by decide +kernel

theorem supportRow005 : ∀ v : Fin 144,
    0 ≤ slackNumerator 5 v ∧ (slackNumerator 5 v = 0 ↔ incident 5 v) := by decide +kernel

theorem supportRow006 : ∀ v : Fin 144,
    0 ≤ slackNumerator 6 v ∧ (slackNumerator 6 v = 0 ↔ incident 6 v) := by decide +kernel

theorem supportRow007 : ∀ v : Fin 144,
    0 ≤ slackNumerator 7 v ∧ (slackNumerator 7 v = 0 ↔ incident 7 v) := by decide +kernel

theorem supportRow008 : ∀ v : Fin 144,
    0 ≤ slackNumerator 8 v ∧ (slackNumerator 8 v = 0 ↔ incident 8 v) := by decide +kernel

theorem supportRow009 : ∀ v : Fin 144,
    0 ≤ slackNumerator 9 v ∧ (slackNumerator 9 v = 0 ↔ incident 9 v) := by decide +kernel

end CubicalIndecomposability
