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

theorem supportRow050 : ∀ v : Fin 144,
    0 ≤ slackNumerator 50 v ∧ (slackNumerator 50 v = 0 ↔ incident 50 v) := by decide +kernel

theorem supportRow051 : ∀ v : Fin 144,
    0 ≤ slackNumerator 51 v ∧ (slackNumerator 51 v = 0 ↔ incident 51 v) := by decide +kernel

theorem supportRow052 : ∀ v : Fin 144,
    0 ≤ slackNumerator 52 v ∧ (slackNumerator 52 v = 0 ↔ incident 52 v) := by decide +kernel

theorem supportRow053 : ∀ v : Fin 144,
    0 ≤ slackNumerator 53 v ∧ (slackNumerator 53 v = 0 ↔ incident 53 v) := by decide +kernel

theorem supportRow054 : ∀ v : Fin 144,
    0 ≤ slackNumerator 54 v ∧ (slackNumerator 54 v = 0 ↔ incident 54 v) := by decide +kernel

theorem supportRow055 : ∀ v : Fin 144,
    0 ≤ slackNumerator 55 v ∧ (slackNumerator 55 v = 0 ↔ incident 55 v) := by decide +kernel

theorem supportRow056 : ∀ v : Fin 144,
    0 ≤ slackNumerator 56 v ∧ (slackNumerator 56 v = 0 ↔ incident 56 v) := by decide +kernel

theorem supportRow057 : ∀ v : Fin 144,
    0 ≤ slackNumerator 57 v ∧ (slackNumerator 57 v = 0 ↔ incident 57 v) := by decide +kernel

theorem supportRow058 : ∀ v : Fin 144,
    0 ≤ slackNumerator 58 v ∧ (slackNumerator 58 v = 0 ↔ incident 58 v) := by decide +kernel

theorem supportRow059 : ∀ v : Fin 144,
    0 ≤ slackNumerator 59 v ∧ (slackNumerator 59 v = 0 ↔ incident 59 v) := by decide +kernel

end CubicalIndecomposability
