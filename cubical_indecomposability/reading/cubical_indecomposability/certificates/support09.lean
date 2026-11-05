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

theorem supportRow090 : ∀ v : Fin 144,
    0 ≤ slackNumerator 90 v ∧ (slackNumerator 90 v = 0 ↔ incident 90 v) := by decide +kernel

theorem supportRow091 : ∀ v : Fin 144,
    0 ≤ slackNumerator 91 v ∧ (slackNumerator 91 v = 0 ↔ incident 91 v) := by decide +kernel

theorem supportRow092 : ∀ v : Fin 144,
    0 ≤ slackNumerator 92 v ∧ (slackNumerator 92 v = 0 ↔ incident 92 v) := by decide +kernel

theorem supportRow093 : ∀ v : Fin 144,
    0 ≤ slackNumerator 93 v ∧ (slackNumerator 93 v = 0 ↔ incident 93 v) := by decide +kernel

theorem supportRow094 : ∀ v : Fin 144,
    0 ≤ slackNumerator 94 v ∧ (slackNumerator 94 v = 0 ↔ incident 94 v) := by decide +kernel

theorem supportRow095 : ∀ v : Fin 144,
    0 ≤ slackNumerator 95 v ∧ (slackNumerator 95 v = 0 ↔ incident 95 v) := by decide +kernel

theorem supportRow096 : ∀ v : Fin 144,
    0 ≤ slackNumerator 96 v ∧ (slackNumerator 96 v = 0 ↔ incident 96 v) := by decide +kernel

theorem supportRow097 : ∀ v : Fin 144,
    0 ≤ slackNumerator 97 v ∧ (slackNumerator 97 v = 0 ↔ incident 97 v) := by decide +kernel

theorem supportRow098 : ∀ v : Fin 144,
    0 ≤ slackNumerator 98 v ∧ (slackNumerator 98 v = 0 ↔ incident 98 v) := by decide +kernel

theorem supportRow099 : ∀ v : Fin 144,
    0 ≤ slackNumerator 99 v ∧ (slackNumerator 99 v = 0 ↔ incident 99 v) := by decide +kernel

end CubicalIndecomposability
