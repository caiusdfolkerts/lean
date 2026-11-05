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

theorem supportRow060 : ∀ v : Fin 144,
    0 ≤ slackNumerator 60 v ∧ (slackNumerator 60 v = 0 ↔ incident 60 v) := by decide +kernel

theorem supportRow061 : ∀ v : Fin 144,
    0 ≤ slackNumerator 61 v ∧ (slackNumerator 61 v = 0 ↔ incident 61 v) := by decide +kernel

theorem supportRow062 : ∀ v : Fin 144,
    0 ≤ slackNumerator 62 v ∧ (slackNumerator 62 v = 0 ↔ incident 62 v) := by decide +kernel

theorem supportRow063 : ∀ v : Fin 144,
    0 ≤ slackNumerator 63 v ∧ (slackNumerator 63 v = 0 ↔ incident 63 v) := by decide +kernel

theorem supportRow064 : ∀ v : Fin 144,
    0 ≤ slackNumerator 64 v ∧ (slackNumerator 64 v = 0 ↔ incident 64 v) := by decide +kernel

theorem supportRow065 : ∀ v : Fin 144,
    0 ≤ slackNumerator 65 v ∧ (slackNumerator 65 v = 0 ↔ incident 65 v) := by decide +kernel

theorem supportRow066 : ∀ v : Fin 144,
    0 ≤ slackNumerator 66 v ∧ (slackNumerator 66 v = 0 ↔ incident 66 v) := by decide +kernel

theorem supportRow067 : ∀ v : Fin 144,
    0 ≤ slackNumerator 67 v ∧ (slackNumerator 67 v = 0 ↔ incident 67 v) := by decide +kernel

theorem supportRow068 : ∀ v : Fin 144,
    0 ≤ slackNumerator 68 v ∧ (slackNumerator 68 v = 0 ↔ incident 68 v) := by decide +kernel

theorem supportRow069 : ∀ v : Fin 144,
    0 ≤ slackNumerator 69 v ∧ (slackNumerator 69 v = 0 ↔ incident 69 v) := by decide +kernel

end CubicalIndecomposability
