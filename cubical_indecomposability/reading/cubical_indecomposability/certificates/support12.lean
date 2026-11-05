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

theorem supportRow120 : ∀ v : Fin 144,
    0 ≤ slackNumerator 120 v ∧ (slackNumerator 120 v = 0 ↔ incident 120 v) := by decide +kernel

theorem supportRow121 : ∀ v : Fin 144,
    0 ≤ slackNumerator 121 v ∧ (slackNumerator 121 v = 0 ↔ incident 121 v) := by decide +kernel

theorem supportRow122 : ∀ v : Fin 144,
    0 ≤ slackNumerator 122 v ∧ (slackNumerator 122 v = 0 ↔ incident 122 v) := by decide +kernel

theorem supportRow123 : ∀ v : Fin 144,
    0 ≤ slackNumerator 123 v ∧ (slackNumerator 123 v = 0 ↔ incident 123 v) := by decide +kernel

theorem supportRow124 : ∀ v : Fin 144,
    0 ≤ slackNumerator 124 v ∧ (slackNumerator 124 v = 0 ↔ incident 124 v) := by decide +kernel

theorem supportRow125 : ∀ v : Fin 144,
    0 ≤ slackNumerator 125 v ∧ (slackNumerator 125 v = 0 ↔ incident 125 v) := by decide +kernel

theorem supportRow126 : ∀ v : Fin 144,
    0 ≤ slackNumerator 126 v ∧ (slackNumerator 126 v = 0 ↔ incident 126 v) := by decide +kernel

theorem supportRow127 : ∀ v : Fin 144,
    0 ≤ slackNumerator 127 v ∧ (slackNumerator 127 v = 0 ↔ incident 127 v) := by decide +kernel

theorem supportRow128 : ∀ v : Fin 144,
    0 ≤ slackNumerator 128 v ∧ (slackNumerator 128 v = 0 ↔ incident 128 v) := by decide +kernel

theorem supportRow129 : ∀ v : Fin 144,
    0 ≤ slackNumerator 129 v ∧ (slackNumerator 129 v = 0 ↔ incident 129 v) := by decide +kernel

end CubicalIndecomposability
