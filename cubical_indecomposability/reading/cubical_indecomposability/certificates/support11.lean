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

theorem supportRow110 : ∀ v : Fin 144,
    0 ≤ slackNumerator 110 v ∧ (slackNumerator 110 v = 0 ↔ incident 110 v) := by decide +kernel

theorem supportRow111 : ∀ v : Fin 144,
    0 ≤ slackNumerator 111 v ∧ (slackNumerator 111 v = 0 ↔ incident 111 v) := by decide +kernel

theorem supportRow112 : ∀ v : Fin 144,
    0 ≤ slackNumerator 112 v ∧ (slackNumerator 112 v = 0 ↔ incident 112 v) := by decide +kernel

theorem supportRow113 : ∀ v : Fin 144,
    0 ≤ slackNumerator 113 v ∧ (slackNumerator 113 v = 0 ↔ incident 113 v) := by decide +kernel

theorem supportRow114 : ∀ v : Fin 144,
    0 ≤ slackNumerator 114 v ∧ (slackNumerator 114 v = 0 ↔ incident 114 v) := by decide +kernel

theorem supportRow115 : ∀ v : Fin 144,
    0 ≤ slackNumerator 115 v ∧ (slackNumerator 115 v = 0 ↔ incident 115 v) := by decide +kernel

theorem supportRow116 : ∀ v : Fin 144,
    0 ≤ slackNumerator 116 v ∧ (slackNumerator 116 v = 0 ↔ incident 116 v) := by decide +kernel

theorem supportRow117 : ∀ v : Fin 144,
    0 ≤ slackNumerator 117 v ∧ (slackNumerator 117 v = 0 ↔ incident 117 v) := by decide +kernel

theorem supportRow118 : ∀ v : Fin 144,
    0 ≤ slackNumerator 118 v ∧ (slackNumerator 118 v = 0 ↔ incident 118 v) := by decide +kernel

theorem supportRow119 : ∀ v : Fin 144,
    0 ≤ slackNumerator 119 v ∧ (slackNumerator 119 v = 0 ↔ incident 119 v) := by decide +kernel

end CubicalIndecomposability
