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

theorem supportRow080 : ∀ v : Fin 144,
    0 ≤ slackNumerator 80 v ∧ (slackNumerator 80 v = 0 ↔ incident 80 v) := by decide +kernel

theorem supportRow081 : ∀ v : Fin 144,
    0 ≤ slackNumerator 81 v ∧ (slackNumerator 81 v = 0 ↔ incident 81 v) := by decide +kernel

theorem supportRow082 : ∀ v : Fin 144,
    0 ≤ slackNumerator 82 v ∧ (slackNumerator 82 v = 0 ↔ incident 82 v) := by decide +kernel

theorem supportRow083 : ∀ v : Fin 144,
    0 ≤ slackNumerator 83 v ∧ (slackNumerator 83 v = 0 ↔ incident 83 v) := by decide +kernel

theorem supportRow084 : ∀ v : Fin 144,
    0 ≤ slackNumerator 84 v ∧ (slackNumerator 84 v = 0 ↔ incident 84 v) := by decide +kernel

theorem supportRow085 : ∀ v : Fin 144,
    0 ≤ slackNumerator 85 v ∧ (slackNumerator 85 v = 0 ↔ incident 85 v) := by decide +kernel

theorem supportRow086 : ∀ v : Fin 144,
    0 ≤ slackNumerator 86 v ∧ (slackNumerator 86 v = 0 ↔ incident 86 v) := by decide +kernel

theorem supportRow087 : ∀ v : Fin 144,
    0 ≤ slackNumerator 87 v ∧ (slackNumerator 87 v = 0 ↔ incident 87 v) := by decide +kernel

theorem supportRow088 : ∀ v : Fin 144,
    0 ≤ slackNumerator 88 v ∧ (slackNumerator 88 v = 0 ↔ incident 88 v) := by decide +kernel

theorem supportRow089 : ∀ v : Fin 144,
    0 ≤ slackNumerator 89 v ∧ (slackNumerator 89 v = 0 ↔ incident 89 v) := by decide +kernel

end CubicalIndecomposability
