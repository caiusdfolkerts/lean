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

theorem supportRow070 : ∀ v : Fin 144,
    0 ≤ slackNumerator 70 v ∧ (slackNumerator 70 v = 0 ↔ incident 70 v) := by decide +kernel

theorem supportRow071 : ∀ v : Fin 144,
    0 ≤ slackNumerator 71 v ∧ (slackNumerator 71 v = 0 ↔ incident 71 v) := by decide +kernel

theorem supportRow072 : ∀ v : Fin 144,
    0 ≤ slackNumerator 72 v ∧ (slackNumerator 72 v = 0 ↔ incident 72 v) := by decide +kernel

theorem supportRow073 : ∀ v : Fin 144,
    0 ≤ slackNumerator 73 v ∧ (slackNumerator 73 v = 0 ↔ incident 73 v) := by decide +kernel

theorem supportRow074 : ∀ v : Fin 144,
    0 ≤ slackNumerator 74 v ∧ (slackNumerator 74 v = 0 ↔ incident 74 v) := by decide +kernel

theorem supportRow075 : ∀ v : Fin 144,
    0 ≤ slackNumerator 75 v ∧ (slackNumerator 75 v = 0 ↔ incident 75 v) := by decide +kernel

theorem supportRow076 : ∀ v : Fin 144,
    0 ≤ slackNumerator 76 v ∧ (slackNumerator 76 v = 0 ↔ incident 76 v) := by decide +kernel

theorem supportRow077 : ∀ v : Fin 144,
    0 ≤ slackNumerator 77 v ∧ (slackNumerator 77 v = 0 ↔ incident 77 v) := by decide +kernel

theorem supportRow078 : ∀ v : Fin 144,
    0 ≤ slackNumerator 78 v ∧ (slackNumerator 78 v = 0 ↔ incident 78 v) := by decide +kernel

theorem supportRow079 : ∀ v : Fin 144,
    0 ≤ slackNumerator 79 v ∧ (slackNumerator 79 v = 0 ↔ incident 79 v) := by decide +kernel

end CubicalIndecomposability
