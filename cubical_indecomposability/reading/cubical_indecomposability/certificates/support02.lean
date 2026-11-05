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

theorem supportRow020 : ∀ v : Fin 144,
    0 ≤ slackNumerator 20 v ∧ (slackNumerator 20 v = 0 ↔ incident 20 v) := by decide +kernel

theorem supportRow021 : ∀ v : Fin 144,
    0 ≤ slackNumerator 21 v ∧ (slackNumerator 21 v = 0 ↔ incident 21 v) := by decide +kernel

theorem supportRow022 : ∀ v : Fin 144,
    0 ≤ slackNumerator 22 v ∧ (slackNumerator 22 v = 0 ↔ incident 22 v) := by decide +kernel

theorem supportRow023 : ∀ v : Fin 144,
    0 ≤ slackNumerator 23 v ∧ (slackNumerator 23 v = 0 ↔ incident 23 v) := by decide +kernel

theorem supportRow024 : ∀ v : Fin 144,
    0 ≤ slackNumerator 24 v ∧ (slackNumerator 24 v = 0 ↔ incident 24 v) := by decide +kernel

theorem supportRow025 : ∀ v : Fin 144,
    0 ≤ slackNumerator 25 v ∧ (slackNumerator 25 v = 0 ↔ incident 25 v) := by decide +kernel

theorem supportRow026 : ∀ v : Fin 144,
    0 ≤ slackNumerator 26 v ∧ (slackNumerator 26 v = 0 ↔ incident 26 v) := by decide +kernel

theorem supportRow027 : ∀ v : Fin 144,
    0 ≤ slackNumerator 27 v ∧ (slackNumerator 27 v = 0 ↔ incident 27 v) := by decide +kernel

theorem supportRow028 : ∀ v : Fin 144,
    0 ≤ slackNumerator 28 v ∧ (slackNumerator 28 v = 0 ↔ incident 28 v) := by decide +kernel

theorem supportRow029 : ∀ v : Fin 144,
    0 ≤ slackNumerator 29 v ∧ (slackNumerator 29 v = 0 ↔ incident 29 v) := by decide +kernel

end CubicalIndecomposability
