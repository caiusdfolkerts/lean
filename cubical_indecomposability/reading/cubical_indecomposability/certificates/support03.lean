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

theorem supportRow030 : ∀ v : Fin 144,
    0 ≤ slackNumerator 30 v ∧ (slackNumerator 30 v = 0 ↔ incident 30 v) := by decide +kernel

theorem supportRow031 : ∀ v : Fin 144,
    0 ≤ slackNumerator 31 v ∧ (slackNumerator 31 v = 0 ↔ incident 31 v) := by decide +kernel

theorem supportRow032 : ∀ v : Fin 144,
    0 ≤ slackNumerator 32 v ∧ (slackNumerator 32 v = 0 ↔ incident 32 v) := by decide +kernel

theorem supportRow033 : ∀ v : Fin 144,
    0 ≤ slackNumerator 33 v ∧ (slackNumerator 33 v = 0 ↔ incident 33 v) := by decide +kernel

theorem supportRow034 : ∀ v : Fin 144,
    0 ≤ slackNumerator 34 v ∧ (slackNumerator 34 v = 0 ↔ incident 34 v) := by decide +kernel

theorem supportRow035 : ∀ v : Fin 144,
    0 ≤ slackNumerator 35 v ∧ (slackNumerator 35 v = 0 ↔ incident 35 v) := by decide +kernel

theorem supportRow036 : ∀ v : Fin 144,
    0 ≤ slackNumerator 36 v ∧ (slackNumerator 36 v = 0 ↔ incident 36 v) := by decide +kernel

theorem supportRow037 : ∀ v : Fin 144,
    0 ≤ slackNumerator 37 v ∧ (slackNumerator 37 v = 0 ↔ incident 37 v) := by decide +kernel

theorem supportRow038 : ∀ v : Fin 144,
    0 ≤ slackNumerator 38 v ∧ (slackNumerator 38 v = 0 ↔ incident 38 v) := by decide +kernel

theorem supportRow039 : ∀ v : Fin 144,
    0 ≤ slackNumerator 39 v ∧ (slackNumerator 39 v = 0 ↔ incident 39 v) := by decide +kernel

end CubicalIndecomposability
