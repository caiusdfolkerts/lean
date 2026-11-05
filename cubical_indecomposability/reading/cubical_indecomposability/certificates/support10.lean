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

theorem supportRow100 : ∀ v : Fin 144,
    0 ≤ slackNumerator 100 v ∧ (slackNumerator 100 v = 0 ↔ incident 100 v) := by decide +kernel

theorem supportRow101 : ∀ v : Fin 144,
    0 ≤ slackNumerator 101 v ∧ (slackNumerator 101 v = 0 ↔ incident 101 v) := by decide +kernel

theorem supportRow102 : ∀ v : Fin 144,
    0 ≤ slackNumerator 102 v ∧ (slackNumerator 102 v = 0 ↔ incident 102 v) := by decide +kernel

theorem supportRow103 : ∀ v : Fin 144,
    0 ≤ slackNumerator 103 v ∧ (slackNumerator 103 v = 0 ↔ incident 103 v) := by decide +kernel

theorem supportRow104 : ∀ v : Fin 144,
    0 ≤ slackNumerator 104 v ∧ (slackNumerator 104 v = 0 ↔ incident 104 v) := by decide +kernel

theorem supportRow105 : ∀ v : Fin 144,
    0 ≤ slackNumerator 105 v ∧ (slackNumerator 105 v = 0 ↔ incident 105 v) := by decide +kernel

theorem supportRow106 : ∀ v : Fin 144,
    0 ≤ slackNumerator 106 v ∧ (slackNumerator 106 v = 0 ↔ incident 106 v) := by decide +kernel

theorem supportRow107 : ∀ v : Fin 144,
    0 ≤ slackNumerator 107 v ∧ (slackNumerator 107 v = 0 ↔ incident 107 v) := by decide +kernel

theorem supportRow108 : ∀ v : Fin 144,
    0 ≤ slackNumerator 108 v ∧ (slackNumerator 108 v = 0 ↔ incident 108 v) := by decide +kernel

theorem supportRow109 : ∀ v : Fin 144,
    0 ≤ slackNumerator 109 v ∧ (slackNumerator 109 v = 0 ↔ incident 109 v) := by decide +kernel

end CubicalIndecomposability
