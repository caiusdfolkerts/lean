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

theorem supportRow010 : ∀ v : Fin 144,
    0 ≤ slackNumerator 10 v ∧ (slackNumerator 10 v = 0 ↔ incident 10 v) := by decide +kernel

theorem supportRow011 : ∀ v : Fin 144,
    0 ≤ slackNumerator 11 v ∧ (slackNumerator 11 v = 0 ↔ incident 11 v) := by decide +kernel

theorem supportRow012 : ∀ v : Fin 144,
    0 ≤ slackNumerator 12 v ∧ (slackNumerator 12 v = 0 ↔ incident 12 v) := by decide +kernel

theorem supportRow013 : ∀ v : Fin 144,
    0 ≤ slackNumerator 13 v ∧ (slackNumerator 13 v = 0 ↔ incident 13 v) := by decide +kernel

theorem supportRow014 : ∀ v : Fin 144,
    0 ≤ slackNumerator 14 v ∧ (slackNumerator 14 v = 0 ↔ incident 14 v) := by decide +kernel

theorem supportRow015 : ∀ v : Fin 144,
    0 ≤ slackNumerator 15 v ∧ (slackNumerator 15 v = 0 ↔ incident 15 v) := by decide +kernel

theorem supportRow016 : ∀ v : Fin 144,
    0 ≤ slackNumerator 16 v ∧ (slackNumerator 16 v = 0 ↔ incident 16 v) := by decide +kernel

theorem supportRow017 : ∀ v : Fin 144,
    0 ≤ slackNumerator 17 v ∧ (slackNumerator 17 v = 0 ↔ incident 17 v) := by decide +kernel

theorem supportRow018 : ∀ v : Fin 144,
    0 ≤ slackNumerator 18 v ∧ (slackNumerator 18 v = 0 ↔ incident 18 v) := by decide +kernel

theorem supportRow019 : ∀ v : Fin 144,
    0 ≤ slackNumerator 19 v ∧ (slackNumerator 19 v = 0 ↔ incident 19 v) := by decide +kernel

end CubicalIndecomposability
