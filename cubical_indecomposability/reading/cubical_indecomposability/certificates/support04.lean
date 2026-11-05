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

theorem supportRow040 : ∀ v : Fin 144,
    0 ≤ slackNumerator 40 v ∧ (slackNumerator 40 v = 0 ↔ incident 40 v) := by decide +kernel

theorem supportRow041 : ∀ v : Fin 144,
    0 ≤ slackNumerator 41 v ∧ (slackNumerator 41 v = 0 ↔ incident 41 v) := by decide +kernel

theorem supportRow042 : ∀ v : Fin 144,
    0 ≤ slackNumerator 42 v ∧ (slackNumerator 42 v = 0 ↔ incident 42 v) := by decide +kernel

theorem supportRow043 : ∀ v : Fin 144,
    0 ≤ slackNumerator 43 v ∧ (slackNumerator 43 v = 0 ↔ incident 43 v) := by decide +kernel

theorem supportRow044 : ∀ v : Fin 144,
    0 ≤ slackNumerator 44 v ∧ (slackNumerator 44 v = 0 ↔ incident 44 v) := by decide +kernel

theorem supportRow045 : ∀ v : Fin 144,
    0 ≤ slackNumerator 45 v ∧ (slackNumerator 45 v = 0 ↔ incident 45 v) := by decide +kernel

theorem supportRow046 : ∀ v : Fin 144,
    0 ≤ slackNumerator 46 v ∧ (slackNumerator 46 v = 0 ↔ incident 46 v) := by decide +kernel

theorem supportRow047 : ∀ v : Fin 144,
    0 ≤ slackNumerator 47 v ∧ (slackNumerator 47 v = 0 ↔ incident 47 v) := by decide +kernel

theorem supportRow048 : ∀ v : Fin 144,
    0 ≤ slackNumerator 48 v ∧ (slackNumerator 48 v = 0 ↔ incident 48 v) := by decide +kernel

theorem supportRow049 : ∀ v : Fin 144,
    0 ≤ slackNumerator 49 v ∧ (slackNumerator 49 v = 0 ↔ incident 49 v) := by decide +kernel

end CubicalIndecomposability
