module

public import Mathlib.Logic.Embedding.Basic

/-! # Extending prescribed lifts along an injective family inclusion -/

public theorem exists_compatible_lift_extension {A B X Y : Type*}
    (inclusion : A ↪ B) (projection : X → Y) (surjective : Function.Surjective projection)
    (desired : B → Y) (old : A → X)
    (compatible : ∀ a, projection (old a) = desired (inclusion a)) :
    ∃ lifts : B → X, (∀ b, projection (lifts b) = desired b) ∧
      ∀ a, lifts (inclusion a) = old a := by
  classical
  let fallback := fun b => (surjective (desired b)).choose
  refine ⟨Function.extend inclusion old fallback,?_,?_⟩
  · intro b
    by_cases member : ∃ a, inclusion a = b
    · obtain ⟨a,rfl⟩ := member
      rw [inclusion.injective.extend_apply]
      exact compatible a
    · rw [Function.extend_apply' _ _ _ member]
      exact (surjective (desired b)).choose_spec
  · exact inclusion.injective.extend_apply old fallback

