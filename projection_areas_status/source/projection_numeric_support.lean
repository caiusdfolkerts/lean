module

public import Mathlib.Data.Nat.Init

/-! Named genuine witnesses for the exact numeric proof arguments measured in raw exports. -/
@[expose] public section
namespace PalomarProjectionAreas.NumericProofs
/-- The measured nonzero dimension proof for two coordinate positions. -/
theorem twoNeZero : NeZero (1 + 1 : ℕ) := by infer_instance
/-- The measured lower bound used by the literal exponent two. -/
theorem twoAtLeastTwo : Nat.AtLeastTwo (1 + 1 : ℕ) := by infer_instance
/-- The measured nonzero dimension proof for four coordinate positions. -/
theorem fourNeZero : NeZero (3 + 1 : ℕ) := by infer_instance
end PalomarProjectionAreas.NumericProofs

