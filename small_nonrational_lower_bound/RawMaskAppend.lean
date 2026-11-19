module
prelude
public import RawNatGrowthCheck
public import Init.Data.Nat.Bitwise.Lemmas

@[expose] public section

/-!
# Combining exact mask certificates for list chunks

The mask of an appended list is the bitwise union of its chunk masks.
Consequently independently checked chunks determine the exact original
support mask, without evaluating that full list a second time.
-/

namespace Papers.RationalityTen.RawMaskAppend

open RawNatGrowthCheck

theorem mask_nil : mask ([] : List Nat) = 0 := rfl

theorem union_append (value : α → Nat) (xs ys : List α) :
    union value (xs ++ ys) = Nat.lor (union value xs) (union value ys) := by
  induction xs with
  | nil =>
    change union value ys = Nat.lor 0 (union value ys)
    exact (Nat.zero_or _).symm
  | cons x xs ih =>
    change Nat.lor (value x) (union value (xs ++ ys)) =
      Nat.lor (Nat.lor (value x) (union value xs)) (union value ys)
    rw [ih]
    exact (Nat.or_assoc _ _ _).symm

theorem mask_append (xs ys : List Nat) :
    mask (xs ++ ys) = Nat.lor (mask xs) (mask ys) :=
  union_append (Nat.shiftLeft 1) xs ys

/-- A list of independently checked chunks reconstructs the same mask. -/
theorem mask_flatten (chunks : List (List Nat)) :
    mask chunks.flatten = union mask chunks := by
  induction chunks with
  | nil => rfl
  | cons xs rest ih =>
    change mask (xs ++ rest.flatten) = Nat.lor (mask xs) (union mask rest)
    rw [mask_append, ih]

#print axioms union_append
#print axioms mask_append
#print axioms mask_flatten

end Papers.RationalityTen.RawMaskAppend
