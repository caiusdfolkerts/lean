module

@[expose] public section

namespace Papers.RationalityTen.MatroidChecked

/-- Balanced literal lookup. The finite checks concern its returned values;
no ordering or completeness invariant is trusted about the producer. -/
inductive LiteralLookup (α : Type) where
  | leaf (value : α)
  | node (cut : Nat) (left right : LiteralLookup α)

def LiteralLookup.get {α : Type} (tree : LiteralLookup α) (i : Nat) : α :=
  match tree with
  | .leaf x => x
  | .node cut left right => if i < cut then left.get i else right.get i

end Papers.RationalityTen.MatroidChecked
