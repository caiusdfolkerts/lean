module
prelude
public import Init.Data.List.Basic

@[expose] public section

/-! Executable left-to-right action of a finite generator word. Its exact
agreement with genuine geometric frames is proved in the separate semantic
word adapters; this definition has no geometric assumptions or conclusions. -/
namespace Papers.RationalityTen.CheckedGraphGrowthWords

def rawApply (generators : Nat → Nat → Nat) : List Nat → Nat → Nat
  | [], x => x
  | g :: rest, x => rawApply generators rest (generators g x)

end Papers.RationalityTen.CheckedGraphGrowthWords
