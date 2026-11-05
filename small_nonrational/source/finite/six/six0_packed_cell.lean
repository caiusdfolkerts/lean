module
prelude
public import ConcreteGrowth

@[expose] public section

/-! Transparent ten-bit decoding for the fixed six-vertex template type zero. -/

namespace Papers.RationalityTen.Six0PackedCell

open ConcreteGrowth

def digit (code index : Nat) : Nat := Nat.land (code >>> (10 * index)) 1023

def unpack (code : Nat) : Cell where
  kind := 4
  vertices := digit code 0
  edges := (List.range 12).map fun j => digit code (j + 1)
  ridgeMasks := (List.range 8).map fun j => digit code (j + 13)

end Papers.RationalityTen.Six0PackedCell
