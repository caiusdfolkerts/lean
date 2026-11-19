module
prelude
public import GraphCatalogueCheck
public import TenGraphEdges
public import FiniteChecks

@[expose] public section

/-! Transparent decoding of bounded catalogue records.  The decoder supplies
no correctness claim; every resulting choice is checked by the semantic
checker.  Tags zero and one denote selected edges and saturated vertices,
while the remaining tags denote a concrete extension and vertex frame. -/

namespace Papers.RationalityTen.GraphCatalogueData

open GraphCatalogueCheck

def decodeChoice {after frames : Nat} [NeZero after] [NeZero frames]
    (word : Nat) : Choice 10 after frames :=
  if Nat.land word 3 = 0 then .selected
  else if Nat.land word 3 = 1 then
    .saturated (Fin.ofNat 10 (Nat.land (word >>> 2) 15))
  else .extension (Fin.ofNat after (Nat.land (word >>> 2) 16383))
    (Fin.ofNat frames (Nat.land (word >>> 16) 32767))

def choiceAt {after frames : Nat} [NeZero after] [NeZero frames]
    (row : Nat) (edge : Fin 45) : Choice 10 after frames :=
  decodeChoice (Nat.land (row >>> (32*edge.val)) 4294967295)

end Papers.RationalityTen.GraphCatalogueData
