module
prelude
public import RootedSmallGeneratorWordsData
public import BitsetAdjacentCellCheck

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedSmallGeneratorWords
open Papers.RationalityTen ConcreteGrowth FiniteChecks

def swapIndex : Nat → Nat
  | 0 => 0 | 1 => 1 | 2 => 3 | 3 => 5 | 4 => 6 | 5 => 7 | _ => 8

theorem vertexCode_eq (g : Fin 7) :
    vertexTable.get g.val = FastAdjacentMask.vertexCode (swapIndex g.val) := by
  have h : ∀ g : Fin 7,
      vertexTable.get g.val = FastAdjacentMask.vertexCode (swapIndex g.val) := by
    decide +kernel
  exact h g

noncomputable def bitTest (g i : Nat) : Bool :=
  let gen := Fin.ofNat 7 g
  let cell := Fin.ofNat 3436 i
  RawGraphGrowthFrames.inverseCheckAt (forward gen) (forward gen) cell &&
    BitsetAdjacentCellCheck.check (swapIndex gen.val)
      (FacetUniverses.Small.cells cell)
      (FacetUniverses.Small.cells (forward gen cell))

theorem bitTest_eq (g i : Nat) : bitTest g i = cellTest g i := by
  simp only [bitTest, cellTest, BitsetAdjacentCellCheck.check_eq, vertices, vertexCode_eq]

end Papers.RationalityTen.RootedSmallGeneratorWords
