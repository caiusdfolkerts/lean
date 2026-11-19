module
prelude
public import RootedSevenTwoSix13FastGenerators

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.FastWords
open Papers.RationalityTen PackedRawNatGrowth FiniteChecks

def wordCode : Nat := 0xb84c5c94b8685c40b9805ccb1285a40b18058c0b5805a384a1c9038601c3039601c831201a30316018803500190848048c0858042009400440118022001400040048000
def rawWords (frame : Nat) : List Nat :=
  if frame < 36 then
    let code := take 15 (drop (15*frame) wordCode)
    ((readList 2 (take 3 code) (drop 3 code)).1).map
      (fun x => x % 4)
  else Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.rawWords frame
def rawMaps (frame cell : Nat) : Nat :=
  if frame = 0 then cell else
    CheckedGraphGrowthWords.rawApply Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.Fast.rawGenerators (rawWords frame) cell
def test (i : Nat) : Bool := rawWords i == Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.rawWords i
end Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.FastWords
