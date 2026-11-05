module
prelude
public import RootedSixExtra00FastGenerators

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.FastWords
open Papers.RationalityTen PackedRawNatGrowth FiniteChecks

def wordCode : Nat := 0x8c1408811940871182887023408602328860046885118281702328160230506004608500465050008c840230516004681500460a50008c140008d04000118300465150008d140008ca4000119300011a300002321014087021408602028860044085004288500088840202816004281500405050008084000850400010830040515000881400080a40001013000110300002020008514000111300010a30000212000022200000410c1408701940860182886003408500328850006884018281600328150030505000608400065040000c830030515000681400060a40000c130000d03000018200065140000d130000ca3000019200001a200000310014086001408500028850004084000288400008830002815000281400005040000083000050300000820000514000081300000a30000012000010200000010000513000011200000a2000001100000210000000
def rawWords (frame : Nat) : List Nat :=
  if frame < 96 then
    let code := take 28 (drop (28*frame) wordCode)
    ((readList 3 (take 4 code) (drop 4 code)).1).map
      (fun x => x % 5)
  else Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.rawWords frame
def rawMaps (frame cell : Nat) : Nat :=
  if frame = 0 then cell else
    CheckedGraphGrowthWords.rawApply Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.Fast.rawGenerators (rawWords frame) cell
def test (i : Nat) : Bool := rawWords i == Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.rawWords i
end Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.FastWords
