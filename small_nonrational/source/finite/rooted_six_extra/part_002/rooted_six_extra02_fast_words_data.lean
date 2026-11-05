module
prelude
public import RootedSixExtra02FastGenerators

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.FastWords
open Papers.RationalityTen PackedRawNatGrowth FiniteChecks

def wordCode : Nat := 0xc6139b098c64c1c250d9281c90c61c1b0d0c62818900d8801a30c6681c300c68018b00e1801880d9801cb00d9801a800e40019061303094064a042401920048c061a030c00620008c0186002200660042c0066000a0021000040196004a00190002400220000
def rawWords (frame : Nat) : List Nat :=
  if frame < 48 then
    let code := take 17 (drop (17*frame) wordCode)
    ((readList 2 (take 3 code) (drop 3 code)).1).map
      (fun x => x % 4)
  else Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.rawWords frame
def rawMaps (frame cell : Nat) : Nat :=
  if frame = 0 then cell else
    CheckedGraphGrowthWords.rawApply Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Fast.rawGenerators (rawWords frame) cell
def test (i : Nat) : Bool := rawWords i == Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.rawWords i
end Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.FastWords
