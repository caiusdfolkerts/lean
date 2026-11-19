module
prelude
public meta import CertificateNumbers
public import RootedSixExtra01FastGenerators

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.FastWords
open Papers.RationalityTen PackedRawNatGrowth FiniteChecks

def wordCode : Nat := (certNat% 0)
def rawWords (frame : Nat) : List Nat :=
  if frame < 48 then
    let code := take 17 (drop (17*frame) wordCode)
    ((readList 2 (take 3 code) (drop 3 code)).1).map
      (fun x => x % 4)
  else Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.rawWords frame
def rawMaps (frame cell : Nat) : Nat :=
  if frame = 0 then cell else
    CheckedGraphGrowthWords.rawApply Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.Fast.rawGenerators (rawWords frame) cell
def test (i : Nat) : Bool := rawWords i == Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.rawWords i
end Papers.RationalityTen.FacetUniverses.RootedSixExtra01.Generators.FastWords
