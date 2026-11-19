module
prelude
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixExtra04FastGenerators

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.FastWords
open Papers.RationalityTen PackedRawNatGrowth FiniteChecks

def wordCode : Nat := ((certNat% 0))
def rawWords (frame : Nat) : List Nat :=
  if frame < 1152 then
    let code := take 49 (drop (49*frame) wordCode)
    ((readList 3 (take 4 code) (drop 4 code)).1).map
      (fun x => x % 6)
  else Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.rawWords frame
def rawMaps (frame cell : Nat) : Nat :=
  if frame = 0 then cell else
    CheckedGraphGrowthWords.rawApply Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.Fast.rawGenerators (rawWords frame) cell
def test (i : Nat) : Bool := rawWords i == Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.rawWords i
end Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.FastWords
