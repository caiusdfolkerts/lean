module
prelude
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixExtra04GeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.Fast
open Papers.RationalityTen ConcreteGrowth

/- One integer stores the whole image list for each generator. -/
def mapTable : Table Nat :=
(.branch 3
 (.branch 1
 (.leaf ((certNat% 0)))
 (.branch 2
 (.leaf ((certNat% 1)))
 (.leaf ((certNat% 2)))))
 (.branch 4
 (.leaf ((certNat% 3)))
 (.branch 5
 (.leaf ((certNat% 4)))
 (.leaf ((certNat% 5))))))
def rawGenerators (a c : Nat) : Nat :=
  PackedRawNatGrowth.take 12
    (PackedRawNatGrowth.drop (12 * c) (mapTable.get a))
def rawMaps (frame cell : Nat) : Nat :=
  CheckedGraphGrowthWords.rawApply rawGenerators
    (Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.rawWords frame) cell
def test (i : Nat) : Bool :=
  rawGenerators (i / 3640) (i % 3640) ==
    Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.rawGenerators (i / 3640) (i % 3640)
end Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.Fast
