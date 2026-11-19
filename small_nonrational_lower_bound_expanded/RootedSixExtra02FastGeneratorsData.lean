module
prelude
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixExtra02GeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Fast
open Papers.RationalityTen ConcreteGrowth

/- One integer stores the whole image list for each generator. -/
def mapTable : Table Nat :=
(.branch 2
 (.branch 1
 (.leaf ((certNat% 0)))
 (.leaf ((certNat% 1))))
 (.branch 3
 (.leaf ((certNat% 2)))
 (.leaf ((certNat% 3)))))
def rawGenerators (a c : Nat) : Nat :=
  PackedRawNatGrowth.take 13
    (PackedRawNatGrowth.drop (13 * c) (mapTable.get a))
def rawMaps (frame cell : Nat) : Nat :=
  CheckedGraphGrowthWords.rawApply rawGenerators
    (Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.rawWords frame) cell
def test (i : Nat) : Bool :=
  rawGenerators (i / 6620) (i % 6620) ==
    Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.rawGenerators (i / 6620) (i % 6620)
end Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Fast
