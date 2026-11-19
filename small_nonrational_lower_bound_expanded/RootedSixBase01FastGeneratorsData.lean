module
prelude
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSixBase01GeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
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
  PackedRawNatGrowth.take 14
    (PackedRawNatGrowth.drop (14 * c) (mapTable.get a))
def rawMaps (frame cell : Nat) : Nat :=
  CheckedGraphGrowthWords.rawApply rawGenerators
    (Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.rawWords frame) cell
def test (i : Nat) : Bool :=
  rawGenerators (i / 15246) (i % 15246) ==
    Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.rawGenerators (i / 15246) (i % 15246)
end Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
