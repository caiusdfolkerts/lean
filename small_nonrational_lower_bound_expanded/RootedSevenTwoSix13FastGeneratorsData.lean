module
prelude
public meta import CertificateNumbers
import HexNatLiteral
public import RootedSevenTwoSix13GeneratorsData
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.Fast
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
  PackedRawNatGrowth.take 11
    (PackedRawNatGrowth.drop (11 * c) (mapTable.get a))
def rawMaps (frame cell : Nat) : Nat :=
  CheckedGraphGrowthWords.rawApply rawGenerators
    (Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.rawWords frame) cell
def test (i : Nat) : Bool :=
  rawGenerators (i / 2038) (i % 2038) ==
    Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.rawGenerators (i / 2038) (i % 2038)
end Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.Fast
