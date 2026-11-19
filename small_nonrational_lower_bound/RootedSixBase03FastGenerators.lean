module
prelude
public import RootedSixBase03FastGeneratorsCheck00
public import RootedSixBase03FastGeneratorsCheck01
public import RootedSixBase03FastGeneratorsCheck02
public import RootedSixBase03FastGeneratorsCheck03
public import RootedSixBase03FastGeneratorsCheck04
public import RootedSixBase03FastGeneratorsCheck05
public import RootedSixBase03FastGeneratorsCheck06
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.Fast
open Papers.RationalityTen ConcreteGrowth

theorem checked : FiniteChecks.Interval test 0 26190 :=
  (FiniteChecks.interval_append test 0 12288 26190
  (FiniteChecks.interval_append test 0 4096 12288
  interval_0
  (FiniteChecks.interval_append test 4096 8192 12288
  interval_4096
  interval_8192))
  (FiniteChecks.interval_append test 12288 20480 26190
  (FiniteChecks.interval_append test 12288 16384 20480
  interval_12288
  interval_16384)
  (FiniteChecks.interval_append test 20480 24576 26190
  interval_20480
  interval_24576)))
theorem raw_generators_eq (a c : Nat) (ha : a < 5) (hc : c < 5238) :
    rawGenerators a c = Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.rawGenerators a c :=
  FastGeneratorWords.bounded_eq_of_interval (n := 5238) (g := 5) (by decide)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.rawGenerators checked a ha c hc
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 5238) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.rawMaps frame cell := by
  apply FastGeneratorWords.rawApply_eq_of_bounded_eq (n := 5238) (g := 5)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.rawGenerators
    (fun a ha c hc => raw_generators_eq a c ha hc)
  · intro a c
    exact Nat.mod_lt _ (by decide)
  · intro a ha
    have h := Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.word_bounds frame
    exact of_decide_eq_true (List.all_eq_true.mp h a ha)
  · exact hc
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixBase03.Generators.Fast
