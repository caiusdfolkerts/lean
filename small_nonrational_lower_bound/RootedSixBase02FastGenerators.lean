module
prelude
public import RootedSixBase02FastGeneratorsCheck00
public import RootedSixBase02FastGeneratorsCheck01
public import RootedSixBase02FastGeneratorsCheck02
public import RootedSixBase02FastGeneratorsCheck03
public import RootedSixBase02FastGeneratorsCheck04
public import RootedSixBase02FastGeneratorsCheck05
public import RootedSixBase02FastGeneratorsCheck06
public import RootedSixBase02FastGeneratorsCheck07
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
open Papers.RationalityTen ConcreteGrowth

theorem checked : FiniteChecks.Interval test 0 32336 :=
  (FiniteChecks.interval_append test 0 16384 32336
  (FiniteChecks.interval_append test 0 8192 16384
  (FiniteChecks.interval_append test 0 4096 8192
  interval_0
  interval_4096)
  (FiniteChecks.interval_append test 8192 12288 16384
  interval_8192
  interval_12288))
  (FiniteChecks.interval_append test 16384 24576 32336
  (FiniteChecks.interval_append test 16384 20480 24576
  interval_16384
  interval_20480)
  (FiniteChecks.interval_append test 24576 28672 32336
  interval_24576
  interval_28672)))
theorem raw_generators_eq (a c : Nat) (ha : a < 4) (hc : c < 8084) :
    rawGenerators a c = Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.rawGenerators a c :=
  FastGeneratorWords.bounded_eq_of_interval (n := 8084) (g := 4) (by decide)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.rawGenerators checked a ha c hc
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 8084) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.rawMaps frame cell := by
  apply FastGeneratorWords.rawApply_eq_of_bounded_eq (n := 8084) (g := 4)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.rawGenerators
    (fun a ha c hc => raw_generators_eq a c ha hc)
  · intro a c
    exact Nat.mod_lt _ (by decide)
  · intro a ha
    have h := Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.word_bounds frame
    exact of_decide_eq_true (List.all_eq_true.mp h a ha)
  · exact hc
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixBase02.Generators.Fast
