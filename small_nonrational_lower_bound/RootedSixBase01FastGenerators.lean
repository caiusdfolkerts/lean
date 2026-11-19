module
prelude
public import RootedSixBase01FastGeneratorsCheck00
public import RootedSixBase01FastGeneratorsCheck01
public import RootedSixBase01FastGeneratorsCheck02
public import RootedSixBase01FastGeneratorsCheck03
public import RootedSixBase01FastGeneratorsCheck04
public import RootedSixBase01FastGeneratorsCheck05
public import RootedSixBase01FastGeneratorsCheck06
public import RootedSixBase01FastGeneratorsCheck07
public import RootedSixBase01FastGeneratorsCheck08
public import RootedSixBase01FastGeneratorsCheck09
public import RootedSixBase01FastGeneratorsCheck10
public import RootedSixBase01FastGeneratorsCheck11
public import RootedSixBase01FastGeneratorsCheck12
public import RootedSixBase01FastGeneratorsCheck13
public import RootedSixBase01FastGeneratorsCheck14
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
open Papers.RationalityTen ConcreteGrowth

theorem checked : FiniteChecks.Interval test 0 60984 :=
  (FiniteChecks.interval_append test 0 28672 60984
  (FiniteChecks.interval_append test 0 12288 28672
  (FiniteChecks.interval_append test 0 4096 12288
  interval_0
  (FiniteChecks.interval_append test 4096 8192 12288
  interval_4096
  interval_8192))
  (FiniteChecks.interval_append test 12288 20480 28672
  (FiniteChecks.interval_append test 12288 16384 20480
  interval_12288
  interval_16384)
  (FiniteChecks.interval_append test 20480 24576 28672
  interval_20480
  interval_24576)))
  (FiniteChecks.interval_append test 28672 45056 60984
  (FiniteChecks.interval_append test 28672 36864 45056
  (FiniteChecks.interval_append test 28672 32768 36864
  interval_28672
  interval_32768)
  (FiniteChecks.interval_append test 36864 40960 45056
  interval_36864
  interval_40960))
  (FiniteChecks.interval_append test 45056 53248 60984
  (FiniteChecks.interval_append test 45056 49152 53248
  interval_45056
  interval_49152)
  (FiniteChecks.interval_append test 53248 57344 60984
  interval_53248
  interval_57344))))
theorem raw_generators_eq (a c : Nat) (ha : a < 4) (hc : c < 15246) :
    rawGenerators a c = Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.rawGenerators a c :=
  FastGeneratorWords.bounded_eq_of_interval (n := 15246) (g := 4) (by decide)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.rawGenerators checked a ha c hc
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 15246) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.rawMaps frame cell := by
  apply FastGeneratorWords.rawApply_eq_of_bounded_eq (n := 15246) (g := 4)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.rawGenerators
    (fun a ha c hc => raw_generators_eq a c ha hc)
  · intro a c
    exact Nat.mod_lt _ (by decide)
  · intro a ha
    have h := Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.word_bounds frame
    exact of_decide_eq_true (List.all_eq_true.mp h a ha)
  · exact hc
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixBase01.Generators.Fast
