module
prelude
public import RootedSixBase00FastGeneratorsCheck00
public import RootedSixBase00FastGeneratorsCheck01
public import RootedSixBase00FastGeneratorsCheck02
public import RootedSixBase00FastGeneratorsCheck03
public import RootedSixBase00FastGeneratorsCheck04
public import RootedSixBase00FastGeneratorsCheck05
public import RootedSixBase00FastGeneratorsCheck06
public import RootedSixBase00FastGeneratorsCheck07
public import RootedSixBase00FastGeneratorsCheck08
public import RootedSixBase00FastGeneratorsCheck09
public import RootedSixBase00FastGeneratorsCheck10
public import RootedSixBase00FastGeneratorsCheck11
public import RootedSixBase00FastGeneratorsCheck12
public import RootedSixBase00FastGeneratorsCheck13
public import RootedSixBase00FastGeneratorsCheck14
public import RootedSixBase00FastGeneratorsCheck15
public import RootedSixBase00FastGeneratorsCheck16
public import RootedSixBase00FastGeneratorsCheck17
public import RootedSixBase00FastGeneratorsCheck18
public import RootedSixBase00FastGeneratorsCheck19
public import RootedSixBase00FastGeneratorsCheck20
public import RootedSixBase00FastGeneratorsCheck21
public import RootedSixBase00FastGeneratorsCheck22
public import RootedSixBase00FastGeneratorsCheck23
public import RootedSixBase00FastGeneratorsCheck24
public import RootedSixBase00FastGeneratorsCheck25
public import RootedSixBase00FastGeneratorsCheck26
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth

theorem checked : FiniteChecks.Interval test 0 109880 :=
  (FiniteChecks.interval_append test 0 53248 109880
  (FiniteChecks.interval_append test 0 24576 53248
  (FiniteChecks.interval_append test 0 12288 24576
  (FiniteChecks.interval_append test 0 4096 12288
  interval_0
  (FiniteChecks.interval_append test 4096 8192 12288
  interval_4096
  interval_8192))
  (FiniteChecks.interval_append test 12288 16384 24576
  interval_12288
  (FiniteChecks.interval_append test 16384 20480 24576
  interval_16384
  interval_20480)))
  (FiniteChecks.interval_append test 24576 36864 53248
  (FiniteChecks.interval_append test 24576 28672 36864
  interval_24576
  (FiniteChecks.interval_append test 28672 32768 36864
  interval_28672
  interval_32768))
  (FiniteChecks.interval_append test 36864 45056 53248
  (FiniteChecks.interval_append test 36864 40960 45056
  interval_36864
  interval_40960)
  (FiniteChecks.interval_append test 45056 49152 53248
  interval_45056
  interval_49152))))
  (FiniteChecks.interval_append test 53248 81920 109880
  (FiniteChecks.interval_append test 53248 65536 81920
  (FiniteChecks.interval_append test 53248 57344 65536
  interval_53248
  (FiniteChecks.interval_append test 57344 61440 65536
  interval_57344
  interval_61440))
  (FiniteChecks.interval_append test 65536 73728 81920
  (FiniteChecks.interval_append test 65536 69632 73728
  interval_65536
  interval_69632)
  (FiniteChecks.interval_append test 73728 77824 81920
  interval_73728
  interval_77824)))
  (FiniteChecks.interval_append test 81920 94208 109880
  (FiniteChecks.interval_append test 81920 86016 94208
  interval_81920
  (FiniteChecks.interval_append test 86016 90112 94208
  interval_86016
  interval_90112))
  (FiniteChecks.interval_append test 94208 102400 109880
  (FiniteChecks.interval_append test 94208 98304 102400
  interval_94208
  interval_98304)
  (FiniteChecks.interval_append test 102400 106496 109880
  interval_102400
  interval_106496)))))
theorem raw_generators_eq (a c : Nat) (ha : a < 5) (hc : c < 21976) :
    rawGenerators a c = Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.rawGenerators a c :=
  FastGeneratorWords.bounded_eq_of_interval (n := 21976) (g := 5) (by decide)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.rawGenerators checked a ha c hc
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 21976) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.rawMaps frame cell := by
  apply FastGeneratorWords.rawApply_eq_of_bounded_eq (n := 21976) (g := 5)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.rawGenerators
    (fun a ha c hc => raw_generators_eq a c ha hc)
  · intro a c
    exact Nat.mod_lt _ (by decide)
  · intro a ha
    have h := Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.word_bounds frame
    exact of_decide_eq_true (List.all_eq_true.mp h a ha)
  · exact hc
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixBase00.Generators.Fast
