module
prelude
public import RootedSixExtra00FastGeneratorsCheck00
public import RootedSixExtra00FastGeneratorsCheck01
public import RootedSixExtra00FastGeneratorsCheck02
public import RootedSixExtra00FastGeneratorsCheck03
public import RootedSixExtra00FastGeneratorsCheck04
public import RootedSixExtra00FastGeneratorsCheck05
public import RootedSixExtra00FastGeneratorsCheck06
public import RootedSixExtra00FastGeneratorsCheck07
public import RootedSixExtra00FastGeneratorsCheck08
public import RootedSixExtra00FastGeneratorsCheck09
public import RootedSixExtra00FastGeneratorsCheck10
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.Fast
open Papers.RationalityTen ConcreteGrowth

theorem checked : FiniteChecks.Interval test 0 44120 :=
  (FiniteChecks.interval_append test 0 20480 44120
  (FiniteChecks.interval_append test 0 8192 20480
  (FiniteChecks.interval_append test 0 4096 8192
  interval_0
  interval_4096)
  (FiniteChecks.interval_append test 8192 12288 20480
  interval_8192
  (FiniteChecks.interval_append test 12288 16384 20480
  interval_12288
  interval_16384)))
  (FiniteChecks.interval_append test 20480 32768 44120
  (FiniteChecks.interval_append test 20480 24576 32768
  interval_20480
  (FiniteChecks.interval_append test 24576 28672 32768
  interval_24576
  interval_28672))
  (FiniteChecks.interval_append test 32768 36864 44120
  interval_32768
  (FiniteChecks.interval_append test 36864 40960 44120
  interval_36864
  interval_40960))))
theorem raw_generators_eq (a c : Nat) (ha : a < 5) (hc : c < 8824) :
    rawGenerators a c = Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.rawGenerators a c :=
  FastGeneratorWords.bounded_eq_of_interval (n := 8824) (g := 5) (by decide)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.rawGenerators checked a ha c hc
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 8824) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.rawMaps frame cell := by
  apply FastGeneratorWords.rawApply_eq_of_bounded_eq (n := 8824) (g := 5)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.rawGenerators
    (fun a ha c hc => raw_generators_eq a c ha hc)
  · intro a c
    exact Nat.mod_lt _ (by decide)
  · intro a ha
    have h := Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.word_bounds frame
    exact of_decide_eq_true (List.all_eq_true.mp h a ha)
  · exact hc
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixExtra00.Generators.Fast
