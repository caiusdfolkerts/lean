module
prelude
public import RootedSixExtra02FastGeneratorsCheck00
public import RootedSixExtra02FastGeneratorsCheck01
public import RootedSixExtra02FastGeneratorsCheck02
public import RootedSixExtra02FastGeneratorsCheck03
public import RootedSixExtra02FastGeneratorsCheck04
public import RootedSixExtra02FastGeneratorsCheck05
public import RootedSixExtra02FastGeneratorsCheck06
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Fast
open Papers.RationalityTen ConcreteGrowth

theorem checked : FiniteChecks.Interval test 0 26480 :=
  (FiniteChecks.interval_append test 0 12288 26480
  (FiniteChecks.interval_append test 0 4096 12288
  interval_0
  (FiniteChecks.interval_append test 4096 8192 12288
  interval_4096
  interval_8192))
  (FiniteChecks.interval_append test 12288 20480 26480
  (FiniteChecks.interval_append test 12288 16384 20480
  interval_12288
  interval_16384)
  (FiniteChecks.interval_append test 20480 24576 26480
  interval_20480
  interval_24576)))
theorem raw_generators_eq (a c : Nat) (ha : a < 4) (hc : c < 6620) :
    rawGenerators a c = Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.rawGenerators a c :=
  FastGeneratorWords.bounded_eq_of_interval (n := 6620) (g := 4) (by decide)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.rawGenerators checked a ha c hc
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 6620) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.rawMaps frame cell := by
  apply FastGeneratorWords.rawApply_eq_of_bounded_eq (n := 6620) (g := 4)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.rawGenerators
    (fun a ha c hc => raw_generators_eq a c ha hc)
  · intro a c
    exact Nat.mod_lt _ (by decide)
  · intro a ha
    have h := Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.word_bounds frame
    exact of_decide_eq_true (List.all_eq_true.mp h a ha)
  · exact hc
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Fast
