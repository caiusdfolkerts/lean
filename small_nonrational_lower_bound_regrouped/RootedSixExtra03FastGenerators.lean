module
prelude
public import RootedSixExtra03FastGeneratorsCheck00
public import RootedSixExtra03FastGeneratorsCheck01
public import RootedSixExtra03FastGeneratorsCheck02
public import RootedSixExtra03FastGeneratorsCheck03
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.Fast
open Papers.RationalityTen ConcreteGrowth

theorem checked : FiniteChecks.Interval test 0 15750 :=
  (FiniteChecks.interval_append test 0 8192 15750
  (FiniteChecks.interval_append test 0 4096 8192
  interval_0
  interval_4096)
  (FiniteChecks.interval_append test 8192 12288 15750
  interval_8192
  interval_12288))
theorem raw_generators_eq (a c : Nat) (ha : a < 5) (hc : c < 3150) :
    rawGenerators a c = Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.rawGenerators a c :=
  FastGeneratorWords.bounded_eq_of_interval (n := 3150) (g := 5) (by decide)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.rawGenerators checked a ha c hc
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 3150) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.rawMaps frame cell := by
  apply FastGeneratorWords.rawApply_eq_of_bounded_eq (n := 3150) (g := 5)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.rawGenerators
    (fun a ha c hc => raw_generators_eq a c ha hc)
  · intro a c
    exact Nat.mod_lt _ (by decide)
  · intro a ha
    have h := Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.word_bounds frame
    exact of_decide_eq_true (List.all_eq_true.mp h a ha)
  · exact hc
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixExtra03.Generators.Fast
