module
prelude
public import RootedSixExtra05FastGeneratorsCheck00
public import RootedSixExtra05FastGeneratorsCheck01
public import RootedSixExtra05FastGeneratorsCheck02
public import RootedSixExtra05FastGeneratorsCheck03
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.Fast
open Papers.RationalityTen ConcreteGrowth

theorem checked : FiniteChecks.Interval test 0 13020 :=
  (FiniteChecks.interval_append test 0 8192 13020
  (FiniteChecks.interval_append test 0 4096 8192
  interval_0
  interval_4096)
  (FiniteChecks.interval_append test 8192 12288 13020
  interval_8192
  interval_12288))
theorem raw_generators_eq (a c : Nat) (ha : a < 6) (hc : c < 2170) :
    rawGenerators a c = Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.rawGenerators a c :=
  FastGeneratorWords.bounded_eq_of_interval (n := 2170) (g := 6) (by decide)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.rawGenerators checked a ha c hc
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 2170) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.rawMaps frame cell := by
  apply FastGeneratorWords.rawApply_eq_of_bounded_eq (n := 2170) (g := 6)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.rawGenerators
    (fun a ha c hc => raw_generators_eq a c ha hc)
  · intro a c
    exact Nat.mod_lt _ (by decide)
  · intro a ha
    have h := Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.word_bounds frame
    exact of_decide_eq_true (List.all_eq_true.mp h a ha)
  · exact hc
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.Fast
