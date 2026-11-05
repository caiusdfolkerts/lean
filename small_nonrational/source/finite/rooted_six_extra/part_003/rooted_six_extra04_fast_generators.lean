module
prelude
public import RootedSixExtra04FastGeneratorsCheck00
public import RootedSixExtra04FastGeneratorsCheck01
public import RootedSixExtra04FastGeneratorsCheck02
public import RootedSixExtra04FastGeneratorsCheck03
public import RootedSixExtra04FastGeneratorsCheck04
public import RootedSixExtra04FastGeneratorsCheck05
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.Fast
open Papers.RationalityTen ConcreteGrowth

theorem checked : FiniteChecks.Interval test 0 21840 :=
  (FiniteChecks.interval_append test 0 12288 21840
  (FiniteChecks.interval_append test 0 4096 12288
  interval_0
  (FiniteChecks.interval_append test 4096 8192 12288
  interval_4096
  interval_8192))
  (FiniteChecks.interval_append test 12288 16384 21840
  interval_12288
  (FiniteChecks.interval_append test 16384 20480 21840
  interval_16384
  interval_20480)))
theorem raw_generators_eq (a c : Nat) (ha : a < 6) (hc : c < 3640) :
    rawGenerators a c = Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.rawGenerators a c :=
  FastGeneratorWords.bounded_eq_of_interval (n := 3640) (g := 6) (by decide)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.rawGenerators checked a ha c hc
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 3640) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.rawMaps frame cell := by
  apply FastGeneratorWords.rawApply_eq_of_bounded_eq (n := 3640) (g := 6)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.rawGenerators
    (fun a ha c hc => raw_generators_eq a c ha hc)
  · intro a c
    exact Nat.mod_lt _ (by decide)
  · intro a ha
    have h := Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.word_bounds frame
    exact of_decide_eq_true (List.all_eq_true.mp h a ha)
  · exact hc
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.Fast
