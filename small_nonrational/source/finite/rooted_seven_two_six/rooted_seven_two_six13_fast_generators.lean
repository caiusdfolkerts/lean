module
prelude
public import RootedSevenTwoSix13FastGeneratorsCheck00
public import RootedSevenTwoSix13FastGeneratorsCheck01
public import FastGeneratorWords

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.Fast
open Papers.RationalityTen ConcreteGrowth

theorem checked : FiniteChecks.Interval test 0 8152 :=
  (FiniteChecks.interval_append test 0 4096 8152
  interval_0
  interval_4096)
theorem raw_generators_eq (a c : Nat) (ha : a < 4) (hc : c < 2038) :
    rawGenerators a c = Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.rawGenerators a c :=
  FastGeneratorWords.bounded_eq_of_interval (n := 2038) (g := 4) (by decide)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.rawGenerators checked a ha c hc
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 2038) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.rawMaps frame cell := by
  apply FastGeneratorWords.rawApply_eq_of_bounded_eq (n := 2038) (g := 4)
    rawGenerators Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.rawGenerators
    (fun a ha c hc => raw_generators_eq a c ha hc)
  · intro a c
    exact Nat.mod_lt _ (by decide)
  · intro a ha
    have h := Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.word_bounds frame
    exact of_decide_eq_true (List.all_eq_true.mp h a ha)
  · exact hc
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSevenTwoSix13.Generators.Fast
