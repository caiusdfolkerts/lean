module
prelude
public import RootedSixExtra02FastWordsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.FastWords
open Papers.RationalityTen PackedRawNatGrowth FiniteChecks
theorem checked_0 : Interval test 0 48 :=
  interval_of_check test 0 48 (by decide +kernel)

theorem checked : Interval test 0 48 :=
  checked_0
theorem raw_words_eq (frame : Nat) : rawWords frame = Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.rawWords frame := by
  by_cases hf : frame < 48
  · exact eq_of_beq (checked frame (Nat.zero_le _) hf)
  · simp only [rawWords, hf, if_false]
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 6620) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.rawMaps frame cell := by
  by_cases hf : frame = 0
  · subst frame
    exact (Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.identity_exact cell).symm
  · simp only [rawMaps, hf, if_false, raw_words_eq]
    exact Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.Fast.raw_maps_eq frame cell hc
#print axioms raw_words_eq
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixExtra02.Generators.FastWords
