module
prelude
public import RootedSixExtra06FastWordsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.FastWords
open Papers.RationalityTen PackedRawNatGrowth FiniteChecks
theorem checked_0 : Interval test 0 64 :=
  interval_of_check test 0 64 (by decide +kernel)
theorem checked_64 : Interval test 64 128 :=
  interval_of_check test 64 64 (by decide +kernel)
theorem checked_128 : Interval test 128 192 :=
  interval_of_check test 128 64 (by decide +kernel)
theorem checked_192 : Interval test 192 240 :=
  interval_of_check test 192 48 (by decide +kernel)

theorem checked : Interval test 0 240 :=
  (FiniteChecks.interval_append test 0 128 240
  (FiniteChecks.interval_append test 0 64 128
  checked_0
  checked_64)
  (FiniteChecks.interval_append test 128 192 240
  checked_128
  checked_192))
theorem raw_words_eq (frame : Nat) : rawWords frame = Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.rawWords frame := by
  by_cases hf : frame < 240
  · exact eq_of_beq (checked frame (Nat.zero_le _) hf)
  · simp only [rawWords, hf, if_false]
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 2300) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.rawMaps frame cell := by
  by_cases hf : frame = 0
  · subst frame
    exact (Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.identity_exact cell).symm
  · simp only [rawMaps, hf, if_false, raw_words_eq]
    exact Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.Fast.raw_maps_eq frame cell hc
#print axioms raw_words_eq
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixExtra06.Generators.FastWords
