module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra05FastWordsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords
open Papers.RationalityTen PackedRawNatGrowth FiniteChecks
cert_checked_10 0 64
cert_checked_10 64 128
cert_checked_10 128 192
cert_checked_10 192 256
theorem checked_256 : Interval test 256 288 :=
  interval_of_check test 256 32 (by decide +kernel)

theorem checked : Interval test 0 288 :=
  (FiniteChecks.interval_append test 0 128 288
  (FiniteChecks.interval_append test 0 64 128
  checked_0
  checked_64)
  (FiniteChecks.interval_append test 128 192 288
  checked_128
  (FiniteChecks.interval_append test 192 256 288
  checked_192
  checked_256)))
theorem raw_words_eq (frame : Nat) : rawWords frame = Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.rawWords frame := by
  by_cases hf : frame < 288
  · exact eq_of_beq (checked frame (Nat.zero_le _) hf)
  · simp only [rawWords, hf, if_false]
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 2170) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.rawMaps frame cell := by
  by_cases hf : frame = 0
  · subst frame
    exact (Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.identity_exact cell).symm
  · simp only [rawMaps, hf, if_false, raw_words_eq]
    exact Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.Fast.raw_maps_eq frame cell hc
end Papers.RationalityTen.FacetUniverses.RootedSixExtra05.Generators.FastWords
