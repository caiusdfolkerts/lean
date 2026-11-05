module
prelude
public import RootedSixExtra04FastWordsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.FastWords
open Papers.RationalityTen PackedRawNatGrowth FiniteChecks
theorem checked_0 : Interval test 0 64 :=
  interval_of_check test 0 64 (by decide +kernel)
theorem checked_64 : Interval test 64 128 :=
  interval_of_check test 64 64 (by decide +kernel)
theorem checked_128 : Interval test 128 192 :=
  interval_of_check test 128 64 (by decide +kernel)
theorem checked_192 : Interval test 192 256 :=
  interval_of_check test 192 64 (by decide +kernel)
theorem checked_256 : Interval test 256 320 :=
  interval_of_check test 256 64 (by decide +kernel)
theorem checked_320 : Interval test 320 384 :=
  interval_of_check test 320 64 (by decide +kernel)
theorem checked_384 : Interval test 384 448 :=
  interval_of_check test 384 64 (by decide +kernel)
theorem checked_448 : Interval test 448 512 :=
  interval_of_check test 448 64 (by decide +kernel)
theorem checked_512 : Interval test 512 576 :=
  interval_of_check test 512 64 (by decide +kernel)
theorem checked_576 : Interval test 576 640 :=
  interval_of_check test 576 64 (by decide +kernel)
theorem checked_640 : Interval test 640 704 :=
  interval_of_check test 640 64 (by decide +kernel)
theorem checked_704 : Interval test 704 768 :=
  interval_of_check test 704 64 (by decide +kernel)
theorem checked_768 : Interval test 768 832 :=
  interval_of_check test 768 64 (by decide +kernel)
theorem checked_832 : Interval test 832 896 :=
  interval_of_check test 832 64 (by decide +kernel)
theorem checked_896 : Interval test 896 960 :=
  interval_of_check test 896 64 (by decide +kernel)
theorem checked_960 : Interval test 960 1024 :=
  interval_of_check test 960 64 (by decide +kernel)
theorem checked_1024 : Interval test 1024 1088 :=
  interval_of_check test 1024 64 (by decide +kernel)
theorem checked_1088 : Interval test 1088 1152 :=
  interval_of_check test 1088 64 (by decide +kernel)

theorem checked : Interval test 0 1152 :=
  (FiniteChecks.interval_append test 0 576 1152
  (FiniteChecks.interval_append test 0 256 576
  (FiniteChecks.interval_append test 0 128 256
  (FiniteChecks.interval_append test 0 64 128
  checked_0
  checked_64)
  (FiniteChecks.interval_append test 128 192 256
  checked_128
  checked_192))
  (FiniteChecks.interval_append test 256 384 576
  (FiniteChecks.interval_append test 256 320 384
  checked_256
  checked_320)
  (FiniteChecks.interval_append test 384 448 576
  checked_384
  (FiniteChecks.interval_append test 448 512 576
  checked_448
  checked_512))))
  (FiniteChecks.interval_append test 576 832 1152
  (FiniteChecks.interval_append test 576 704 832
  (FiniteChecks.interval_append test 576 640 704
  checked_576
  checked_640)
  (FiniteChecks.interval_append test 704 768 832
  checked_704
  checked_768))
  (FiniteChecks.interval_append test 832 960 1152
  (FiniteChecks.interval_append test 832 896 960
  checked_832
  checked_896)
  (FiniteChecks.interval_append test 960 1024 1152
  checked_960
  (FiniteChecks.interval_append test 1024 1088 1152
  checked_1024
  checked_1088)))))
theorem raw_words_eq (frame : Nat) : rawWords frame = Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.rawWords frame := by
  by_cases hf : frame < 1152
  · exact eq_of_beq (checked frame (Nat.zero_le _) hf)
  · simp only [rawWords, hf, if_false]
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 3640) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.rawMaps frame cell := by
  by_cases hf : frame = 0
  · subst frame
    exact (Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.identity_exact cell).symm
  · simp only [rawMaps, hf, if_false, raw_words_eq]
    exact Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.Fast.raw_maps_eq frame cell hc
#print axioms raw_words_eq
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixExtra04.Generators.FastWords
