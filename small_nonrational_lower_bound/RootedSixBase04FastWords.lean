module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase04FastWordsData

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.FastWords
open Papers.RationalityTen PackedRawNatGrowth FiniteChecks
cert_checked_8 0 64
cert_checked_8 64 128
cert_checked_8 128 192
cert_checked_8 192 256
cert_checked_8 256 320
cert_checked_8 320 384
cert_checked_8 384 448
cert_checked_8 448 512
cert_checked_8 512 576
cert_checked_8 576 640
cert_checked_8 640 704
cert_checked_8 704 768
cert_checked_8 768 832
cert_checked_8 832 896
cert_checked_8 896 960
cert_checked_8 960 1024
cert_checked_8 1024 1088
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
theorem raw_words_eq (frame : Nat) : rawWords frame = Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.rawWords frame := by
  by_cases hf : frame < 1152
  · exact eq_of_beq (checked frame (Nat.zero_le _) hf)
  · simp only [rawWords, hf, if_false]
theorem raw_maps_eq (frame cell : Nat) (hc : cell < 2824) :
    rawMaps frame cell = Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.rawMaps frame cell := by
  by_cases hf : frame = 0
  · subst frame
    exact (Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.identity_exact cell).symm
  · simp only [rawMaps, hf, if_false, raw_words_eq]
    exact Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.Fast.raw_maps_eq frame cell hc
#print axioms raw_words_eq
#print axioms raw_maps_eq
end Papers.RationalityTen.FacetUniverses.RootedSixBase04.Generators.FastWords
