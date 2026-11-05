module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport536Part000
public import RootedSixExtra00GrowthCacheRidgeSupport536Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport536_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport536_rest_009 =
    (ridgeSupport536_suffix_009, ridgeSupport536_rest_009) := by rfl
theorem ridgeSupport536_suffix_decode_008 : PackedRawNatGrowth.readList 14 7 ridgeSupport536_rest_008 =
    (ridgeSupport536_suffix_008, ridgeSupport536_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 7 0
    ridgeSupport536_rest_008 ridgeSupport536_rest_009 ridgeSupport536_rest_009
    ridgeSupport536_008 ridgeSupport536_suffix_009 ridgeSupport536_008_decode ridgeSupport536_suffix_decode_009
theorem ridgeSupport536_suffix_decode_007 : PackedRawNatGrowth.readList 14 39 ridgeSupport536_rest_007 =
    (ridgeSupport536_suffix_007, ridgeSupport536_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 7
    ridgeSupport536_rest_007 ridgeSupport536_rest_008 ridgeSupport536_rest_009
    ridgeSupport536_007 ridgeSupport536_suffix_008 ridgeSupport536_007_decode ridgeSupport536_suffix_decode_008
theorem ridgeSupport536_suffix_decode_006 : PackedRawNatGrowth.readList 14 71 ridgeSupport536_rest_006 =
    (ridgeSupport536_suffix_006, ridgeSupport536_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 39
    ridgeSupport536_rest_006 ridgeSupport536_rest_007 ridgeSupport536_rest_009
    ridgeSupport536_006 ridgeSupport536_suffix_007 ridgeSupport536_006_decode ridgeSupport536_suffix_decode_007
theorem ridgeSupport536_suffix_decode_005 : PackedRawNatGrowth.readList 14 103 ridgeSupport536_rest_005 =
    (ridgeSupport536_suffix_005, ridgeSupport536_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 71
    ridgeSupport536_rest_005 ridgeSupport536_rest_006 ridgeSupport536_rest_009
    ridgeSupport536_005 ridgeSupport536_suffix_006 ridgeSupport536_005_decode ridgeSupport536_suffix_decode_006
theorem ridgeSupport536_suffix_decode_004 : PackedRawNatGrowth.readList 14 135 ridgeSupport536_rest_004 =
    (ridgeSupport536_suffix_004, ridgeSupport536_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 103
    ridgeSupport536_rest_004 ridgeSupport536_rest_005 ridgeSupport536_rest_009
    ridgeSupport536_004 ridgeSupport536_suffix_005 ridgeSupport536_004_decode ridgeSupport536_suffix_decode_005
theorem ridgeSupport536_suffix_decode_003 : PackedRawNatGrowth.readList 14 167 ridgeSupport536_rest_003 =
    (ridgeSupport536_suffix_003, ridgeSupport536_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 135
    ridgeSupport536_rest_003 ridgeSupport536_rest_004 ridgeSupport536_rest_009
    ridgeSupport536_003 ridgeSupport536_suffix_004 ridgeSupport536_003_decode ridgeSupport536_suffix_decode_004
theorem ridgeSupport536_suffix_decode_002 : PackedRawNatGrowth.readList 14 199 ridgeSupport536_rest_002 =
    (ridgeSupport536_suffix_002, ridgeSupport536_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 167
    ridgeSupport536_rest_002 ridgeSupport536_rest_003 ridgeSupport536_rest_009
    ridgeSupport536_002 ridgeSupport536_suffix_003 ridgeSupport536_002_decode ridgeSupport536_suffix_decode_003
theorem ridgeSupport536_suffix_decode_001 : PackedRawNatGrowth.readList 14 231 ridgeSupport536_rest_001 =
    (ridgeSupport536_suffix_001, ridgeSupport536_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 199
    ridgeSupport536_rest_001 ridgeSupport536_rest_002 ridgeSupport536_rest_009
    ridgeSupport536_001 ridgeSupport536_suffix_002 ridgeSupport536_001_decode ridgeSupport536_suffix_decode_002
theorem ridgeSupport536_suffix_decode_000 : PackedRawNatGrowth.readList 14 263 ridgeSupport536_rest_000 =
    (ridgeSupport536_suffix_000, ridgeSupport536_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 231
    ridgeSupport536_rest_000 ridgeSupport536_rest_001 ridgeSupport536_rest_009
    ridgeSupport536_000 ridgeSupport536_suffix_001 ridgeSupport536_000_decode ridgeSupport536_suffix_decode_001
theorem ridgeSupport536_eq : candidateRows 536 = ridgeSupport536_suffix_000 := by
  change candidateSupports 536 = ridgeSupport536_suffix_000
  rw [ridgeSupport536_source]
  exact congrArg Prod.fst ridgeSupport536_suffix_decode_000
theorem ridgeTest_large_536 : ridgeTest 536 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport536_eq]
    simp only [ridgeSupport536_suffix_000, ridgeSupport536_suffix_001, ridgeSupport536_suffix_002, ridgeSupport536_suffix_003, ridgeSupport536_suffix_004, ridgeSupport536_suffix_005, ridgeSupport536_suffix_006, ridgeSupport536_suffix_007, ridgeSupport536_suffix_008, ridgeSupport536_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport536_000_mask, ridgeSupport536_001_mask, ridgeSupport536_002_mask, ridgeSupport536_003_mask, ridgeSupport536_004_mask, ridgeSupport536_005_mask, ridgeSupport536_006_mask, ridgeSupport536_007_mask, ridgeSupport536_008_mask]
    decide +kernel
  · rw [ridgeSupport536_eq]
    simp only [ridgeSupport536_suffix_000, ridgeSupport536_suffix_001, ridgeSupport536_suffix_002, ridgeSupport536_suffix_003, ridgeSupport536_suffix_004, ridgeSupport536_suffix_005, ridgeSupport536_suffix_006, ridgeSupport536_suffix_007, ridgeSupport536_suffix_008, ridgeSupport536_suffix_009, List.all_append, List.all_nil, ridgeSupport536_000_checked, ridgeSupport536_001_checked, ridgeSupport536_002_checked, ridgeSupport536_003_checked, ridgeSupport536_004_checked, ridgeSupport536_005_checked, ridgeSupport536_006_checked, ridgeSupport536_007_checked, ridgeSupport536_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
