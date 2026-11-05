module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport522Part000
public import RootedSixExtra02GrowthCacheRidgeSupport522Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport522_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport522_rest_009 =
    (ridgeSupport522_suffix_009, ridgeSupport522_rest_009) := by rfl
theorem ridgeSupport522_suffix_decode_008 : PackedRawNatGrowth.readList 13 25 ridgeSupport522_rest_008 =
    (ridgeSupport522_suffix_008, ridgeSupport522_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 25 0
    ridgeSupport522_rest_008 ridgeSupport522_rest_009 ridgeSupport522_rest_009
    ridgeSupport522_008 ridgeSupport522_suffix_009 ridgeSupport522_008_decode ridgeSupport522_suffix_decode_009
theorem ridgeSupport522_suffix_decode_007 : PackedRawNatGrowth.readList 13 57 ridgeSupport522_rest_007 =
    (ridgeSupport522_suffix_007, ridgeSupport522_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 25
    ridgeSupport522_rest_007 ridgeSupport522_rest_008 ridgeSupport522_rest_009
    ridgeSupport522_007 ridgeSupport522_suffix_008 ridgeSupport522_007_decode ridgeSupport522_suffix_decode_008
theorem ridgeSupport522_suffix_decode_006 : PackedRawNatGrowth.readList 13 89 ridgeSupport522_rest_006 =
    (ridgeSupport522_suffix_006, ridgeSupport522_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 57
    ridgeSupport522_rest_006 ridgeSupport522_rest_007 ridgeSupport522_rest_009
    ridgeSupport522_006 ridgeSupport522_suffix_007 ridgeSupport522_006_decode ridgeSupport522_suffix_decode_007
theorem ridgeSupport522_suffix_decode_005 : PackedRawNatGrowth.readList 13 121 ridgeSupport522_rest_005 =
    (ridgeSupport522_suffix_005, ridgeSupport522_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 89
    ridgeSupport522_rest_005 ridgeSupport522_rest_006 ridgeSupport522_rest_009
    ridgeSupport522_005 ridgeSupport522_suffix_006 ridgeSupport522_005_decode ridgeSupport522_suffix_decode_006
theorem ridgeSupport522_suffix_decode_004 : PackedRawNatGrowth.readList 13 153 ridgeSupport522_rest_004 =
    (ridgeSupport522_suffix_004, ridgeSupport522_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 121
    ridgeSupport522_rest_004 ridgeSupport522_rest_005 ridgeSupport522_rest_009
    ridgeSupport522_004 ridgeSupport522_suffix_005 ridgeSupport522_004_decode ridgeSupport522_suffix_decode_005
theorem ridgeSupport522_suffix_decode_003 : PackedRawNatGrowth.readList 13 185 ridgeSupport522_rest_003 =
    (ridgeSupport522_suffix_003, ridgeSupport522_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 153
    ridgeSupport522_rest_003 ridgeSupport522_rest_004 ridgeSupport522_rest_009
    ridgeSupport522_003 ridgeSupport522_suffix_004 ridgeSupport522_003_decode ridgeSupport522_suffix_decode_004
theorem ridgeSupport522_suffix_decode_002 : PackedRawNatGrowth.readList 13 217 ridgeSupport522_rest_002 =
    (ridgeSupport522_suffix_002, ridgeSupport522_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 185
    ridgeSupport522_rest_002 ridgeSupport522_rest_003 ridgeSupport522_rest_009
    ridgeSupport522_002 ridgeSupport522_suffix_003 ridgeSupport522_002_decode ridgeSupport522_suffix_decode_003
theorem ridgeSupport522_suffix_decode_001 : PackedRawNatGrowth.readList 13 249 ridgeSupport522_rest_001 =
    (ridgeSupport522_suffix_001, ridgeSupport522_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 217
    ridgeSupport522_rest_001 ridgeSupport522_rest_002 ridgeSupport522_rest_009
    ridgeSupport522_001 ridgeSupport522_suffix_002 ridgeSupport522_001_decode ridgeSupport522_suffix_decode_002
theorem ridgeSupport522_suffix_decode_000 : PackedRawNatGrowth.readList 13 281 ridgeSupport522_rest_000 =
    (ridgeSupport522_suffix_000, ridgeSupport522_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 249
    ridgeSupport522_rest_000 ridgeSupport522_rest_001 ridgeSupport522_rest_009
    ridgeSupport522_000 ridgeSupport522_suffix_001 ridgeSupport522_000_decode ridgeSupport522_suffix_decode_001
theorem ridgeSupport522_eq : candidateRows 522 = ridgeSupport522_suffix_000 := by
  change candidateSupports 522 = ridgeSupport522_suffix_000
  rw [ridgeSupport522_source]
  exact congrArg Prod.fst ridgeSupport522_suffix_decode_000
theorem ridgeTest_large_522 : ridgeTest 522 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport522_eq]
    simp only [ridgeSupport522_suffix_000, ridgeSupport522_suffix_001, ridgeSupport522_suffix_002, ridgeSupport522_suffix_003, ridgeSupport522_suffix_004, ridgeSupport522_suffix_005, ridgeSupport522_suffix_006, ridgeSupport522_suffix_007, ridgeSupport522_suffix_008, ridgeSupport522_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport522_000_mask, ridgeSupport522_001_mask, ridgeSupport522_002_mask, ridgeSupport522_003_mask, ridgeSupport522_004_mask, ridgeSupport522_005_mask, ridgeSupport522_006_mask, ridgeSupport522_007_mask, ridgeSupport522_008_mask]
    decide +kernel
  · rw [ridgeSupport522_eq]
    simp only [ridgeSupport522_suffix_000, ridgeSupport522_suffix_001, ridgeSupport522_suffix_002, ridgeSupport522_suffix_003, ridgeSupport522_suffix_004, ridgeSupport522_suffix_005, ridgeSupport522_suffix_006, ridgeSupport522_suffix_007, ridgeSupport522_suffix_008, ridgeSupport522_suffix_009, List.all_append, List.all_nil, ridgeSupport522_000_checked, ridgeSupport522_001_checked, ridgeSupport522_002_checked, ridgeSupport522_003_checked, ridgeSupport522_004_checked, ridgeSupport522_005_checked, ridgeSupport522_006_checked, ridgeSupport522_007_checked, ridgeSupport522_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
