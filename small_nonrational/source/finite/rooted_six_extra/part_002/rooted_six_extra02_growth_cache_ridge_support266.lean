module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport266Part000
public import RootedSixExtra02GrowthCacheRidgeSupport266Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport266_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport266_rest_009 =
    (ridgeSupport266_suffix_009, ridgeSupport266_rest_009) := by rfl
theorem ridgeSupport266_suffix_decode_008 : PackedRawNatGrowth.readList 13 25 ridgeSupport266_rest_008 =
    (ridgeSupport266_suffix_008, ridgeSupport266_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 25 0
    ridgeSupport266_rest_008 ridgeSupport266_rest_009 ridgeSupport266_rest_009
    ridgeSupport266_008 ridgeSupport266_suffix_009 ridgeSupport266_008_decode ridgeSupport266_suffix_decode_009
theorem ridgeSupport266_suffix_decode_007 : PackedRawNatGrowth.readList 13 57 ridgeSupport266_rest_007 =
    (ridgeSupport266_suffix_007, ridgeSupport266_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 25
    ridgeSupport266_rest_007 ridgeSupport266_rest_008 ridgeSupport266_rest_009
    ridgeSupport266_007 ridgeSupport266_suffix_008 ridgeSupport266_007_decode ridgeSupport266_suffix_decode_008
theorem ridgeSupport266_suffix_decode_006 : PackedRawNatGrowth.readList 13 89 ridgeSupport266_rest_006 =
    (ridgeSupport266_suffix_006, ridgeSupport266_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 57
    ridgeSupport266_rest_006 ridgeSupport266_rest_007 ridgeSupport266_rest_009
    ridgeSupport266_006 ridgeSupport266_suffix_007 ridgeSupport266_006_decode ridgeSupport266_suffix_decode_007
theorem ridgeSupport266_suffix_decode_005 : PackedRawNatGrowth.readList 13 121 ridgeSupport266_rest_005 =
    (ridgeSupport266_suffix_005, ridgeSupport266_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 89
    ridgeSupport266_rest_005 ridgeSupport266_rest_006 ridgeSupport266_rest_009
    ridgeSupport266_005 ridgeSupport266_suffix_006 ridgeSupport266_005_decode ridgeSupport266_suffix_decode_006
theorem ridgeSupport266_suffix_decode_004 : PackedRawNatGrowth.readList 13 153 ridgeSupport266_rest_004 =
    (ridgeSupport266_suffix_004, ridgeSupport266_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 121
    ridgeSupport266_rest_004 ridgeSupport266_rest_005 ridgeSupport266_rest_009
    ridgeSupport266_004 ridgeSupport266_suffix_005 ridgeSupport266_004_decode ridgeSupport266_suffix_decode_005
theorem ridgeSupport266_suffix_decode_003 : PackedRawNatGrowth.readList 13 185 ridgeSupport266_rest_003 =
    (ridgeSupport266_suffix_003, ridgeSupport266_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 153
    ridgeSupport266_rest_003 ridgeSupport266_rest_004 ridgeSupport266_rest_009
    ridgeSupport266_003 ridgeSupport266_suffix_004 ridgeSupport266_003_decode ridgeSupport266_suffix_decode_004
theorem ridgeSupport266_suffix_decode_002 : PackedRawNatGrowth.readList 13 217 ridgeSupport266_rest_002 =
    (ridgeSupport266_suffix_002, ridgeSupport266_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 185
    ridgeSupport266_rest_002 ridgeSupport266_rest_003 ridgeSupport266_rest_009
    ridgeSupport266_002 ridgeSupport266_suffix_003 ridgeSupport266_002_decode ridgeSupport266_suffix_decode_003
theorem ridgeSupport266_suffix_decode_001 : PackedRawNatGrowth.readList 13 249 ridgeSupport266_rest_001 =
    (ridgeSupport266_suffix_001, ridgeSupport266_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 217
    ridgeSupport266_rest_001 ridgeSupport266_rest_002 ridgeSupport266_rest_009
    ridgeSupport266_001 ridgeSupport266_suffix_002 ridgeSupport266_001_decode ridgeSupport266_suffix_decode_002
theorem ridgeSupport266_suffix_decode_000 : PackedRawNatGrowth.readList 13 281 ridgeSupport266_rest_000 =
    (ridgeSupport266_suffix_000, ridgeSupport266_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 249
    ridgeSupport266_rest_000 ridgeSupport266_rest_001 ridgeSupport266_rest_009
    ridgeSupport266_000 ridgeSupport266_suffix_001 ridgeSupport266_000_decode ridgeSupport266_suffix_decode_001
theorem ridgeSupport266_eq : candidateRows 266 = ridgeSupport266_suffix_000 := by
  change candidateSupports 266 = ridgeSupport266_suffix_000
  rw [ridgeSupport266_source]
  exact congrArg Prod.fst ridgeSupport266_suffix_decode_000
theorem ridgeTest_large_266 : ridgeTest 266 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport266_eq]
    simp only [ridgeSupport266_suffix_000, ridgeSupport266_suffix_001, ridgeSupport266_suffix_002, ridgeSupport266_suffix_003, ridgeSupport266_suffix_004, ridgeSupport266_suffix_005, ridgeSupport266_suffix_006, ridgeSupport266_suffix_007, ridgeSupport266_suffix_008, ridgeSupport266_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport266_000_mask, ridgeSupport266_001_mask, ridgeSupport266_002_mask, ridgeSupport266_003_mask, ridgeSupport266_004_mask, ridgeSupport266_005_mask, ridgeSupport266_006_mask, ridgeSupport266_007_mask, ridgeSupport266_008_mask]
    decide +kernel
  · rw [ridgeSupport266_eq]
    simp only [ridgeSupport266_suffix_000, ridgeSupport266_suffix_001, ridgeSupport266_suffix_002, ridgeSupport266_suffix_003, ridgeSupport266_suffix_004, ridgeSupport266_suffix_005, ridgeSupport266_suffix_006, ridgeSupport266_suffix_007, ridgeSupport266_suffix_008, ridgeSupport266_suffix_009, List.all_append, List.all_nil, ridgeSupport266_000_checked, ridgeSupport266_001_checked, ridgeSupport266_002_checked, ridgeSupport266_003_checked, ridgeSupport266_004_checked, ridgeSupport266_005_checked, ridgeSupport266_006_checked, ridgeSupport266_007_checked, ridgeSupport266_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
