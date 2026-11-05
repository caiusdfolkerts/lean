module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport388Part000
public import RootedSixExtra00GrowthCacheRidgeSupport388Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport388_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport388_rest_016 =
    (ridgeSupport388_suffix_016, ridgeSupport388_rest_016) := by rfl
theorem ridgeSupport388_suffix_decode_015 : PackedRawNatGrowth.readList 14 19 ridgeSupport388_rest_015 =
    (ridgeSupport388_suffix_015, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 19 0
    ridgeSupport388_rest_015 ridgeSupport388_rest_016 ridgeSupport388_rest_016
    ridgeSupport388_015 ridgeSupport388_suffix_016 ridgeSupport388_015_decode ridgeSupport388_suffix_decode_016
theorem ridgeSupport388_suffix_decode_014 : PackedRawNatGrowth.readList 14 51 ridgeSupport388_rest_014 =
    (ridgeSupport388_suffix_014, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 19
    ridgeSupport388_rest_014 ridgeSupport388_rest_015 ridgeSupport388_rest_016
    ridgeSupport388_014 ridgeSupport388_suffix_015 ridgeSupport388_014_decode ridgeSupport388_suffix_decode_015
theorem ridgeSupport388_suffix_decode_013 : PackedRawNatGrowth.readList 14 83 ridgeSupport388_rest_013 =
    (ridgeSupport388_suffix_013, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 51
    ridgeSupport388_rest_013 ridgeSupport388_rest_014 ridgeSupport388_rest_016
    ridgeSupport388_013 ridgeSupport388_suffix_014 ridgeSupport388_013_decode ridgeSupport388_suffix_decode_014
theorem ridgeSupport388_suffix_decode_012 : PackedRawNatGrowth.readList 14 115 ridgeSupport388_rest_012 =
    (ridgeSupport388_suffix_012, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 83
    ridgeSupport388_rest_012 ridgeSupport388_rest_013 ridgeSupport388_rest_016
    ridgeSupport388_012 ridgeSupport388_suffix_013 ridgeSupport388_012_decode ridgeSupport388_suffix_decode_013
theorem ridgeSupport388_suffix_decode_011 : PackedRawNatGrowth.readList 14 147 ridgeSupport388_rest_011 =
    (ridgeSupport388_suffix_011, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 115
    ridgeSupport388_rest_011 ridgeSupport388_rest_012 ridgeSupport388_rest_016
    ridgeSupport388_011 ridgeSupport388_suffix_012 ridgeSupport388_011_decode ridgeSupport388_suffix_decode_012
theorem ridgeSupport388_suffix_decode_010 : PackedRawNatGrowth.readList 14 179 ridgeSupport388_rest_010 =
    (ridgeSupport388_suffix_010, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 147
    ridgeSupport388_rest_010 ridgeSupport388_rest_011 ridgeSupport388_rest_016
    ridgeSupport388_010 ridgeSupport388_suffix_011 ridgeSupport388_010_decode ridgeSupport388_suffix_decode_011
theorem ridgeSupport388_suffix_decode_009 : PackedRawNatGrowth.readList 14 211 ridgeSupport388_rest_009 =
    (ridgeSupport388_suffix_009, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 179
    ridgeSupport388_rest_009 ridgeSupport388_rest_010 ridgeSupport388_rest_016
    ridgeSupport388_009 ridgeSupport388_suffix_010 ridgeSupport388_009_decode ridgeSupport388_suffix_decode_010
theorem ridgeSupport388_suffix_decode_008 : PackedRawNatGrowth.readList 14 243 ridgeSupport388_rest_008 =
    (ridgeSupport388_suffix_008, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 211
    ridgeSupport388_rest_008 ridgeSupport388_rest_009 ridgeSupport388_rest_016
    ridgeSupport388_008 ridgeSupport388_suffix_009 ridgeSupport388_008_decode ridgeSupport388_suffix_decode_009
theorem ridgeSupport388_suffix_decode_007 : PackedRawNatGrowth.readList 14 275 ridgeSupport388_rest_007 =
    (ridgeSupport388_suffix_007, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 243
    ridgeSupport388_rest_007 ridgeSupport388_rest_008 ridgeSupport388_rest_016
    ridgeSupport388_007 ridgeSupport388_suffix_008 ridgeSupport388_007_decode ridgeSupport388_suffix_decode_008
theorem ridgeSupport388_suffix_decode_006 : PackedRawNatGrowth.readList 14 307 ridgeSupport388_rest_006 =
    (ridgeSupport388_suffix_006, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 275
    ridgeSupport388_rest_006 ridgeSupport388_rest_007 ridgeSupport388_rest_016
    ridgeSupport388_006 ridgeSupport388_suffix_007 ridgeSupport388_006_decode ridgeSupport388_suffix_decode_007
theorem ridgeSupport388_suffix_decode_005 : PackedRawNatGrowth.readList 14 339 ridgeSupport388_rest_005 =
    (ridgeSupport388_suffix_005, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 307
    ridgeSupport388_rest_005 ridgeSupport388_rest_006 ridgeSupport388_rest_016
    ridgeSupport388_005 ridgeSupport388_suffix_006 ridgeSupport388_005_decode ridgeSupport388_suffix_decode_006
theorem ridgeSupport388_suffix_decode_004 : PackedRawNatGrowth.readList 14 371 ridgeSupport388_rest_004 =
    (ridgeSupport388_suffix_004, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 339
    ridgeSupport388_rest_004 ridgeSupport388_rest_005 ridgeSupport388_rest_016
    ridgeSupport388_004 ridgeSupport388_suffix_005 ridgeSupport388_004_decode ridgeSupport388_suffix_decode_005
theorem ridgeSupport388_suffix_decode_003 : PackedRawNatGrowth.readList 14 403 ridgeSupport388_rest_003 =
    (ridgeSupport388_suffix_003, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 371
    ridgeSupport388_rest_003 ridgeSupport388_rest_004 ridgeSupport388_rest_016
    ridgeSupport388_003 ridgeSupport388_suffix_004 ridgeSupport388_003_decode ridgeSupport388_suffix_decode_004
theorem ridgeSupport388_suffix_decode_002 : PackedRawNatGrowth.readList 14 435 ridgeSupport388_rest_002 =
    (ridgeSupport388_suffix_002, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 403
    ridgeSupport388_rest_002 ridgeSupport388_rest_003 ridgeSupport388_rest_016
    ridgeSupport388_002 ridgeSupport388_suffix_003 ridgeSupport388_002_decode ridgeSupport388_suffix_decode_003
theorem ridgeSupport388_suffix_decode_001 : PackedRawNatGrowth.readList 14 467 ridgeSupport388_rest_001 =
    (ridgeSupport388_suffix_001, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 435
    ridgeSupport388_rest_001 ridgeSupport388_rest_002 ridgeSupport388_rest_016
    ridgeSupport388_001 ridgeSupport388_suffix_002 ridgeSupport388_001_decode ridgeSupport388_suffix_decode_002
theorem ridgeSupport388_suffix_decode_000 : PackedRawNatGrowth.readList 14 499 ridgeSupport388_rest_000 =
    (ridgeSupport388_suffix_000, ridgeSupport388_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 467
    ridgeSupport388_rest_000 ridgeSupport388_rest_001 ridgeSupport388_rest_016
    ridgeSupport388_000 ridgeSupport388_suffix_001 ridgeSupport388_000_decode ridgeSupport388_suffix_decode_001
theorem ridgeSupport388_eq : candidateRows 388 = ridgeSupport388_suffix_000 := by
  change candidateSupports 388 = ridgeSupport388_suffix_000
  rw [ridgeSupport388_source]
  exact congrArg Prod.fst ridgeSupport388_suffix_decode_000
theorem ridgeTest_large_388 : ridgeTest 388 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport388_eq]
    simp only [ridgeSupport388_suffix_000, ridgeSupport388_suffix_001, ridgeSupport388_suffix_002, ridgeSupport388_suffix_003, ridgeSupport388_suffix_004, ridgeSupport388_suffix_005, ridgeSupport388_suffix_006, ridgeSupport388_suffix_007, ridgeSupport388_suffix_008, ridgeSupport388_suffix_009, ridgeSupport388_suffix_010, ridgeSupport388_suffix_011, ridgeSupport388_suffix_012, ridgeSupport388_suffix_013, ridgeSupport388_suffix_014, ridgeSupport388_suffix_015, ridgeSupport388_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport388_000_mask, ridgeSupport388_001_mask, ridgeSupport388_002_mask, ridgeSupport388_003_mask, ridgeSupport388_004_mask, ridgeSupport388_005_mask, ridgeSupport388_006_mask, ridgeSupport388_007_mask, ridgeSupport388_008_mask, ridgeSupport388_009_mask, ridgeSupport388_010_mask, ridgeSupport388_011_mask, ridgeSupport388_012_mask, ridgeSupport388_013_mask, ridgeSupport388_014_mask, ridgeSupport388_015_mask]
    decide +kernel
  · rw [ridgeSupport388_eq]
    simp only [ridgeSupport388_suffix_000, ridgeSupport388_suffix_001, ridgeSupport388_suffix_002, ridgeSupport388_suffix_003, ridgeSupport388_suffix_004, ridgeSupport388_suffix_005, ridgeSupport388_suffix_006, ridgeSupport388_suffix_007, ridgeSupport388_suffix_008, ridgeSupport388_suffix_009, ridgeSupport388_suffix_010, ridgeSupport388_suffix_011, ridgeSupport388_suffix_012, ridgeSupport388_suffix_013, ridgeSupport388_suffix_014, ridgeSupport388_suffix_015, ridgeSupport388_suffix_016, List.all_append, List.all_nil, ridgeSupport388_000_checked, ridgeSupport388_001_checked, ridgeSupport388_002_checked, ridgeSupport388_003_checked, ridgeSupport388_004_checked, ridgeSupport388_005_checked, ridgeSupport388_006_checked, ridgeSupport388_007_checked, ridgeSupport388_008_checked, ridgeSupport388_009_checked, ridgeSupport388_010_checked, ridgeSupport388_011_checked, ridgeSupport388_012_checked, ridgeSupport388_013_checked, ridgeSupport388_014_checked, ridgeSupport388_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
