module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport776Part000
public import RootedSixExtra00GrowthCacheRidgeSupport776Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport776_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport776_rest_016 =
    (ridgeSupport776_suffix_016, ridgeSupport776_rest_016) := by rfl
theorem ridgeSupport776_suffix_decode_015 : PackedRawNatGrowth.readList 14 19 ridgeSupport776_rest_015 =
    (ridgeSupport776_suffix_015, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 19 0
    ridgeSupport776_rest_015 ridgeSupport776_rest_016 ridgeSupport776_rest_016
    ridgeSupport776_015 ridgeSupport776_suffix_016 ridgeSupport776_015_decode ridgeSupport776_suffix_decode_016
theorem ridgeSupport776_suffix_decode_014 : PackedRawNatGrowth.readList 14 51 ridgeSupport776_rest_014 =
    (ridgeSupport776_suffix_014, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 19
    ridgeSupport776_rest_014 ridgeSupport776_rest_015 ridgeSupport776_rest_016
    ridgeSupport776_014 ridgeSupport776_suffix_015 ridgeSupport776_014_decode ridgeSupport776_suffix_decode_015
theorem ridgeSupport776_suffix_decode_013 : PackedRawNatGrowth.readList 14 83 ridgeSupport776_rest_013 =
    (ridgeSupport776_suffix_013, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 51
    ridgeSupport776_rest_013 ridgeSupport776_rest_014 ridgeSupport776_rest_016
    ridgeSupport776_013 ridgeSupport776_suffix_014 ridgeSupport776_013_decode ridgeSupport776_suffix_decode_014
theorem ridgeSupport776_suffix_decode_012 : PackedRawNatGrowth.readList 14 115 ridgeSupport776_rest_012 =
    (ridgeSupport776_suffix_012, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 83
    ridgeSupport776_rest_012 ridgeSupport776_rest_013 ridgeSupport776_rest_016
    ridgeSupport776_012 ridgeSupport776_suffix_013 ridgeSupport776_012_decode ridgeSupport776_suffix_decode_013
theorem ridgeSupport776_suffix_decode_011 : PackedRawNatGrowth.readList 14 147 ridgeSupport776_rest_011 =
    (ridgeSupport776_suffix_011, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 115
    ridgeSupport776_rest_011 ridgeSupport776_rest_012 ridgeSupport776_rest_016
    ridgeSupport776_011 ridgeSupport776_suffix_012 ridgeSupport776_011_decode ridgeSupport776_suffix_decode_012
theorem ridgeSupport776_suffix_decode_010 : PackedRawNatGrowth.readList 14 179 ridgeSupport776_rest_010 =
    (ridgeSupport776_suffix_010, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 147
    ridgeSupport776_rest_010 ridgeSupport776_rest_011 ridgeSupport776_rest_016
    ridgeSupport776_010 ridgeSupport776_suffix_011 ridgeSupport776_010_decode ridgeSupport776_suffix_decode_011
theorem ridgeSupport776_suffix_decode_009 : PackedRawNatGrowth.readList 14 211 ridgeSupport776_rest_009 =
    (ridgeSupport776_suffix_009, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 179
    ridgeSupport776_rest_009 ridgeSupport776_rest_010 ridgeSupport776_rest_016
    ridgeSupport776_009 ridgeSupport776_suffix_010 ridgeSupport776_009_decode ridgeSupport776_suffix_decode_010
theorem ridgeSupport776_suffix_decode_008 : PackedRawNatGrowth.readList 14 243 ridgeSupport776_rest_008 =
    (ridgeSupport776_suffix_008, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 211
    ridgeSupport776_rest_008 ridgeSupport776_rest_009 ridgeSupport776_rest_016
    ridgeSupport776_008 ridgeSupport776_suffix_009 ridgeSupport776_008_decode ridgeSupport776_suffix_decode_009
theorem ridgeSupport776_suffix_decode_007 : PackedRawNatGrowth.readList 14 275 ridgeSupport776_rest_007 =
    (ridgeSupport776_suffix_007, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 243
    ridgeSupport776_rest_007 ridgeSupport776_rest_008 ridgeSupport776_rest_016
    ridgeSupport776_007 ridgeSupport776_suffix_008 ridgeSupport776_007_decode ridgeSupport776_suffix_decode_008
theorem ridgeSupport776_suffix_decode_006 : PackedRawNatGrowth.readList 14 307 ridgeSupport776_rest_006 =
    (ridgeSupport776_suffix_006, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 275
    ridgeSupport776_rest_006 ridgeSupport776_rest_007 ridgeSupport776_rest_016
    ridgeSupport776_006 ridgeSupport776_suffix_007 ridgeSupport776_006_decode ridgeSupport776_suffix_decode_007
theorem ridgeSupport776_suffix_decode_005 : PackedRawNatGrowth.readList 14 339 ridgeSupport776_rest_005 =
    (ridgeSupport776_suffix_005, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 307
    ridgeSupport776_rest_005 ridgeSupport776_rest_006 ridgeSupport776_rest_016
    ridgeSupport776_005 ridgeSupport776_suffix_006 ridgeSupport776_005_decode ridgeSupport776_suffix_decode_006
theorem ridgeSupport776_suffix_decode_004 : PackedRawNatGrowth.readList 14 371 ridgeSupport776_rest_004 =
    (ridgeSupport776_suffix_004, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 339
    ridgeSupport776_rest_004 ridgeSupport776_rest_005 ridgeSupport776_rest_016
    ridgeSupport776_004 ridgeSupport776_suffix_005 ridgeSupport776_004_decode ridgeSupport776_suffix_decode_005
theorem ridgeSupport776_suffix_decode_003 : PackedRawNatGrowth.readList 14 403 ridgeSupport776_rest_003 =
    (ridgeSupport776_suffix_003, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 371
    ridgeSupport776_rest_003 ridgeSupport776_rest_004 ridgeSupport776_rest_016
    ridgeSupport776_003 ridgeSupport776_suffix_004 ridgeSupport776_003_decode ridgeSupport776_suffix_decode_004
theorem ridgeSupport776_suffix_decode_002 : PackedRawNatGrowth.readList 14 435 ridgeSupport776_rest_002 =
    (ridgeSupport776_suffix_002, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 403
    ridgeSupport776_rest_002 ridgeSupport776_rest_003 ridgeSupport776_rest_016
    ridgeSupport776_002 ridgeSupport776_suffix_003 ridgeSupport776_002_decode ridgeSupport776_suffix_decode_003
theorem ridgeSupport776_suffix_decode_001 : PackedRawNatGrowth.readList 14 467 ridgeSupport776_rest_001 =
    (ridgeSupport776_suffix_001, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 435
    ridgeSupport776_rest_001 ridgeSupport776_rest_002 ridgeSupport776_rest_016
    ridgeSupport776_001 ridgeSupport776_suffix_002 ridgeSupport776_001_decode ridgeSupport776_suffix_decode_002
theorem ridgeSupport776_suffix_decode_000 : PackedRawNatGrowth.readList 14 499 ridgeSupport776_rest_000 =
    (ridgeSupport776_suffix_000, ridgeSupport776_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 467
    ridgeSupport776_rest_000 ridgeSupport776_rest_001 ridgeSupport776_rest_016
    ridgeSupport776_000 ridgeSupport776_suffix_001 ridgeSupport776_000_decode ridgeSupport776_suffix_decode_001
theorem ridgeSupport776_eq : candidateRows 776 = ridgeSupport776_suffix_000 := by
  change candidateSupports 776 = ridgeSupport776_suffix_000
  rw [ridgeSupport776_source]
  exact congrArg Prod.fst ridgeSupport776_suffix_decode_000
theorem ridgeTest_large_776 : ridgeTest 776 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport776_eq]
    simp only [ridgeSupport776_suffix_000, ridgeSupport776_suffix_001, ridgeSupport776_suffix_002, ridgeSupport776_suffix_003, ridgeSupport776_suffix_004, ridgeSupport776_suffix_005, ridgeSupport776_suffix_006, ridgeSupport776_suffix_007, ridgeSupport776_suffix_008, ridgeSupport776_suffix_009, ridgeSupport776_suffix_010, ridgeSupport776_suffix_011, ridgeSupport776_suffix_012, ridgeSupport776_suffix_013, ridgeSupport776_suffix_014, ridgeSupport776_suffix_015, ridgeSupport776_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport776_000_mask, ridgeSupport776_001_mask, ridgeSupport776_002_mask, ridgeSupport776_003_mask, ridgeSupport776_004_mask, ridgeSupport776_005_mask, ridgeSupport776_006_mask, ridgeSupport776_007_mask, ridgeSupport776_008_mask, ridgeSupport776_009_mask, ridgeSupport776_010_mask, ridgeSupport776_011_mask, ridgeSupport776_012_mask, ridgeSupport776_013_mask, ridgeSupport776_014_mask, ridgeSupport776_015_mask]
    decide +kernel
  · rw [ridgeSupport776_eq]
    simp only [ridgeSupport776_suffix_000, ridgeSupport776_suffix_001, ridgeSupport776_suffix_002, ridgeSupport776_suffix_003, ridgeSupport776_suffix_004, ridgeSupport776_suffix_005, ridgeSupport776_suffix_006, ridgeSupport776_suffix_007, ridgeSupport776_suffix_008, ridgeSupport776_suffix_009, ridgeSupport776_suffix_010, ridgeSupport776_suffix_011, ridgeSupport776_suffix_012, ridgeSupport776_suffix_013, ridgeSupport776_suffix_014, ridgeSupport776_suffix_015, ridgeSupport776_suffix_016, List.all_append, List.all_nil, ridgeSupport776_000_checked, ridgeSupport776_001_checked, ridgeSupport776_002_checked, ridgeSupport776_003_checked, ridgeSupport776_004_checked, ridgeSupport776_005_checked, ridgeSupport776_006_checked, ridgeSupport776_007_checked, ridgeSupport776_008_checked, ridgeSupport776_009_checked, ridgeSupport776_010_checked, ridgeSupport776_011_checked, ridgeSupport776_012_checked, ridgeSupport776_013_checked, ridgeSupport776_014_checked, ridgeSupport776_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
