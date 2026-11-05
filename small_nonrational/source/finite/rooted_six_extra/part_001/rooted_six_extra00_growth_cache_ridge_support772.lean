module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport772Part000
public import RootedSixExtra00GrowthCacheRidgeSupport772Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport772_suffix_decode_016 : PackedRawNatGrowth.readList 14 0 ridgeSupport772_rest_016 =
    (ridgeSupport772_suffix_016, ridgeSupport772_rest_016) := by rfl
theorem ridgeSupport772_suffix_decode_015 : PackedRawNatGrowth.readList 14 19 ridgeSupport772_rest_015 =
    (ridgeSupport772_suffix_015, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 19 0
    ridgeSupport772_rest_015 ridgeSupport772_rest_016 ridgeSupport772_rest_016
    ridgeSupport772_015 ridgeSupport772_suffix_016 ridgeSupport772_015_decode ridgeSupport772_suffix_decode_016
theorem ridgeSupport772_suffix_decode_014 : PackedRawNatGrowth.readList 14 51 ridgeSupport772_rest_014 =
    (ridgeSupport772_suffix_014, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 19
    ridgeSupport772_rest_014 ridgeSupport772_rest_015 ridgeSupport772_rest_016
    ridgeSupport772_014 ridgeSupport772_suffix_015 ridgeSupport772_014_decode ridgeSupport772_suffix_decode_015
theorem ridgeSupport772_suffix_decode_013 : PackedRawNatGrowth.readList 14 83 ridgeSupport772_rest_013 =
    (ridgeSupport772_suffix_013, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 51
    ridgeSupport772_rest_013 ridgeSupport772_rest_014 ridgeSupport772_rest_016
    ridgeSupport772_013 ridgeSupport772_suffix_014 ridgeSupport772_013_decode ridgeSupport772_suffix_decode_014
theorem ridgeSupport772_suffix_decode_012 : PackedRawNatGrowth.readList 14 115 ridgeSupport772_rest_012 =
    (ridgeSupport772_suffix_012, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 83
    ridgeSupport772_rest_012 ridgeSupport772_rest_013 ridgeSupport772_rest_016
    ridgeSupport772_012 ridgeSupport772_suffix_013 ridgeSupport772_012_decode ridgeSupport772_suffix_decode_013
theorem ridgeSupport772_suffix_decode_011 : PackedRawNatGrowth.readList 14 147 ridgeSupport772_rest_011 =
    (ridgeSupport772_suffix_011, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 115
    ridgeSupport772_rest_011 ridgeSupport772_rest_012 ridgeSupport772_rest_016
    ridgeSupport772_011 ridgeSupport772_suffix_012 ridgeSupport772_011_decode ridgeSupport772_suffix_decode_012
theorem ridgeSupport772_suffix_decode_010 : PackedRawNatGrowth.readList 14 179 ridgeSupport772_rest_010 =
    (ridgeSupport772_suffix_010, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 147
    ridgeSupport772_rest_010 ridgeSupport772_rest_011 ridgeSupport772_rest_016
    ridgeSupport772_010 ridgeSupport772_suffix_011 ridgeSupport772_010_decode ridgeSupport772_suffix_decode_011
theorem ridgeSupport772_suffix_decode_009 : PackedRawNatGrowth.readList 14 211 ridgeSupport772_rest_009 =
    (ridgeSupport772_suffix_009, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 179
    ridgeSupport772_rest_009 ridgeSupport772_rest_010 ridgeSupport772_rest_016
    ridgeSupport772_009 ridgeSupport772_suffix_010 ridgeSupport772_009_decode ridgeSupport772_suffix_decode_010
theorem ridgeSupport772_suffix_decode_008 : PackedRawNatGrowth.readList 14 243 ridgeSupport772_rest_008 =
    (ridgeSupport772_suffix_008, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 211
    ridgeSupport772_rest_008 ridgeSupport772_rest_009 ridgeSupport772_rest_016
    ridgeSupport772_008 ridgeSupport772_suffix_009 ridgeSupport772_008_decode ridgeSupport772_suffix_decode_009
theorem ridgeSupport772_suffix_decode_007 : PackedRawNatGrowth.readList 14 275 ridgeSupport772_rest_007 =
    (ridgeSupport772_suffix_007, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 243
    ridgeSupport772_rest_007 ridgeSupport772_rest_008 ridgeSupport772_rest_016
    ridgeSupport772_007 ridgeSupport772_suffix_008 ridgeSupport772_007_decode ridgeSupport772_suffix_decode_008
theorem ridgeSupport772_suffix_decode_006 : PackedRawNatGrowth.readList 14 307 ridgeSupport772_rest_006 =
    (ridgeSupport772_suffix_006, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 275
    ridgeSupport772_rest_006 ridgeSupport772_rest_007 ridgeSupport772_rest_016
    ridgeSupport772_006 ridgeSupport772_suffix_007 ridgeSupport772_006_decode ridgeSupport772_suffix_decode_007
theorem ridgeSupport772_suffix_decode_005 : PackedRawNatGrowth.readList 14 339 ridgeSupport772_rest_005 =
    (ridgeSupport772_suffix_005, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 307
    ridgeSupport772_rest_005 ridgeSupport772_rest_006 ridgeSupport772_rest_016
    ridgeSupport772_005 ridgeSupport772_suffix_006 ridgeSupport772_005_decode ridgeSupport772_suffix_decode_006
theorem ridgeSupport772_suffix_decode_004 : PackedRawNatGrowth.readList 14 371 ridgeSupport772_rest_004 =
    (ridgeSupport772_suffix_004, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 339
    ridgeSupport772_rest_004 ridgeSupport772_rest_005 ridgeSupport772_rest_016
    ridgeSupport772_004 ridgeSupport772_suffix_005 ridgeSupport772_004_decode ridgeSupport772_suffix_decode_005
theorem ridgeSupport772_suffix_decode_003 : PackedRawNatGrowth.readList 14 403 ridgeSupport772_rest_003 =
    (ridgeSupport772_suffix_003, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 371
    ridgeSupport772_rest_003 ridgeSupport772_rest_004 ridgeSupport772_rest_016
    ridgeSupport772_003 ridgeSupport772_suffix_004 ridgeSupport772_003_decode ridgeSupport772_suffix_decode_004
theorem ridgeSupport772_suffix_decode_002 : PackedRawNatGrowth.readList 14 435 ridgeSupport772_rest_002 =
    (ridgeSupport772_suffix_002, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 403
    ridgeSupport772_rest_002 ridgeSupport772_rest_003 ridgeSupport772_rest_016
    ridgeSupport772_002 ridgeSupport772_suffix_003 ridgeSupport772_002_decode ridgeSupport772_suffix_decode_003
theorem ridgeSupport772_suffix_decode_001 : PackedRawNatGrowth.readList 14 467 ridgeSupport772_rest_001 =
    (ridgeSupport772_suffix_001, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 435
    ridgeSupport772_rest_001 ridgeSupport772_rest_002 ridgeSupport772_rest_016
    ridgeSupport772_001 ridgeSupport772_suffix_002 ridgeSupport772_001_decode ridgeSupport772_suffix_decode_002
theorem ridgeSupport772_suffix_decode_000 : PackedRawNatGrowth.readList 14 499 ridgeSupport772_rest_000 =
    (ridgeSupport772_suffix_000, ridgeSupport772_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 467
    ridgeSupport772_rest_000 ridgeSupport772_rest_001 ridgeSupport772_rest_016
    ridgeSupport772_000 ridgeSupport772_suffix_001 ridgeSupport772_000_decode ridgeSupport772_suffix_decode_001
theorem ridgeSupport772_eq : candidateRows 772 = ridgeSupport772_suffix_000 := by
  change candidateSupports 772 = ridgeSupport772_suffix_000
  rw [ridgeSupport772_source]
  exact congrArg Prod.fst ridgeSupport772_suffix_decode_000
theorem ridgeTest_large_772 : ridgeTest 772 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport772_eq]
    simp only [ridgeSupport772_suffix_000, ridgeSupport772_suffix_001, ridgeSupport772_suffix_002, ridgeSupport772_suffix_003, ridgeSupport772_suffix_004, ridgeSupport772_suffix_005, ridgeSupport772_suffix_006, ridgeSupport772_suffix_007, ridgeSupport772_suffix_008, ridgeSupport772_suffix_009, ridgeSupport772_suffix_010, ridgeSupport772_suffix_011, ridgeSupport772_suffix_012, ridgeSupport772_suffix_013, ridgeSupport772_suffix_014, ridgeSupport772_suffix_015, ridgeSupport772_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport772_000_mask, ridgeSupport772_001_mask, ridgeSupport772_002_mask, ridgeSupport772_003_mask, ridgeSupport772_004_mask, ridgeSupport772_005_mask, ridgeSupport772_006_mask, ridgeSupport772_007_mask, ridgeSupport772_008_mask, ridgeSupport772_009_mask, ridgeSupport772_010_mask, ridgeSupport772_011_mask, ridgeSupport772_012_mask, ridgeSupport772_013_mask, ridgeSupport772_014_mask, ridgeSupport772_015_mask]
    decide +kernel
  · rw [ridgeSupport772_eq]
    simp only [ridgeSupport772_suffix_000, ridgeSupport772_suffix_001, ridgeSupport772_suffix_002, ridgeSupport772_suffix_003, ridgeSupport772_suffix_004, ridgeSupport772_suffix_005, ridgeSupport772_suffix_006, ridgeSupport772_suffix_007, ridgeSupport772_suffix_008, ridgeSupport772_suffix_009, ridgeSupport772_suffix_010, ridgeSupport772_suffix_011, ridgeSupport772_suffix_012, ridgeSupport772_suffix_013, ridgeSupport772_suffix_014, ridgeSupport772_suffix_015, ridgeSupport772_suffix_016, List.all_append, List.all_nil, ridgeSupport772_000_checked, ridgeSupport772_001_checked, ridgeSupport772_002_checked, ridgeSupport772_003_checked, ridgeSupport772_004_checked, ridgeSupport772_005_checked, ridgeSupport772_006_checked, ridgeSupport772_007_checked, ridgeSupport772_008_checked, ridgeSupport772_009_checked, ridgeSupport772_010_checked, ridgeSupport772_011_checked, ridgeSupport772_012_checked, ridgeSupport772_013_checked, ridgeSupport772_014_checked, ridgeSupport772_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
