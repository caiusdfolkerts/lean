module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport52Part000
public import RootedSixExtra00GrowthCacheRidgeSupport52Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport52_suffix_decode_015 : PackedRawNatGrowth.readList 14 0 ridgeSupport52_rest_015 =
    (ridgeSupport52_suffix_015, ridgeSupport52_rest_015) := by rfl
theorem ridgeSupport52_suffix_decode_014 : PackedRawNatGrowth.readList 14 13 ridgeSupport52_rest_014 =
    (ridgeSupport52_suffix_014, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport52_rest_014 ridgeSupport52_rest_015 ridgeSupport52_rest_015
    ridgeSupport52_014 ridgeSupport52_suffix_015 ridgeSupport52_014_decode ridgeSupport52_suffix_decode_015
theorem ridgeSupport52_suffix_decode_013 : PackedRawNatGrowth.readList 14 45 ridgeSupport52_rest_013 =
    (ridgeSupport52_suffix_013, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport52_rest_013 ridgeSupport52_rest_014 ridgeSupport52_rest_015
    ridgeSupport52_013 ridgeSupport52_suffix_014 ridgeSupport52_013_decode ridgeSupport52_suffix_decode_014
theorem ridgeSupport52_suffix_decode_012 : PackedRawNatGrowth.readList 14 77 ridgeSupport52_rest_012 =
    (ridgeSupport52_suffix_012, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport52_rest_012 ridgeSupport52_rest_013 ridgeSupport52_rest_015
    ridgeSupport52_012 ridgeSupport52_suffix_013 ridgeSupport52_012_decode ridgeSupport52_suffix_decode_013
theorem ridgeSupport52_suffix_decode_011 : PackedRawNatGrowth.readList 14 109 ridgeSupport52_rest_011 =
    (ridgeSupport52_suffix_011, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport52_rest_011 ridgeSupport52_rest_012 ridgeSupport52_rest_015
    ridgeSupport52_011 ridgeSupport52_suffix_012 ridgeSupport52_011_decode ridgeSupport52_suffix_decode_012
theorem ridgeSupport52_suffix_decode_010 : PackedRawNatGrowth.readList 14 141 ridgeSupport52_rest_010 =
    (ridgeSupport52_suffix_010, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport52_rest_010 ridgeSupport52_rest_011 ridgeSupport52_rest_015
    ridgeSupport52_010 ridgeSupport52_suffix_011 ridgeSupport52_010_decode ridgeSupport52_suffix_decode_011
theorem ridgeSupport52_suffix_decode_009 : PackedRawNatGrowth.readList 14 173 ridgeSupport52_rest_009 =
    (ridgeSupport52_suffix_009, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport52_rest_009 ridgeSupport52_rest_010 ridgeSupport52_rest_015
    ridgeSupport52_009 ridgeSupport52_suffix_010 ridgeSupport52_009_decode ridgeSupport52_suffix_decode_010
theorem ridgeSupport52_suffix_decode_008 : PackedRawNatGrowth.readList 14 205 ridgeSupport52_rest_008 =
    (ridgeSupport52_suffix_008, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport52_rest_008 ridgeSupport52_rest_009 ridgeSupport52_rest_015
    ridgeSupport52_008 ridgeSupport52_suffix_009 ridgeSupport52_008_decode ridgeSupport52_suffix_decode_009
theorem ridgeSupport52_suffix_decode_007 : PackedRawNatGrowth.readList 14 237 ridgeSupport52_rest_007 =
    (ridgeSupport52_suffix_007, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport52_rest_007 ridgeSupport52_rest_008 ridgeSupport52_rest_015
    ridgeSupport52_007 ridgeSupport52_suffix_008 ridgeSupport52_007_decode ridgeSupport52_suffix_decode_008
theorem ridgeSupport52_suffix_decode_006 : PackedRawNatGrowth.readList 14 269 ridgeSupport52_rest_006 =
    (ridgeSupport52_suffix_006, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport52_rest_006 ridgeSupport52_rest_007 ridgeSupport52_rest_015
    ridgeSupport52_006 ridgeSupport52_suffix_007 ridgeSupport52_006_decode ridgeSupport52_suffix_decode_007
theorem ridgeSupport52_suffix_decode_005 : PackedRawNatGrowth.readList 14 301 ridgeSupport52_rest_005 =
    (ridgeSupport52_suffix_005, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport52_rest_005 ridgeSupport52_rest_006 ridgeSupport52_rest_015
    ridgeSupport52_005 ridgeSupport52_suffix_006 ridgeSupport52_005_decode ridgeSupport52_suffix_decode_006
theorem ridgeSupport52_suffix_decode_004 : PackedRawNatGrowth.readList 14 333 ridgeSupport52_rest_004 =
    (ridgeSupport52_suffix_004, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport52_rest_004 ridgeSupport52_rest_005 ridgeSupport52_rest_015
    ridgeSupport52_004 ridgeSupport52_suffix_005 ridgeSupport52_004_decode ridgeSupport52_suffix_decode_005
theorem ridgeSupport52_suffix_decode_003 : PackedRawNatGrowth.readList 14 365 ridgeSupport52_rest_003 =
    (ridgeSupport52_suffix_003, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport52_rest_003 ridgeSupport52_rest_004 ridgeSupport52_rest_015
    ridgeSupport52_003 ridgeSupport52_suffix_004 ridgeSupport52_003_decode ridgeSupport52_suffix_decode_004
theorem ridgeSupport52_suffix_decode_002 : PackedRawNatGrowth.readList 14 397 ridgeSupport52_rest_002 =
    (ridgeSupport52_suffix_002, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport52_rest_002 ridgeSupport52_rest_003 ridgeSupport52_rest_015
    ridgeSupport52_002 ridgeSupport52_suffix_003 ridgeSupport52_002_decode ridgeSupport52_suffix_decode_003
theorem ridgeSupport52_suffix_decode_001 : PackedRawNatGrowth.readList 14 429 ridgeSupport52_rest_001 =
    (ridgeSupport52_suffix_001, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport52_rest_001 ridgeSupport52_rest_002 ridgeSupport52_rest_015
    ridgeSupport52_001 ridgeSupport52_suffix_002 ridgeSupport52_001_decode ridgeSupport52_suffix_decode_002
theorem ridgeSupport52_suffix_decode_000 : PackedRawNatGrowth.readList 14 461 ridgeSupport52_rest_000 =
    (ridgeSupport52_suffix_000, ridgeSupport52_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport52_rest_000 ridgeSupport52_rest_001 ridgeSupport52_rest_015
    ridgeSupport52_000 ridgeSupport52_suffix_001 ridgeSupport52_000_decode ridgeSupport52_suffix_decode_001
theorem ridgeSupport52_eq : candidateRows 52 = ridgeSupport52_suffix_000 := by
  change candidateSupports 52 = ridgeSupport52_suffix_000
  rw [ridgeSupport52_source]
  exact congrArg Prod.fst ridgeSupport52_suffix_decode_000
theorem ridgeTest_large_52 : ridgeTest 52 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport52_eq]
    simp only [ridgeSupport52_suffix_000, ridgeSupport52_suffix_001, ridgeSupport52_suffix_002, ridgeSupport52_suffix_003, ridgeSupport52_suffix_004, ridgeSupport52_suffix_005, ridgeSupport52_suffix_006, ridgeSupport52_suffix_007, ridgeSupport52_suffix_008, ridgeSupport52_suffix_009, ridgeSupport52_suffix_010, ridgeSupport52_suffix_011, ridgeSupport52_suffix_012, ridgeSupport52_suffix_013, ridgeSupport52_suffix_014, ridgeSupport52_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport52_000_mask, ridgeSupport52_001_mask, ridgeSupport52_002_mask, ridgeSupport52_003_mask, ridgeSupport52_004_mask, ridgeSupport52_005_mask, ridgeSupport52_006_mask, ridgeSupport52_007_mask, ridgeSupport52_008_mask, ridgeSupport52_009_mask, ridgeSupport52_010_mask, ridgeSupport52_011_mask, ridgeSupport52_012_mask, ridgeSupport52_013_mask, ridgeSupport52_014_mask]
    decide +kernel
  · rw [ridgeSupport52_eq]
    simp only [ridgeSupport52_suffix_000, ridgeSupport52_suffix_001, ridgeSupport52_suffix_002, ridgeSupport52_suffix_003, ridgeSupport52_suffix_004, ridgeSupport52_suffix_005, ridgeSupport52_suffix_006, ridgeSupport52_suffix_007, ridgeSupport52_suffix_008, ridgeSupport52_suffix_009, ridgeSupport52_suffix_010, ridgeSupport52_suffix_011, ridgeSupport52_suffix_012, ridgeSupport52_suffix_013, ridgeSupport52_suffix_014, ridgeSupport52_suffix_015, List.all_append, List.all_nil, ridgeSupport52_000_checked, ridgeSupport52_001_checked, ridgeSupport52_002_checked, ridgeSupport52_003_checked, ridgeSupport52_004_checked, ridgeSupport52_005_checked, ridgeSupport52_006_checked, ridgeSupport52_007_checked, ridgeSupport52_008_checked, ridgeSupport52_009_checked, ridgeSupport52_010_checked, ridgeSupport52_011_checked, ridgeSupport52_012_checked, ridgeSupport52_013_checked, ridgeSupport52_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
