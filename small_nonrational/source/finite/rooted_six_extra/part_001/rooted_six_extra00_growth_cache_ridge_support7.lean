module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport7Part000
public import RootedSixExtra00GrowthCacheRidgeSupport7Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport7_suffix_decode_015 : PackedRawNatGrowth.readList 14 0 ridgeSupport7_rest_015 =
    (ridgeSupport7_suffix_015, ridgeSupport7_rest_015) := by rfl
theorem ridgeSupport7_suffix_decode_014 : PackedRawNatGrowth.readList 14 13 ridgeSupport7_rest_014 =
    (ridgeSupport7_suffix_014, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport7_rest_014 ridgeSupport7_rest_015 ridgeSupport7_rest_015
    ridgeSupport7_014 ridgeSupport7_suffix_015 ridgeSupport7_014_decode ridgeSupport7_suffix_decode_015
theorem ridgeSupport7_suffix_decode_013 : PackedRawNatGrowth.readList 14 45 ridgeSupport7_rest_013 =
    (ridgeSupport7_suffix_013, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport7_rest_013 ridgeSupport7_rest_014 ridgeSupport7_rest_015
    ridgeSupport7_013 ridgeSupport7_suffix_014 ridgeSupport7_013_decode ridgeSupport7_suffix_decode_014
theorem ridgeSupport7_suffix_decode_012 : PackedRawNatGrowth.readList 14 77 ridgeSupport7_rest_012 =
    (ridgeSupport7_suffix_012, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport7_rest_012 ridgeSupport7_rest_013 ridgeSupport7_rest_015
    ridgeSupport7_012 ridgeSupport7_suffix_013 ridgeSupport7_012_decode ridgeSupport7_suffix_decode_013
theorem ridgeSupport7_suffix_decode_011 : PackedRawNatGrowth.readList 14 109 ridgeSupport7_rest_011 =
    (ridgeSupport7_suffix_011, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport7_rest_011 ridgeSupport7_rest_012 ridgeSupport7_rest_015
    ridgeSupport7_011 ridgeSupport7_suffix_012 ridgeSupport7_011_decode ridgeSupport7_suffix_decode_012
theorem ridgeSupport7_suffix_decode_010 : PackedRawNatGrowth.readList 14 141 ridgeSupport7_rest_010 =
    (ridgeSupport7_suffix_010, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport7_rest_010 ridgeSupport7_rest_011 ridgeSupport7_rest_015
    ridgeSupport7_010 ridgeSupport7_suffix_011 ridgeSupport7_010_decode ridgeSupport7_suffix_decode_011
theorem ridgeSupport7_suffix_decode_009 : PackedRawNatGrowth.readList 14 173 ridgeSupport7_rest_009 =
    (ridgeSupport7_suffix_009, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport7_rest_009 ridgeSupport7_rest_010 ridgeSupport7_rest_015
    ridgeSupport7_009 ridgeSupport7_suffix_010 ridgeSupport7_009_decode ridgeSupport7_suffix_decode_010
theorem ridgeSupport7_suffix_decode_008 : PackedRawNatGrowth.readList 14 205 ridgeSupport7_rest_008 =
    (ridgeSupport7_suffix_008, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport7_rest_008 ridgeSupport7_rest_009 ridgeSupport7_rest_015
    ridgeSupport7_008 ridgeSupport7_suffix_009 ridgeSupport7_008_decode ridgeSupport7_suffix_decode_009
theorem ridgeSupport7_suffix_decode_007 : PackedRawNatGrowth.readList 14 237 ridgeSupport7_rest_007 =
    (ridgeSupport7_suffix_007, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport7_rest_007 ridgeSupport7_rest_008 ridgeSupport7_rest_015
    ridgeSupport7_007 ridgeSupport7_suffix_008 ridgeSupport7_007_decode ridgeSupport7_suffix_decode_008
theorem ridgeSupport7_suffix_decode_006 : PackedRawNatGrowth.readList 14 269 ridgeSupport7_rest_006 =
    (ridgeSupport7_suffix_006, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport7_rest_006 ridgeSupport7_rest_007 ridgeSupport7_rest_015
    ridgeSupport7_006 ridgeSupport7_suffix_007 ridgeSupport7_006_decode ridgeSupport7_suffix_decode_007
theorem ridgeSupport7_suffix_decode_005 : PackedRawNatGrowth.readList 14 301 ridgeSupport7_rest_005 =
    (ridgeSupport7_suffix_005, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport7_rest_005 ridgeSupport7_rest_006 ridgeSupport7_rest_015
    ridgeSupport7_005 ridgeSupport7_suffix_006 ridgeSupport7_005_decode ridgeSupport7_suffix_decode_006
theorem ridgeSupport7_suffix_decode_004 : PackedRawNatGrowth.readList 14 333 ridgeSupport7_rest_004 =
    (ridgeSupport7_suffix_004, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport7_rest_004 ridgeSupport7_rest_005 ridgeSupport7_rest_015
    ridgeSupport7_004 ridgeSupport7_suffix_005 ridgeSupport7_004_decode ridgeSupport7_suffix_decode_005
theorem ridgeSupport7_suffix_decode_003 : PackedRawNatGrowth.readList 14 365 ridgeSupport7_rest_003 =
    (ridgeSupport7_suffix_003, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport7_rest_003 ridgeSupport7_rest_004 ridgeSupport7_rest_015
    ridgeSupport7_003 ridgeSupport7_suffix_004 ridgeSupport7_003_decode ridgeSupport7_suffix_decode_004
theorem ridgeSupport7_suffix_decode_002 : PackedRawNatGrowth.readList 14 397 ridgeSupport7_rest_002 =
    (ridgeSupport7_suffix_002, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport7_rest_002 ridgeSupport7_rest_003 ridgeSupport7_rest_015
    ridgeSupport7_002 ridgeSupport7_suffix_003 ridgeSupport7_002_decode ridgeSupport7_suffix_decode_003
theorem ridgeSupport7_suffix_decode_001 : PackedRawNatGrowth.readList 14 429 ridgeSupport7_rest_001 =
    (ridgeSupport7_suffix_001, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport7_rest_001 ridgeSupport7_rest_002 ridgeSupport7_rest_015
    ridgeSupport7_001 ridgeSupport7_suffix_002 ridgeSupport7_001_decode ridgeSupport7_suffix_decode_002
theorem ridgeSupport7_suffix_decode_000 : PackedRawNatGrowth.readList 14 461 ridgeSupport7_rest_000 =
    (ridgeSupport7_suffix_000, ridgeSupport7_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport7_rest_000 ridgeSupport7_rest_001 ridgeSupport7_rest_015
    ridgeSupport7_000 ridgeSupport7_suffix_001 ridgeSupport7_000_decode ridgeSupport7_suffix_decode_001
theorem ridgeSupport7_eq : candidateRows 7 = ridgeSupport7_suffix_000 := by
  change candidateSupports 7 = ridgeSupport7_suffix_000
  rw [ridgeSupport7_source]
  exact congrArg Prod.fst ridgeSupport7_suffix_decode_000
theorem ridgeTest_large_7 : ridgeTest 7 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport7_eq]
    simp only [ridgeSupport7_suffix_000, ridgeSupport7_suffix_001, ridgeSupport7_suffix_002, ridgeSupport7_suffix_003, ridgeSupport7_suffix_004, ridgeSupport7_suffix_005, ridgeSupport7_suffix_006, ridgeSupport7_suffix_007, ridgeSupport7_suffix_008, ridgeSupport7_suffix_009, ridgeSupport7_suffix_010, ridgeSupport7_suffix_011, ridgeSupport7_suffix_012, ridgeSupport7_suffix_013, ridgeSupport7_suffix_014, ridgeSupport7_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport7_000_mask, ridgeSupport7_001_mask, ridgeSupport7_002_mask, ridgeSupport7_003_mask, ridgeSupport7_004_mask, ridgeSupport7_005_mask, ridgeSupport7_006_mask, ridgeSupport7_007_mask, ridgeSupport7_008_mask, ridgeSupport7_009_mask, ridgeSupport7_010_mask, ridgeSupport7_011_mask, ridgeSupport7_012_mask, ridgeSupport7_013_mask, ridgeSupport7_014_mask]
    decide +kernel
  · rw [ridgeSupport7_eq]
    simp only [ridgeSupport7_suffix_000, ridgeSupport7_suffix_001, ridgeSupport7_suffix_002, ridgeSupport7_suffix_003, ridgeSupport7_suffix_004, ridgeSupport7_suffix_005, ridgeSupport7_suffix_006, ridgeSupport7_suffix_007, ridgeSupport7_suffix_008, ridgeSupport7_suffix_009, ridgeSupport7_suffix_010, ridgeSupport7_suffix_011, ridgeSupport7_suffix_012, ridgeSupport7_suffix_013, ridgeSupport7_suffix_014, ridgeSupport7_suffix_015, List.all_append, List.all_nil, ridgeSupport7_000_checked, ridgeSupport7_001_checked, ridgeSupport7_002_checked, ridgeSupport7_003_checked, ridgeSupport7_004_checked, ridgeSupport7_005_checked, ridgeSupport7_006_checked, ridgeSupport7_007_checked, ridgeSupport7_008_checked, ridgeSupport7_009_checked, ridgeSupport7_010_checked, ridgeSupport7_011_checked, ridgeSupport7_012_checked, ridgeSupport7_013_checked, ridgeSupport7_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
