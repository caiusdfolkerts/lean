module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport13Part000
public import RootedSixExtra00GrowthCacheRidgeSupport13Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport13_suffix_decode_015 : PackedRawNatGrowth.readList 14 0 ridgeSupport13_rest_015 =
    (ridgeSupport13_suffix_015, ridgeSupport13_rest_015) := by rfl
theorem ridgeSupport13_suffix_decode_014 : PackedRawNatGrowth.readList 14 13 ridgeSupport13_rest_014 =
    (ridgeSupport13_suffix_014, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport13_rest_014 ridgeSupport13_rest_015 ridgeSupport13_rest_015
    ridgeSupport13_014 ridgeSupport13_suffix_015 ridgeSupport13_014_decode ridgeSupport13_suffix_decode_015
theorem ridgeSupport13_suffix_decode_013 : PackedRawNatGrowth.readList 14 45 ridgeSupport13_rest_013 =
    (ridgeSupport13_suffix_013, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport13_rest_013 ridgeSupport13_rest_014 ridgeSupport13_rest_015
    ridgeSupport13_013 ridgeSupport13_suffix_014 ridgeSupport13_013_decode ridgeSupport13_suffix_decode_014
theorem ridgeSupport13_suffix_decode_012 : PackedRawNatGrowth.readList 14 77 ridgeSupport13_rest_012 =
    (ridgeSupport13_suffix_012, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport13_rest_012 ridgeSupport13_rest_013 ridgeSupport13_rest_015
    ridgeSupport13_012 ridgeSupport13_suffix_013 ridgeSupport13_012_decode ridgeSupport13_suffix_decode_013
theorem ridgeSupport13_suffix_decode_011 : PackedRawNatGrowth.readList 14 109 ridgeSupport13_rest_011 =
    (ridgeSupport13_suffix_011, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport13_rest_011 ridgeSupport13_rest_012 ridgeSupport13_rest_015
    ridgeSupport13_011 ridgeSupport13_suffix_012 ridgeSupport13_011_decode ridgeSupport13_suffix_decode_012
theorem ridgeSupport13_suffix_decode_010 : PackedRawNatGrowth.readList 14 141 ridgeSupport13_rest_010 =
    (ridgeSupport13_suffix_010, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport13_rest_010 ridgeSupport13_rest_011 ridgeSupport13_rest_015
    ridgeSupport13_010 ridgeSupport13_suffix_011 ridgeSupport13_010_decode ridgeSupport13_suffix_decode_011
theorem ridgeSupport13_suffix_decode_009 : PackedRawNatGrowth.readList 14 173 ridgeSupport13_rest_009 =
    (ridgeSupport13_suffix_009, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport13_rest_009 ridgeSupport13_rest_010 ridgeSupport13_rest_015
    ridgeSupport13_009 ridgeSupport13_suffix_010 ridgeSupport13_009_decode ridgeSupport13_suffix_decode_010
theorem ridgeSupport13_suffix_decode_008 : PackedRawNatGrowth.readList 14 205 ridgeSupport13_rest_008 =
    (ridgeSupport13_suffix_008, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport13_rest_008 ridgeSupport13_rest_009 ridgeSupport13_rest_015
    ridgeSupport13_008 ridgeSupport13_suffix_009 ridgeSupport13_008_decode ridgeSupport13_suffix_decode_009
theorem ridgeSupport13_suffix_decode_007 : PackedRawNatGrowth.readList 14 237 ridgeSupport13_rest_007 =
    (ridgeSupport13_suffix_007, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport13_rest_007 ridgeSupport13_rest_008 ridgeSupport13_rest_015
    ridgeSupport13_007 ridgeSupport13_suffix_008 ridgeSupport13_007_decode ridgeSupport13_suffix_decode_008
theorem ridgeSupport13_suffix_decode_006 : PackedRawNatGrowth.readList 14 269 ridgeSupport13_rest_006 =
    (ridgeSupport13_suffix_006, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport13_rest_006 ridgeSupport13_rest_007 ridgeSupport13_rest_015
    ridgeSupport13_006 ridgeSupport13_suffix_007 ridgeSupport13_006_decode ridgeSupport13_suffix_decode_007
theorem ridgeSupport13_suffix_decode_005 : PackedRawNatGrowth.readList 14 301 ridgeSupport13_rest_005 =
    (ridgeSupport13_suffix_005, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport13_rest_005 ridgeSupport13_rest_006 ridgeSupport13_rest_015
    ridgeSupport13_005 ridgeSupport13_suffix_006 ridgeSupport13_005_decode ridgeSupport13_suffix_decode_006
theorem ridgeSupport13_suffix_decode_004 : PackedRawNatGrowth.readList 14 333 ridgeSupport13_rest_004 =
    (ridgeSupport13_suffix_004, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport13_rest_004 ridgeSupport13_rest_005 ridgeSupport13_rest_015
    ridgeSupport13_004 ridgeSupport13_suffix_005 ridgeSupport13_004_decode ridgeSupport13_suffix_decode_005
theorem ridgeSupport13_suffix_decode_003 : PackedRawNatGrowth.readList 14 365 ridgeSupport13_rest_003 =
    (ridgeSupport13_suffix_003, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport13_rest_003 ridgeSupport13_rest_004 ridgeSupport13_rest_015
    ridgeSupport13_003 ridgeSupport13_suffix_004 ridgeSupport13_003_decode ridgeSupport13_suffix_decode_004
theorem ridgeSupport13_suffix_decode_002 : PackedRawNatGrowth.readList 14 397 ridgeSupport13_rest_002 =
    (ridgeSupport13_suffix_002, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport13_rest_002 ridgeSupport13_rest_003 ridgeSupport13_rest_015
    ridgeSupport13_002 ridgeSupport13_suffix_003 ridgeSupport13_002_decode ridgeSupport13_suffix_decode_003
theorem ridgeSupport13_suffix_decode_001 : PackedRawNatGrowth.readList 14 429 ridgeSupport13_rest_001 =
    (ridgeSupport13_suffix_001, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport13_rest_001 ridgeSupport13_rest_002 ridgeSupport13_rest_015
    ridgeSupport13_001 ridgeSupport13_suffix_002 ridgeSupport13_001_decode ridgeSupport13_suffix_decode_002
theorem ridgeSupport13_suffix_decode_000 : PackedRawNatGrowth.readList 14 461 ridgeSupport13_rest_000 =
    (ridgeSupport13_suffix_000, ridgeSupport13_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport13_rest_000 ridgeSupport13_rest_001 ridgeSupport13_rest_015
    ridgeSupport13_000 ridgeSupport13_suffix_001 ridgeSupport13_000_decode ridgeSupport13_suffix_decode_001
theorem ridgeSupport13_eq : candidateRows 13 = ridgeSupport13_suffix_000 := by
  change candidateSupports 13 = ridgeSupport13_suffix_000
  rw [ridgeSupport13_source]
  exact congrArg Prod.fst ridgeSupport13_suffix_decode_000
theorem ridgeTest_large_13 : ridgeTest 13 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport13_eq]
    simp only [ridgeSupport13_suffix_000, ridgeSupport13_suffix_001, ridgeSupport13_suffix_002, ridgeSupport13_suffix_003, ridgeSupport13_suffix_004, ridgeSupport13_suffix_005, ridgeSupport13_suffix_006, ridgeSupport13_suffix_007, ridgeSupport13_suffix_008, ridgeSupport13_suffix_009, ridgeSupport13_suffix_010, ridgeSupport13_suffix_011, ridgeSupport13_suffix_012, ridgeSupport13_suffix_013, ridgeSupport13_suffix_014, ridgeSupport13_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport13_000_mask, ridgeSupport13_001_mask, ridgeSupport13_002_mask, ridgeSupport13_003_mask, ridgeSupport13_004_mask, ridgeSupport13_005_mask, ridgeSupport13_006_mask, ridgeSupport13_007_mask, ridgeSupport13_008_mask, ridgeSupport13_009_mask, ridgeSupport13_010_mask, ridgeSupport13_011_mask, ridgeSupport13_012_mask, ridgeSupport13_013_mask, ridgeSupport13_014_mask]
    decide +kernel
  · rw [ridgeSupport13_eq]
    simp only [ridgeSupport13_suffix_000, ridgeSupport13_suffix_001, ridgeSupport13_suffix_002, ridgeSupport13_suffix_003, ridgeSupport13_suffix_004, ridgeSupport13_suffix_005, ridgeSupport13_suffix_006, ridgeSupport13_suffix_007, ridgeSupport13_suffix_008, ridgeSupport13_suffix_009, ridgeSupport13_suffix_010, ridgeSupport13_suffix_011, ridgeSupport13_suffix_012, ridgeSupport13_suffix_013, ridgeSupport13_suffix_014, ridgeSupport13_suffix_015, List.all_append, List.all_nil, ridgeSupport13_000_checked, ridgeSupport13_001_checked, ridgeSupport13_002_checked, ridgeSupport13_003_checked, ridgeSupport13_004_checked, ridgeSupport13_005_checked, ridgeSupport13_006_checked, ridgeSupport13_007_checked, ridgeSupport13_008_checked, ridgeSupport13_009_checked, ridgeSupport13_010_checked, ridgeSupport13_011_checked, ridgeSupport13_012_checked, ridgeSupport13_013_checked, ridgeSupport13_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
