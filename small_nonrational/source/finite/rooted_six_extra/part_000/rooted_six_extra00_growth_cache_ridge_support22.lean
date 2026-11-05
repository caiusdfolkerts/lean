module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport22Part000
public import RootedSixExtra00GrowthCacheRidgeSupport22Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport22_suffix_decode_015 : PackedRawNatGrowth.readList 14 0 ridgeSupport22_rest_015 =
    (ridgeSupport22_suffix_015, ridgeSupport22_rest_015) := by rfl
theorem ridgeSupport22_suffix_decode_014 : PackedRawNatGrowth.readList 14 13 ridgeSupport22_rest_014 =
    (ridgeSupport22_suffix_014, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport22_rest_014 ridgeSupport22_rest_015 ridgeSupport22_rest_015
    ridgeSupport22_014 ridgeSupport22_suffix_015 ridgeSupport22_014_decode ridgeSupport22_suffix_decode_015
theorem ridgeSupport22_suffix_decode_013 : PackedRawNatGrowth.readList 14 45 ridgeSupport22_rest_013 =
    (ridgeSupport22_suffix_013, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport22_rest_013 ridgeSupport22_rest_014 ridgeSupport22_rest_015
    ridgeSupport22_013 ridgeSupport22_suffix_014 ridgeSupport22_013_decode ridgeSupport22_suffix_decode_014
theorem ridgeSupport22_suffix_decode_012 : PackedRawNatGrowth.readList 14 77 ridgeSupport22_rest_012 =
    (ridgeSupport22_suffix_012, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport22_rest_012 ridgeSupport22_rest_013 ridgeSupport22_rest_015
    ridgeSupport22_012 ridgeSupport22_suffix_013 ridgeSupport22_012_decode ridgeSupport22_suffix_decode_013
theorem ridgeSupport22_suffix_decode_011 : PackedRawNatGrowth.readList 14 109 ridgeSupport22_rest_011 =
    (ridgeSupport22_suffix_011, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport22_rest_011 ridgeSupport22_rest_012 ridgeSupport22_rest_015
    ridgeSupport22_011 ridgeSupport22_suffix_012 ridgeSupport22_011_decode ridgeSupport22_suffix_decode_012
theorem ridgeSupport22_suffix_decode_010 : PackedRawNatGrowth.readList 14 141 ridgeSupport22_rest_010 =
    (ridgeSupport22_suffix_010, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport22_rest_010 ridgeSupport22_rest_011 ridgeSupport22_rest_015
    ridgeSupport22_010 ridgeSupport22_suffix_011 ridgeSupport22_010_decode ridgeSupport22_suffix_decode_011
theorem ridgeSupport22_suffix_decode_009 : PackedRawNatGrowth.readList 14 173 ridgeSupport22_rest_009 =
    (ridgeSupport22_suffix_009, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport22_rest_009 ridgeSupport22_rest_010 ridgeSupport22_rest_015
    ridgeSupport22_009 ridgeSupport22_suffix_010 ridgeSupport22_009_decode ridgeSupport22_suffix_decode_010
theorem ridgeSupport22_suffix_decode_008 : PackedRawNatGrowth.readList 14 205 ridgeSupport22_rest_008 =
    (ridgeSupport22_suffix_008, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport22_rest_008 ridgeSupport22_rest_009 ridgeSupport22_rest_015
    ridgeSupport22_008 ridgeSupport22_suffix_009 ridgeSupport22_008_decode ridgeSupport22_suffix_decode_009
theorem ridgeSupport22_suffix_decode_007 : PackedRawNatGrowth.readList 14 237 ridgeSupport22_rest_007 =
    (ridgeSupport22_suffix_007, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport22_rest_007 ridgeSupport22_rest_008 ridgeSupport22_rest_015
    ridgeSupport22_007 ridgeSupport22_suffix_008 ridgeSupport22_007_decode ridgeSupport22_suffix_decode_008
theorem ridgeSupport22_suffix_decode_006 : PackedRawNatGrowth.readList 14 269 ridgeSupport22_rest_006 =
    (ridgeSupport22_suffix_006, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport22_rest_006 ridgeSupport22_rest_007 ridgeSupport22_rest_015
    ridgeSupport22_006 ridgeSupport22_suffix_007 ridgeSupport22_006_decode ridgeSupport22_suffix_decode_007
theorem ridgeSupport22_suffix_decode_005 : PackedRawNatGrowth.readList 14 301 ridgeSupport22_rest_005 =
    (ridgeSupport22_suffix_005, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport22_rest_005 ridgeSupport22_rest_006 ridgeSupport22_rest_015
    ridgeSupport22_005 ridgeSupport22_suffix_006 ridgeSupport22_005_decode ridgeSupport22_suffix_decode_006
theorem ridgeSupport22_suffix_decode_004 : PackedRawNatGrowth.readList 14 333 ridgeSupport22_rest_004 =
    (ridgeSupport22_suffix_004, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport22_rest_004 ridgeSupport22_rest_005 ridgeSupport22_rest_015
    ridgeSupport22_004 ridgeSupport22_suffix_005 ridgeSupport22_004_decode ridgeSupport22_suffix_decode_005
theorem ridgeSupport22_suffix_decode_003 : PackedRawNatGrowth.readList 14 365 ridgeSupport22_rest_003 =
    (ridgeSupport22_suffix_003, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport22_rest_003 ridgeSupport22_rest_004 ridgeSupport22_rest_015
    ridgeSupport22_003 ridgeSupport22_suffix_004 ridgeSupport22_003_decode ridgeSupport22_suffix_decode_004
theorem ridgeSupport22_suffix_decode_002 : PackedRawNatGrowth.readList 14 397 ridgeSupport22_rest_002 =
    (ridgeSupport22_suffix_002, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport22_rest_002 ridgeSupport22_rest_003 ridgeSupport22_rest_015
    ridgeSupport22_002 ridgeSupport22_suffix_003 ridgeSupport22_002_decode ridgeSupport22_suffix_decode_003
theorem ridgeSupport22_suffix_decode_001 : PackedRawNatGrowth.readList 14 429 ridgeSupport22_rest_001 =
    (ridgeSupport22_suffix_001, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport22_rest_001 ridgeSupport22_rest_002 ridgeSupport22_rest_015
    ridgeSupport22_001 ridgeSupport22_suffix_002 ridgeSupport22_001_decode ridgeSupport22_suffix_decode_002
theorem ridgeSupport22_suffix_decode_000 : PackedRawNatGrowth.readList 14 461 ridgeSupport22_rest_000 =
    (ridgeSupport22_suffix_000, ridgeSupport22_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport22_rest_000 ridgeSupport22_rest_001 ridgeSupport22_rest_015
    ridgeSupport22_000 ridgeSupport22_suffix_001 ridgeSupport22_000_decode ridgeSupport22_suffix_decode_001
theorem ridgeSupport22_eq : candidateRows 22 = ridgeSupport22_suffix_000 := by
  change candidateSupports 22 = ridgeSupport22_suffix_000
  rw [ridgeSupport22_source]
  exact congrArg Prod.fst ridgeSupport22_suffix_decode_000
theorem ridgeTest_large_22 : ridgeTest 22 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport22_eq]
    simp only [ridgeSupport22_suffix_000, ridgeSupport22_suffix_001, ridgeSupport22_suffix_002, ridgeSupport22_suffix_003, ridgeSupport22_suffix_004, ridgeSupport22_suffix_005, ridgeSupport22_suffix_006, ridgeSupport22_suffix_007, ridgeSupport22_suffix_008, ridgeSupport22_suffix_009, ridgeSupport22_suffix_010, ridgeSupport22_suffix_011, ridgeSupport22_suffix_012, ridgeSupport22_suffix_013, ridgeSupport22_suffix_014, ridgeSupport22_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport22_000_mask, ridgeSupport22_001_mask, ridgeSupport22_002_mask, ridgeSupport22_003_mask, ridgeSupport22_004_mask, ridgeSupport22_005_mask, ridgeSupport22_006_mask, ridgeSupport22_007_mask, ridgeSupport22_008_mask, ridgeSupport22_009_mask, ridgeSupport22_010_mask, ridgeSupport22_011_mask, ridgeSupport22_012_mask, ridgeSupport22_013_mask, ridgeSupport22_014_mask]
    decide +kernel
  · rw [ridgeSupport22_eq]
    simp only [ridgeSupport22_suffix_000, ridgeSupport22_suffix_001, ridgeSupport22_suffix_002, ridgeSupport22_suffix_003, ridgeSupport22_suffix_004, ridgeSupport22_suffix_005, ridgeSupport22_suffix_006, ridgeSupport22_suffix_007, ridgeSupport22_suffix_008, ridgeSupport22_suffix_009, ridgeSupport22_suffix_010, ridgeSupport22_suffix_011, ridgeSupport22_suffix_012, ridgeSupport22_suffix_013, ridgeSupport22_suffix_014, ridgeSupport22_suffix_015, List.all_append, List.all_nil, ridgeSupport22_000_checked, ridgeSupport22_001_checked, ridgeSupport22_002_checked, ridgeSupport22_003_checked, ridgeSupport22_004_checked, ridgeSupport22_005_checked, ridgeSupport22_006_checked, ridgeSupport22_007_checked, ridgeSupport22_008_checked, ridgeSupport22_009_checked, ridgeSupport22_010_checked, ridgeSupport22_011_checked, ridgeSupport22_012_checked, ridgeSupport22_013_checked, ridgeSupport22_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
