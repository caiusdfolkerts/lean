module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport26Part000
public import RootedSixExtra00GrowthCacheRidgeSupport26Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport26_suffix_decode_015 : PackedRawNatGrowth.readList 14 0 ridgeSupport26_rest_015 =
    (ridgeSupport26_suffix_015, ridgeSupport26_rest_015) := by rfl
theorem ridgeSupport26_suffix_decode_014 : PackedRawNatGrowth.readList 14 13 ridgeSupport26_rest_014 =
    (ridgeSupport26_suffix_014, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport26_rest_014 ridgeSupport26_rest_015 ridgeSupport26_rest_015
    ridgeSupport26_014 ridgeSupport26_suffix_015 ridgeSupport26_014_decode ridgeSupport26_suffix_decode_015
theorem ridgeSupport26_suffix_decode_013 : PackedRawNatGrowth.readList 14 45 ridgeSupport26_rest_013 =
    (ridgeSupport26_suffix_013, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport26_rest_013 ridgeSupport26_rest_014 ridgeSupport26_rest_015
    ridgeSupport26_013 ridgeSupport26_suffix_014 ridgeSupport26_013_decode ridgeSupport26_suffix_decode_014
theorem ridgeSupport26_suffix_decode_012 : PackedRawNatGrowth.readList 14 77 ridgeSupport26_rest_012 =
    (ridgeSupport26_suffix_012, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport26_rest_012 ridgeSupport26_rest_013 ridgeSupport26_rest_015
    ridgeSupport26_012 ridgeSupport26_suffix_013 ridgeSupport26_012_decode ridgeSupport26_suffix_decode_013
theorem ridgeSupport26_suffix_decode_011 : PackedRawNatGrowth.readList 14 109 ridgeSupport26_rest_011 =
    (ridgeSupport26_suffix_011, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport26_rest_011 ridgeSupport26_rest_012 ridgeSupport26_rest_015
    ridgeSupport26_011 ridgeSupport26_suffix_012 ridgeSupport26_011_decode ridgeSupport26_suffix_decode_012
theorem ridgeSupport26_suffix_decode_010 : PackedRawNatGrowth.readList 14 141 ridgeSupport26_rest_010 =
    (ridgeSupport26_suffix_010, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport26_rest_010 ridgeSupport26_rest_011 ridgeSupport26_rest_015
    ridgeSupport26_010 ridgeSupport26_suffix_011 ridgeSupport26_010_decode ridgeSupport26_suffix_decode_011
theorem ridgeSupport26_suffix_decode_009 : PackedRawNatGrowth.readList 14 173 ridgeSupport26_rest_009 =
    (ridgeSupport26_suffix_009, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport26_rest_009 ridgeSupport26_rest_010 ridgeSupport26_rest_015
    ridgeSupport26_009 ridgeSupport26_suffix_010 ridgeSupport26_009_decode ridgeSupport26_suffix_decode_010
theorem ridgeSupport26_suffix_decode_008 : PackedRawNatGrowth.readList 14 205 ridgeSupport26_rest_008 =
    (ridgeSupport26_suffix_008, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport26_rest_008 ridgeSupport26_rest_009 ridgeSupport26_rest_015
    ridgeSupport26_008 ridgeSupport26_suffix_009 ridgeSupport26_008_decode ridgeSupport26_suffix_decode_009
theorem ridgeSupport26_suffix_decode_007 : PackedRawNatGrowth.readList 14 237 ridgeSupport26_rest_007 =
    (ridgeSupport26_suffix_007, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport26_rest_007 ridgeSupport26_rest_008 ridgeSupport26_rest_015
    ridgeSupport26_007 ridgeSupport26_suffix_008 ridgeSupport26_007_decode ridgeSupport26_suffix_decode_008
theorem ridgeSupport26_suffix_decode_006 : PackedRawNatGrowth.readList 14 269 ridgeSupport26_rest_006 =
    (ridgeSupport26_suffix_006, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport26_rest_006 ridgeSupport26_rest_007 ridgeSupport26_rest_015
    ridgeSupport26_006 ridgeSupport26_suffix_007 ridgeSupport26_006_decode ridgeSupport26_suffix_decode_007
theorem ridgeSupport26_suffix_decode_005 : PackedRawNatGrowth.readList 14 301 ridgeSupport26_rest_005 =
    (ridgeSupport26_suffix_005, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport26_rest_005 ridgeSupport26_rest_006 ridgeSupport26_rest_015
    ridgeSupport26_005 ridgeSupport26_suffix_006 ridgeSupport26_005_decode ridgeSupport26_suffix_decode_006
theorem ridgeSupport26_suffix_decode_004 : PackedRawNatGrowth.readList 14 333 ridgeSupport26_rest_004 =
    (ridgeSupport26_suffix_004, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport26_rest_004 ridgeSupport26_rest_005 ridgeSupport26_rest_015
    ridgeSupport26_004 ridgeSupport26_suffix_005 ridgeSupport26_004_decode ridgeSupport26_suffix_decode_005
theorem ridgeSupport26_suffix_decode_003 : PackedRawNatGrowth.readList 14 365 ridgeSupport26_rest_003 =
    (ridgeSupport26_suffix_003, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport26_rest_003 ridgeSupport26_rest_004 ridgeSupport26_rest_015
    ridgeSupport26_003 ridgeSupport26_suffix_004 ridgeSupport26_003_decode ridgeSupport26_suffix_decode_004
theorem ridgeSupport26_suffix_decode_002 : PackedRawNatGrowth.readList 14 397 ridgeSupport26_rest_002 =
    (ridgeSupport26_suffix_002, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport26_rest_002 ridgeSupport26_rest_003 ridgeSupport26_rest_015
    ridgeSupport26_002 ridgeSupport26_suffix_003 ridgeSupport26_002_decode ridgeSupport26_suffix_decode_003
theorem ridgeSupport26_suffix_decode_001 : PackedRawNatGrowth.readList 14 429 ridgeSupport26_rest_001 =
    (ridgeSupport26_suffix_001, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport26_rest_001 ridgeSupport26_rest_002 ridgeSupport26_rest_015
    ridgeSupport26_001 ridgeSupport26_suffix_002 ridgeSupport26_001_decode ridgeSupport26_suffix_decode_002
theorem ridgeSupport26_suffix_decode_000 : PackedRawNatGrowth.readList 14 461 ridgeSupport26_rest_000 =
    (ridgeSupport26_suffix_000, ridgeSupport26_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport26_rest_000 ridgeSupport26_rest_001 ridgeSupport26_rest_015
    ridgeSupport26_000 ridgeSupport26_suffix_001 ridgeSupport26_000_decode ridgeSupport26_suffix_decode_001
theorem ridgeSupport26_eq : candidateRows 26 = ridgeSupport26_suffix_000 := by
  change candidateSupports 26 = ridgeSupport26_suffix_000
  rw [ridgeSupport26_source]
  exact congrArg Prod.fst ridgeSupport26_suffix_decode_000
theorem ridgeTest_large_26 : ridgeTest 26 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport26_eq]
    simp only [ridgeSupport26_suffix_000, ridgeSupport26_suffix_001, ridgeSupport26_suffix_002, ridgeSupport26_suffix_003, ridgeSupport26_suffix_004, ridgeSupport26_suffix_005, ridgeSupport26_suffix_006, ridgeSupport26_suffix_007, ridgeSupport26_suffix_008, ridgeSupport26_suffix_009, ridgeSupport26_suffix_010, ridgeSupport26_suffix_011, ridgeSupport26_suffix_012, ridgeSupport26_suffix_013, ridgeSupport26_suffix_014, ridgeSupport26_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport26_000_mask, ridgeSupport26_001_mask, ridgeSupport26_002_mask, ridgeSupport26_003_mask, ridgeSupport26_004_mask, ridgeSupport26_005_mask, ridgeSupport26_006_mask, ridgeSupport26_007_mask, ridgeSupport26_008_mask, ridgeSupport26_009_mask, ridgeSupport26_010_mask, ridgeSupport26_011_mask, ridgeSupport26_012_mask, ridgeSupport26_013_mask, ridgeSupport26_014_mask]
    decide +kernel
  · rw [ridgeSupport26_eq]
    simp only [ridgeSupport26_suffix_000, ridgeSupport26_suffix_001, ridgeSupport26_suffix_002, ridgeSupport26_suffix_003, ridgeSupport26_suffix_004, ridgeSupport26_suffix_005, ridgeSupport26_suffix_006, ridgeSupport26_suffix_007, ridgeSupport26_suffix_008, ridgeSupport26_suffix_009, ridgeSupport26_suffix_010, ridgeSupport26_suffix_011, ridgeSupport26_suffix_012, ridgeSupport26_suffix_013, ridgeSupport26_suffix_014, ridgeSupport26_suffix_015, List.all_append, List.all_nil, ridgeSupport26_000_checked, ridgeSupport26_001_checked, ridgeSupport26_002_checked, ridgeSupport26_003_checked, ridgeSupport26_004_checked, ridgeSupport26_005_checked, ridgeSupport26_006_checked, ridgeSupport26_007_checked, ridgeSupport26_008_checked, ridgeSupport26_009_checked, ridgeSupport26_010_checked, ridgeSupport26_011_checked, ridgeSupport26_012_checked, ridgeSupport26_013_checked, ridgeSupport26_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
