module
prelude
public import RootedSixExtra00GrowthCacheRidgeSupport56Part000
public import RootedSixExtra00GrowthCacheRidgeSupport56Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport56_suffix_decode_015 : PackedRawNatGrowth.readList 14 0 ridgeSupport56_rest_015 =
    (ridgeSupport56_suffix_015, ridgeSupport56_rest_015) := by rfl
theorem ridgeSupport56_suffix_decode_014 : PackedRawNatGrowth.readList 14 13 ridgeSupport56_rest_014 =
    (ridgeSupport56_suffix_014, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 13 0
    ridgeSupport56_rest_014 ridgeSupport56_rest_015 ridgeSupport56_rest_015
    ridgeSupport56_014 ridgeSupport56_suffix_015 ridgeSupport56_014_decode ridgeSupport56_suffix_decode_015
theorem ridgeSupport56_suffix_decode_013 : PackedRawNatGrowth.readList 14 45 ridgeSupport56_rest_013 =
    (ridgeSupport56_suffix_013, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 13
    ridgeSupport56_rest_013 ridgeSupport56_rest_014 ridgeSupport56_rest_015
    ridgeSupport56_013 ridgeSupport56_suffix_014 ridgeSupport56_013_decode ridgeSupport56_suffix_decode_014
theorem ridgeSupport56_suffix_decode_012 : PackedRawNatGrowth.readList 14 77 ridgeSupport56_rest_012 =
    (ridgeSupport56_suffix_012, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 45
    ridgeSupport56_rest_012 ridgeSupport56_rest_013 ridgeSupport56_rest_015
    ridgeSupport56_012 ridgeSupport56_suffix_013 ridgeSupport56_012_decode ridgeSupport56_suffix_decode_013
theorem ridgeSupport56_suffix_decode_011 : PackedRawNatGrowth.readList 14 109 ridgeSupport56_rest_011 =
    (ridgeSupport56_suffix_011, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 77
    ridgeSupport56_rest_011 ridgeSupport56_rest_012 ridgeSupport56_rest_015
    ridgeSupport56_011 ridgeSupport56_suffix_012 ridgeSupport56_011_decode ridgeSupport56_suffix_decode_012
theorem ridgeSupport56_suffix_decode_010 : PackedRawNatGrowth.readList 14 141 ridgeSupport56_rest_010 =
    (ridgeSupport56_suffix_010, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 109
    ridgeSupport56_rest_010 ridgeSupport56_rest_011 ridgeSupport56_rest_015
    ridgeSupport56_010 ridgeSupport56_suffix_011 ridgeSupport56_010_decode ridgeSupport56_suffix_decode_011
theorem ridgeSupport56_suffix_decode_009 : PackedRawNatGrowth.readList 14 173 ridgeSupport56_rest_009 =
    (ridgeSupport56_suffix_009, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 141
    ridgeSupport56_rest_009 ridgeSupport56_rest_010 ridgeSupport56_rest_015
    ridgeSupport56_009 ridgeSupport56_suffix_010 ridgeSupport56_009_decode ridgeSupport56_suffix_decode_010
theorem ridgeSupport56_suffix_decode_008 : PackedRawNatGrowth.readList 14 205 ridgeSupport56_rest_008 =
    (ridgeSupport56_suffix_008, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 173
    ridgeSupport56_rest_008 ridgeSupport56_rest_009 ridgeSupport56_rest_015
    ridgeSupport56_008 ridgeSupport56_suffix_009 ridgeSupport56_008_decode ridgeSupport56_suffix_decode_009
theorem ridgeSupport56_suffix_decode_007 : PackedRawNatGrowth.readList 14 237 ridgeSupport56_rest_007 =
    (ridgeSupport56_suffix_007, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 205
    ridgeSupport56_rest_007 ridgeSupport56_rest_008 ridgeSupport56_rest_015
    ridgeSupport56_007 ridgeSupport56_suffix_008 ridgeSupport56_007_decode ridgeSupport56_suffix_decode_008
theorem ridgeSupport56_suffix_decode_006 : PackedRawNatGrowth.readList 14 269 ridgeSupport56_rest_006 =
    (ridgeSupport56_suffix_006, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 237
    ridgeSupport56_rest_006 ridgeSupport56_rest_007 ridgeSupport56_rest_015
    ridgeSupport56_006 ridgeSupport56_suffix_007 ridgeSupport56_006_decode ridgeSupport56_suffix_decode_007
theorem ridgeSupport56_suffix_decode_005 : PackedRawNatGrowth.readList 14 301 ridgeSupport56_rest_005 =
    (ridgeSupport56_suffix_005, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 269
    ridgeSupport56_rest_005 ridgeSupport56_rest_006 ridgeSupport56_rest_015
    ridgeSupport56_005 ridgeSupport56_suffix_006 ridgeSupport56_005_decode ridgeSupport56_suffix_decode_006
theorem ridgeSupport56_suffix_decode_004 : PackedRawNatGrowth.readList 14 333 ridgeSupport56_rest_004 =
    (ridgeSupport56_suffix_004, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 301
    ridgeSupport56_rest_004 ridgeSupport56_rest_005 ridgeSupport56_rest_015
    ridgeSupport56_004 ridgeSupport56_suffix_005 ridgeSupport56_004_decode ridgeSupport56_suffix_decode_005
theorem ridgeSupport56_suffix_decode_003 : PackedRawNatGrowth.readList 14 365 ridgeSupport56_rest_003 =
    (ridgeSupport56_suffix_003, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 333
    ridgeSupport56_rest_003 ridgeSupport56_rest_004 ridgeSupport56_rest_015
    ridgeSupport56_003 ridgeSupport56_suffix_004 ridgeSupport56_003_decode ridgeSupport56_suffix_decode_004
theorem ridgeSupport56_suffix_decode_002 : PackedRawNatGrowth.readList 14 397 ridgeSupport56_rest_002 =
    (ridgeSupport56_suffix_002, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 365
    ridgeSupport56_rest_002 ridgeSupport56_rest_003 ridgeSupport56_rest_015
    ridgeSupport56_002 ridgeSupport56_suffix_003 ridgeSupport56_002_decode ridgeSupport56_suffix_decode_003
theorem ridgeSupport56_suffix_decode_001 : PackedRawNatGrowth.readList 14 429 ridgeSupport56_rest_001 =
    (ridgeSupport56_suffix_001, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 397
    ridgeSupport56_rest_001 ridgeSupport56_rest_002 ridgeSupport56_rest_015
    ridgeSupport56_001 ridgeSupport56_suffix_002 ridgeSupport56_001_decode ridgeSupport56_suffix_decode_002
theorem ridgeSupport56_suffix_decode_000 : PackedRawNatGrowth.readList 14 461 ridgeSupport56_rest_000 =
    (ridgeSupport56_suffix_000, ridgeSupport56_rest_015) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 429
    ridgeSupport56_rest_000 ridgeSupport56_rest_001 ridgeSupport56_rest_015
    ridgeSupport56_000 ridgeSupport56_suffix_001 ridgeSupport56_000_decode ridgeSupport56_suffix_decode_001
theorem ridgeSupport56_eq : candidateRows 56 = ridgeSupport56_suffix_000 := by
  change candidateSupports 56 = ridgeSupport56_suffix_000
  rw [ridgeSupport56_source]
  exact congrArg Prod.fst ridgeSupport56_suffix_decode_000
theorem ridgeTest_large_56 : ridgeTest 56 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport56_eq]
    simp only [ridgeSupport56_suffix_000, ridgeSupport56_suffix_001, ridgeSupport56_suffix_002, ridgeSupport56_suffix_003, ridgeSupport56_suffix_004, ridgeSupport56_suffix_005, ridgeSupport56_suffix_006, ridgeSupport56_suffix_007, ridgeSupport56_suffix_008, ridgeSupport56_suffix_009, ridgeSupport56_suffix_010, ridgeSupport56_suffix_011, ridgeSupport56_suffix_012, ridgeSupport56_suffix_013, ridgeSupport56_suffix_014, ridgeSupport56_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport56_000_mask, ridgeSupport56_001_mask, ridgeSupport56_002_mask, ridgeSupport56_003_mask, ridgeSupport56_004_mask, ridgeSupport56_005_mask, ridgeSupport56_006_mask, ridgeSupport56_007_mask, ridgeSupport56_008_mask, ridgeSupport56_009_mask, ridgeSupport56_010_mask, ridgeSupport56_011_mask, ridgeSupport56_012_mask, ridgeSupport56_013_mask, ridgeSupport56_014_mask]
    decide +kernel
  · rw [ridgeSupport56_eq]
    simp only [ridgeSupport56_suffix_000, ridgeSupport56_suffix_001, ridgeSupport56_suffix_002, ridgeSupport56_suffix_003, ridgeSupport56_suffix_004, ridgeSupport56_suffix_005, ridgeSupport56_suffix_006, ridgeSupport56_suffix_007, ridgeSupport56_suffix_008, ridgeSupport56_suffix_009, ridgeSupport56_suffix_010, ridgeSupport56_suffix_011, ridgeSupport56_suffix_012, ridgeSupport56_suffix_013, ridgeSupport56_suffix_014, ridgeSupport56_suffix_015, List.all_append, List.all_nil, ridgeSupport56_000_checked, ridgeSupport56_001_checked, ridgeSupport56_002_checked, ridgeSupport56_003_checked, ridgeSupport56_004_checked, ridgeSupport56_005_checked, ridgeSupport56_006_checked, ridgeSupport56_007_checked, ridgeSupport56_008_checked, ridgeSupport56_009_checked, ridgeSupport56_010_checked, ridgeSupport56_011_checked, ridgeSupport56_012_checked, ridgeSupport56_013_checked, ridgeSupport56_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
