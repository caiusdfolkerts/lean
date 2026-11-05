module
prelude
public import RootedSixExtra04GrowthCacheRidgeSupport448Part000
public import RootedSixExtra04GrowthCacheRidgeSupport448Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport448_suffix_decode_016 : PackedRawNatGrowth.readList 12 0 ridgeSupport448_rest_016 =
    (ridgeSupport448_suffix_016, ridgeSupport448_rest_016) := by rfl
theorem ridgeSupport448_suffix_decode_015 : PackedRawNatGrowth.readList 12 7 ridgeSupport448_rest_015 =
    (ridgeSupport448_suffix_015, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 7 0
    ridgeSupport448_rest_015 ridgeSupport448_rest_016 ridgeSupport448_rest_016
    ridgeSupport448_015 ridgeSupport448_suffix_016 ridgeSupport448_015_decode ridgeSupport448_suffix_decode_016
theorem ridgeSupport448_suffix_decode_014 : PackedRawNatGrowth.readList 12 39 ridgeSupport448_rest_014 =
    (ridgeSupport448_suffix_014, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 7
    ridgeSupport448_rest_014 ridgeSupport448_rest_015 ridgeSupport448_rest_016
    ridgeSupport448_014 ridgeSupport448_suffix_015 ridgeSupport448_014_decode ridgeSupport448_suffix_decode_015
theorem ridgeSupport448_suffix_decode_013 : PackedRawNatGrowth.readList 12 71 ridgeSupport448_rest_013 =
    (ridgeSupport448_suffix_013, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 39
    ridgeSupport448_rest_013 ridgeSupport448_rest_014 ridgeSupport448_rest_016
    ridgeSupport448_013 ridgeSupport448_suffix_014 ridgeSupport448_013_decode ridgeSupport448_suffix_decode_014
theorem ridgeSupport448_suffix_decode_012 : PackedRawNatGrowth.readList 12 103 ridgeSupport448_rest_012 =
    (ridgeSupport448_suffix_012, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 71
    ridgeSupport448_rest_012 ridgeSupport448_rest_013 ridgeSupport448_rest_016
    ridgeSupport448_012 ridgeSupport448_suffix_013 ridgeSupport448_012_decode ridgeSupport448_suffix_decode_013
theorem ridgeSupport448_suffix_decode_011 : PackedRawNatGrowth.readList 12 135 ridgeSupport448_rest_011 =
    (ridgeSupport448_suffix_011, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 103
    ridgeSupport448_rest_011 ridgeSupport448_rest_012 ridgeSupport448_rest_016
    ridgeSupport448_011 ridgeSupport448_suffix_012 ridgeSupport448_011_decode ridgeSupport448_suffix_decode_012
theorem ridgeSupport448_suffix_decode_010 : PackedRawNatGrowth.readList 12 167 ridgeSupport448_rest_010 =
    (ridgeSupport448_suffix_010, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 135
    ridgeSupport448_rest_010 ridgeSupport448_rest_011 ridgeSupport448_rest_016
    ridgeSupport448_010 ridgeSupport448_suffix_011 ridgeSupport448_010_decode ridgeSupport448_suffix_decode_011
theorem ridgeSupport448_suffix_decode_009 : PackedRawNatGrowth.readList 12 199 ridgeSupport448_rest_009 =
    (ridgeSupport448_suffix_009, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 167
    ridgeSupport448_rest_009 ridgeSupport448_rest_010 ridgeSupport448_rest_016
    ridgeSupport448_009 ridgeSupport448_suffix_010 ridgeSupport448_009_decode ridgeSupport448_suffix_decode_010
theorem ridgeSupport448_suffix_decode_008 : PackedRawNatGrowth.readList 12 231 ridgeSupport448_rest_008 =
    (ridgeSupport448_suffix_008, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 199
    ridgeSupport448_rest_008 ridgeSupport448_rest_009 ridgeSupport448_rest_016
    ridgeSupport448_008 ridgeSupport448_suffix_009 ridgeSupport448_008_decode ridgeSupport448_suffix_decode_009
theorem ridgeSupport448_suffix_decode_007 : PackedRawNatGrowth.readList 12 263 ridgeSupport448_rest_007 =
    (ridgeSupport448_suffix_007, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 231
    ridgeSupport448_rest_007 ridgeSupport448_rest_008 ridgeSupport448_rest_016
    ridgeSupport448_007 ridgeSupport448_suffix_008 ridgeSupport448_007_decode ridgeSupport448_suffix_decode_008
theorem ridgeSupport448_suffix_decode_006 : PackedRawNatGrowth.readList 12 295 ridgeSupport448_rest_006 =
    (ridgeSupport448_suffix_006, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 263
    ridgeSupport448_rest_006 ridgeSupport448_rest_007 ridgeSupport448_rest_016
    ridgeSupport448_006 ridgeSupport448_suffix_007 ridgeSupport448_006_decode ridgeSupport448_suffix_decode_007
theorem ridgeSupport448_suffix_decode_005 : PackedRawNatGrowth.readList 12 327 ridgeSupport448_rest_005 =
    (ridgeSupport448_suffix_005, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 295
    ridgeSupport448_rest_005 ridgeSupport448_rest_006 ridgeSupport448_rest_016
    ridgeSupport448_005 ridgeSupport448_suffix_006 ridgeSupport448_005_decode ridgeSupport448_suffix_decode_006
theorem ridgeSupport448_suffix_decode_004 : PackedRawNatGrowth.readList 12 359 ridgeSupport448_rest_004 =
    (ridgeSupport448_suffix_004, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 327
    ridgeSupport448_rest_004 ridgeSupport448_rest_005 ridgeSupport448_rest_016
    ridgeSupport448_004 ridgeSupport448_suffix_005 ridgeSupport448_004_decode ridgeSupport448_suffix_decode_005
theorem ridgeSupport448_suffix_decode_003 : PackedRawNatGrowth.readList 12 391 ridgeSupport448_rest_003 =
    (ridgeSupport448_suffix_003, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 359
    ridgeSupport448_rest_003 ridgeSupport448_rest_004 ridgeSupport448_rest_016
    ridgeSupport448_003 ridgeSupport448_suffix_004 ridgeSupport448_003_decode ridgeSupport448_suffix_decode_004
theorem ridgeSupport448_suffix_decode_002 : PackedRawNatGrowth.readList 12 423 ridgeSupport448_rest_002 =
    (ridgeSupport448_suffix_002, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 391
    ridgeSupport448_rest_002 ridgeSupport448_rest_003 ridgeSupport448_rest_016
    ridgeSupport448_002 ridgeSupport448_suffix_003 ridgeSupport448_002_decode ridgeSupport448_suffix_decode_003
theorem ridgeSupport448_suffix_decode_001 : PackedRawNatGrowth.readList 12 455 ridgeSupport448_rest_001 =
    (ridgeSupport448_suffix_001, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 423
    ridgeSupport448_rest_001 ridgeSupport448_rest_002 ridgeSupport448_rest_016
    ridgeSupport448_001 ridgeSupport448_suffix_002 ridgeSupport448_001_decode ridgeSupport448_suffix_decode_002
theorem ridgeSupport448_suffix_decode_000 : PackedRawNatGrowth.readList 12 487 ridgeSupport448_rest_000 =
    (ridgeSupport448_suffix_000, ridgeSupport448_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 455
    ridgeSupport448_rest_000 ridgeSupport448_rest_001 ridgeSupport448_rest_016
    ridgeSupport448_000 ridgeSupport448_suffix_001 ridgeSupport448_000_decode ridgeSupport448_suffix_decode_001
theorem ridgeSupport448_eq : candidateRows 448 = ridgeSupport448_suffix_000 := by
  change candidateSupports 448 = ridgeSupport448_suffix_000
  rw [ridgeSupport448_source]
  exact congrArg Prod.fst ridgeSupport448_suffix_decode_000
theorem ridgeTest_large_448 : ridgeTest 448 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, ridgeSupport448_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport448_000_mask, ridgeSupport448_001_mask, ridgeSupport448_002_mask, ridgeSupport448_003_mask, ridgeSupport448_004_mask, ridgeSupport448_005_mask, ridgeSupport448_006_mask, ridgeSupport448_007_mask, ridgeSupport448_008_mask, ridgeSupport448_009_mask, ridgeSupport448_010_mask, ridgeSupport448_011_mask, ridgeSupport448_012_mask, ridgeSupport448_013_mask, ridgeSupport448_014_mask, ridgeSupport448_015_mask]
    decide +kernel
  · rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, ridgeSupport448_suffix_016, List.all_append, List.all_nil, ridgeSupport448_000_checked, ridgeSupport448_001_checked, ridgeSupport448_002_checked, ridgeSupport448_003_checked, ridgeSupport448_004_checked, ridgeSupport448_005_checked, ridgeSupport448_006_checked, ridgeSupport448_007_checked, ridgeSupport448_008_checked, ridgeSupport448_009_checked, ridgeSupport448_010_checked, ridgeSupport448_011_checked, ridgeSupport448_012_checked, ridgeSupport448_013_checked, ridgeSupport448_014_checked, ridgeSupport448_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra04
