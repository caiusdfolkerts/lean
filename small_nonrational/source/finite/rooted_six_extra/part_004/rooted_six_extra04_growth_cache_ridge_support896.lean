module
prelude
public import RootedSixExtra04GrowthCacheRidgeSupport896Part000
public import RootedSixExtra04GrowthCacheRidgeSupport896Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport896_suffix_decode_016 : PackedRawNatGrowth.readList 12 0 ridgeSupport896_rest_016 =
    (ridgeSupport896_suffix_016, ridgeSupport896_rest_016) := by rfl
theorem ridgeSupport896_suffix_decode_015 : PackedRawNatGrowth.readList 12 7 ridgeSupport896_rest_015 =
    (ridgeSupport896_suffix_015, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 7 0
    ridgeSupport896_rest_015 ridgeSupport896_rest_016 ridgeSupport896_rest_016
    ridgeSupport896_015 ridgeSupport896_suffix_016 ridgeSupport896_015_decode ridgeSupport896_suffix_decode_016
theorem ridgeSupport896_suffix_decode_014 : PackedRawNatGrowth.readList 12 39 ridgeSupport896_rest_014 =
    (ridgeSupport896_suffix_014, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 7
    ridgeSupport896_rest_014 ridgeSupport896_rest_015 ridgeSupport896_rest_016
    ridgeSupport896_014 ridgeSupport896_suffix_015 ridgeSupport896_014_decode ridgeSupport896_suffix_decode_015
theorem ridgeSupport896_suffix_decode_013 : PackedRawNatGrowth.readList 12 71 ridgeSupport896_rest_013 =
    (ridgeSupport896_suffix_013, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 39
    ridgeSupport896_rest_013 ridgeSupport896_rest_014 ridgeSupport896_rest_016
    ridgeSupport896_013 ridgeSupport896_suffix_014 ridgeSupport896_013_decode ridgeSupport896_suffix_decode_014
theorem ridgeSupport896_suffix_decode_012 : PackedRawNatGrowth.readList 12 103 ridgeSupport896_rest_012 =
    (ridgeSupport896_suffix_012, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 71
    ridgeSupport896_rest_012 ridgeSupport896_rest_013 ridgeSupport896_rest_016
    ridgeSupport896_012 ridgeSupport896_suffix_013 ridgeSupport896_012_decode ridgeSupport896_suffix_decode_013
theorem ridgeSupport896_suffix_decode_011 : PackedRawNatGrowth.readList 12 135 ridgeSupport896_rest_011 =
    (ridgeSupport896_suffix_011, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 103
    ridgeSupport896_rest_011 ridgeSupport896_rest_012 ridgeSupport896_rest_016
    ridgeSupport896_011 ridgeSupport896_suffix_012 ridgeSupport896_011_decode ridgeSupport896_suffix_decode_012
theorem ridgeSupport896_suffix_decode_010 : PackedRawNatGrowth.readList 12 167 ridgeSupport896_rest_010 =
    (ridgeSupport896_suffix_010, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 135
    ridgeSupport896_rest_010 ridgeSupport896_rest_011 ridgeSupport896_rest_016
    ridgeSupport896_010 ridgeSupport896_suffix_011 ridgeSupport896_010_decode ridgeSupport896_suffix_decode_011
theorem ridgeSupport896_suffix_decode_009 : PackedRawNatGrowth.readList 12 199 ridgeSupport896_rest_009 =
    (ridgeSupport896_suffix_009, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 167
    ridgeSupport896_rest_009 ridgeSupport896_rest_010 ridgeSupport896_rest_016
    ridgeSupport896_009 ridgeSupport896_suffix_010 ridgeSupport896_009_decode ridgeSupport896_suffix_decode_010
theorem ridgeSupport896_suffix_decode_008 : PackedRawNatGrowth.readList 12 231 ridgeSupport896_rest_008 =
    (ridgeSupport896_suffix_008, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 199
    ridgeSupport896_rest_008 ridgeSupport896_rest_009 ridgeSupport896_rest_016
    ridgeSupport896_008 ridgeSupport896_suffix_009 ridgeSupport896_008_decode ridgeSupport896_suffix_decode_009
theorem ridgeSupport896_suffix_decode_007 : PackedRawNatGrowth.readList 12 263 ridgeSupport896_rest_007 =
    (ridgeSupport896_suffix_007, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 231
    ridgeSupport896_rest_007 ridgeSupport896_rest_008 ridgeSupport896_rest_016
    ridgeSupport896_007 ridgeSupport896_suffix_008 ridgeSupport896_007_decode ridgeSupport896_suffix_decode_008
theorem ridgeSupport896_suffix_decode_006 : PackedRawNatGrowth.readList 12 295 ridgeSupport896_rest_006 =
    (ridgeSupport896_suffix_006, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 263
    ridgeSupport896_rest_006 ridgeSupport896_rest_007 ridgeSupport896_rest_016
    ridgeSupport896_006 ridgeSupport896_suffix_007 ridgeSupport896_006_decode ridgeSupport896_suffix_decode_007
theorem ridgeSupport896_suffix_decode_005 : PackedRawNatGrowth.readList 12 327 ridgeSupport896_rest_005 =
    (ridgeSupport896_suffix_005, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 295
    ridgeSupport896_rest_005 ridgeSupport896_rest_006 ridgeSupport896_rest_016
    ridgeSupport896_005 ridgeSupport896_suffix_006 ridgeSupport896_005_decode ridgeSupport896_suffix_decode_006
theorem ridgeSupport896_suffix_decode_004 : PackedRawNatGrowth.readList 12 359 ridgeSupport896_rest_004 =
    (ridgeSupport896_suffix_004, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 327
    ridgeSupport896_rest_004 ridgeSupport896_rest_005 ridgeSupport896_rest_016
    ridgeSupport896_004 ridgeSupport896_suffix_005 ridgeSupport896_004_decode ridgeSupport896_suffix_decode_005
theorem ridgeSupport896_suffix_decode_003 : PackedRawNatGrowth.readList 12 391 ridgeSupport896_rest_003 =
    (ridgeSupport896_suffix_003, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 359
    ridgeSupport896_rest_003 ridgeSupport896_rest_004 ridgeSupport896_rest_016
    ridgeSupport896_003 ridgeSupport896_suffix_004 ridgeSupport896_003_decode ridgeSupport896_suffix_decode_004
theorem ridgeSupport896_suffix_decode_002 : PackedRawNatGrowth.readList 12 423 ridgeSupport896_rest_002 =
    (ridgeSupport896_suffix_002, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 391
    ridgeSupport896_rest_002 ridgeSupport896_rest_003 ridgeSupport896_rest_016
    ridgeSupport896_002 ridgeSupport896_suffix_003 ridgeSupport896_002_decode ridgeSupport896_suffix_decode_003
theorem ridgeSupport896_suffix_decode_001 : PackedRawNatGrowth.readList 12 455 ridgeSupport896_rest_001 =
    (ridgeSupport896_suffix_001, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 423
    ridgeSupport896_rest_001 ridgeSupport896_rest_002 ridgeSupport896_rest_016
    ridgeSupport896_001 ridgeSupport896_suffix_002 ridgeSupport896_001_decode ridgeSupport896_suffix_decode_002
theorem ridgeSupport896_suffix_decode_000 : PackedRawNatGrowth.readList 12 487 ridgeSupport896_rest_000 =
    (ridgeSupport896_suffix_000, ridgeSupport896_rest_016) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 455
    ridgeSupport896_rest_000 ridgeSupport896_rest_001 ridgeSupport896_rest_016
    ridgeSupport896_000 ridgeSupport896_suffix_001 ridgeSupport896_000_decode ridgeSupport896_suffix_decode_001
theorem ridgeSupport896_eq : candidateRows 896 = ridgeSupport896_suffix_000 := by
  change candidateSupports 896 = ridgeSupport896_suffix_000
  rw [ridgeSupport896_source]
  exact congrArg Prod.fst ridgeSupport896_suffix_decode_000
theorem ridgeTest_large_896 : ridgeTest 896 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, ridgeSupport896_suffix_015, ridgeSupport896_suffix_016, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport896_000_mask, ridgeSupport896_001_mask, ridgeSupport896_002_mask, ridgeSupport896_003_mask, ridgeSupport896_004_mask, ridgeSupport896_005_mask, ridgeSupport896_006_mask, ridgeSupport896_007_mask, ridgeSupport896_008_mask, ridgeSupport896_009_mask, ridgeSupport896_010_mask, ridgeSupport896_011_mask, ridgeSupport896_012_mask, ridgeSupport896_013_mask, ridgeSupport896_014_mask, ridgeSupport896_015_mask]
    decide +kernel
  · rw [ridgeSupport896_eq]
    simp only [ridgeSupport896_suffix_000, ridgeSupport896_suffix_001, ridgeSupport896_suffix_002, ridgeSupport896_suffix_003, ridgeSupport896_suffix_004, ridgeSupport896_suffix_005, ridgeSupport896_suffix_006, ridgeSupport896_suffix_007, ridgeSupport896_suffix_008, ridgeSupport896_suffix_009, ridgeSupport896_suffix_010, ridgeSupport896_suffix_011, ridgeSupport896_suffix_012, ridgeSupport896_suffix_013, ridgeSupport896_suffix_014, ridgeSupport896_suffix_015, ridgeSupport896_suffix_016, List.all_append, List.all_nil, ridgeSupport896_000_checked, ridgeSupport896_001_checked, ridgeSupport896_002_checked, ridgeSupport896_003_checked, ridgeSupport896_004_checked, ridgeSupport896_005_checked, ridgeSupport896_006_checked, ridgeSupport896_007_checked, ridgeSupport896_008_checked, ridgeSupport896_009_checked, ridgeSupport896_010_checked, ridgeSupport896_011_checked, ridgeSupport896_012_checked, ridgeSupport896_013_checked, ridgeSupport896_014_checked, ridgeSupport896_015_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra04
