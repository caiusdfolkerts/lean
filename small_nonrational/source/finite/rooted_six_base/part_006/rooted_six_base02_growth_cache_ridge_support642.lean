module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport642Part000
public import RootedSixBase02GrowthCacheRidgeSupport642Part001
public import RootedSixBase02GrowthCacheRidgeSupport642Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport642_suffix_decode_017 : PackedRawNatGrowth.readList 13 0 ridgeSupport642_rest_017 =
    (ridgeSupport642_suffix_017, ridgeSupport642_rest_017) := by rfl
theorem ridgeSupport642_suffix_decode_016 : PackedRawNatGrowth.readList 13 30 ridgeSupport642_rest_016 =
    (ridgeSupport642_suffix_016, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 30 0
    ridgeSupport642_rest_016 ridgeSupport642_rest_017 ridgeSupport642_rest_017
    ridgeSupport642_016 ridgeSupport642_suffix_017 ridgeSupport642_016_decode ridgeSupport642_suffix_decode_017
theorem ridgeSupport642_suffix_decode_015 : PackedRawNatGrowth.readList 13 62 ridgeSupport642_rest_015 =
    (ridgeSupport642_suffix_015, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 30
    ridgeSupport642_rest_015 ridgeSupport642_rest_016 ridgeSupport642_rest_017
    ridgeSupport642_015 ridgeSupport642_suffix_016 ridgeSupport642_015_decode ridgeSupport642_suffix_decode_016
theorem ridgeSupport642_suffix_decode_014 : PackedRawNatGrowth.readList 13 94 ridgeSupport642_rest_014 =
    (ridgeSupport642_suffix_014, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 62
    ridgeSupport642_rest_014 ridgeSupport642_rest_015 ridgeSupport642_rest_017
    ridgeSupport642_014 ridgeSupport642_suffix_015 ridgeSupport642_014_decode ridgeSupport642_suffix_decode_015
theorem ridgeSupport642_suffix_decode_013 : PackedRawNatGrowth.readList 13 126 ridgeSupport642_rest_013 =
    (ridgeSupport642_suffix_013, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 94
    ridgeSupport642_rest_013 ridgeSupport642_rest_014 ridgeSupport642_rest_017
    ridgeSupport642_013 ridgeSupport642_suffix_014 ridgeSupport642_013_decode ridgeSupport642_suffix_decode_014
theorem ridgeSupport642_suffix_decode_012 : PackedRawNatGrowth.readList 13 158 ridgeSupport642_rest_012 =
    (ridgeSupport642_suffix_012, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 126
    ridgeSupport642_rest_012 ridgeSupport642_rest_013 ridgeSupport642_rest_017
    ridgeSupport642_012 ridgeSupport642_suffix_013 ridgeSupport642_012_decode ridgeSupport642_suffix_decode_013
theorem ridgeSupport642_suffix_decode_011 : PackedRawNatGrowth.readList 13 190 ridgeSupport642_rest_011 =
    (ridgeSupport642_suffix_011, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 158
    ridgeSupport642_rest_011 ridgeSupport642_rest_012 ridgeSupport642_rest_017
    ridgeSupport642_011 ridgeSupport642_suffix_012 ridgeSupport642_011_decode ridgeSupport642_suffix_decode_012
theorem ridgeSupport642_suffix_decode_010 : PackedRawNatGrowth.readList 13 222 ridgeSupport642_rest_010 =
    (ridgeSupport642_suffix_010, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 190
    ridgeSupport642_rest_010 ridgeSupport642_rest_011 ridgeSupport642_rest_017
    ridgeSupport642_010 ridgeSupport642_suffix_011 ridgeSupport642_010_decode ridgeSupport642_suffix_decode_011
theorem ridgeSupport642_suffix_decode_009 : PackedRawNatGrowth.readList 13 254 ridgeSupport642_rest_009 =
    (ridgeSupport642_suffix_009, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 222
    ridgeSupport642_rest_009 ridgeSupport642_rest_010 ridgeSupport642_rest_017
    ridgeSupport642_009 ridgeSupport642_suffix_010 ridgeSupport642_009_decode ridgeSupport642_suffix_decode_010
theorem ridgeSupport642_suffix_decode_008 : PackedRawNatGrowth.readList 13 286 ridgeSupport642_rest_008 =
    (ridgeSupport642_suffix_008, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 254
    ridgeSupport642_rest_008 ridgeSupport642_rest_009 ridgeSupport642_rest_017
    ridgeSupport642_008 ridgeSupport642_suffix_009 ridgeSupport642_008_decode ridgeSupport642_suffix_decode_009
theorem ridgeSupport642_suffix_decode_007 : PackedRawNatGrowth.readList 13 318 ridgeSupport642_rest_007 =
    (ridgeSupport642_suffix_007, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 286
    ridgeSupport642_rest_007 ridgeSupport642_rest_008 ridgeSupport642_rest_017
    ridgeSupport642_007 ridgeSupport642_suffix_008 ridgeSupport642_007_decode ridgeSupport642_suffix_decode_008
theorem ridgeSupport642_suffix_decode_006 : PackedRawNatGrowth.readList 13 350 ridgeSupport642_rest_006 =
    (ridgeSupport642_suffix_006, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 318
    ridgeSupport642_rest_006 ridgeSupport642_rest_007 ridgeSupport642_rest_017
    ridgeSupport642_006 ridgeSupport642_suffix_007 ridgeSupport642_006_decode ridgeSupport642_suffix_decode_007
theorem ridgeSupport642_suffix_decode_005 : PackedRawNatGrowth.readList 13 382 ridgeSupport642_rest_005 =
    (ridgeSupport642_suffix_005, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 350
    ridgeSupport642_rest_005 ridgeSupport642_rest_006 ridgeSupport642_rest_017
    ridgeSupport642_005 ridgeSupport642_suffix_006 ridgeSupport642_005_decode ridgeSupport642_suffix_decode_006
theorem ridgeSupport642_suffix_decode_004 : PackedRawNatGrowth.readList 13 414 ridgeSupport642_rest_004 =
    (ridgeSupport642_suffix_004, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 382
    ridgeSupport642_rest_004 ridgeSupport642_rest_005 ridgeSupport642_rest_017
    ridgeSupport642_004 ridgeSupport642_suffix_005 ridgeSupport642_004_decode ridgeSupport642_suffix_decode_005
theorem ridgeSupport642_suffix_decode_003 : PackedRawNatGrowth.readList 13 446 ridgeSupport642_rest_003 =
    (ridgeSupport642_suffix_003, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 414
    ridgeSupport642_rest_003 ridgeSupport642_rest_004 ridgeSupport642_rest_017
    ridgeSupport642_003 ridgeSupport642_suffix_004 ridgeSupport642_003_decode ridgeSupport642_suffix_decode_004
theorem ridgeSupport642_suffix_decode_002 : PackedRawNatGrowth.readList 13 478 ridgeSupport642_rest_002 =
    (ridgeSupport642_suffix_002, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 446
    ridgeSupport642_rest_002 ridgeSupport642_rest_003 ridgeSupport642_rest_017
    ridgeSupport642_002 ridgeSupport642_suffix_003 ridgeSupport642_002_decode ridgeSupport642_suffix_decode_003
theorem ridgeSupport642_suffix_decode_001 : PackedRawNatGrowth.readList 13 510 ridgeSupport642_rest_001 =
    (ridgeSupport642_suffix_001, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 478
    ridgeSupport642_rest_001 ridgeSupport642_rest_002 ridgeSupport642_rest_017
    ridgeSupport642_001 ridgeSupport642_suffix_002 ridgeSupport642_001_decode ridgeSupport642_suffix_decode_002
theorem ridgeSupport642_suffix_decode_000 : PackedRawNatGrowth.readList 13 542 ridgeSupport642_rest_000 =
    (ridgeSupport642_suffix_000, ridgeSupport642_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 510
    ridgeSupport642_rest_000 ridgeSupport642_rest_001 ridgeSupport642_rest_017
    ridgeSupport642_000 ridgeSupport642_suffix_001 ridgeSupport642_000_decode ridgeSupport642_suffix_decode_001
theorem ridgeSupport642_eq : candidateRows 642 = ridgeSupport642_suffix_000 := by
  change candidateSupports 642 = ridgeSupport642_suffix_000
  rw [ridgeSupport642_source]
  exact congrArg Prod.fst ridgeSupport642_suffix_decode_000
theorem ridgeTest_large_642 : ridgeTest 642 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport642_eq]
    simp only [ridgeSupport642_suffix_000, ridgeSupport642_suffix_001, ridgeSupport642_suffix_002, ridgeSupport642_suffix_003, ridgeSupport642_suffix_004, ridgeSupport642_suffix_005, ridgeSupport642_suffix_006, ridgeSupport642_suffix_007, ridgeSupport642_suffix_008, ridgeSupport642_suffix_009, ridgeSupport642_suffix_010, ridgeSupport642_suffix_011, ridgeSupport642_suffix_012, ridgeSupport642_suffix_013, ridgeSupport642_suffix_014, ridgeSupport642_suffix_015, ridgeSupport642_suffix_016, ridgeSupport642_suffix_017, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport642_000_mask, ridgeSupport642_001_mask, ridgeSupport642_002_mask, ridgeSupport642_003_mask, ridgeSupport642_004_mask, ridgeSupport642_005_mask, ridgeSupport642_006_mask, ridgeSupport642_007_mask, ridgeSupport642_008_mask, ridgeSupport642_009_mask, ridgeSupport642_010_mask, ridgeSupport642_011_mask, ridgeSupport642_012_mask, ridgeSupport642_013_mask, ridgeSupport642_014_mask, ridgeSupport642_015_mask, ridgeSupport642_016_mask]
    decide +kernel
  · rw [ridgeSupport642_eq]
    simp only [ridgeSupport642_suffix_000, ridgeSupport642_suffix_001, ridgeSupport642_suffix_002, ridgeSupport642_suffix_003, ridgeSupport642_suffix_004, ridgeSupport642_suffix_005, ridgeSupport642_suffix_006, ridgeSupport642_suffix_007, ridgeSupport642_suffix_008, ridgeSupport642_suffix_009, ridgeSupport642_suffix_010, ridgeSupport642_suffix_011, ridgeSupport642_suffix_012, ridgeSupport642_suffix_013, ridgeSupport642_suffix_014, ridgeSupport642_suffix_015, ridgeSupport642_suffix_016, ridgeSupport642_suffix_017, List.all_append, List.all_nil, ridgeSupport642_000_checked, ridgeSupport642_001_checked, ridgeSupport642_002_checked, ridgeSupport642_003_checked, ridgeSupport642_004_checked, ridgeSupport642_005_checked, ridgeSupport642_006_checked, ridgeSupport642_007_checked, ridgeSupport642_008_checked, ridgeSupport642_009_checked, ridgeSupport642_010_checked, ridgeSupport642_011_checked, ridgeSupport642_012_checked, ridgeSupport642_013_checked, ridgeSupport642_014_checked, ridgeSupport642_015_checked, ridgeSupport642_016_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
