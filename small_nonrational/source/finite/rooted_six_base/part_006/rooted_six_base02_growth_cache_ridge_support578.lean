module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport578Part000
public import RootedSixBase02GrowthCacheRidgeSupport578Part001
public import RootedSixBase02GrowthCacheRidgeSupport578Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport578_suffix_decode_017 : PackedRawNatGrowth.readList 13 0 ridgeSupport578_rest_017 =
    (ridgeSupport578_suffix_017, ridgeSupport578_rest_017) := by rfl
theorem ridgeSupport578_suffix_decode_016 : PackedRawNatGrowth.readList 13 30 ridgeSupport578_rest_016 =
    (ridgeSupport578_suffix_016, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 30 0
    ridgeSupport578_rest_016 ridgeSupport578_rest_017 ridgeSupport578_rest_017
    ridgeSupport578_016 ridgeSupport578_suffix_017 ridgeSupport578_016_decode ridgeSupport578_suffix_decode_017
theorem ridgeSupport578_suffix_decode_015 : PackedRawNatGrowth.readList 13 62 ridgeSupport578_rest_015 =
    (ridgeSupport578_suffix_015, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 30
    ridgeSupport578_rest_015 ridgeSupport578_rest_016 ridgeSupport578_rest_017
    ridgeSupport578_015 ridgeSupport578_suffix_016 ridgeSupport578_015_decode ridgeSupport578_suffix_decode_016
theorem ridgeSupport578_suffix_decode_014 : PackedRawNatGrowth.readList 13 94 ridgeSupport578_rest_014 =
    (ridgeSupport578_suffix_014, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 62
    ridgeSupport578_rest_014 ridgeSupport578_rest_015 ridgeSupport578_rest_017
    ridgeSupport578_014 ridgeSupport578_suffix_015 ridgeSupport578_014_decode ridgeSupport578_suffix_decode_015
theorem ridgeSupport578_suffix_decode_013 : PackedRawNatGrowth.readList 13 126 ridgeSupport578_rest_013 =
    (ridgeSupport578_suffix_013, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 94
    ridgeSupport578_rest_013 ridgeSupport578_rest_014 ridgeSupport578_rest_017
    ridgeSupport578_013 ridgeSupport578_suffix_014 ridgeSupport578_013_decode ridgeSupport578_suffix_decode_014
theorem ridgeSupport578_suffix_decode_012 : PackedRawNatGrowth.readList 13 158 ridgeSupport578_rest_012 =
    (ridgeSupport578_suffix_012, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 126
    ridgeSupport578_rest_012 ridgeSupport578_rest_013 ridgeSupport578_rest_017
    ridgeSupport578_012 ridgeSupport578_suffix_013 ridgeSupport578_012_decode ridgeSupport578_suffix_decode_013
theorem ridgeSupport578_suffix_decode_011 : PackedRawNatGrowth.readList 13 190 ridgeSupport578_rest_011 =
    (ridgeSupport578_suffix_011, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 158
    ridgeSupport578_rest_011 ridgeSupport578_rest_012 ridgeSupport578_rest_017
    ridgeSupport578_011 ridgeSupport578_suffix_012 ridgeSupport578_011_decode ridgeSupport578_suffix_decode_012
theorem ridgeSupport578_suffix_decode_010 : PackedRawNatGrowth.readList 13 222 ridgeSupport578_rest_010 =
    (ridgeSupport578_suffix_010, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 190
    ridgeSupport578_rest_010 ridgeSupport578_rest_011 ridgeSupport578_rest_017
    ridgeSupport578_010 ridgeSupport578_suffix_011 ridgeSupport578_010_decode ridgeSupport578_suffix_decode_011
theorem ridgeSupport578_suffix_decode_009 : PackedRawNatGrowth.readList 13 254 ridgeSupport578_rest_009 =
    (ridgeSupport578_suffix_009, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 222
    ridgeSupport578_rest_009 ridgeSupport578_rest_010 ridgeSupport578_rest_017
    ridgeSupport578_009 ridgeSupport578_suffix_010 ridgeSupport578_009_decode ridgeSupport578_suffix_decode_010
theorem ridgeSupport578_suffix_decode_008 : PackedRawNatGrowth.readList 13 286 ridgeSupport578_rest_008 =
    (ridgeSupport578_suffix_008, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 254
    ridgeSupport578_rest_008 ridgeSupport578_rest_009 ridgeSupport578_rest_017
    ridgeSupport578_008 ridgeSupport578_suffix_009 ridgeSupport578_008_decode ridgeSupport578_suffix_decode_009
theorem ridgeSupport578_suffix_decode_007 : PackedRawNatGrowth.readList 13 318 ridgeSupport578_rest_007 =
    (ridgeSupport578_suffix_007, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 286
    ridgeSupport578_rest_007 ridgeSupport578_rest_008 ridgeSupport578_rest_017
    ridgeSupport578_007 ridgeSupport578_suffix_008 ridgeSupport578_007_decode ridgeSupport578_suffix_decode_008
theorem ridgeSupport578_suffix_decode_006 : PackedRawNatGrowth.readList 13 350 ridgeSupport578_rest_006 =
    (ridgeSupport578_suffix_006, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 318
    ridgeSupport578_rest_006 ridgeSupport578_rest_007 ridgeSupport578_rest_017
    ridgeSupport578_006 ridgeSupport578_suffix_007 ridgeSupport578_006_decode ridgeSupport578_suffix_decode_007
theorem ridgeSupport578_suffix_decode_005 : PackedRawNatGrowth.readList 13 382 ridgeSupport578_rest_005 =
    (ridgeSupport578_suffix_005, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 350
    ridgeSupport578_rest_005 ridgeSupport578_rest_006 ridgeSupport578_rest_017
    ridgeSupport578_005 ridgeSupport578_suffix_006 ridgeSupport578_005_decode ridgeSupport578_suffix_decode_006
theorem ridgeSupport578_suffix_decode_004 : PackedRawNatGrowth.readList 13 414 ridgeSupport578_rest_004 =
    (ridgeSupport578_suffix_004, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 382
    ridgeSupport578_rest_004 ridgeSupport578_rest_005 ridgeSupport578_rest_017
    ridgeSupport578_004 ridgeSupport578_suffix_005 ridgeSupport578_004_decode ridgeSupport578_suffix_decode_005
theorem ridgeSupport578_suffix_decode_003 : PackedRawNatGrowth.readList 13 446 ridgeSupport578_rest_003 =
    (ridgeSupport578_suffix_003, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 414
    ridgeSupport578_rest_003 ridgeSupport578_rest_004 ridgeSupport578_rest_017
    ridgeSupport578_003 ridgeSupport578_suffix_004 ridgeSupport578_003_decode ridgeSupport578_suffix_decode_004
theorem ridgeSupport578_suffix_decode_002 : PackedRawNatGrowth.readList 13 478 ridgeSupport578_rest_002 =
    (ridgeSupport578_suffix_002, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 446
    ridgeSupport578_rest_002 ridgeSupport578_rest_003 ridgeSupport578_rest_017
    ridgeSupport578_002 ridgeSupport578_suffix_003 ridgeSupport578_002_decode ridgeSupport578_suffix_decode_003
theorem ridgeSupport578_suffix_decode_001 : PackedRawNatGrowth.readList 13 510 ridgeSupport578_rest_001 =
    (ridgeSupport578_suffix_001, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 478
    ridgeSupport578_rest_001 ridgeSupport578_rest_002 ridgeSupport578_rest_017
    ridgeSupport578_001 ridgeSupport578_suffix_002 ridgeSupport578_001_decode ridgeSupport578_suffix_decode_002
theorem ridgeSupport578_suffix_decode_000 : PackedRawNatGrowth.readList 13 542 ridgeSupport578_rest_000 =
    (ridgeSupport578_suffix_000, ridgeSupport578_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 510
    ridgeSupport578_rest_000 ridgeSupport578_rest_001 ridgeSupport578_rest_017
    ridgeSupport578_000 ridgeSupport578_suffix_001 ridgeSupport578_000_decode ridgeSupport578_suffix_decode_001
theorem ridgeSupport578_eq : candidateRows 578 = ridgeSupport578_suffix_000 := by
  change candidateSupports 578 = ridgeSupport578_suffix_000
  rw [ridgeSupport578_source]
  exact congrArg Prod.fst ridgeSupport578_suffix_decode_000
theorem ridgeTest_large_578 : ridgeTest 578 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport578_eq]
    simp only [ridgeSupport578_suffix_000, ridgeSupport578_suffix_001, ridgeSupport578_suffix_002, ridgeSupport578_suffix_003, ridgeSupport578_suffix_004, ridgeSupport578_suffix_005, ridgeSupport578_suffix_006, ridgeSupport578_suffix_007, ridgeSupport578_suffix_008, ridgeSupport578_suffix_009, ridgeSupport578_suffix_010, ridgeSupport578_suffix_011, ridgeSupport578_suffix_012, ridgeSupport578_suffix_013, ridgeSupport578_suffix_014, ridgeSupport578_suffix_015, ridgeSupport578_suffix_016, ridgeSupport578_suffix_017, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport578_000_mask, ridgeSupport578_001_mask, ridgeSupport578_002_mask, ridgeSupport578_003_mask, ridgeSupport578_004_mask, ridgeSupport578_005_mask, ridgeSupport578_006_mask, ridgeSupport578_007_mask, ridgeSupport578_008_mask, ridgeSupport578_009_mask, ridgeSupport578_010_mask, ridgeSupport578_011_mask, ridgeSupport578_012_mask, ridgeSupport578_013_mask, ridgeSupport578_014_mask, ridgeSupport578_015_mask, ridgeSupport578_016_mask]
    decide +kernel
  · rw [ridgeSupport578_eq]
    simp only [ridgeSupport578_suffix_000, ridgeSupport578_suffix_001, ridgeSupport578_suffix_002, ridgeSupport578_suffix_003, ridgeSupport578_suffix_004, ridgeSupport578_suffix_005, ridgeSupport578_suffix_006, ridgeSupport578_suffix_007, ridgeSupport578_suffix_008, ridgeSupport578_suffix_009, ridgeSupport578_suffix_010, ridgeSupport578_suffix_011, ridgeSupport578_suffix_012, ridgeSupport578_suffix_013, ridgeSupport578_suffix_014, ridgeSupport578_suffix_015, ridgeSupport578_suffix_016, ridgeSupport578_suffix_017, List.all_append, List.all_nil, ridgeSupport578_000_checked, ridgeSupport578_001_checked, ridgeSupport578_002_checked, ridgeSupport578_003_checked, ridgeSupport578_004_checked, ridgeSupport578_005_checked, ridgeSupport578_006_checked, ridgeSupport578_007_checked, ridgeSupport578_008_checked, ridgeSupport578_009_checked, ridgeSupport578_010_checked, ridgeSupport578_011_checked, ridgeSupport578_012_checked, ridgeSupport578_013_checked, ridgeSupport578_014_checked, ridgeSupport578_015_checked, ridgeSupport578_016_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
