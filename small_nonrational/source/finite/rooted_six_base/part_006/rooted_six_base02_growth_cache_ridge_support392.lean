module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport392Part000
public import RootedSixBase02GrowthCacheRidgeSupport392Part001
public import RootedSixBase02GrowthCacheRidgeSupport392Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport392_suffix_decode_017 : PackedRawNatGrowth.readList 13 0 ridgeSupport392_rest_017 =
    (ridgeSupport392_suffix_017, ridgeSupport392_rest_017) := by rfl
theorem ridgeSupport392_suffix_decode_016 : PackedRawNatGrowth.readList 13 30 ridgeSupport392_rest_016 =
    (ridgeSupport392_suffix_016, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 30 0
    ridgeSupport392_rest_016 ridgeSupport392_rest_017 ridgeSupport392_rest_017
    ridgeSupport392_016 ridgeSupport392_suffix_017 ridgeSupport392_016_decode ridgeSupport392_suffix_decode_017
theorem ridgeSupport392_suffix_decode_015 : PackedRawNatGrowth.readList 13 62 ridgeSupport392_rest_015 =
    (ridgeSupport392_suffix_015, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 30
    ridgeSupport392_rest_015 ridgeSupport392_rest_016 ridgeSupport392_rest_017
    ridgeSupport392_015 ridgeSupport392_suffix_016 ridgeSupport392_015_decode ridgeSupport392_suffix_decode_016
theorem ridgeSupport392_suffix_decode_014 : PackedRawNatGrowth.readList 13 94 ridgeSupport392_rest_014 =
    (ridgeSupport392_suffix_014, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 62
    ridgeSupport392_rest_014 ridgeSupport392_rest_015 ridgeSupport392_rest_017
    ridgeSupport392_014 ridgeSupport392_suffix_015 ridgeSupport392_014_decode ridgeSupport392_suffix_decode_015
theorem ridgeSupport392_suffix_decode_013 : PackedRawNatGrowth.readList 13 126 ridgeSupport392_rest_013 =
    (ridgeSupport392_suffix_013, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 94
    ridgeSupport392_rest_013 ridgeSupport392_rest_014 ridgeSupport392_rest_017
    ridgeSupport392_013 ridgeSupport392_suffix_014 ridgeSupport392_013_decode ridgeSupport392_suffix_decode_014
theorem ridgeSupport392_suffix_decode_012 : PackedRawNatGrowth.readList 13 158 ridgeSupport392_rest_012 =
    (ridgeSupport392_suffix_012, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 126
    ridgeSupport392_rest_012 ridgeSupport392_rest_013 ridgeSupport392_rest_017
    ridgeSupport392_012 ridgeSupport392_suffix_013 ridgeSupport392_012_decode ridgeSupport392_suffix_decode_013
theorem ridgeSupport392_suffix_decode_011 : PackedRawNatGrowth.readList 13 190 ridgeSupport392_rest_011 =
    (ridgeSupport392_suffix_011, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 158
    ridgeSupport392_rest_011 ridgeSupport392_rest_012 ridgeSupport392_rest_017
    ridgeSupport392_011 ridgeSupport392_suffix_012 ridgeSupport392_011_decode ridgeSupport392_suffix_decode_012
theorem ridgeSupport392_suffix_decode_010 : PackedRawNatGrowth.readList 13 222 ridgeSupport392_rest_010 =
    (ridgeSupport392_suffix_010, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 190
    ridgeSupport392_rest_010 ridgeSupport392_rest_011 ridgeSupport392_rest_017
    ridgeSupport392_010 ridgeSupport392_suffix_011 ridgeSupport392_010_decode ridgeSupport392_suffix_decode_011
theorem ridgeSupport392_suffix_decode_009 : PackedRawNatGrowth.readList 13 254 ridgeSupport392_rest_009 =
    (ridgeSupport392_suffix_009, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 222
    ridgeSupport392_rest_009 ridgeSupport392_rest_010 ridgeSupport392_rest_017
    ridgeSupport392_009 ridgeSupport392_suffix_010 ridgeSupport392_009_decode ridgeSupport392_suffix_decode_010
theorem ridgeSupport392_suffix_decode_008 : PackedRawNatGrowth.readList 13 286 ridgeSupport392_rest_008 =
    (ridgeSupport392_suffix_008, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 254
    ridgeSupport392_rest_008 ridgeSupport392_rest_009 ridgeSupport392_rest_017
    ridgeSupport392_008 ridgeSupport392_suffix_009 ridgeSupport392_008_decode ridgeSupport392_suffix_decode_009
theorem ridgeSupport392_suffix_decode_007 : PackedRawNatGrowth.readList 13 318 ridgeSupport392_rest_007 =
    (ridgeSupport392_suffix_007, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 286
    ridgeSupport392_rest_007 ridgeSupport392_rest_008 ridgeSupport392_rest_017
    ridgeSupport392_007 ridgeSupport392_suffix_008 ridgeSupport392_007_decode ridgeSupport392_suffix_decode_008
theorem ridgeSupport392_suffix_decode_006 : PackedRawNatGrowth.readList 13 350 ridgeSupport392_rest_006 =
    (ridgeSupport392_suffix_006, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 318
    ridgeSupport392_rest_006 ridgeSupport392_rest_007 ridgeSupport392_rest_017
    ridgeSupport392_006 ridgeSupport392_suffix_007 ridgeSupport392_006_decode ridgeSupport392_suffix_decode_007
theorem ridgeSupport392_suffix_decode_005 : PackedRawNatGrowth.readList 13 382 ridgeSupport392_rest_005 =
    (ridgeSupport392_suffix_005, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 350
    ridgeSupport392_rest_005 ridgeSupport392_rest_006 ridgeSupport392_rest_017
    ridgeSupport392_005 ridgeSupport392_suffix_006 ridgeSupport392_005_decode ridgeSupport392_suffix_decode_006
theorem ridgeSupport392_suffix_decode_004 : PackedRawNatGrowth.readList 13 414 ridgeSupport392_rest_004 =
    (ridgeSupport392_suffix_004, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 382
    ridgeSupport392_rest_004 ridgeSupport392_rest_005 ridgeSupport392_rest_017
    ridgeSupport392_004 ridgeSupport392_suffix_005 ridgeSupport392_004_decode ridgeSupport392_suffix_decode_005
theorem ridgeSupport392_suffix_decode_003 : PackedRawNatGrowth.readList 13 446 ridgeSupport392_rest_003 =
    (ridgeSupport392_suffix_003, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 414
    ridgeSupport392_rest_003 ridgeSupport392_rest_004 ridgeSupport392_rest_017
    ridgeSupport392_003 ridgeSupport392_suffix_004 ridgeSupport392_003_decode ridgeSupport392_suffix_decode_004
theorem ridgeSupport392_suffix_decode_002 : PackedRawNatGrowth.readList 13 478 ridgeSupport392_rest_002 =
    (ridgeSupport392_suffix_002, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 446
    ridgeSupport392_rest_002 ridgeSupport392_rest_003 ridgeSupport392_rest_017
    ridgeSupport392_002 ridgeSupport392_suffix_003 ridgeSupport392_002_decode ridgeSupport392_suffix_decode_003
theorem ridgeSupport392_suffix_decode_001 : PackedRawNatGrowth.readList 13 510 ridgeSupport392_rest_001 =
    (ridgeSupport392_suffix_001, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 478
    ridgeSupport392_rest_001 ridgeSupport392_rest_002 ridgeSupport392_rest_017
    ridgeSupport392_001 ridgeSupport392_suffix_002 ridgeSupport392_001_decode ridgeSupport392_suffix_decode_002
theorem ridgeSupport392_suffix_decode_000 : PackedRawNatGrowth.readList 13 542 ridgeSupport392_rest_000 =
    (ridgeSupport392_suffix_000, ridgeSupport392_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 510
    ridgeSupport392_rest_000 ridgeSupport392_rest_001 ridgeSupport392_rest_017
    ridgeSupport392_000 ridgeSupport392_suffix_001 ridgeSupport392_000_decode ridgeSupport392_suffix_decode_001
theorem ridgeSupport392_eq : candidateRows 392 = ridgeSupport392_suffix_000 := by
  change candidateSupports 392 = ridgeSupport392_suffix_000
  rw [ridgeSupport392_source]
  exact congrArg Prod.fst ridgeSupport392_suffix_decode_000
theorem ridgeTest_large_392 : ridgeTest 392 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport392_eq]
    simp only [ridgeSupport392_suffix_000, ridgeSupport392_suffix_001, ridgeSupport392_suffix_002, ridgeSupport392_suffix_003, ridgeSupport392_suffix_004, ridgeSupport392_suffix_005, ridgeSupport392_suffix_006, ridgeSupport392_suffix_007, ridgeSupport392_suffix_008, ridgeSupport392_suffix_009, ridgeSupport392_suffix_010, ridgeSupport392_suffix_011, ridgeSupport392_suffix_012, ridgeSupport392_suffix_013, ridgeSupport392_suffix_014, ridgeSupport392_suffix_015, ridgeSupport392_suffix_016, ridgeSupport392_suffix_017, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport392_000_mask, ridgeSupport392_001_mask, ridgeSupport392_002_mask, ridgeSupport392_003_mask, ridgeSupport392_004_mask, ridgeSupport392_005_mask, ridgeSupport392_006_mask, ridgeSupport392_007_mask, ridgeSupport392_008_mask, ridgeSupport392_009_mask, ridgeSupport392_010_mask, ridgeSupport392_011_mask, ridgeSupport392_012_mask, ridgeSupport392_013_mask, ridgeSupport392_014_mask, ridgeSupport392_015_mask, ridgeSupport392_016_mask]
    decide +kernel
  · rw [ridgeSupport392_eq]
    simp only [ridgeSupport392_suffix_000, ridgeSupport392_suffix_001, ridgeSupport392_suffix_002, ridgeSupport392_suffix_003, ridgeSupport392_suffix_004, ridgeSupport392_suffix_005, ridgeSupport392_suffix_006, ridgeSupport392_suffix_007, ridgeSupport392_suffix_008, ridgeSupport392_suffix_009, ridgeSupport392_suffix_010, ridgeSupport392_suffix_011, ridgeSupport392_suffix_012, ridgeSupport392_suffix_013, ridgeSupport392_suffix_014, ridgeSupport392_suffix_015, ridgeSupport392_suffix_016, ridgeSupport392_suffix_017, List.all_append, List.all_nil, ridgeSupport392_000_checked, ridgeSupport392_001_checked, ridgeSupport392_002_checked, ridgeSupport392_003_checked, ridgeSupport392_004_checked, ridgeSupport392_005_checked, ridgeSupport392_006_checked, ridgeSupport392_007_checked, ridgeSupport392_008_checked, ridgeSupport392_009_checked, ridgeSupport392_010_checked, ridgeSupport392_011_checked, ridgeSupport392_012_checked, ridgeSupport392_013_checked, ridgeSupport392_014_checked, ridgeSupport392_015_checked, ridgeSupport392_016_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
