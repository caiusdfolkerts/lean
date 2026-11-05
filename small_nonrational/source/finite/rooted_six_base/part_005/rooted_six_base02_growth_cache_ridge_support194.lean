module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport194Part000
public import RootedSixBase02GrowthCacheRidgeSupport194Part001
public import RootedSixBase02GrowthCacheRidgeSupport194Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport194_suffix_decode_017 : PackedRawNatGrowth.readList 13 0 ridgeSupport194_rest_017 =
    (ridgeSupport194_suffix_017, ridgeSupport194_rest_017) := by rfl
theorem ridgeSupport194_suffix_decode_016 : PackedRawNatGrowth.readList 13 30 ridgeSupport194_rest_016 =
    (ridgeSupport194_suffix_016, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 30 0
    ridgeSupport194_rest_016 ridgeSupport194_rest_017 ridgeSupport194_rest_017
    ridgeSupport194_016 ridgeSupport194_suffix_017 ridgeSupport194_016_decode ridgeSupport194_suffix_decode_017
theorem ridgeSupport194_suffix_decode_015 : PackedRawNatGrowth.readList 13 62 ridgeSupport194_rest_015 =
    (ridgeSupport194_suffix_015, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 30
    ridgeSupport194_rest_015 ridgeSupport194_rest_016 ridgeSupport194_rest_017
    ridgeSupport194_015 ridgeSupport194_suffix_016 ridgeSupport194_015_decode ridgeSupport194_suffix_decode_016
theorem ridgeSupport194_suffix_decode_014 : PackedRawNatGrowth.readList 13 94 ridgeSupport194_rest_014 =
    (ridgeSupport194_suffix_014, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 62
    ridgeSupport194_rest_014 ridgeSupport194_rest_015 ridgeSupport194_rest_017
    ridgeSupport194_014 ridgeSupport194_suffix_015 ridgeSupport194_014_decode ridgeSupport194_suffix_decode_015
theorem ridgeSupport194_suffix_decode_013 : PackedRawNatGrowth.readList 13 126 ridgeSupport194_rest_013 =
    (ridgeSupport194_suffix_013, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 94
    ridgeSupport194_rest_013 ridgeSupport194_rest_014 ridgeSupport194_rest_017
    ridgeSupport194_013 ridgeSupport194_suffix_014 ridgeSupport194_013_decode ridgeSupport194_suffix_decode_014
theorem ridgeSupport194_suffix_decode_012 : PackedRawNatGrowth.readList 13 158 ridgeSupport194_rest_012 =
    (ridgeSupport194_suffix_012, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 126
    ridgeSupport194_rest_012 ridgeSupport194_rest_013 ridgeSupport194_rest_017
    ridgeSupport194_012 ridgeSupport194_suffix_013 ridgeSupport194_012_decode ridgeSupport194_suffix_decode_013
theorem ridgeSupport194_suffix_decode_011 : PackedRawNatGrowth.readList 13 190 ridgeSupport194_rest_011 =
    (ridgeSupport194_suffix_011, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 158
    ridgeSupport194_rest_011 ridgeSupport194_rest_012 ridgeSupport194_rest_017
    ridgeSupport194_011 ridgeSupport194_suffix_012 ridgeSupport194_011_decode ridgeSupport194_suffix_decode_012
theorem ridgeSupport194_suffix_decode_010 : PackedRawNatGrowth.readList 13 222 ridgeSupport194_rest_010 =
    (ridgeSupport194_suffix_010, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 190
    ridgeSupport194_rest_010 ridgeSupport194_rest_011 ridgeSupport194_rest_017
    ridgeSupport194_010 ridgeSupport194_suffix_011 ridgeSupport194_010_decode ridgeSupport194_suffix_decode_011
theorem ridgeSupport194_suffix_decode_009 : PackedRawNatGrowth.readList 13 254 ridgeSupport194_rest_009 =
    (ridgeSupport194_suffix_009, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 222
    ridgeSupport194_rest_009 ridgeSupport194_rest_010 ridgeSupport194_rest_017
    ridgeSupport194_009 ridgeSupport194_suffix_010 ridgeSupport194_009_decode ridgeSupport194_suffix_decode_010
theorem ridgeSupport194_suffix_decode_008 : PackedRawNatGrowth.readList 13 286 ridgeSupport194_rest_008 =
    (ridgeSupport194_suffix_008, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 254
    ridgeSupport194_rest_008 ridgeSupport194_rest_009 ridgeSupport194_rest_017
    ridgeSupport194_008 ridgeSupport194_suffix_009 ridgeSupport194_008_decode ridgeSupport194_suffix_decode_009
theorem ridgeSupport194_suffix_decode_007 : PackedRawNatGrowth.readList 13 318 ridgeSupport194_rest_007 =
    (ridgeSupport194_suffix_007, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 286
    ridgeSupport194_rest_007 ridgeSupport194_rest_008 ridgeSupport194_rest_017
    ridgeSupport194_007 ridgeSupport194_suffix_008 ridgeSupport194_007_decode ridgeSupport194_suffix_decode_008
theorem ridgeSupport194_suffix_decode_006 : PackedRawNatGrowth.readList 13 350 ridgeSupport194_rest_006 =
    (ridgeSupport194_suffix_006, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 318
    ridgeSupport194_rest_006 ridgeSupport194_rest_007 ridgeSupport194_rest_017
    ridgeSupport194_006 ridgeSupport194_suffix_007 ridgeSupport194_006_decode ridgeSupport194_suffix_decode_007
theorem ridgeSupport194_suffix_decode_005 : PackedRawNatGrowth.readList 13 382 ridgeSupport194_rest_005 =
    (ridgeSupport194_suffix_005, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 350
    ridgeSupport194_rest_005 ridgeSupport194_rest_006 ridgeSupport194_rest_017
    ridgeSupport194_005 ridgeSupport194_suffix_006 ridgeSupport194_005_decode ridgeSupport194_suffix_decode_006
theorem ridgeSupport194_suffix_decode_004 : PackedRawNatGrowth.readList 13 414 ridgeSupport194_rest_004 =
    (ridgeSupport194_suffix_004, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 382
    ridgeSupport194_rest_004 ridgeSupport194_rest_005 ridgeSupport194_rest_017
    ridgeSupport194_004 ridgeSupport194_suffix_005 ridgeSupport194_004_decode ridgeSupport194_suffix_decode_005
theorem ridgeSupport194_suffix_decode_003 : PackedRawNatGrowth.readList 13 446 ridgeSupport194_rest_003 =
    (ridgeSupport194_suffix_003, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 414
    ridgeSupport194_rest_003 ridgeSupport194_rest_004 ridgeSupport194_rest_017
    ridgeSupport194_003 ridgeSupport194_suffix_004 ridgeSupport194_003_decode ridgeSupport194_suffix_decode_004
theorem ridgeSupport194_suffix_decode_002 : PackedRawNatGrowth.readList 13 478 ridgeSupport194_rest_002 =
    (ridgeSupport194_suffix_002, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 446
    ridgeSupport194_rest_002 ridgeSupport194_rest_003 ridgeSupport194_rest_017
    ridgeSupport194_002 ridgeSupport194_suffix_003 ridgeSupport194_002_decode ridgeSupport194_suffix_decode_003
theorem ridgeSupport194_suffix_decode_001 : PackedRawNatGrowth.readList 13 510 ridgeSupport194_rest_001 =
    (ridgeSupport194_suffix_001, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 478
    ridgeSupport194_rest_001 ridgeSupport194_rest_002 ridgeSupport194_rest_017
    ridgeSupport194_001 ridgeSupport194_suffix_002 ridgeSupport194_001_decode ridgeSupport194_suffix_decode_002
theorem ridgeSupport194_suffix_decode_000 : PackedRawNatGrowth.readList 13 542 ridgeSupport194_rest_000 =
    (ridgeSupport194_suffix_000, ridgeSupport194_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 510
    ridgeSupport194_rest_000 ridgeSupport194_rest_001 ridgeSupport194_rest_017
    ridgeSupport194_000 ridgeSupport194_suffix_001 ridgeSupport194_000_decode ridgeSupport194_suffix_decode_001
theorem ridgeSupport194_eq : candidateRows 194 = ridgeSupport194_suffix_000 := by
  change candidateSupports 194 = ridgeSupport194_suffix_000
  rw [ridgeSupport194_source]
  exact congrArg Prod.fst ridgeSupport194_suffix_decode_000
theorem ridgeTest_large_194 : ridgeTest 194 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport194_eq]
    simp only [ridgeSupport194_suffix_000, ridgeSupport194_suffix_001, ridgeSupport194_suffix_002, ridgeSupport194_suffix_003, ridgeSupport194_suffix_004, ridgeSupport194_suffix_005, ridgeSupport194_suffix_006, ridgeSupport194_suffix_007, ridgeSupport194_suffix_008, ridgeSupport194_suffix_009, ridgeSupport194_suffix_010, ridgeSupport194_suffix_011, ridgeSupport194_suffix_012, ridgeSupport194_suffix_013, ridgeSupport194_suffix_014, ridgeSupport194_suffix_015, ridgeSupport194_suffix_016, ridgeSupport194_suffix_017, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport194_000_mask, ridgeSupport194_001_mask, ridgeSupport194_002_mask, ridgeSupport194_003_mask, ridgeSupport194_004_mask, ridgeSupport194_005_mask, ridgeSupport194_006_mask, ridgeSupport194_007_mask, ridgeSupport194_008_mask, ridgeSupport194_009_mask, ridgeSupport194_010_mask, ridgeSupport194_011_mask, ridgeSupport194_012_mask, ridgeSupport194_013_mask, ridgeSupport194_014_mask, ridgeSupport194_015_mask, ridgeSupport194_016_mask]
    decide +kernel
  · rw [ridgeSupport194_eq]
    simp only [ridgeSupport194_suffix_000, ridgeSupport194_suffix_001, ridgeSupport194_suffix_002, ridgeSupport194_suffix_003, ridgeSupport194_suffix_004, ridgeSupport194_suffix_005, ridgeSupport194_suffix_006, ridgeSupport194_suffix_007, ridgeSupport194_suffix_008, ridgeSupport194_suffix_009, ridgeSupport194_suffix_010, ridgeSupport194_suffix_011, ridgeSupport194_suffix_012, ridgeSupport194_suffix_013, ridgeSupport194_suffix_014, ridgeSupport194_suffix_015, ridgeSupport194_suffix_016, ridgeSupport194_suffix_017, List.all_append, List.all_nil, ridgeSupport194_000_checked, ridgeSupport194_001_checked, ridgeSupport194_002_checked, ridgeSupport194_003_checked, ridgeSupport194_004_checked, ridgeSupport194_005_checked, ridgeSupport194_006_checked, ridgeSupport194_007_checked, ridgeSupport194_008_checked, ridgeSupport194_009_checked, ridgeSupport194_010_checked, ridgeSupport194_011_checked, ridgeSupport194_012_checked, ridgeSupport194_013_checked, ridgeSupport194_014_checked, ridgeSupport194_015_checked, ridgeSupport194_016_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
