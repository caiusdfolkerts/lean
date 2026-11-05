module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport322Part000
public import RootedSixBase02GrowthCacheRidgeSupport322Part001
public import RootedSixBase02GrowthCacheRidgeSupport322Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport322_suffix_decode_017 : PackedRawNatGrowth.readList 13 0 ridgeSupport322_rest_017 =
    (ridgeSupport322_suffix_017, ridgeSupport322_rest_017) := by rfl
theorem ridgeSupport322_suffix_decode_016 : PackedRawNatGrowth.readList 13 30 ridgeSupport322_rest_016 =
    (ridgeSupport322_suffix_016, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 30 0
    ridgeSupport322_rest_016 ridgeSupport322_rest_017 ridgeSupport322_rest_017
    ridgeSupport322_016 ridgeSupport322_suffix_017 ridgeSupport322_016_decode ridgeSupport322_suffix_decode_017
theorem ridgeSupport322_suffix_decode_015 : PackedRawNatGrowth.readList 13 62 ridgeSupport322_rest_015 =
    (ridgeSupport322_suffix_015, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 30
    ridgeSupport322_rest_015 ridgeSupport322_rest_016 ridgeSupport322_rest_017
    ridgeSupport322_015 ridgeSupport322_suffix_016 ridgeSupport322_015_decode ridgeSupport322_suffix_decode_016
theorem ridgeSupport322_suffix_decode_014 : PackedRawNatGrowth.readList 13 94 ridgeSupport322_rest_014 =
    (ridgeSupport322_suffix_014, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 62
    ridgeSupport322_rest_014 ridgeSupport322_rest_015 ridgeSupport322_rest_017
    ridgeSupport322_014 ridgeSupport322_suffix_015 ridgeSupport322_014_decode ridgeSupport322_suffix_decode_015
theorem ridgeSupport322_suffix_decode_013 : PackedRawNatGrowth.readList 13 126 ridgeSupport322_rest_013 =
    (ridgeSupport322_suffix_013, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 94
    ridgeSupport322_rest_013 ridgeSupport322_rest_014 ridgeSupport322_rest_017
    ridgeSupport322_013 ridgeSupport322_suffix_014 ridgeSupport322_013_decode ridgeSupport322_suffix_decode_014
theorem ridgeSupport322_suffix_decode_012 : PackedRawNatGrowth.readList 13 158 ridgeSupport322_rest_012 =
    (ridgeSupport322_suffix_012, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 126
    ridgeSupport322_rest_012 ridgeSupport322_rest_013 ridgeSupport322_rest_017
    ridgeSupport322_012 ridgeSupport322_suffix_013 ridgeSupport322_012_decode ridgeSupport322_suffix_decode_013
theorem ridgeSupport322_suffix_decode_011 : PackedRawNatGrowth.readList 13 190 ridgeSupport322_rest_011 =
    (ridgeSupport322_suffix_011, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 158
    ridgeSupport322_rest_011 ridgeSupport322_rest_012 ridgeSupport322_rest_017
    ridgeSupport322_011 ridgeSupport322_suffix_012 ridgeSupport322_011_decode ridgeSupport322_suffix_decode_012
theorem ridgeSupport322_suffix_decode_010 : PackedRawNatGrowth.readList 13 222 ridgeSupport322_rest_010 =
    (ridgeSupport322_suffix_010, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 190
    ridgeSupport322_rest_010 ridgeSupport322_rest_011 ridgeSupport322_rest_017
    ridgeSupport322_010 ridgeSupport322_suffix_011 ridgeSupport322_010_decode ridgeSupport322_suffix_decode_011
theorem ridgeSupport322_suffix_decode_009 : PackedRawNatGrowth.readList 13 254 ridgeSupport322_rest_009 =
    (ridgeSupport322_suffix_009, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 222
    ridgeSupport322_rest_009 ridgeSupport322_rest_010 ridgeSupport322_rest_017
    ridgeSupport322_009 ridgeSupport322_suffix_010 ridgeSupport322_009_decode ridgeSupport322_suffix_decode_010
theorem ridgeSupport322_suffix_decode_008 : PackedRawNatGrowth.readList 13 286 ridgeSupport322_rest_008 =
    (ridgeSupport322_suffix_008, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 254
    ridgeSupport322_rest_008 ridgeSupport322_rest_009 ridgeSupport322_rest_017
    ridgeSupport322_008 ridgeSupport322_suffix_009 ridgeSupport322_008_decode ridgeSupport322_suffix_decode_009
theorem ridgeSupport322_suffix_decode_007 : PackedRawNatGrowth.readList 13 318 ridgeSupport322_rest_007 =
    (ridgeSupport322_suffix_007, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 286
    ridgeSupport322_rest_007 ridgeSupport322_rest_008 ridgeSupport322_rest_017
    ridgeSupport322_007 ridgeSupport322_suffix_008 ridgeSupport322_007_decode ridgeSupport322_suffix_decode_008
theorem ridgeSupport322_suffix_decode_006 : PackedRawNatGrowth.readList 13 350 ridgeSupport322_rest_006 =
    (ridgeSupport322_suffix_006, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 318
    ridgeSupport322_rest_006 ridgeSupport322_rest_007 ridgeSupport322_rest_017
    ridgeSupport322_006 ridgeSupport322_suffix_007 ridgeSupport322_006_decode ridgeSupport322_suffix_decode_007
theorem ridgeSupport322_suffix_decode_005 : PackedRawNatGrowth.readList 13 382 ridgeSupport322_rest_005 =
    (ridgeSupport322_suffix_005, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 350
    ridgeSupport322_rest_005 ridgeSupport322_rest_006 ridgeSupport322_rest_017
    ridgeSupport322_005 ridgeSupport322_suffix_006 ridgeSupport322_005_decode ridgeSupport322_suffix_decode_006
theorem ridgeSupport322_suffix_decode_004 : PackedRawNatGrowth.readList 13 414 ridgeSupport322_rest_004 =
    (ridgeSupport322_suffix_004, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 382
    ridgeSupport322_rest_004 ridgeSupport322_rest_005 ridgeSupport322_rest_017
    ridgeSupport322_004 ridgeSupport322_suffix_005 ridgeSupport322_004_decode ridgeSupport322_suffix_decode_005
theorem ridgeSupport322_suffix_decode_003 : PackedRawNatGrowth.readList 13 446 ridgeSupport322_rest_003 =
    (ridgeSupport322_suffix_003, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 414
    ridgeSupport322_rest_003 ridgeSupport322_rest_004 ridgeSupport322_rest_017
    ridgeSupport322_003 ridgeSupport322_suffix_004 ridgeSupport322_003_decode ridgeSupport322_suffix_decode_004
theorem ridgeSupport322_suffix_decode_002 : PackedRawNatGrowth.readList 13 478 ridgeSupport322_rest_002 =
    (ridgeSupport322_suffix_002, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 446
    ridgeSupport322_rest_002 ridgeSupport322_rest_003 ridgeSupport322_rest_017
    ridgeSupport322_002 ridgeSupport322_suffix_003 ridgeSupport322_002_decode ridgeSupport322_suffix_decode_003
theorem ridgeSupport322_suffix_decode_001 : PackedRawNatGrowth.readList 13 510 ridgeSupport322_rest_001 =
    (ridgeSupport322_suffix_001, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 478
    ridgeSupport322_rest_001 ridgeSupport322_rest_002 ridgeSupport322_rest_017
    ridgeSupport322_001 ridgeSupport322_suffix_002 ridgeSupport322_001_decode ridgeSupport322_suffix_decode_002
theorem ridgeSupport322_suffix_decode_000 : PackedRawNatGrowth.readList 13 542 ridgeSupport322_rest_000 =
    (ridgeSupport322_suffix_000, ridgeSupport322_rest_017) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 510
    ridgeSupport322_rest_000 ridgeSupport322_rest_001 ridgeSupport322_rest_017
    ridgeSupport322_000 ridgeSupport322_suffix_001 ridgeSupport322_000_decode ridgeSupport322_suffix_decode_001
theorem ridgeSupport322_eq : candidateRows 322 = ridgeSupport322_suffix_000 := by
  change candidateSupports 322 = ridgeSupport322_suffix_000
  rw [ridgeSupport322_source]
  exact congrArg Prod.fst ridgeSupport322_suffix_decode_000
theorem ridgeTest_large_322 : ridgeTest 322 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport322_eq]
    simp only [ridgeSupport322_suffix_000, ridgeSupport322_suffix_001, ridgeSupport322_suffix_002, ridgeSupport322_suffix_003, ridgeSupport322_suffix_004, ridgeSupport322_suffix_005, ridgeSupport322_suffix_006, ridgeSupport322_suffix_007, ridgeSupport322_suffix_008, ridgeSupport322_suffix_009, ridgeSupport322_suffix_010, ridgeSupport322_suffix_011, ridgeSupport322_suffix_012, ridgeSupport322_suffix_013, ridgeSupport322_suffix_014, ridgeSupport322_suffix_015, ridgeSupport322_suffix_016, ridgeSupport322_suffix_017, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport322_000_mask, ridgeSupport322_001_mask, ridgeSupport322_002_mask, ridgeSupport322_003_mask, ridgeSupport322_004_mask, ridgeSupport322_005_mask, ridgeSupport322_006_mask, ridgeSupport322_007_mask, ridgeSupport322_008_mask, ridgeSupport322_009_mask, ridgeSupport322_010_mask, ridgeSupport322_011_mask, ridgeSupport322_012_mask, ridgeSupport322_013_mask, ridgeSupport322_014_mask, ridgeSupport322_015_mask, ridgeSupport322_016_mask]
    decide +kernel
  · rw [ridgeSupport322_eq]
    simp only [ridgeSupport322_suffix_000, ridgeSupport322_suffix_001, ridgeSupport322_suffix_002, ridgeSupport322_suffix_003, ridgeSupport322_suffix_004, ridgeSupport322_suffix_005, ridgeSupport322_suffix_006, ridgeSupport322_suffix_007, ridgeSupport322_suffix_008, ridgeSupport322_suffix_009, ridgeSupport322_suffix_010, ridgeSupport322_suffix_011, ridgeSupport322_suffix_012, ridgeSupport322_suffix_013, ridgeSupport322_suffix_014, ridgeSupport322_suffix_015, ridgeSupport322_suffix_016, ridgeSupport322_suffix_017, List.all_append, List.all_nil, ridgeSupport322_000_checked, ridgeSupport322_001_checked, ridgeSupport322_002_checked, ridgeSupport322_003_checked, ridgeSupport322_004_checked, ridgeSupport322_005_checked, ridgeSupport322_006_checked, ridgeSupport322_007_checked, ridgeSupport322_008_checked, ridgeSupport322_009_checked, ridgeSupport322_010_checked, ridgeSupport322_011_checked, ridgeSupport322_012_checked, ridgeSupport322_013_checked, ridgeSupport322_014_checked, ridgeSupport322_015_checked, ridgeSupport322_016_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
