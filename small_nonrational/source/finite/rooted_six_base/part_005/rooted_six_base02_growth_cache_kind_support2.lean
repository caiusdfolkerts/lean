module
prelude
public import RootedSixBase02GrowthCacheKindSupport2Part000
public import RootedSixBase02GrowthCacheKindSupport2Part001
public import RootedSixBase02GrowthCacheKindSupport2Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_suffix_decode_018 : PackedRawNatGrowth.readList 13 0 kindSupport2_rest_018 =
    (kindSupport2_suffix_018, kindSupport2_rest_018) := by rfl
theorem kindSupport2_suffix_decode_017 : PackedRawNatGrowth.readList 13 20 kindSupport2_rest_017 =
    (kindSupport2_suffix_017, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 20 0
    kindSupport2_rest_017 kindSupport2_rest_018 kindSupport2_rest_018
    kindSupport2_017 kindSupport2_suffix_018 kindSupport2_017_decode kindSupport2_suffix_decode_018
theorem kindSupport2_suffix_decode_016 : PackedRawNatGrowth.readList 13 52 kindSupport2_rest_016 =
    (kindSupport2_suffix_016, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 20
    kindSupport2_rest_016 kindSupport2_rest_017 kindSupport2_rest_018
    kindSupport2_016 kindSupport2_suffix_017 kindSupport2_016_decode kindSupport2_suffix_decode_017
theorem kindSupport2_suffix_decode_015 : PackedRawNatGrowth.readList 13 84 kindSupport2_rest_015 =
    (kindSupport2_suffix_015, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 52
    kindSupport2_rest_015 kindSupport2_rest_016 kindSupport2_rest_018
    kindSupport2_015 kindSupport2_suffix_016 kindSupport2_015_decode kindSupport2_suffix_decode_016
theorem kindSupport2_suffix_decode_014 : PackedRawNatGrowth.readList 13 116 kindSupport2_rest_014 =
    (kindSupport2_suffix_014, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 84
    kindSupport2_rest_014 kindSupport2_rest_015 kindSupport2_rest_018
    kindSupport2_014 kindSupport2_suffix_015 kindSupport2_014_decode kindSupport2_suffix_decode_015
theorem kindSupport2_suffix_decode_013 : PackedRawNatGrowth.readList 13 148 kindSupport2_rest_013 =
    (kindSupport2_suffix_013, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 116
    kindSupport2_rest_013 kindSupport2_rest_014 kindSupport2_rest_018
    kindSupport2_013 kindSupport2_suffix_014 kindSupport2_013_decode kindSupport2_suffix_decode_014
theorem kindSupport2_suffix_decode_012 : PackedRawNatGrowth.readList 13 180 kindSupport2_rest_012 =
    (kindSupport2_suffix_012, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 148
    kindSupport2_rest_012 kindSupport2_rest_013 kindSupport2_rest_018
    kindSupport2_012 kindSupport2_suffix_013 kindSupport2_012_decode kindSupport2_suffix_decode_013
theorem kindSupport2_suffix_decode_011 : PackedRawNatGrowth.readList 13 212 kindSupport2_rest_011 =
    (kindSupport2_suffix_011, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 180
    kindSupport2_rest_011 kindSupport2_rest_012 kindSupport2_rest_018
    kindSupport2_011 kindSupport2_suffix_012 kindSupport2_011_decode kindSupport2_suffix_decode_012
theorem kindSupport2_suffix_decode_010 : PackedRawNatGrowth.readList 13 244 kindSupport2_rest_010 =
    (kindSupport2_suffix_010, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 212
    kindSupport2_rest_010 kindSupport2_rest_011 kindSupport2_rest_018
    kindSupport2_010 kindSupport2_suffix_011 kindSupport2_010_decode kindSupport2_suffix_decode_011
theorem kindSupport2_suffix_decode_009 : PackedRawNatGrowth.readList 13 276 kindSupport2_rest_009 =
    (kindSupport2_suffix_009, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 244
    kindSupport2_rest_009 kindSupport2_rest_010 kindSupport2_rest_018
    kindSupport2_009 kindSupport2_suffix_010 kindSupport2_009_decode kindSupport2_suffix_decode_010
theorem kindSupport2_suffix_decode_008 : PackedRawNatGrowth.readList 13 308 kindSupport2_rest_008 =
    (kindSupport2_suffix_008, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 276
    kindSupport2_rest_008 kindSupport2_rest_009 kindSupport2_rest_018
    kindSupport2_008 kindSupport2_suffix_009 kindSupport2_008_decode kindSupport2_suffix_decode_009
theorem kindSupport2_suffix_decode_007 : PackedRawNatGrowth.readList 13 340 kindSupport2_rest_007 =
    (kindSupport2_suffix_007, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 308
    kindSupport2_rest_007 kindSupport2_rest_008 kindSupport2_rest_018
    kindSupport2_007 kindSupport2_suffix_008 kindSupport2_007_decode kindSupport2_suffix_decode_008
theorem kindSupport2_suffix_decode_006 : PackedRawNatGrowth.readList 13 372 kindSupport2_rest_006 =
    (kindSupport2_suffix_006, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 340
    kindSupport2_rest_006 kindSupport2_rest_007 kindSupport2_rest_018
    kindSupport2_006 kindSupport2_suffix_007 kindSupport2_006_decode kindSupport2_suffix_decode_007
theorem kindSupport2_suffix_decode_005 : PackedRawNatGrowth.readList 13 404 kindSupport2_rest_005 =
    (kindSupport2_suffix_005, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 372
    kindSupport2_rest_005 kindSupport2_rest_006 kindSupport2_rest_018
    kindSupport2_005 kindSupport2_suffix_006 kindSupport2_005_decode kindSupport2_suffix_decode_006
theorem kindSupport2_suffix_decode_004 : PackedRawNatGrowth.readList 13 436 kindSupport2_rest_004 =
    (kindSupport2_suffix_004, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 404
    kindSupport2_rest_004 kindSupport2_rest_005 kindSupport2_rest_018
    kindSupport2_004 kindSupport2_suffix_005 kindSupport2_004_decode kindSupport2_suffix_decode_005
theorem kindSupport2_suffix_decode_003 : PackedRawNatGrowth.readList 13 468 kindSupport2_rest_003 =
    (kindSupport2_suffix_003, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 436
    kindSupport2_rest_003 kindSupport2_rest_004 kindSupport2_rest_018
    kindSupport2_003 kindSupport2_suffix_004 kindSupport2_003_decode kindSupport2_suffix_decode_004
theorem kindSupport2_suffix_decode_002 : PackedRawNatGrowth.readList 13 500 kindSupport2_rest_002 =
    (kindSupport2_suffix_002, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 468
    kindSupport2_rest_002 kindSupport2_rest_003 kindSupport2_rest_018
    kindSupport2_002 kindSupport2_suffix_003 kindSupport2_002_decode kindSupport2_suffix_decode_003
theorem kindSupport2_suffix_decode_001 : PackedRawNatGrowth.readList 13 532 kindSupport2_rest_001 =
    (kindSupport2_suffix_001, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 500
    kindSupport2_rest_001 kindSupport2_rest_002 kindSupport2_rest_018
    kindSupport2_001 kindSupport2_suffix_002 kindSupport2_001_decode kindSupport2_suffix_decode_002
theorem kindSupport2_suffix_decode_000 : PackedRawNatGrowth.readList 13 564 kindSupport2_rest_000 =
    (kindSupport2_suffix_000, kindSupport2_rest_018) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 532
    kindSupport2_rest_000 kindSupport2_rest_001 kindSupport2_rest_018
    kindSupport2_000 kindSupport2_suffix_001 kindSupport2_000_decode kindSupport2_suffix_decode_001
theorem kindSupport2_eq : kindRows 2 = kindSupport2_suffix_000 := by
  change kindSupports 2 = kindSupport2_suffix_000
  rw [kindSupport2_source]
  exact congrArg Prod.fst kindSupport2_suffix_decode_000
theorem kindTest_large_2 : kindTest 2 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, kindSupport2_suffix_016, kindSupport2_suffix_017, kindSupport2_suffix_018, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport2_000_mask, kindSupport2_001_mask, kindSupport2_002_mask, kindSupport2_003_mask, kindSupport2_004_mask, kindSupport2_005_mask, kindSupport2_006_mask, kindSupport2_007_mask, kindSupport2_008_mask, kindSupport2_009_mask, kindSupport2_010_mask, kindSupport2_011_mask, kindSupport2_012_mask, kindSupport2_013_mask, kindSupport2_014_mask, kindSupport2_015_mask, kindSupport2_016_mask, kindSupport2_017_mask]
    decide +kernel
  · rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, kindSupport2_suffix_016, kindSupport2_suffix_017, kindSupport2_suffix_018, List.all_append, List.all_nil, kindSupport2_000_checked, kindSupport2_001_checked, kindSupport2_002_checked, kindSupport2_003_checked, kindSupport2_004_checked, kindSupport2_005_checked, kindSupport2_006_checked, kindSupport2_007_checked, kindSupport2_008_checked, kindSupport2_009_checked, kindSupport2_010_checked, kindSupport2_011_checked, kindSupport2_012_checked, kindSupport2_013_checked, kindSupport2_014_checked, kindSupport2_015_checked, kindSupport2_016_checked, kindSupport2_017_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
