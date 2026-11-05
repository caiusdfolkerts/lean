module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport960Part000
public import RootedSixExtra02GrowthCacheRidgeSupport960Part001
public import RootedSixExtra02GrowthCacheRidgeSupport960Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport960_suffix_decode_020 : PackedRawNatGrowth.readList 13 0 ridgeSupport960_rest_020 =
    (ridgeSupport960_suffix_020, ridgeSupport960_rest_020) := by rfl
theorem ridgeSupport960_suffix_decode_019 : PackedRawNatGrowth.readList 13 10 ridgeSupport960_rest_019 =
    (ridgeSupport960_suffix_019, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 10 0
    ridgeSupport960_rest_019 ridgeSupport960_rest_020 ridgeSupport960_rest_020
    ridgeSupport960_019 ridgeSupport960_suffix_020 ridgeSupport960_019_decode ridgeSupport960_suffix_decode_020
theorem ridgeSupport960_suffix_decode_018 : PackedRawNatGrowth.readList 13 42 ridgeSupport960_rest_018 =
    (ridgeSupport960_suffix_018, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 10
    ridgeSupport960_rest_018 ridgeSupport960_rest_019 ridgeSupport960_rest_020
    ridgeSupport960_018 ridgeSupport960_suffix_019 ridgeSupport960_018_decode ridgeSupport960_suffix_decode_019
theorem ridgeSupport960_suffix_decode_017 : PackedRawNatGrowth.readList 13 74 ridgeSupport960_rest_017 =
    (ridgeSupport960_suffix_017, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 42
    ridgeSupport960_rest_017 ridgeSupport960_rest_018 ridgeSupport960_rest_020
    ridgeSupport960_017 ridgeSupport960_suffix_018 ridgeSupport960_017_decode ridgeSupport960_suffix_decode_018
theorem ridgeSupport960_suffix_decode_016 : PackedRawNatGrowth.readList 13 106 ridgeSupport960_rest_016 =
    (ridgeSupport960_suffix_016, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 74
    ridgeSupport960_rest_016 ridgeSupport960_rest_017 ridgeSupport960_rest_020
    ridgeSupport960_016 ridgeSupport960_suffix_017 ridgeSupport960_016_decode ridgeSupport960_suffix_decode_017
theorem ridgeSupport960_suffix_decode_015 : PackedRawNatGrowth.readList 13 138 ridgeSupport960_rest_015 =
    (ridgeSupport960_suffix_015, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 106
    ridgeSupport960_rest_015 ridgeSupport960_rest_016 ridgeSupport960_rest_020
    ridgeSupport960_015 ridgeSupport960_suffix_016 ridgeSupport960_015_decode ridgeSupport960_suffix_decode_016
theorem ridgeSupport960_suffix_decode_014 : PackedRawNatGrowth.readList 13 170 ridgeSupport960_rest_014 =
    (ridgeSupport960_suffix_014, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 138
    ridgeSupport960_rest_014 ridgeSupport960_rest_015 ridgeSupport960_rest_020
    ridgeSupport960_014 ridgeSupport960_suffix_015 ridgeSupport960_014_decode ridgeSupport960_suffix_decode_015
theorem ridgeSupport960_suffix_decode_013 : PackedRawNatGrowth.readList 13 202 ridgeSupport960_rest_013 =
    (ridgeSupport960_suffix_013, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 170
    ridgeSupport960_rest_013 ridgeSupport960_rest_014 ridgeSupport960_rest_020
    ridgeSupport960_013 ridgeSupport960_suffix_014 ridgeSupport960_013_decode ridgeSupport960_suffix_decode_014
theorem ridgeSupport960_suffix_decode_012 : PackedRawNatGrowth.readList 13 234 ridgeSupport960_rest_012 =
    (ridgeSupport960_suffix_012, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 202
    ridgeSupport960_rest_012 ridgeSupport960_rest_013 ridgeSupport960_rest_020
    ridgeSupport960_012 ridgeSupport960_suffix_013 ridgeSupport960_012_decode ridgeSupport960_suffix_decode_013
theorem ridgeSupport960_suffix_decode_011 : PackedRawNatGrowth.readList 13 266 ridgeSupport960_rest_011 =
    (ridgeSupport960_suffix_011, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 234
    ridgeSupport960_rest_011 ridgeSupport960_rest_012 ridgeSupport960_rest_020
    ridgeSupport960_011 ridgeSupport960_suffix_012 ridgeSupport960_011_decode ridgeSupport960_suffix_decode_012
theorem ridgeSupport960_suffix_decode_010 : PackedRawNatGrowth.readList 13 298 ridgeSupport960_rest_010 =
    (ridgeSupport960_suffix_010, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 266
    ridgeSupport960_rest_010 ridgeSupport960_rest_011 ridgeSupport960_rest_020
    ridgeSupport960_010 ridgeSupport960_suffix_011 ridgeSupport960_010_decode ridgeSupport960_suffix_decode_011
theorem ridgeSupport960_suffix_decode_009 : PackedRawNatGrowth.readList 13 330 ridgeSupport960_rest_009 =
    (ridgeSupport960_suffix_009, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 298
    ridgeSupport960_rest_009 ridgeSupport960_rest_010 ridgeSupport960_rest_020
    ridgeSupport960_009 ridgeSupport960_suffix_010 ridgeSupport960_009_decode ridgeSupport960_suffix_decode_010
theorem ridgeSupport960_suffix_decode_008 : PackedRawNatGrowth.readList 13 362 ridgeSupport960_rest_008 =
    (ridgeSupport960_suffix_008, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 330
    ridgeSupport960_rest_008 ridgeSupport960_rest_009 ridgeSupport960_rest_020
    ridgeSupport960_008 ridgeSupport960_suffix_009 ridgeSupport960_008_decode ridgeSupport960_suffix_decode_009
theorem ridgeSupport960_suffix_decode_007 : PackedRawNatGrowth.readList 13 394 ridgeSupport960_rest_007 =
    (ridgeSupport960_suffix_007, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 362
    ridgeSupport960_rest_007 ridgeSupport960_rest_008 ridgeSupport960_rest_020
    ridgeSupport960_007 ridgeSupport960_suffix_008 ridgeSupport960_007_decode ridgeSupport960_suffix_decode_008
theorem ridgeSupport960_suffix_decode_006 : PackedRawNatGrowth.readList 13 426 ridgeSupport960_rest_006 =
    (ridgeSupport960_suffix_006, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 394
    ridgeSupport960_rest_006 ridgeSupport960_rest_007 ridgeSupport960_rest_020
    ridgeSupport960_006 ridgeSupport960_suffix_007 ridgeSupport960_006_decode ridgeSupport960_suffix_decode_007
theorem ridgeSupport960_suffix_decode_005 : PackedRawNatGrowth.readList 13 458 ridgeSupport960_rest_005 =
    (ridgeSupport960_suffix_005, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 426
    ridgeSupport960_rest_005 ridgeSupport960_rest_006 ridgeSupport960_rest_020
    ridgeSupport960_005 ridgeSupport960_suffix_006 ridgeSupport960_005_decode ridgeSupport960_suffix_decode_006
theorem ridgeSupport960_suffix_decode_004 : PackedRawNatGrowth.readList 13 490 ridgeSupport960_rest_004 =
    (ridgeSupport960_suffix_004, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 458
    ridgeSupport960_rest_004 ridgeSupport960_rest_005 ridgeSupport960_rest_020
    ridgeSupport960_004 ridgeSupport960_suffix_005 ridgeSupport960_004_decode ridgeSupport960_suffix_decode_005
theorem ridgeSupport960_suffix_decode_003 : PackedRawNatGrowth.readList 13 522 ridgeSupport960_rest_003 =
    (ridgeSupport960_suffix_003, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 490
    ridgeSupport960_rest_003 ridgeSupport960_rest_004 ridgeSupport960_rest_020
    ridgeSupport960_003 ridgeSupport960_suffix_004 ridgeSupport960_003_decode ridgeSupport960_suffix_decode_004
theorem ridgeSupport960_suffix_decode_002 : PackedRawNatGrowth.readList 13 554 ridgeSupport960_rest_002 =
    (ridgeSupport960_suffix_002, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 522
    ridgeSupport960_rest_002 ridgeSupport960_rest_003 ridgeSupport960_rest_020
    ridgeSupport960_002 ridgeSupport960_suffix_003 ridgeSupport960_002_decode ridgeSupport960_suffix_decode_003
theorem ridgeSupport960_suffix_decode_001 : PackedRawNatGrowth.readList 13 586 ridgeSupport960_rest_001 =
    (ridgeSupport960_suffix_001, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 554
    ridgeSupport960_rest_001 ridgeSupport960_rest_002 ridgeSupport960_rest_020
    ridgeSupport960_001 ridgeSupport960_suffix_002 ridgeSupport960_001_decode ridgeSupport960_suffix_decode_002
theorem ridgeSupport960_suffix_decode_000 : PackedRawNatGrowth.readList 13 618 ridgeSupport960_rest_000 =
    (ridgeSupport960_suffix_000, ridgeSupport960_rest_020) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 586
    ridgeSupport960_rest_000 ridgeSupport960_rest_001 ridgeSupport960_rest_020
    ridgeSupport960_000 ridgeSupport960_suffix_001 ridgeSupport960_000_decode ridgeSupport960_suffix_decode_001
theorem ridgeSupport960_eq : candidateRows 960 = ridgeSupport960_suffix_000 := by
  change candidateSupports 960 = ridgeSupport960_suffix_000
  rw [ridgeSupport960_source]
  exact congrArg Prod.fst ridgeSupport960_suffix_decode_000
theorem ridgeTest_large_960 : ridgeTest 960 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, ridgeSupport960_suffix_010, ridgeSupport960_suffix_011, ridgeSupport960_suffix_012, ridgeSupport960_suffix_013, ridgeSupport960_suffix_014, ridgeSupport960_suffix_015, ridgeSupport960_suffix_016, ridgeSupport960_suffix_017, ridgeSupport960_suffix_018, ridgeSupport960_suffix_019, ridgeSupport960_suffix_020, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport960_000_mask, ridgeSupport960_001_mask, ridgeSupport960_002_mask, ridgeSupport960_003_mask, ridgeSupport960_004_mask, ridgeSupport960_005_mask, ridgeSupport960_006_mask, ridgeSupport960_007_mask, ridgeSupport960_008_mask, ridgeSupport960_009_mask, ridgeSupport960_010_mask, ridgeSupport960_011_mask, ridgeSupport960_012_mask, ridgeSupport960_013_mask, ridgeSupport960_014_mask, ridgeSupport960_015_mask, ridgeSupport960_016_mask, ridgeSupport960_017_mask, ridgeSupport960_018_mask, ridgeSupport960_019_mask]
    decide +kernel
  · rw [ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, ridgeSupport960_suffix_010, ridgeSupport960_suffix_011, ridgeSupport960_suffix_012, ridgeSupport960_suffix_013, ridgeSupport960_suffix_014, ridgeSupport960_suffix_015, ridgeSupport960_suffix_016, ridgeSupport960_suffix_017, ridgeSupport960_suffix_018, ridgeSupport960_suffix_019, ridgeSupport960_suffix_020, List.all_append, List.all_nil, ridgeSupport960_000_checked, ridgeSupport960_001_checked, ridgeSupport960_002_checked, ridgeSupport960_003_checked, ridgeSupport960_004_checked, ridgeSupport960_005_checked, ridgeSupport960_006_checked, ridgeSupport960_007_checked, ridgeSupport960_008_checked, ridgeSupport960_009_checked, ridgeSupport960_010_checked, ridgeSupport960_011_checked, ridgeSupport960_012_checked, ridgeSupport960_013_checked, ridgeSupport960_014_checked, ridgeSupport960_015_checked, ridgeSupport960_016_checked, ridgeSupport960_017_checked, ridgeSupport960_018_checked, ridgeSupport960_019_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
