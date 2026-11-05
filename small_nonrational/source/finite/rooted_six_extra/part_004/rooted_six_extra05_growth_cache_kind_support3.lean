module
prelude
public import RootedSixExtra05GrowthCacheKindSupport3Part000
public import RootedSixExtra05GrowthCacheKindSupport3Part001
public import RootedSixExtra05GrowthCacheKindSupport3Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_suffix_decode_019 : PackedRawNatGrowth.readList 12 0 kindSupport3_rest_019 =
    (kindSupport3_suffix_019, kindSupport3_rest_019) := by rfl
theorem kindSupport3_suffix_decode_018 : PackedRawNatGrowth.readList 12 30 kindSupport3_rest_018 =
    (kindSupport3_suffix_018, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 30 0
    kindSupport3_rest_018 kindSupport3_rest_019 kindSupport3_rest_019
    kindSupport3_018 kindSupport3_suffix_019 kindSupport3_018_decode kindSupport3_suffix_decode_019
theorem kindSupport3_suffix_decode_017 : PackedRawNatGrowth.readList 12 62 kindSupport3_rest_017 =
    (kindSupport3_suffix_017, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 30
    kindSupport3_rest_017 kindSupport3_rest_018 kindSupport3_rest_019
    kindSupport3_017 kindSupport3_suffix_018 kindSupport3_017_decode kindSupport3_suffix_decode_018
theorem kindSupport3_suffix_decode_016 : PackedRawNatGrowth.readList 12 94 kindSupport3_rest_016 =
    (kindSupport3_suffix_016, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 62
    kindSupport3_rest_016 kindSupport3_rest_017 kindSupport3_rest_019
    kindSupport3_016 kindSupport3_suffix_017 kindSupport3_016_decode kindSupport3_suffix_decode_017
theorem kindSupport3_suffix_decode_015 : PackedRawNatGrowth.readList 12 126 kindSupport3_rest_015 =
    (kindSupport3_suffix_015, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 94
    kindSupport3_rest_015 kindSupport3_rest_016 kindSupport3_rest_019
    kindSupport3_015 kindSupport3_suffix_016 kindSupport3_015_decode kindSupport3_suffix_decode_016
theorem kindSupport3_suffix_decode_014 : PackedRawNatGrowth.readList 12 158 kindSupport3_rest_014 =
    (kindSupport3_suffix_014, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 126
    kindSupport3_rest_014 kindSupport3_rest_015 kindSupport3_rest_019
    kindSupport3_014 kindSupport3_suffix_015 kindSupport3_014_decode kindSupport3_suffix_decode_015
theorem kindSupport3_suffix_decode_013 : PackedRawNatGrowth.readList 12 190 kindSupport3_rest_013 =
    (kindSupport3_suffix_013, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 158
    kindSupport3_rest_013 kindSupport3_rest_014 kindSupport3_rest_019
    kindSupport3_013 kindSupport3_suffix_014 kindSupport3_013_decode kindSupport3_suffix_decode_014
theorem kindSupport3_suffix_decode_012 : PackedRawNatGrowth.readList 12 222 kindSupport3_rest_012 =
    (kindSupport3_suffix_012, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 190
    kindSupport3_rest_012 kindSupport3_rest_013 kindSupport3_rest_019
    kindSupport3_012 kindSupport3_suffix_013 kindSupport3_012_decode kindSupport3_suffix_decode_013
theorem kindSupport3_suffix_decode_011 : PackedRawNatGrowth.readList 12 254 kindSupport3_rest_011 =
    (kindSupport3_suffix_011, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 222
    kindSupport3_rest_011 kindSupport3_rest_012 kindSupport3_rest_019
    kindSupport3_011 kindSupport3_suffix_012 kindSupport3_011_decode kindSupport3_suffix_decode_012
theorem kindSupport3_suffix_decode_010 : PackedRawNatGrowth.readList 12 286 kindSupport3_rest_010 =
    (kindSupport3_suffix_010, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 254
    kindSupport3_rest_010 kindSupport3_rest_011 kindSupport3_rest_019
    kindSupport3_010 kindSupport3_suffix_011 kindSupport3_010_decode kindSupport3_suffix_decode_011
theorem kindSupport3_suffix_decode_009 : PackedRawNatGrowth.readList 12 318 kindSupport3_rest_009 =
    (kindSupport3_suffix_009, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 286
    kindSupport3_rest_009 kindSupport3_rest_010 kindSupport3_rest_019
    kindSupport3_009 kindSupport3_suffix_010 kindSupport3_009_decode kindSupport3_suffix_decode_010
theorem kindSupport3_suffix_decode_008 : PackedRawNatGrowth.readList 12 350 kindSupport3_rest_008 =
    (kindSupport3_suffix_008, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 318
    kindSupport3_rest_008 kindSupport3_rest_009 kindSupport3_rest_019
    kindSupport3_008 kindSupport3_suffix_009 kindSupport3_008_decode kindSupport3_suffix_decode_009
theorem kindSupport3_suffix_decode_007 : PackedRawNatGrowth.readList 12 382 kindSupport3_rest_007 =
    (kindSupport3_suffix_007, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 350
    kindSupport3_rest_007 kindSupport3_rest_008 kindSupport3_rest_019
    kindSupport3_007 kindSupport3_suffix_008 kindSupport3_007_decode kindSupport3_suffix_decode_008
theorem kindSupport3_suffix_decode_006 : PackedRawNatGrowth.readList 12 414 kindSupport3_rest_006 =
    (kindSupport3_suffix_006, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 382
    kindSupport3_rest_006 kindSupport3_rest_007 kindSupport3_rest_019
    kindSupport3_006 kindSupport3_suffix_007 kindSupport3_006_decode kindSupport3_suffix_decode_007
theorem kindSupport3_suffix_decode_005 : PackedRawNatGrowth.readList 12 446 kindSupport3_rest_005 =
    (kindSupport3_suffix_005, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 414
    kindSupport3_rest_005 kindSupport3_rest_006 kindSupport3_rest_019
    kindSupport3_005 kindSupport3_suffix_006 kindSupport3_005_decode kindSupport3_suffix_decode_006
theorem kindSupport3_suffix_decode_004 : PackedRawNatGrowth.readList 12 478 kindSupport3_rest_004 =
    (kindSupport3_suffix_004, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 446
    kindSupport3_rest_004 kindSupport3_rest_005 kindSupport3_rest_019
    kindSupport3_004 kindSupport3_suffix_005 kindSupport3_004_decode kindSupport3_suffix_decode_005
theorem kindSupport3_suffix_decode_003 : PackedRawNatGrowth.readList 12 510 kindSupport3_rest_003 =
    (kindSupport3_suffix_003, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 478
    kindSupport3_rest_003 kindSupport3_rest_004 kindSupport3_rest_019
    kindSupport3_003 kindSupport3_suffix_004 kindSupport3_003_decode kindSupport3_suffix_decode_004
theorem kindSupport3_suffix_decode_002 : PackedRawNatGrowth.readList 12 542 kindSupport3_rest_002 =
    (kindSupport3_suffix_002, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 510
    kindSupport3_rest_002 kindSupport3_rest_003 kindSupport3_rest_019
    kindSupport3_002 kindSupport3_suffix_003 kindSupport3_002_decode kindSupport3_suffix_decode_003
theorem kindSupport3_suffix_decode_001 : PackedRawNatGrowth.readList 12 574 kindSupport3_rest_001 =
    (kindSupport3_suffix_001, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 542
    kindSupport3_rest_001 kindSupport3_rest_002 kindSupport3_rest_019
    kindSupport3_001 kindSupport3_suffix_002 kindSupport3_001_decode kindSupport3_suffix_decode_002
theorem kindSupport3_suffix_decode_000 : PackedRawNatGrowth.readList 12 606 kindSupport3_rest_000 =
    (kindSupport3_suffix_000, kindSupport3_rest_019) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 574
    kindSupport3_rest_000 kindSupport3_rest_001 kindSupport3_rest_019
    kindSupport3_000 kindSupport3_suffix_001 kindSupport3_000_decode kindSupport3_suffix_decode_001
theorem kindSupport3_eq : kindRows 3 = kindSupport3_suffix_000 := by
  change kindSupports 3 = kindSupport3_suffix_000
  rw [kindSupport3_source]
  exact congrArg Prod.fst kindSupport3_suffix_decode_000
theorem kindTest_large_3 : kindTest 3 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport3_000_mask, kindSupport3_001_mask, kindSupport3_002_mask, kindSupport3_003_mask, kindSupport3_004_mask, kindSupport3_005_mask, kindSupport3_006_mask, kindSupport3_007_mask, kindSupport3_008_mask, kindSupport3_009_mask, kindSupport3_010_mask, kindSupport3_011_mask, kindSupport3_012_mask, kindSupport3_013_mask, kindSupport3_014_mask, kindSupport3_015_mask, kindSupport3_016_mask, kindSupport3_017_mask, kindSupport3_018_mask]
    decide +kernel
  · rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, List.all_append, List.all_nil, kindSupport3_000_checked, kindSupport3_001_checked, kindSupport3_002_checked, kindSupport3_003_checked, kindSupport3_004_checked, kindSupport3_005_checked, kindSupport3_006_checked, kindSupport3_007_checked, kindSupport3_008_checked, kindSupport3_009_checked, kindSupport3_010_checked, kindSupport3_011_checked, kindSupport3_012_checked, kindSupport3_013_checked, kindSupport3_014_checked, kindSupport3_015_checked, kindSupport3_016_checked, kindSupport3_017_checked, kindSupport3_018_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
