module
prelude
public import RootedSixBase03GrowthCacheKindSupport3Part000
public import RootedSixBase03GrowthCacheKindSupport3Part001
public import RootedSixBase03GrowthCacheKindSupport3Part002
public import RootedSixBase03GrowthCacheKindSupport3Part003
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_suffix_decode_027 : PackedRawNatGrowth.readList 13 0 kindSupport3_rest_027 =
    (kindSupport3_suffix_027, kindSupport3_rest_027) := by rfl
theorem kindSupport3_suffix_decode_026 : PackedRawNatGrowth.readList 13 6 kindSupport3_rest_026 =
    (kindSupport3_suffix_026, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 6 0
    kindSupport3_rest_026 kindSupport3_rest_027 kindSupport3_rest_027
    kindSupport3_026 kindSupport3_suffix_027 kindSupport3_026_decode kindSupport3_suffix_decode_027
theorem kindSupport3_suffix_decode_025 : PackedRawNatGrowth.readList 13 38 kindSupport3_rest_025 =
    (kindSupport3_suffix_025, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 6
    kindSupport3_rest_025 kindSupport3_rest_026 kindSupport3_rest_027
    kindSupport3_025 kindSupport3_suffix_026 kindSupport3_025_decode kindSupport3_suffix_decode_026
theorem kindSupport3_suffix_decode_024 : PackedRawNatGrowth.readList 13 70 kindSupport3_rest_024 =
    (kindSupport3_suffix_024, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 38
    kindSupport3_rest_024 kindSupport3_rest_025 kindSupport3_rest_027
    kindSupport3_024 kindSupport3_suffix_025 kindSupport3_024_decode kindSupport3_suffix_decode_025
theorem kindSupport3_suffix_decode_023 : PackedRawNatGrowth.readList 13 102 kindSupport3_rest_023 =
    (kindSupport3_suffix_023, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 70
    kindSupport3_rest_023 kindSupport3_rest_024 kindSupport3_rest_027
    kindSupport3_023 kindSupport3_suffix_024 kindSupport3_023_decode kindSupport3_suffix_decode_024
theorem kindSupport3_suffix_decode_022 : PackedRawNatGrowth.readList 13 134 kindSupport3_rest_022 =
    (kindSupport3_suffix_022, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 102
    kindSupport3_rest_022 kindSupport3_rest_023 kindSupport3_rest_027
    kindSupport3_022 kindSupport3_suffix_023 kindSupport3_022_decode kindSupport3_suffix_decode_023
theorem kindSupport3_suffix_decode_021 : PackedRawNatGrowth.readList 13 166 kindSupport3_rest_021 =
    (kindSupport3_suffix_021, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 134
    kindSupport3_rest_021 kindSupport3_rest_022 kindSupport3_rest_027
    kindSupport3_021 kindSupport3_suffix_022 kindSupport3_021_decode kindSupport3_suffix_decode_022
theorem kindSupport3_suffix_decode_020 : PackedRawNatGrowth.readList 13 198 kindSupport3_rest_020 =
    (kindSupport3_suffix_020, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 166
    kindSupport3_rest_020 kindSupport3_rest_021 kindSupport3_rest_027
    kindSupport3_020 kindSupport3_suffix_021 kindSupport3_020_decode kindSupport3_suffix_decode_021
theorem kindSupport3_suffix_decode_019 : PackedRawNatGrowth.readList 13 230 kindSupport3_rest_019 =
    (kindSupport3_suffix_019, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 198
    kindSupport3_rest_019 kindSupport3_rest_020 kindSupport3_rest_027
    kindSupport3_019 kindSupport3_suffix_020 kindSupport3_019_decode kindSupport3_suffix_decode_020
theorem kindSupport3_suffix_decode_018 : PackedRawNatGrowth.readList 13 262 kindSupport3_rest_018 =
    (kindSupport3_suffix_018, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 230
    kindSupport3_rest_018 kindSupport3_rest_019 kindSupport3_rest_027
    kindSupport3_018 kindSupport3_suffix_019 kindSupport3_018_decode kindSupport3_suffix_decode_019
theorem kindSupport3_suffix_decode_017 : PackedRawNatGrowth.readList 13 294 kindSupport3_rest_017 =
    (kindSupport3_suffix_017, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 262
    kindSupport3_rest_017 kindSupport3_rest_018 kindSupport3_rest_027
    kindSupport3_017 kindSupport3_suffix_018 kindSupport3_017_decode kindSupport3_suffix_decode_018
theorem kindSupport3_suffix_decode_016 : PackedRawNatGrowth.readList 13 326 kindSupport3_rest_016 =
    (kindSupport3_suffix_016, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 294
    kindSupport3_rest_016 kindSupport3_rest_017 kindSupport3_rest_027
    kindSupport3_016 kindSupport3_suffix_017 kindSupport3_016_decode kindSupport3_suffix_decode_017
theorem kindSupport3_suffix_decode_015 : PackedRawNatGrowth.readList 13 358 kindSupport3_rest_015 =
    (kindSupport3_suffix_015, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 326
    kindSupport3_rest_015 kindSupport3_rest_016 kindSupport3_rest_027
    kindSupport3_015 kindSupport3_suffix_016 kindSupport3_015_decode kindSupport3_suffix_decode_016
theorem kindSupport3_suffix_decode_014 : PackedRawNatGrowth.readList 13 390 kindSupport3_rest_014 =
    (kindSupport3_suffix_014, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 358
    kindSupport3_rest_014 kindSupport3_rest_015 kindSupport3_rest_027
    kindSupport3_014 kindSupport3_suffix_015 kindSupport3_014_decode kindSupport3_suffix_decode_015
theorem kindSupport3_suffix_decode_013 : PackedRawNatGrowth.readList 13 422 kindSupport3_rest_013 =
    (kindSupport3_suffix_013, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 390
    kindSupport3_rest_013 kindSupport3_rest_014 kindSupport3_rest_027
    kindSupport3_013 kindSupport3_suffix_014 kindSupport3_013_decode kindSupport3_suffix_decode_014
theorem kindSupport3_suffix_decode_012 : PackedRawNatGrowth.readList 13 454 kindSupport3_rest_012 =
    (kindSupport3_suffix_012, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 422
    kindSupport3_rest_012 kindSupport3_rest_013 kindSupport3_rest_027
    kindSupport3_012 kindSupport3_suffix_013 kindSupport3_012_decode kindSupport3_suffix_decode_013
theorem kindSupport3_suffix_decode_011 : PackedRawNatGrowth.readList 13 486 kindSupport3_rest_011 =
    (kindSupport3_suffix_011, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 454
    kindSupport3_rest_011 kindSupport3_rest_012 kindSupport3_rest_027
    kindSupport3_011 kindSupport3_suffix_012 kindSupport3_011_decode kindSupport3_suffix_decode_012
theorem kindSupport3_suffix_decode_010 : PackedRawNatGrowth.readList 13 518 kindSupport3_rest_010 =
    (kindSupport3_suffix_010, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 486
    kindSupport3_rest_010 kindSupport3_rest_011 kindSupport3_rest_027
    kindSupport3_010 kindSupport3_suffix_011 kindSupport3_010_decode kindSupport3_suffix_decode_011
theorem kindSupport3_suffix_decode_009 : PackedRawNatGrowth.readList 13 550 kindSupport3_rest_009 =
    (kindSupport3_suffix_009, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 518
    kindSupport3_rest_009 kindSupport3_rest_010 kindSupport3_rest_027
    kindSupport3_009 kindSupport3_suffix_010 kindSupport3_009_decode kindSupport3_suffix_decode_010
theorem kindSupport3_suffix_decode_008 : PackedRawNatGrowth.readList 13 582 kindSupport3_rest_008 =
    (kindSupport3_suffix_008, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 550
    kindSupport3_rest_008 kindSupport3_rest_009 kindSupport3_rest_027
    kindSupport3_008 kindSupport3_suffix_009 kindSupport3_008_decode kindSupport3_suffix_decode_009
theorem kindSupport3_suffix_decode_007 : PackedRawNatGrowth.readList 13 614 kindSupport3_rest_007 =
    (kindSupport3_suffix_007, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 582
    kindSupport3_rest_007 kindSupport3_rest_008 kindSupport3_rest_027
    kindSupport3_007 kindSupport3_suffix_008 kindSupport3_007_decode kindSupport3_suffix_decode_008
theorem kindSupport3_suffix_decode_006 : PackedRawNatGrowth.readList 13 646 kindSupport3_rest_006 =
    (kindSupport3_suffix_006, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 614
    kindSupport3_rest_006 kindSupport3_rest_007 kindSupport3_rest_027
    kindSupport3_006 kindSupport3_suffix_007 kindSupport3_006_decode kindSupport3_suffix_decode_007
theorem kindSupport3_suffix_decode_005 : PackedRawNatGrowth.readList 13 678 kindSupport3_rest_005 =
    (kindSupport3_suffix_005, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 646
    kindSupport3_rest_005 kindSupport3_rest_006 kindSupport3_rest_027
    kindSupport3_005 kindSupport3_suffix_006 kindSupport3_005_decode kindSupport3_suffix_decode_006
theorem kindSupport3_suffix_decode_004 : PackedRawNatGrowth.readList 13 710 kindSupport3_rest_004 =
    (kindSupport3_suffix_004, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 678
    kindSupport3_rest_004 kindSupport3_rest_005 kindSupport3_rest_027
    kindSupport3_004 kindSupport3_suffix_005 kindSupport3_004_decode kindSupport3_suffix_decode_005
theorem kindSupport3_suffix_decode_003 : PackedRawNatGrowth.readList 13 742 kindSupport3_rest_003 =
    (kindSupport3_suffix_003, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 710
    kindSupport3_rest_003 kindSupport3_rest_004 kindSupport3_rest_027
    kindSupport3_003 kindSupport3_suffix_004 kindSupport3_003_decode kindSupport3_suffix_decode_004
theorem kindSupport3_suffix_decode_002 : PackedRawNatGrowth.readList 13 774 kindSupport3_rest_002 =
    (kindSupport3_suffix_002, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 742
    kindSupport3_rest_002 kindSupport3_rest_003 kindSupport3_rest_027
    kindSupport3_002 kindSupport3_suffix_003 kindSupport3_002_decode kindSupport3_suffix_decode_003
theorem kindSupport3_suffix_decode_001 : PackedRawNatGrowth.readList 13 806 kindSupport3_rest_001 =
    (kindSupport3_suffix_001, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 774
    kindSupport3_rest_001 kindSupport3_rest_002 kindSupport3_rest_027
    kindSupport3_001 kindSupport3_suffix_002 kindSupport3_001_decode kindSupport3_suffix_decode_002
theorem kindSupport3_suffix_decode_000 : PackedRawNatGrowth.readList 13 838 kindSupport3_rest_000 =
    (kindSupport3_suffix_000, kindSupport3_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 806
    kindSupport3_rest_000 kindSupport3_rest_001 kindSupport3_rest_027
    kindSupport3_000 kindSupport3_suffix_001 kindSupport3_000_decode kindSupport3_suffix_decode_001
theorem kindSupport3_eq : kindSupports 3 = kindSupport3_suffix_000 := by
  rw [kindSupport3_source]
  exact congrArg Prod.fst kindSupport3_suffix_decode_000
theorem kindTest_large_3 : kindTest 3 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show kindRows 3 = kindSupport3_suffix_000 from kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, kindSupport3_suffix_020, kindSupport3_suffix_021, kindSupport3_suffix_022, kindSupport3_suffix_023, kindSupport3_suffix_024, kindSupport3_suffix_025, kindSupport3_suffix_026, kindSupport3_suffix_027, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport3_000_mask, kindSupport3_001_mask, kindSupport3_002_mask, kindSupport3_003_mask, kindSupport3_004_mask, kindSupport3_005_mask, kindSupport3_006_mask, kindSupport3_007_mask, kindSupport3_008_mask, kindSupport3_009_mask, kindSupport3_010_mask, kindSupport3_011_mask, kindSupport3_012_mask, kindSupport3_013_mask, kindSupport3_014_mask, kindSupport3_015_mask, kindSupport3_016_mask, kindSupport3_017_mask, kindSupport3_018_mask, kindSupport3_019_mask, kindSupport3_020_mask, kindSupport3_021_mask, kindSupport3_022_mask, kindSupport3_023_mask, kindSupport3_024_mask, kindSupport3_025_mask, kindSupport3_026_mask]
    decide +kernel
  · rw [show kindRows 3 = kindSupport3_suffix_000 from kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, kindSupport3_suffix_020, kindSupport3_suffix_021, kindSupport3_suffix_022, kindSupport3_suffix_023, kindSupport3_suffix_024, kindSupport3_suffix_025, kindSupport3_suffix_026, kindSupport3_suffix_027, List.all_append, List.all_nil, kindSupport3_000_checked, kindSupport3_001_checked, kindSupport3_002_checked, kindSupport3_003_checked, kindSupport3_004_checked, kindSupport3_005_checked, kindSupport3_006_checked, kindSupport3_007_checked, kindSupport3_008_checked, kindSupport3_009_checked, kindSupport3_010_checked, kindSupport3_011_checked, kindSupport3_012_checked, kindSupport3_013_checked, kindSupport3_014_checked, kindSupport3_015_checked, kindSupport3_016_checked, kindSupport3_017_checked, kindSupport3_018_checked, kindSupport3_019_checked, kindSupport3_020_checked, kindSupport3_021_checked, kindSupport3_022_checked, kindSupport3_023_checked, kindSupport3_024_checked, kindSupport3_025_checked, kindSupport3_026_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
