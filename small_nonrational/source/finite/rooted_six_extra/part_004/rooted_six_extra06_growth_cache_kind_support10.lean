module
prelude
public import RootedSixExtra06GrowthCacheKindSupport10Part000
public import RootedSixExtra06GrowthCacheKindSupport10Part001
public import RootedSixExtra06GrowthCacheKindSupport10Part002
public import RootedSixExtra06GrowthCacheKindSupport10Part003
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport10_suffix_decode_027 : PackedRawNatGrowth.readList 12 0 kindSupport10_rest_027 =
    (kindSupport10_suffix_027, kindSupport10_rest_027) := by rfl
theorem kindSupport10_suffix_decode_026 : PackedRawNatGrowth.readList 12 12 kindSupport10_rest_026 =
    (kindSupport10_suffix_026, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 12 0
    kindSupport10_rest_026 kindSupport10_rest_027 kindSupport10_rest_027
    kindSupport10_026 kindSupport10_suffix_027 kindSupport10_026_decode kindSupport10_suffix_decode_027
theorem kindSupport10_suffix_decode_025 : PackedRawNatGrowth.readList 12 44 kindSupport10_rest_025 =
    (kindSupport10_suffix_025, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 12
    kindSupport10_rest_025 kindSupport10_rest_026 kindSupport10_rest_027
    kindSupport10_025 kindSupport10_suffix_026 kindSupport10_025_decode kindSupport10_suffix_decode_026
theorem kindSupport10_suffix_decode_024 : PackedRawNatGrowth.readList 12 76 kindSupport10_rest_024 =
    (kindSupport10_suffix_024, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 44
    kindSupport10_rest_024 kindSupport10_rest_025 kindSupport10_rest_027
    kindSupport10_024 kindSupport10_suffix_025 kindSupport10_024_decode kindSupport10_suffix_decode_025
theorem kindSupport10_suffix_decode_023 : PackedRawNatGrowth.readList 12 108 kindSupport10_rest_023 =
    (kindSupport10_suffix_023, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 76
    kindSupport10_rest_023 kindSupport10_rest_024 kindSupport10_rest_027
    kindSupport10_023 kindSupport10_suffix_024 kindSupport10_023_decode kindSupport10_suffix_decode_024
theorem kindSupport10_suffix_decode_022 : PackedRawNatGrowth.readList 12 140 kindSupport10_rest_022 =
    (kindSupport10_suffix_022, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 108
    kindSupport10_rest_022 kindSupport10_rest_023 kindSupport10_rest_027
    kindSupport10_022 kindSupport10_suffix_023 kindSupport10_022_decode kindSupport10_suffix_decode_023
theorem kindSupport10_suffix_decode_021 : PackedRawNatGrowth.readList 12 172 kindSupport10_rest_021 =
    (kindSupport10_suffix_021, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 140
    kindSupport10_rest_021 kindSupport10_rest_022 kindSupport10_rest_027
    kindSupport10_021 kindSupport10_suffix_022 kindSupport10_021_decode kindSupport10_suffix_decode_022
theorem kindSupport10_suffix_decode_020 : PackedRawNatGrowth.readList 12 204 kindSupport10_rest_020 =
    (kindSupport10_suffix_020, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 172
    kindSupport10_rest_020 kindSupport10_rest_021 kindSupport10_rest_027
    kindSupport10_020 kindSupport10_suffix_021 kindSupport10_020_decode kindSupport10_suffix_decode_021
theorem kindSupport10_suffix_decode_019 : PackedRawNatGrowth.readList 12 236 kindSupport10_rest_019 =
    (kindSupport10_suffix_019, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 204
    kindSupport10_rest_019 kindSupport10_rest_020 kindSupport10_rest_027
    kindSupport10_019 kindSupport10_suffix_020 kindSupport10_019_decode kindSupport10_suffix_decode_020
theorem kindSupport10_suffix_decode_018 : PackedRawNatGrowth.readList 12 268 kindSupport10_rest_018 =
    (kindSupport10_suffix_018, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 236
    kindSupport10_rest_018 kindSupport10_rest_019 kindSupport10_rest_027
    kindSupport10_018 kindSupport10_suffix_019 kindSupport10_018_decode kindSupport10_suffix_decode_019
theorem kindSupport10_suffix_decode_017 : PackedRawNatGrowth.readList 12 300 kindSupport10_rest_017 =
    (kindSupport10_suffix_017, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 268
    kindSupport10_rest_017 kindSupport10_rest_018 kindSupport10_rest_027
    kindSupport10_017 kindSupport10_suffix_018 kindSupport10_017_decode kindSupport10_suffix_decode_018
theorem kindSupport10_suffix_decode_016 : PackedRawNatGrowth.readList 12 332 kindSupport10_rest_016 =
    (kindSupport10_suffix_016, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 300
    kindSupport10_rest_016 kindSupport10_rest_017 kindSupport10_rest_027
    kindSupport10_016 kindSupport10_suffix_017 kindSupport10_016_decode kindSupport10_suffix_decode_017
theorem kindSupport10_suffix_decode_015 : PackedRawNatGrowth.readList 12 364 kindSupport10_rest_015 =
    (kindSupport10_suffix_015, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 332
    kindSupport10_rest_015 kindSupport10_rest_016 kindSupport10_rest_027
    kindSupport10_015 kindSupport10_suffix_016 kindSupport10_015_decode kindSupport10_suffix_decode_016
theorem kindSupport10_suffix_decode_014 : PackedRawNatGrowth.readList 12 396 kindSupport10_rest_014 =
    (kindSupport10_suffix_014, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 364
    kindSupport10_rest_014 kindSupport10_rest_015 kindSupport10_rest_027
    kindSupport10_014 kindSupport10_suffix_015 kindSupport10_014_decode kindSupport10_suffix_decode_015
theorem kindSupport10_suffix_decode_013 : PackedRawNatGrowth.readList 12 428 kindSupport10_rest_013 =
    (kindSupport10_suffix_013, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 396
    kindSupport10_rest_013 kindSupport10_rest_014 kindSupport10_rest_027
    kindSupport10_013 kindSupport10_suffix_014 kindSupport10_013_decode kindSupport10_suffix_decode_014
theorem kindSupport10_suffix_decode_012 : PackedRawNatGrowth.readList 12 460 kindSupport10_rest_012 =
    (kindSupport10_suffix_012, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 428
    kindSupport10_rest_012 kindSupport10_rest_013 kindSupport10_rest_027
    kindSupport10_012 kindSupport10_suffix_013 kindSupport10_012_decode kindSupport10_suffix_decode_013
theorem kindSupport10_suffix_decode_011 : PackedRawNatGrowth.readList 12 492 kindSupport10_rest_011 =
    (kindSupport10_suffix_011, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 460
    kindSupport10_rest_011 kindSupport10_rest_012 kindSupport10_rest_027
    kindSupport10_011 kindSupport10_suffix_012 kindSupport10_011_decode kindSupport10_suffix_decode_012
theorem kindSupport10_suffix_decode_010 : PackedRawNatGrowth.readList 12 524 kindSupport10_rest_010 =
    (kindSupport10_suffix_010, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 492
    kindSupport10_rest_010 kindSupport10_rest_011 kindSupport10_rest_027
    kindSupport10_010 kindSupport10_suffix_011 kindSupport10_010_decode kindSupport10_suffix_decode_011
theorem kindSupport10_suffix_decode_009 : PackedRawNatGrowth.readList 12 556 kindSupport10_rest_009 =
    (kindSupport10_suffix_009, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 524
    kindSupport10_rest_009 kindSupport10_rest_010 kindSupport10_rest_027
    kindSupport10_009 kindSupport10_suffix_010 kindSupport10_009_decode kindSupport10_suffix_decode_010
theorem kindSupport10_suffix_decode_008 : PackedRawNatGrowth.readList 12 588 kindSupport10_rest_008 =
    (kindSupport10_suffix_008, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 556
    kindSupport10_rest_008 kindSupport10_rest_009 kindSupport10_rest_027
    kindSupport10_008 kindSupport10_suffix_009 kindSupport10_008_decode kindSupport10_suffix_decode_009
theorem kindSupport10_suffix_decode_007 : PackedRawNatGrowth.readList 12 620 kindSupport10_rest_007 =
    (kindSupport10_suffix_007, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 588
    kindSupport10_rest_007 kindSupport10_rest_008 kindSupport10_rest_027
    kindSupport10_007 kindSupport10_suffix_008 kindSupport10_007_decode kindSupport10_suffix_decode_008
theorem kindSupport10_suffix_decode_006 : PackedRawNatGrowth.readList 12 652 kindSupport10_rest_006 =
    (kindSupport10_suffix_006, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 620
    kindSupport10_rest_006 kindSupport10_rest_007 kindSupport10_rest_027
    kindSupport10_006 kindSupport10_suffix_007 kindSupport10_006_decode kindSupport10_suffix_decode_007
theorem kindSupport10_suffix_decode_005 : PackedRawNatGrowth.readList 12 684 kindSupport10_rest_005 =
    (kindSupport10_suffix_005, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 652
    kindSupport10_rest_005 kindSupport10_rest_006 kindSupport10_rest_027
    kindSupport10_005 kindSupport10_suffix_006 kindSupport10_005_decode kindSupport10_suffix_decode_006
theorem kindSupport10_suffix_decode_004 : PackedRawNatGrowth.readList 12 716 kindSupport10_rest_004 =
    (kindSupport10_suffix_004, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 684
    kindSupport10_rest_004 kindSupport10_rest_005 kindSupport10_rest_027
    kindSupport10_004 kindSupport10_suffix_005 kindSupport10_004_decode kindSupport10_suffix_decode_005
theorem kindSupport10_suffix_decode_003 : PackedRawNatGrowth.readList 12 748 kindSupport10_rest_003 =
    (kindSupport10_suffix_003, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 716
    kindSupport10_rest_003 kindSupport10_rest_004 kindSupport10_rest_027
    kindSupport10_003 kindSupport10_suffix_004 kindSupport10_003_decode kindSupport10_suffix_decode_004
theorem kindSupport10_suffix_decode_002 : PackedRawNatGrowth.readList 12 780 kindSupport10_rest_002 =
    (kindSupport10_suffix_002, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 748
    kindSupport10_rest_002 kindSupport10_rest_003 kindSupport10_rest_027
    kindSupport10_002 kindSupport10_suffix_003 kindSupport10_002_decode kindSupport10_suffix_decode_003
theorem kindSupport10_suffix_decode_001 : PackedRawNatGrowth.readList 12 812 kindSupport10_rest_001 =
    (kindSupport10_suffix_001, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 780
    kindSupport10_rest_001 kindSupport10_rest_002 kindSupport10_rest_027
    kindSupport10_001 kindSupport10_suffix_002 kindSupport10_001_decode kindSupport10_suffix_decode_002
theorem kindSupport10_suffix_decode_000 : PackedRawNatGrowth.readList 12 844 kindSupport10_rest_000 =
    (kindSupport10_suffix_000, kindSupport10_rest_027) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 812
    kindSupport10_rest_000 kindSupport10_rest_001 kindSupport10_rest_027
    kindSupport10_000 kindSupport10_suffix_001 kindSupport10_000_decode kindSupport10_suffix_decode_001
theorem kindSupport10_eq : kindRows 10 = kindSupport10_suffix_000 := by
  change kindSupports 10 = kindSupport10_suffix_000
  rw [kindSupport10_source]
  exact congrArg Prod.fst kindSupport10_suffix_decode_000
theorem kindTest_large_10 : kindTest 10 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport10_eq]
    simp only [kindSupport10_suffix_000, kindSupport10_suffix_001, kindSupport10_suffix_002, kindSupport10_suffix_003, kindSupport10_suffix_004, kindSupport10_suffix_005, kindSupport10_suffix_006, kindSupport10_suffix_007, kindSupport10_suffix_008, kindSupport10_suffix_009, kindSupport10_suffix_010, kindSupport10_suffix_011, kindSupport10_suffix_012, kindSupport10_suffix_013, kindSupport10_suffix_014, kindSupport10_suffix_015, kindSupport10_suffix_016, kindSupport10_suffix_017, kindSupport10_suffix_018, kindSupport10_suffix_019, kindSupport10_suffix_020, kindSupport10_suffix_021, kindSupport10_suffix_022, kindSupport10_suffix_023, kindSupport10_suffix_024, kindSupport10_suffix_025, kindSupport10_suffix_026, kindSupport10_suffix_027, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport10_000_mask, kindSupport10_001_mask, kindSupport10_002_mask, kindSupport10_003_mask, kindSupport10_004_mask, kindSupport10_005_mask, kindSupport10_006_mask, kindSupport10_007_mask, kindSupport10_008_mask, kindSupport10_009_mask, kindSupport10_010_mask, kindSupport10_011_mask, kindSupport10_012_mask, kindSupport10_013_mask, kindSupport10_014_mask, kindSupport10_015_mask, kindSupport10_016_mask, kindSupport10_017_mask, kindSupport10_018_mask, kindSupport10_019_mask, kindSupport10_020_mask, kindSupport10_021_mask, kindSupport10_022_mask, kindSupport10_023_mask, kindSupport10_024_mask, kindSupport10_025_mask, kindSupport10_026_mask]
    decide +kernel
  · rw [kindSupport10_eq]
    simp only [kindSupport10_suffix_000, kindSupport10_suffix_001, kindSupport10_suffix_002, kindSupport10_suffix_003, kindSupport10_suffix_004, kindSupport10_suffix_005, kindSupport10_suffix_006, kindSupport10_suffix_007, kindSupport10_suffix_008, kindSupport10_suffix_009, kindSupport10_suffix_010, kindSupport10_suffix_011, kindSupport10_suffix_012, kindSupport10_suffix_013, kindSupport10_suffix_014, kindSupport10_suffix_015, kindSupport10_suffix_016, kindSupport10_suffix_017, kindSupport10_suffix_018, kindSupport10_suffix_019, kindSupport10_suffix_020, kindSupport10_suffix_021, kindSupport10_suffix_022, kindSupport10_suffix_023, kindSupport10_suffix_024, kindSupport10_suffix_025, kindSupport10_suffix_026, kindSupport10_suffix_027, List.all_append, List.all_nil, kindSupport10_000_checked, kindSupport10_001_checked, kindSupport10_002_checked, kindSupport10_003_checked, kindSupport10_004_checked, kindSupport10_005_checked, kindSupport10_006_checked, kindSupport10_007_checked, kindSupport10_008_checked, kindSupport10_009_checked, kindSupport10_010_checked, kindSupport10_011_checked, kindSupport10_012_checked, kindSupport10_013_checked, kindSupport10_014_checked, kindSupport10_015_checked, kindSupport10_016_checked, kindSupport10_017_checked, kindSupport10_018_checked, kindSupport10_019_checked, kindSupport10_020_checked, kindSupport10_021_checked, kindSupport10_022_checked, kindSupport10_023_checked, kindSupport10_024_checked, kindSupport10_025_checked, kindSupport10_026_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
