module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport193Part000
public import RootedSixExtra02GrowthCacheRidgeSupport193Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport193_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport193_rest_010 =
    (ridgeSupport193_suffix_010, ridgeSupport193_rest_010) := by rfl
theorem ridgeSupport193_suffix_decode_009 : PackedRawNatGrowth.readList 13 11 ridgeSupport193_rest_009 =
    (ridgeSupport193_suffix_009, ridgeSupport193_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 11 0
    ridgeSupport193_rest_009 ridgeSupport193_rest_010 ridgeSupport193_rest_010
    ridgeSupport193_009 ridgeSupport193_suffix_010 ridgeSupport193_009_decode ridgeSupport193_suffix_decode_010
theorem ridgeSupport193_suffix_decode_008 : PackedRawNatGrowth.readList 13 43 ridgeSupport193_rest_008 =
    (ridgeSupport193_suffix_008, ridgeSupport193_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 11
    ridgeSupport193_rest_008 ridgeSupport193_rest_009 ridgeSupport193_rest_010
    ridgeSupport193_008 ridgeSupport193_suffix_009 ridgeSupport193_008_decode ridgeSupport193_suffix_decode_009
theorem ridgeSupport193_suffix_decode_007 : PackedRawNatGrowth.readList 13 75 ridgeSupport193_rest_007 =
    (ridgeSupport193_suffix_007, ridgeSupport193_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 43
    ridgeSupport193_rest_007 ridgeSupport193_rest_008 ridgeSupport193_rest_010
    ridgeSupport193_007 ridgeSupport193_suffix_008 ridgeSupport193_007_decode ridgeSupport193_suffix_decode_008
theorem ridgeSupport193_suffix_decode_006 : PackedRawNatGrowth.readList 13 107 ridgeSupport193_rest_006 =
    (ridgeSupport193_suffix_006, ridgeSupport193_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 75
    ridgeSupport193_rest_006 ridgeSupport193_rest_007 ridgeSupport193_rest_010
    ridgeSupport193_006 ridgeSupport193_suffix_007 ridgeSupport193_006_decode ridgeSupport193_suffix_decode_007
theorem ridgeSupport193_suffix_decode_005 : PackedRawNatGrowth.readList 13 139 ridgeSupport193_rest_005 =
    (ridgeSupport193_suffix_005, ridgeSupport193_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 107
    ridgeSupport193_rest_005 ridgeSupport193_rest_006 ridgeSupport193_rest_010
    ridgeSupport193_005 ridgeSupport193_suffix_006 ridgeSupport193_005_decode ridgeSupport193_suffix_decode_006
theorem ridgeSupport193_suffix_decode_004 : PackedRawNatGrowth.readList 13 171 ridgeSupport193_rest_004 =
    (ridgeSupport193_suffix_004, ridgeSupport193_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 139
    ridgeSupport193_rest_004 ridgeSupport193_rest_005 ridgeSupport193_rest_010
    ridgeSupport193_004 ridgeSupport193_suffix_005 ridgeSupport193_004_decode ridgeSupport193_suffix_decode_005
theorem ridgeSupport193_suffix_decode_003 : PackedRawNatGrowth.readList 13 203 ridgeSupport193_rest_003 =
    (ridgeSupport193_suffix_003, ridgeSupport193_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 171
    ridgeSupport193_rest_003 ridgeSupport193_rest_004 ridgeSupport193_rest_010
    ridgeSupport193_003 ridgeSupport193_suffix_004 ridgeSupport193_003_decode ridgeSupport193_suffix_decode_004
theorem ridgeSupport193_suffix_decode_002 : PackedRawNatGrowth.readList 13 235 ridgeSupport193_rest_002 =
    (ridgeSupport193_suffix_002, ridgeSupport193_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 203
    ridgeSupport193_rest_002 ridgeSupport193_rest_003 ridgeSupport193_rest_010
    ridgeSupport193_002 ridgeSupport193_suffix_003 ridgeSupport193_002_decode ridgeSupport193_suffix_decode_003
theorem ridgeSupport193_suffix_decode_001 : PackedRawNatGrowth.readList 13 267 ridgeSupport193_rest_001 =
    (ridgeSupport193_suffix_001, ridgeSupport193_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 235
    ridgeSupport193_rest_001 ridgeSupport193_rest_002 ridgeSupport193_rest_010
    ridgeSupport193_001 ridgeSupport193_suffix_002 ridgeSupport193_001_decode ridgeSupport193_suffix_decode_002
theorem ridgeSupport193_suffix_decode_000 : PackedRawNatGrowth.readList 13 299 ridgeSupport193_rest_000 =
    (ridgeSupport193_suffix_000, ridgeSupport193_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 267
    ridgeSupport193_rest_000 ridgeSupport193_rest_001 ridgeSupport193_rest_010
    ridgeSupport193_000 ridgeSupport193_suffix_001 ridgeSupport193_000_decode ridgeSupport193_suffix_decode_001
theorem ridgeSupport193_eq : candidateRows 193 = ridgeSupport193_suffix_000 := by
  change candidateSupports 193 = ridgeSupport193_suffix_000
  rw [ridgeSupport193_source]
  exact congrArg Prod.fst ridgeSupport193_suffix_decode_000
theorem ridgeTest_large_193 : ridgeTest 193 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport193_eq]
    simp only [ridgeSupport193_suffix_000, ridgeSupport193_suffix_001, ridgeSupport193_suffix_002, ridgeSupport193_suffix_003, ridgeSupport193_suffix_004, ridgeSupport193_suffix_005, ridgeSupport193_suffix_006, ridgeSupport193_suffix_007, ridgeSupport193_suffix_008, ridgeSupport193_suffix_009, ridgeSupport193_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport193_000_mask, ridgeSupport193_001_mask, ridgeSupport193_002_mask, ridgeSupport193_003_mask, ridgeSupport193_004_mask, ridgeSupport193_005_mask, ridgeSupport193_006_mask, ridgeSupport193_007_mask, ridgeSupport193_008_mask, ridgeSupport193_009_mask]
    decide +kernel
  · rw [ridgeSupport193_eq]
    simp only [ridgeSupport193_suffix_000, ridgeSupport193_suffix_001, ridgeSupport193_suffix_002, ridgeSupport193_suffix_003, ridgeSupport193_suffix_004, ridgeSupport193_suffix_005, ridgeSupport193_suffix_006, ridgeSupport193_suffix_007, ridgeSupport193_suffix_008, ridgeSupport193_suffix_009, ridgeSupport193_suffix_010, List.all_append, List.all_nil, ridgeSupport193_000_checked, ridgeSupport193_001_checked, ridgeSupport193_002_checked, ridgeSupport193_003_checked, ridgeSupport193_004_checked, ridgeSupport193_005_checked, ridgeSupport193_006_checked, ridgeSupport193_007_checked, ridgeSupport193_008_checked, ridgeSupport193_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
