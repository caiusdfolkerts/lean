module
prelude
public import RootedSixExtra03GrowthCacheRidgeSupport832Part000
public import RootedSixExtra03GrowthCacheRidgeSupport832Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport832_suffix_decode_014 : PackedRawNatGrowth.readList 12 0 ridgeSupport832_rest_014 =
    (ridgeSupport832_suffix_014, ridgeSupport832_rest_014) := by rfl
theorem ridgeSupport832_suffix_decode_013 : PackedRawNatGrowth.readList 12 29 ridgeSupport832_rest_013 =
    (ridgeSupport832_suffix_013, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 29 0
    ridgeSupport832_rest_013 ridgeSupport832_rest_014 ridgeSupport832_rest_014
    ridgeSupport832_013 ridgeSupport832_suffix_014 ridgeSupport832_013_decode ridgeSupport832_suffix_decode_014
theorem ridgeSupport832_suffix_decode_012 : PackedRawNatGrowth.readList 12 61 ridgeSupport832_rest_012 =
    (ridgeSupport832_suffix_012, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 29
    ridgeSupport832_rest_012 ridgeSupport832_rest_013 ridgeSupport832_rest_014
    ridgeSupport832_012 ridgeSupport832_suffix_013 ridgeSupport832_012_decode ridgeSupport832_suffix_decode_013
theorem ridgeSupport832_suffix_decode_011 : PackedRawNatGrowth.readList 12 93 ridgeSupport832_rest_011 =
    (ridgeSupport832_suffix_011, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 61
    ridgeSupport832_rest_011 ridgeSupport832_rest_012 ridgeSupport832_rest_014
    ridgeSupport832_011 ridgeSupport832_suffix_012 ridgeSupport832_011_decode ridgeSupport832_suffix_decode_012
theorem ridgeSupport832_suffix_decode_010 : PackedRawNatGrowth.readList 12 125 ridgeSupport832_rest_010 =
    (ridgeSupport832_suffix_010, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 93
    ridgeSupport832_rest_010 ridgeSupport832_rest_011 ridgeSupport832_rest_014
    ridgeSupport832_010 ridgeSupport832_suffix_011 ridgeSupport832_010_decode ridgeSupport832_suffix_decode_011
theorem ridgeSupport832_suffix_decode_009 : PackedRawNatGrowth.readList 12 157 ridgeSupport832_rest_009 =
    (ridgeSupport832_suffix_009, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 125
    ridgeSupport832_rest_009 ridgeSupport832_rest_010 ridgeSupport832_rest_014
    ridgeSupport832_009 ridgeSupport832_suffix_010 ridgeSupport832_009_decode ridgeSupport832_suffix_decode_010
theorem ridgeSupport832_suffix_decode_008 : PackedRawNatGrowth.readList 12 189 ridgeSupport832_rest_008 =
    (ridgeSupport832_suffix_008, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 157
    ridgeSupport832_rest_008 ridgeSupport832_rest_009 ridgeSupport832_rest_014
    ridgeSupport832_008 ridgeSupport832_suffix_009 ridgeSupport832_008_decode ridgeSupport832_suffix_decode_009
theorem ridgeSupport832_suffix_decode_007 : PackedRawNatGrowth.readList 12 221 ridgeSupport832_rest_007 =
    (ridgeSupport832_suffix_007, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 189
    ridgeSupport832_rest_007 ridgeSupport832_rest_008 ridgeSupport832_rest_014
    ridgeSupport832_007 ridgeSupport832_suffix_008 ridgeSupport832_007_decode ridgeSupport832_suffix_decode_008
theorem ridgeSupport832_suffix_decode_006 : PackedRawNatGrowth.readList 12 253 ridgeSupport832_rest_006 =
    (ridgeSupport832_suffix_006, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 221
    ridgeSupport832_rest_006 ridgeSupport832_rest_007 ridgeSupport832_rest_014
    ridgeSupport832_006 ridgeSupport832_suffix_007 ridgeSupport832_006_decode ridgeSupport832_suffix_decode_007
theorem ridgeSupport832_suffix_decode_005 : PackedRawNatGrowth.readList 12 285 ridgeSupport832_rest_005 =
    (ridgeSupport832_suffix_005, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 253
    ridgeSupport832_rest_005 ridgeSupport832_rest_006 ridgeSupport832_rest_014
    ridgeSupport832_005 ridgeSupport832_suffix_006 ridgeSupport832_005_decode ridgeSupport832_suffix_decode_006
theorem ridgeSupport832_suffix_decode_004 : PackedRawNatGrowth.readList 12 317 ridgeSupport832_rest_004 =
    (ridgeSupport832_suffix_004, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 285
    ridgeSupport832_rest_004 ridgeSupport832_rest_005 ridgeSupport832_rest_014
    ridgeSupport832_004 ridgeSupport832_suffix_005 ridgeSupport832_004_decode ridgeSupport832_suffix_decode_005
theorem ridgeSupport832_suffix_decode_003 : PackedRawNatGrowth.readList 12 349 ridgeSupport832_rest_003 =
    (ridgeSupport832_suffix_003, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 317
    ridgeSupport832_rest_003 ridgeSupport832_rest_004 ridgeSupport832_rest_014
    ridgeSupport832_003 ridgeSupport832_suffix_004 ridgeSupport832_003_decode ridgeSupport832_suffix_decode_004
theorem ridgeSupport832_suffix_decode_002 : PackedRawNatGrowth.readList 12 381 ridgeSupport832_rest_002 =
    (ridgeSupport832_suffix_002, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 349
    ridgeSupport832_rest_002 ridgeSupport832_rest_003 ridgeSupport832_rest_014
    ridgeSupport832_002 ridgeSupport832_suffix_003 ridgeSupport832_002_decode ridgeSupport832_suffix_decode_003
theorem ridgeSupport832_suffix_decode_001 : PackedRawNatGrowth.readList 12 413 ridgeSupport832_rest_001 =
    (ridgeSupport832_suffix_001, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 381
    ridgeSupport832_rest_001 ridgeSupport832_rest_002 ridgeSupport832_rest_014
    ridgeSupport832_001 ridgeSupport832_suffix_002 ridgeSupport832_001_decode ridgeSupport832_suffix_decode_002
theorem ridgeSupport832_suffix_decode_000 : PackedRawNatGrowth.readList 12 445 ridgeSupport832_rest_000 =
    (ridgeSupport832_suffix_000, ridgeSupport832_rest_014) :=
  PackedRawNatGrowth.readList_append_of_eq 12 32 413
    ridgeSupport832_rest_000 ridgeSupport832_rest_001 ridgeSupport832_rest_014
    ridgeSupport832_000 ridgeSupport832_suffix_001 ridgeSupport832_000_decode ridgeSupport832_suffix_decode_001
theorem ridgeSupport832_eq : candidateRows 832 = ridgeSupport832_suffix_000 := by
  change candidateSupports 832 = ridgeSupport832_suffix_000
  rw [ridgeSupport832_source]
  exact congrArg Prod.fst ridgeSupport832_suffix_decode_000
theorem ridgeTest_large_832 : ridgeTest 832 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport832_000_mask, ridgeSupport832_001_mask, ridgeSupport832_002_mask, ridgeSupport832_003_mask, ridgeSupport832_004_mask, ridgeSupport832_005_mask, ridgeSupport832_006_mask, ridgeSupport832_007_mask, ridgeSupport832_008_mask, ridgeSupport832_009_mask, ridgeSupport832_010_mask, ridgeSupport832_011_mask, ridgeSupport832_012_mask, ridgeSupport832_013_mask]
    decide +kernel
  · rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, List.all_append, List.all_nil, ridgeSupport832_000_checked, ridgeSupport832_001_checked, ridgeSupport832_002_checked, ridgeSupport832_003_checked, ridgeSupport832_004_checked, ridgeSupport832_005_checked, ridgeSupport832_006_checked, ridgeSupport832_007_checked, ridgeSupport832_008_checked, ridgeSupport832_009_checked, ridgeSupport832_010_checked, ridgeSupport832_011_checked, ridgeSupport832_012_checked, ridgeSupport832_013_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra03
