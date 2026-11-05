module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport200Part000
public import RootedSixExtra02GrowthCacheRidgeSupport200Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport200_suffix_decode_013 : PackedRawNatGrowth.readList 13 0 ridgeSupport200_rest_013 =
    (ridgeSupport200_suffix_013, ridgeSupport200_rest_013) := by rfl
theorem ridgeSupport200_suffix_decode_012 : PackedRawNatGrowth.readList 13 20 ridgeSupport200_rest_012 =
    (ridgeSupport200_suffix_012, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 20 0
    ridgeSupport200_rest_012 ridgeSupport200_rest_013 ridgeSupport200_rest_013
    ridgeSupport200_012 ridgeSupport200_suffix_013 ridgeSupport200_012_decode ridgeSupport200_suffix_decode_013
theorem ridgeSupport200_suffix_decode_011 : PackedRawNatGrowth.readList 13 52 ridgeSupport200_rest_011 =
    (ridgeSupport200_suffix_011, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 20
    ridgeSupport200_rest_011 ridgeSupport200_rest_012 ridgeSupport200_rest_013
    ridgeSupport200_011 ridgeSupport200_suffix_012 ridgeSupport200_011_decode ridgeSupport200_suffix_decode_012
theorem ridgeSupport200_suffix_decode_010 : PackedRawNatGrowth.readList 13 84 ridgeSupport200_rest_010 =
    (ridgeSupport200_suffix_010, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 52
    ridgeSupport200_rest_010 ridgeSupport200_rest_011 ridgeSupport200_rest_013
    ridgeSupport200_010 ridgeSupport200_suffix_011 ridgeSupport200_010_decode ridgeSupport200_suffix_decode_011
theorem ridgeSupport200_suffix_decode_009 : PackedRawNatGrowth.readList 13 116 ridgeSupport200_rest_009 =
    (ridgeSupport200_suffix_009, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 84
    ridgeSupport200_rest_009 ridgeSupport200_rest_010 ridgeSupport200_rest_013
    ridgeSupport200_009 ridgeSupport200_suffix_010 ridgeSupport200_009_decode ridgeSupport200_suffix_decode_010
theorem ridgeSupport200_suffix_decode_008 : PackedRawNatGrowth.readList 13 148 ridgeSupport200_rest_008 =
    (ridgeSupport200_suffix_008, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 116
    ridgeSupport200_rest_008 ridgeSupport200_rest_009 ridgeSupport200_rest_013
    ridgeSupport200_008 ridgeSupport200_suffix_009 ridgeSupport200_008_decode ridgeSupport200_suffix_decode_009
theorem ridgeSupport200_suffix_decode_007 : PackedRawNatGrowth.readList 13 180 ridgeSupport200_rest_007 =
    (ridgeSupport200_suffix_007, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 148
    ridgeSupport200_rest_007 ridgeSupport200_rest_008 ridgeSupport200_rest_013
    ridgeSupport200_007 ridgeSupport200_suffix_008 ridgeSupport200_007_decode ridgeSupport200_suffix_decode_008
theorem ridgeSupport200_suffix_decode_006 : PackedRawNatGrowth.readList 13 212 ridgeSupport200_rest_006 =
    (ridgeSupport200_suffix_006, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 180
    ridgeSupport200_rest_006 ridgeSupport200_rest_007 ridgeSupport200_rest_013
    ridgeSupport200_006 ridgeSupport200_suffix_007 ridgeSupport200_006_decode ridgeSupport200_suffix_decode_007
theorem ridgeSupport200_suffix_decode_005 : PackedRawNatGrowth.readList 13 244 ridgeSupport200_rest_005 =
    (ridgeSupport200_suffix_005, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 212
    ridgeSupport200_rest_005 ridgeSupport200_rest_006 ridgeSupport200_rest_013
    ridgeSupport200_005 ridgeSupport200_suffix_006 ridgeSupport200_005_decode ridgeSupport200_suffix_decode_006
theorem ridgeSupport200_suffix_decode_004 : PackedRawNatGrowth.readList 13 276 ridgeSupport200_rest_004 =
    (ridgeSupport200_suffix_004, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 244
    ridgeSupport200_rest_004 ridgeSupport200_rest_005 ridgeSupport200_rest_013
    ridgeSupport200_004 ridgeSupport200_suffix_005 ridgeSupport200_004_decode ridgeSupport200_suffix_decode_005
theorem ridgeSupport200_suffix_decode_003 : PackedRawNatGrowth.readList 13 308 ridgeSupport200_rest_003 =
    (ridgeSupport200_suffix_003, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 276
    ridgeSupport200_rest_003 ridgeSupport200_rest_004 ridgeSupport200_rest_013
    ridgeSupport200_003 ridgeSupport200_suffix_004 ridgeSupport200_003_decode ridgeSupport200_suffix_decode_004
theorem ridgeSupport200_suffix_decode_002 : PackedRawNatGrowth.readList 13 340 ridgeSupport200_rest_002 =
    (ridgeSupport200_suffix_002, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 308
    ridgeSupport200_rest_002 ridgeSupport200_rest_003 ridgeSupport200_rest_013
    ridgeSupport200_002 ridgeSupport200_suffix_003 ridgeSupport200_002_decode ridgeSupport200_suffix_decode_003
theorem ridgeSupport200_suffix_decode_001 : PackedRawNatGrowth.readList 13 372 ridgeSupport200_rest_001 =
    (ridgeSupport200_suffix_001, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 340
    ridgeSupport200_rest_001 ridgeSupport200_rest_002 ridgeSupport200_rest_013
    ridgeSupport200_001 ridgeSupport200_suffix_002 ridgeSupport200_001_decode ridgeSupport200_suffix_decode_002
theorem ridgeSupport200_suffix_decode_000 : PackedRawNatGrowth.readList 13 404 ridgeSupport200_rest_000 =
    (ridgeSupport200_suffix_000, ridgeSupport200_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 372
    ridgeSupport200_rest_000 ridgeSupport200_rest_001 ridgeSupport200_rest_013
    ridgeSupport200_000 ridgeSupport200_suffix_001 ridgeSupport200_000_decode ridgeSupport200_suffix_decode_001
theorem ridgeSupport200_eq : candidateRows 200 = ridgeSupport200_suffix_000 := by
  change candidateSupports 200 = ridgeSupport200_suffix_000
  rw [ridgeSupport200_source]
  exact congrArg Prod.fst ridgeSupport200_suffix_decode_000
theorem ridgeTest_large_200 : ridgeTest 200 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport200_eq]
    simp only [ridgeSupport200_suffix_000, ridgeSupport200_suffix_001, ridgeSupport200_suffix_002, ridgeSupport200_suffix_003, ridgeSupport200_suffix_004, ridgeSupport200_suffix_005, ridgeSupport200_suffix_006, ridgeSupport200_suffix_007, ridgeSupport200_suffix_008, ridgeSupport200_suffix_009, ridgeSupport200_suffix_010, ridgeSupport200_suffix_011, ridgeSupport200_suffix_012, ridgeSupport200_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport200_000_mask, ridgeSupport200_001_mask, ridgeSupport200_002_mask, ridgeSupport200_003_mask, ridgeSupport200_004_mask, ridgeSupport200_005_mask, ridgeSupport200_006_mask, ridgeSupport200_007_mask, ridgeSupport200_008_mask, ridgeSupport200_009_mask, ridgeSupport200_010_mask, ridgeSupport200_011_mask, ridgeSupport200_012_mask]
    decide +kernel
  · rw [ridgeSupport200_eq]
    simp only [ridgeSupport200_suffix_000, ridgeSupport200_suffix_001, ridgeSupport200_suffix_002, ridgeSupport200_suffix_003, ridgeSupport200_suffix_004, ridgeSupport200_suffix_005, ridgeSupport200_suffix_006, ridgeSupport200_suffix_007, ridgeSupport200_suffix_008, ridgeSupport200_suffix_009, ridgeSupport200_suffix_010, ridgeSupport200_suffix_011, ridgeSupport200_suffix_012, ridgeSupport200_suffix_013, List.all_append, List.all_nil, ridgeSupport200_000_checked, ridgeSupport200_001_checked, ridgeSupport200_002_checked, ridgeSupport200_003_checked, ridgeSupport200_004_checked, ridgeSupport200_005_checked, ridgeSupport200_006_checked, ridgeSupport200_007_checked, ridgeSupport200_008_checked, ridgeSupport200_009_checked, ridgeSupport200_010_checked, ridgeSupport200_011_checked, ridgeSupport200_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
