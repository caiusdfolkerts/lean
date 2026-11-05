module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport776Part000
public import RootedSixExtra02GrowthCacheRidgeSupport776Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport776_suffix_decode_013 : PackedRawNatGrowth.readList 13 0 ridgeSupport776_rest_013 =
    (ridgeSupport776_suffix_013, ridgeSupport776_rest_013) := by rfl
theorem ridgeSupport776_suffix_decode_012 : PackedRawNatGrowth.readList 13 20 ridgeSupport776_rest_012 =
    (ridgeSupport776_suffix_012, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 20 0
    ridgeSupport776_rest_012 ridgeSupport776_rest_013 ridgeSupport776_rest_013
    ridgeSupport776_012 ridgeSupport776_suffix_013 ridgeSupport776_012_decode ridgeSupport776_suffix_decode_013
theorem ridgeSupport776_suffix_decode_011 : PackedRawNatGrowth.readList 13 52 ridgeSupport776_rest_011 =
    (ridgeSupport776_suffix_011, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 20
    ridgeSupport776_rest_011 ridgeSupport776_rest_012 ridgeSupport776_rest_013
    ridgeSupport776_011 ridgeSupport776_suffix_012 ridgeSupport776_011_decode ridgeSupport776_suffix_decode_012
theorem ridgeSupport776_suffix_decode_010 : PackedRawNatGrowth.readList 13 84 ridgeSupport776_rest_010 =
    (ridgeSupport776_suffix_010, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 52
    ridgeSupport776_rest_010 ridgeSupport776_rest_011 ridgeSupport776_rest_013
    ridgeSupport776_010 ridgeSupport776_suffix_011 ridgeSupport776_010_decode ridgeSupport776_suffix_decode_011
theorem ridgeSupport776_suffix_decode_009 : PackedRawNatGrowth.readList 13 116 ridgeSupport776_rest_009 =
    (ridgeSupport776_suffix_009, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 84
    ridgeSupport776_rest_009 ridgeSupport776_rest_010 ridgeSupport776_rest_013
    ridgeSupport776_009 ridgeSupport776_suffix_010 ridgeSupport776_009_decode ridgeSupport776_suffix_decode_010
theorem ridgeSupport776_suffix_decode_008 : PackedRawNatGrowth.readList 13 148 ridgeSupport776_rest_008 =
    (ridgeSupport776_suffix_008, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 116
    ridgeSupport776_rest_008 ridgeSupport776_rest_009 ridgeSupport776_rest_013
    ridgeSupport776_008 ridgeSupport776_suffix_009 ridgeSupport776_008_decode ridgeSupport776_suffix_decode_009
theorem ridgeSupport776_suffix_decode_007 : PackedRawNatGrowth.readList 13 180 ridgeSupport776_rest_007 =
    (ridgeSupport776_suffix_007, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 148
    ridgeSupport776_rest_007 ridgeSupport776_rest_008 ridgeSupport776_rest_013
    ridgeSupport776_007 ridgeSupport776_suffix_008 ridgeSupport776_007_decode ridgeSupport776_suffix_decode_008
theorem ridgeSupport776_suffix_decode_006 : PackedRawNatGrowth.readList 13 212 ridgeSupport776_rest_006 =
    (ridgeSupport776_suffix_006, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 180
    ridgeSupport776_rest_006 ridgeSupport776_rest_007 ridgeSupport776_rest_013
    ridgeSupport776_006 ridgeSupport776_suffix_007 ridgeSupport776_006_decode ridgeSupport776_suffix_decode_007
theorem ridgeSupport776_suffix_decode_005 : PackedRawNatGrowth.readList 13 244 ridgeSupport776_rest_005 =
    (ridgeSupport776_suffix_005, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 212
    ridgeSupport776_rest_005 ridgeSupport776_rest_006 ridgeSupport776_rest_013
    ridgeSupport776_005 ridgeSupport776_suffix_006 ridgeSupport776_005_decode ridgeSupport776_suffix_decode_006
theorem ridgeSupport776_suffix_decode_004 : PackedRawNatGrowth.readList 13 276 ridgeSupport776_rest_004 =
    (ridgeSupport776_suffix_004, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 244
    ridgeSupport776_rest_004 ridgeSupport776_rest_005 ridgeSupport776_rest_013
    ridgeSupport776_004 ridgeSupport776_suffix_005 ridgeSupport776_004_decode ridgeSupport776_suffix_decode_005
theorem ridgeSupport776_suffix_decode_003 : PackedRawNatGrowth.readList 13 308 ridgeSupport776_rest_003 =
    (ridgeSupport776_suffix_003, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 276
    ridgeSupport776_rest_003 ridgeSupport776_rest_004 ridgeSupport776_rest_013
    ridgeSupport776_003 ridgeSupport776_suffix_004 ridgeSupport776_003_decode ridgeSupport776_suffix_decode_004
theorem ridgeSupport776_suffix_decode_002 : PackedRawNatGrowth.readList 13 340 ridgeSupport776_rest_002 =
    (ridgeSupport776_suffix_002, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 308
    ridgeSupport776_rest_002 ridgeSupport776_rest_003 ridgeSupport776_rest_013
    ridgeSupport776_002 ridgeSupport776_suffix_003 ridgeSupport776_002_decode ridgeSupport776_suffix_decode_003
theorem ridgeSupport776_suffix_decode_001 : PackedRawNatGrowth.readList 13 372 ridgeSupport776_rest_001 =
    (ridgeSupport776_suffix_001, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 340
    ridgeSupport776_rest_001 ridgeSupport776_rest_002 ridgeSupport776_rest_013
    ridgeSupport776_001 ridgeSupport776_suffix_002 ridgeSupport776_001_decode ridgeSupport776_suffix_decode_002
theorem ridgeSupport776_suffix_decode_000 : PackedRawNatGrowth.readList 13 404 ridgeSupport776_rest_000 =
    (ridgeSupport776_suffix_000, ridgeSupport776_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 372
    ridgeSupport776_rest_000 ridgeSupport776_rest_001 ridgeSupport776_rest_013
    ridgeSupport776_000 ridgeSupport776_suffix_001 ridgeSupport776_000_decode ridgeSupport776_suffix_decode_001
theorem ridgeSupport776_eq : candidateRows 776 = ridgeSupport776_suffix_000 := by
  change candidateSupports 776 = ridgeSupport776_suffix_000
  rw [ridgeSupport776_source]
  exact congrArg Prod.fst ridgeSupport776_suffix_decode_000
theorem ridgeTest_large_776 : ridgeTest 776 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport776_eq]
    simp only [ridgeSupport776_suffix_000, ridgeSupport776_suffix_001, ridgeSupport776_suffix_002, ridgeSupport776_suffix_003, ridgeSupport776_suffix_004, ridgeSupport776_suffix_005, ridgeSupport776_suffix_006, ridgeSupport776_suffix_007, ridgeSupport776_suffix_008, ridgeSupport776_suffix_009, ridgeSupport776_suffix_010, ridgeSupport776_suffix_011, ridgeSupport776_suffix_012, ridgeSupport776_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport776_000_mask, ridgeSupport776_001_mask, ridgeSupport776_002_mask, ridgeSupport776_003_mask, ridgeSupport776_004_mask, ridgeSupport776_005_mask, ridgeSupport776_006_mask, ridgeSupport776_007_mask, ridgeSupport776_008_mask, ridgeSupport776_009_mask, ridgeSupport776_010_mask, ridgeSupport776_011_mask, ridgeSupport776_012_mask]
    decide +kernel
  · rw [ridgeSupport776_eq]
    simp only [ridgeSupport776_suffix_000, ridgeSupport776_suffix_001, ridgeSupport776_suffix_002, ridgeSupport776_suffix_003, ridgeSupport776_suffix_004, ridgeSupport776_suffix_005, ridgeSupport776_suffix_006, ridgeSupport776_suffix_007, ridgeSupport776_suffix_008, ridgeSupport776_suffix_009, ridgeSupport776_suffix_010, ridgeSupport776_suffix_011, ridgeSupport776_suffix_012, ridgeSupport776_suffix_013, List.all_append, List.all_nil, ridgeSupport776_000_checked, ridgeSupport776_001_checked, ridgeSupport776_002_checked, ridgeSupport776_003_checked, ridgeSupport776_004_checked, ridgeSupport776_005_checked, ridgeSupport776_006_checked, ridgeSupport776_007_checked, ridgeSupport776_008_checked, ridgeSupport776_009_checked, ridgeSupport776_010_checked, ridgeSupport776_011_checked, ridgeSupport776_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
