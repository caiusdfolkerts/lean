module
prelude
public import RootedSevenTwoSix13GrowthCacheRidgeSupport832Part000
public import RootedSevenTwoSix13GrowthCacheRidgeSupport832Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport832_suffix_decode_010 : PackedRawNatGrowth.readList 11 0 ridgeSupport832_rest_010 =
    (ridgeSupport832_suffix_010, ridgeSupport832_rest_010) := by rfl
theorem ridgeSupport832_suffix_decode_009 : PackedRawNatGrowth.readList 11 3 ridgeSupport832_rest_009 =
    (ridgeSupport832_suffix_009, ridgeSupport832_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 11 3 0
    ridgeSupport832_rest_009 ridgeSupport832_rest_010 ridgeSupport832_rest_010
    ridgeSupport832_009 ridgeSupport832_suffix_010 ridgeSupport832_009_decode ridgeSupport832_suffix_decode_010
theorem ridgeSupport832_suffix_decode_008 : PackedRawNatGrowth.readList 11 35 ridgeSupport832_rest_008 =
    (ridgeSupport832_suffix_008, ridgeSupport832_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 3
    ridgeSupport832_rest_008 ridgeSupport832_rest_009 ridgeSupport832_rest_010
    ridgeSupport832_008 ridgeSupport832_suffix_009 ridgeSupport832_008_decode ridgeSupport832_suffix_decode_009
theorem ridgeSupport832_suffix_decode_007 : PackedRawNatGrowth.readList 11 67 ridgeSupport832_rest_007 =
    (ridgeSupport832_suffix_007, ridgeSupport832_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 35
    ridgeSupport832_rest_007 ridgeSupport832_rest_008 ridgeSupport832_rest_010
    ridgeSupport832_007 ridgeSupport832_suffix_008 ridgeSupport832_007_decode ridgeSupport832_suffix_decode_008
theorem ridgeSupport832_suffix_decode_006 : PackedRawNatGrowth.readList 11 99 ridgeSupport832_rest_006 =
    (ridgeSupport832_suffix_006, ridgeSupport832_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 67
    ridgeSupport832_rest_006 ridgeSupport832_rest_007 ridgeSupport832_rest_010
    ridgeSupport832_006 ridgeSupport832_suffix_007 ridgeSupport832_006_decode ridgeSupport832_suffix_decode_007
theorem ridgeSupport832_suffix_decode_005 : PackedRawNatGrowth.readList 11 131 ridgeSupport832_rest_005 =
    (ridgeSupport832_suffix_005, ridgeSupport832_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 99
    ridgeSupport832_rest_005 ridgeSupport832_rest_006 ridgeSupport832_rest_010
    ridgeSupport832_005 ridgeSupport832_suffix_006 ridgeSupport832_005_decode ridgeSupport832_suffix_decode_006
theorem ridgeSupport832_suffix_decode_004 : PackedRawNatGrowth.readList 11 163 ridgeSupport832_rest_004 =
    (ridgeSupport832_suffix_004, ridgeSupport832_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 131
    ridgeSupport832_rest_004 ridgeSupport832_rest_005 ridgeSupport832_rest_010
    ridgeSupport832_004 ridgeSupport832_suffix_005 ridgeSupport832_004_decode ridgeSupport832_suffix_decode_005
theorem ridgeSupport832_suffix_decode_003 : PackedRawNatGrowth.readList 11 195 ridgeSupport832_rest_003 =
    (ridgeSupport832_suffix_003, ridgeSupport832_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 163
    ridgeSupport832_rest_003 ridgeSupport832_rest_004 ridgeSupport832_rest_010
    ridgeSupport832_003 ridgeSupport832_suffix_004 ridgeSupport832_003_decode ridgeSupport832_suffix_decode_004
theorem ridgeSupport832_suffix_decode_002 : PackedRawNatGrowth.readList 11 227 ridgeSupport832_rest_002 =
    (ridgeSupport832_suffix_002, ridgeSupport832_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 195
    ridgeSupport832_rest_002 ridgeSupport832_rest_003 ridgeSupport832_rest_010
    ridgeSupport832_002 ridgeSupport832_suffix_003 ridgeSupport832_002_decode ridgeSupport832_suffix_decode_003
theorem ridgeSupport832_suffix_decode_001 : PackedRawNatGrowth.readList 11 259 ridgeSupport832_rest_001 =
    (ridgeSupport832_suffix_001, ridgeSupport832_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 227
    ridgeSupport832_rest_001 ridgeSupport832_rest_002 ridgeSupport832_rest_010
    ridgeSupport832_001 ridgeSupport832_suffix_002 ridgeSupport832_001_decode ridgeSupport832_suffix_decode_002
theorem ridgeSupport832_suffix_decode_000 : PackedRawNatGrowth.readList 11 291 ridgeSupport832_rest_000 =
    (ridgeSupport832_suffix_000, ridgeSupport832_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 11 32 259
    ridgeSupport832_rest_000 ridgeSupport832_rest_001 ridgeSupport832_rest_010
    ridgeSupport832_000 ridgeSupport832_suffix_001 ridgeSupport832_000_decode ridgeSupport832_suffix_decode_001
theorem ridgeSupport832_eq : candidateRows 832 = ridgeSupport832_suffix_000 := by
  rw [ridgeSupport832_source]
  exact congrArg Prod.fst ridgeSupport832_suffix_decode_000
theorem ridgeTest_large_832 : ridgeTest 832 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport832_000_mask, ridgeSupport832_001_mask, ridgeSupport832_002_mask, ridgeSupport832_003_mask, ridgeSupport832_004_mask, ridgeSupport832_005_mask, ridgeSupport832_006_mask, ridgeSupport832_007_mask, ridgeSupport832_008_mask, ridgeSupport832_009_mask]
    decide +kernel
  · rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, List.all_append, List.all_nil, ridgeSupport832_000_checked, ridgeSupport832_001_checked, ridgeSupport832_002_checked, ridgeSupport832_003_checked, ridgeSupport832_004_checked, ridgeSupport832_005_checked, ridgeSupport832_006_checked, ridgeSupport832_007_checked, ridgeSupport832_008_checked, ridgeSupport832_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSevenTwoSix13
