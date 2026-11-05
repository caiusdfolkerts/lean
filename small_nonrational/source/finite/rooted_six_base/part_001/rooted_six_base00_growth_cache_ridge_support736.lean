module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport736Part000
public import RootedSixBase00GrowthCacheRidgeSupport736Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport736_suffix_decode_010 : PackedRawNatGrowth.readList 15 0 ridgeSupport736_rest_010 =
    (ridgeSupport736_suffix_010, ridgeSupport736_rest_010) := by rfl
theorem ridgeSupport736_suffix_decode_009 : PackedRawNatGrowth.readList 15 3 ridgeSupport736_rest_009 =
    (ridgeSupport736_suffix_009, ridgeSupport736_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport736_rest_009 ridgeSupport736_rest_010 ridgeSupport736_rest_010
    ridgeSupport736_009 ridgeSupport736_suffix_010 ridgeSupport736_009_decode ridgeSupport736_suffix_decode_010
theorem ridgeSupport736_suffix_decode_008 : PackedRawNatGrowth.readList 15 35 ridgeSupport736_rest_008 =
    (ridgeSupport736_suffix_008, ridgeSupport736_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport736_rest_008 ridgeSupport736_rest_009 ridgeSupport736_rest_010
    ridgeSupport736_008 ridgeSupport736_suffix_009 ridgeSupport736_008_decode ridgeSupport736_suffix_decode_009
theorem ridgeSupport736_suffix_decode_007 : PackedRawNatGrowth.readList 15 67 ridgeSupport736_rest_007 =
    (ridgeSupport736_suffix_007, ridgeSupport736_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport736_rest_007 ridgeSupport736_rest_008 ridgeSupport736_rest_010
    ridgeSupport736_007 ridgeSupport736_suffix_008 ridgeSupport736_007_decode ridgeSupport736_suffix_decode_008
theorem ridgeSupport736_suffix_decode_006 : PackedRawNatGrowth.readList 15 99 ridgeSupport736_rest_006 =
    (ridgeSupport736_suffix_006, ridgeSupport736_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport736_rest_006 ridgeSupport736_rest_007 ridgeSupport736_rest_010
    ridgeSupport736_006 ridgeSupport736_suffix_007 ridgeSupport736_006_decode ridgeSupport736_suffix_decode_007
theorem ridgeSupport736_suffix_decode_005 : PackedRawNatGrowth.readList 15 131 ridgeSupport736_rest_005 =
    (ridgeSupport736_suffix_005, ridgeSupport736_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport736_rest_005 ridgeSupport736_rest_006 ridgeSupport736_rest_010
    ridgeSupport736_005 ridgeSupport736_suffix_006 ridgeSupport736_005_decode ridgeSupport736_suffix_decode_006
theorem ridgeSupport736_suffix_decode_004 : PackedRawNatGrowth.readList 15 163 ridgeSupport736_rest_004 =
    (ridgeSupport736_suffix_004, ridgeSupport736_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport736_rest_004 ridgeSupport736_rest_005 ridgeSupport736_rest_010
    ridgeSupport736_004 ridgeSupport736_suffix_005 ridgeSupport736_004_decode ridgeSupport736_suffix_decode_005
theorem ridgeSupport736_suffix_decode_003 : PackedRawNatGrowth.readList 15 195 ridgeSupport736_rest_003 =
    (ridgeSupport736_suffix_003, ridgeSupport736_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport736_rest_003 ridgeSupport736_rest_004 ridgeSupport736_rest_010
    ridgeSupport736_003 ridgeSupport736_suffix_004 ridgeSupport736_003_decode ridgeSupport736_suffix_decode_004
theorem ridgeSupport736_suffix_decode_002 : PackedRawNatGrowth.readList 15 227 ridgeSupport736_rest_002 =
    (ridgeSupport736_suffix_002, ridgeSupport736_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport736_rest_002 ridgeSupport736_rest_003 ridgeSupport736_rest_010
    ridgeSupport736_002 ridgeSupport736_suffix_003 ridgeSupport736_002_decode ridgeSupport736_suffix_decode_003
theorem ridgeSupport736_suffix_decode_001 : PackedRawNatGrowth.readList 15 259 ridgeSupport736_rest_001 =
    (ridgeSupport736_suffix_001, ridgeSupport736_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport736_rest_001 ridgeSupport736_rest_002 ridgeSupport736_rest_010
    ridgeSupport736_001 ridgeSupport736_suffix_002 ridgeSupport736_001_decode ridgeSupport736_suffix_decode_002
theorem ridgeSupport736_suffix_decode_000 : PackedRawNatGrowth.readList 15 291 ridgeSupport736_rest_000 =
    (ridgeSupport736_suffix_000, ridgeSupport736_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport736_rest_000 ridgeSupport736_rest_001 ridgeSupport736_rest_010
    ridgeSupport736_000 ridgeSupport736_suffix_001 ridgeSupport736_000_decode ridgeSupport736_suffix_decode_001
theorem ridgeSupport736_eq : candidateRows 736 = ridgeSupport736_suffix_000 := by
  rw [ridgeSupport736_source]
  exact congrArg Prod.fst ridgeSupport736_suffix_decode_000
theorem ridgeTest_large_736 : ridgeTest 736 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport736_eq]
    simp only [ridgeSupport736_suffix_000, ridgeSupport736_suffix_001, ridgeSupport736_suffix_002, ridgeSupport736_suffix_003, ridgeSupport736_suffix_004, ridgeSupport736_suffix_005, ridgeSupport736_suffix_006, ridgeSupport736_suffix_007, ridgeSupport736_suffix_008, ridgeSupport736_suffix_009, ridgeSupport736_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport736_000_mask, ridgeSupport736_001_mask, ridgeSupport736_002_mask, ridgeSupport736_003_mask, ridgeSupport736_004_mask, ridgeSupport736_005_mask, ridgeSupport736_006_mask, ridgeSupport736_007_mask, ridgeSupport736_008_mask, ridgeSupport736_009_mask]
    decide +kernel
  · rw [ridgeSupport736_eq]
    simp only [ridgeSupport736_suffix_000, ridgeSupport736_suffix_001, ridgeSupport736_suffix_002, ridgeSupport736_suffix_003, ridgeSupport736_suffix_004, ridgeSupport736_suffix_005, ridgeSupport736_suffix_006, ridgeSupport736_suffix_007, ridgeSupport736_suffix_008, ridgeSupport736_suffix_009, ridgeSupport736_suffix_010, List.all_append, List.all_nil, ridgeSupport736_000_checked, ridgeSupport736_001_checked, ridgeSupport736_002_checked, ridgeSupport736_003_checked, ridgeSupport736_004_checked, ridgeSupport736_005_checked, ridgeSupport736_006_checked, ridgeSupport736_007_checked, ridgeSupport736_008_checked, ridgeSupport736_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
