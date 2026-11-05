module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport833Part000
public import RootedSixBase00GrowthCacheRidgeSupport833Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport833_suffix_decode_010 : PackedRawNatGrowth.readList 15 0 ridgeSupport833_rest_010 =
    (ridgeSupport833_suffix_010, ridgeSupport833_rest_010) := by rfl
theorem ridgeSupport833_suffix_decode_009 : PackedRawNatGrowth.readList 15 3 ridgeSupport833_rest_009 =
    (ridgeSupport833_suffix_009, ridgeSupport833_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport833_rest_009 ridgeSupport833_rest_010 ridgeSupport833_rest_010
    ridgeSupport833_009 ridgeSupport833_suffix_010 ridgeSupport833_009_decode ridgeSupport833_suffix_decode_010
theorem ridgeSupport833_suffix_decode_008 : PackedRawNatGrowth.readList 15 35 ridgeSupport833_rest_008 =
    (ridgeSupport833_suffix_008, ridgeSupport833_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport833_rest_008 ridgeSupport833_rest_009 ridgeSupport833_rest_010
    ridgeSupport833_008 ridgeSupport833_suffix_009 ridgeSupport833_008_decode ridgeSupport833_suffix_decode_009
theorem ridgeSupport833_suffix_decode_007 : PackedRawNatGrowth.readList 15 67 ridgeSupport833_rest_007 =
    (ridgeSupport833_suffix_007, ridgeSupport833_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport833_rest_007 ridgeSupport833_rest_008 ridgeSupport833_rest_010
    ridgeSupport833_007 ridgeSupport833_suffix_008 ridgeSupport833_007_decode ridgeSupport833_suffix_decode_008
theorem ridgeSupport833_suffix_decode_006 : PackedRawNatGrowth.readList 15 99 ridgeSupport833_rest_006 =
    (ridgeSupport833_suffix_006, ridgeSupport833_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport833_rest_006 ridgeSupport833_rest_007 ridgeSupport833_rest_010
    ridgeSupport833_006 ridgeSupport833_suffix_007 ridgeSupport833_006_decode ridgeSupport833_suffix_decode_007
theorem ridgeSupport833_suffix_decode_005 : PackedRawNatGrowth.readList 15 131 ridgeSupport833_rest_005 =
    (ridgeSupport833_suffix_005, ridgeSupport833_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport833_rest_005 ridgeSupport833_rest_006 ridgeSupport833_rest_010
    ridgeSupport833_005 ridgeSupport833_suffix_006 ridgeSupport833_005_decode ridgeSupport833_suffix_decode_006
theorem ridgeSupport833_suffix_decode_004 : PackedRawNatGrowth.readList 15 163 ridgeSupport833_rest_004 =
    (ridgeSupport833_suffix_004, ridgeSupport833_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport833_rest_004 ridgeSupport833_rest_005 ridgeSupport833_rest_010
    ridgeSupport833_004 ridgeSupport833_suffix_005 ridgeSupport833_004_decode ridgeSupport833_suffix_decode_005
theorem ridgeSupport833_suffix_decode_003 : PackedRawNatGrowth.readList 15 195 ridgeSupport833_rest_003 =
    (ridgeSupport833_suffix_003, ridgeSupport833_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport833_rest_003 ridgeSupport833_rest_004 ridgeSupport833_rest_010
    ridgeSupport833_003 ridgeSupport833_suffix_004 ridgeSupport833_003_decode ridgeSupport833_suffix_decode_004
theorem ridgeSupport833_suffix_decode_002 : PackedRawNatGrowth.readList 15 227 ridgeSupport833_rest_002 =
    (ridgeSupport833_suffix_002, ridgeSupport833_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport833_rest_002 ridgeSupport833_rest_003 ridgeSupport833_rest_010
    ridgeSupport833_002 ridgeSupport833_suffix_003 ridgeSupport833_002_decode ridgeSupport833_suffix_decode_003
theorem ridgeSupport833_suffix_decode_001 : PackedRawNatGrowth.readList 15 259 ridgeSupport833_rest_001 =
    (ridgeSupport833_suffix_001, ridgeSupport833_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport833_rest_001 ridgeSupport833_rest_002 ridgeSupport833_rest_010
    ridgeSupport833_001 ridgeSupport833_suffix_002 ridgeSupport833_001_decode ridgeSupport833_suffix_decode_002
theorem ridgeSupport833_suffix_decode_000 : PackedRawNatGrowth.readList 15 291 ridgeSupport833_rest_000 =
    (ridgeSupport833_suffix_000, ridgeSupport833_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport833_rest_000 ridgeSupport833_rest_001 ridgeSupport833_rest_010
    ridgeSupport833_000 ridgeSupport833_suffix_001 ridgeSupport833_000_decode ridgeSupport833_suffix_decode_001
theorem ridgeSupport833_eq : candidateRows 833 = ridgeSupport833_suffix_000 := by
  rw [ridgeSupport833_source]
  exact congrArg Prod.fst ridgeSupport833_suffix_decode_000
theorem ridgeTest_large_833 : ridgeTest 833 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport833_eq]
    simp only [ridgeSupport833_suffix_000, ridgeSupport833_suffix_001, ridgeSupport833_suffix_002, ridgeSupport833_suffix_003, ridgeSupport833_suffix_004, ridgeSupport833_suffix_005, ridgeSupport833_suffix_006, ridgeSupport833_suffix_007, ridgeSupport833_suffix_008, ridgeSupport833_suffix_009, ridgeSupport833_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport833_000_mask, ridgeSupport833_001_mask, ridgeSupport833_002_mask, ridgeSupport833_003_mask, ridgeSupport833_004_mask, ridgeSupport833_005_mask, ridgeSupport833_006_mask, ridgeSupport833_007_mask, ridgeSupport833_008_mask, ridgeSupport833_009_mask]
    decide +kernel
  · rw [ridgeSupport833_eq]
    simp only [ridgeSupport833_suffix_000, ridgeSupport833_suffix_001, ridgeSupport833_suffix_002, ridgeSupport833_suffix_003, ridgeSupport833_suffix_004, ridgeSupport833_suffix_005, ridgeSupport833_suffix_006, ridgeSupport833_suffix_007, ridgeSupport833_suffix_008, ridgeSupport833_suffix_009, ridgeSupport833_suffix_010, List.all_append, List.all_nil, ridgeSupport833_000_checked, ridgeSupport833_001_checked, ridgeSupport833_002_checked, ridgeSupport833_003_checked, ridgeSupport833_004_checked, ridgeSupport833_005_checked, ridgeSupport833_006_checked, ridgeSupport833_007_checked, ridgeSupport833_008_checked, ridgeSupport833_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
