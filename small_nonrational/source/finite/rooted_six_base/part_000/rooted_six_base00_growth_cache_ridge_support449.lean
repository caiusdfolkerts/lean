module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport449Part000
public import RootedSixBase00GrowthCacheRidgeSupport449Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport449_suffix_decode_010 : PackedRawNatGrowth.readList 15 0 ridgeSupport449_rest_010 =
    (ridgeSupport449_suffix_010, ridgeSupport449_rest_010) := by rfl
theorem ridgeSupport449_suffix_decode_009 : PackedRawNatGrowth.readList 15 3 ridgeSupport449_rest_009 =
    (ridgeSupport449_suffix_009, ridgeSupport449_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport449_rest_009 ridgeSupport449_rest_010 ridgeSupport449_rest_010
    ridgeSupport449_009 ridgeSupport449_suffix_010 ridgeSupport449_009_decode ridgeSupport449_suffix_decode_010
theorem ridgeSupport449_suffix_decode_008 : PackedRawNatGrowth.readList 15 35 ridgeSupport449_rest_008 =
    (ridgeSupport449_suffix_008, ridgeSupport449_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport449_rest_008 ridgeSupport449_rest_009 ridgeSupport449_rest_010
    ridgeSupport449_008 ridgeSupport449_suffix_009 ridgeSupport449_008_decode ridgeSupport449_suffix_decode_009
theorem ridgeSupport449_suffix_decode_007 : PackedRawNatGrowth.readList 15 67 ridgeSupport449_rest_007 =
    (ridgeSupport449_suffix_007, ridgeSupport449_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport449_rest_007 ridgeSupport449_rest_008 ridgeSupport449_rest_010
    ridgeSupport449_007 ridgeSupport449_suffix_008 ridgeSupport449_007_decode ridgeSupport449_suffix_decode_008
theorem ridgeSupport449_suffix_decode_006 : PackedRawNatGrowth.readList 15 99 ridgeSupport449_rest_006 =
    (ridgeSupport449_suffix_006, ridgeSupport449_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport449_rest_006 ridgeSupport449_rest_007 ridgeSupport449_rest_010
    ridgeSupport449_006 ridgeSupport449_suffix_007 ridgeSupport449_006_decode ridgeSupport449_suffix_decode_007
theorem ridgeSupport449_suffix_decode_005 : PackedRawNatGrowth.readList 15 131 ridgeSupport449_rest_005 =
    (ridgeSupport449_suffix_005, ridgeSupport449_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport449_rest_005 ridgeSupport449_rest_006 ridgeSupport449_rest_010
    ridgeSupport449_005 ridgeSupport449_suffix_006 ridgeSupport449_005_decode ridgeSupport449_suffix_decode_006
theorem ridgeSupport449_suffix_decode_004 : PackedRawNatGrowth.readList 15 163 ridgeSupport449_rest_004 =
    (ridgeSupport449_suffix_004, ridgeSupport449_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport449_rest_004 ridgeSupport449_rest_005 ridgeSupport449_rest_010
    ridgeSupport449_004 ridgeSupport449_suffix_005 ridgeSupport449_004_decode ridgeSupport449_suffix_decode_005
theorem ridgeSupport449_suffix_decode_003 : PackedRawNatGrowth.readList 15 195 ridgeSupport449_rest_003 =
    (ridgeSupport449_suffix_003, ridgeSupport449_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport449_rest_003 ridgeSupport449_rest_004 ridgeSupport449_rest_010
    ridgeSupport449_003 ridgeSupport449_suffix_004 ridgeSupport449_003_decode ridgeSupport449_suffix_decode_004
theorem ridgeSupport449_suffix_decode_002 : PackedRawNatGrowth.readList 15 227 ridgeSupport449_rest_002 =
    (ridgeSupport449_suffix_002, ridgeSupport449_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport449_rest_002 ridgeSupport449_rest_003 ridgeSupport449_rest_010
    ridgeSupport449_002 ridgeSupport449_suffix_003 ridgeSupport449_002_decode ridgeSupport449_suffix_decode_003
theorem ridgeSupport449_suffix_decode_001 : PackedRawNatGrowth.readList 15 259 ridgeSupport449_rest_001 =
    (ridgeSupport449_suffix_001, ridgeSupport449_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport449_rest_001 ridgeSupport449_rest_002 ridgeSupport449_rest_010
    ridgeSupport449_001 ridgeSupport449_suffix_002 ridgeSupport449_001_decode ridgeSupport449_suffix_decode_002
theorem ridgeSupport449_suffix_decode_000 : PackedRawNatGrowth.readList 15 291 ridgeSupport449_rest_000 =
    (ridgeSupport449_suffix_000, ridgeSupport449_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport449_rest_000 ridgeSupport449_rest_001 ridgeSupport449_rest_010
    ridgeSupport449_000 ridgeSupport449_suffix_001 ridgeSupport449_000_decode ridgeSupport449_suffix_decode_001
theorem ridgeSupport449_eq : candidateRows 449 = ridgeSupport449_suffix_000 := by
  rw [ridgeSupport449_source]
  exact congrArg Prod.fst ridgeSupport449_suffix_decode_000
theorem ridgeTest_large_449 : ridgeTest 449 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport449_eq]
    simp only [ridgeSupport449_suffix_000, ridgeSupport449_suffix_001, ridgeSupport449_suffix_002, ridgeSupport449_suffix_003, ridgeSupport449_suffix_004, ridgeSupport449_suffix_005, ridgeSupport449_suffix_006, ridgeSupport449_suffix_007, ridgeSupport449_suffix_008, ridgeSupport449_suffix_009, ridgeSupport449_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport449_000_mask, ridgeSupport449_001_mask, ridgeSupport449_002_mask, ridgeSupport449_003_mask, ridgeSupport449_004_mask, ridgeSupport449_005_mask, ridgeSupport449_006_mask, ridgeSupport449_007_mask, ridgeSupport449_008_mask, ridgeSupport449_009_mask]
    decide +kernel
  · rw [ridgeSupport449_eq]
    simp only [ridgeSupport449_suffix_000, ridgeSupport449_suffix_001, ridgeSupport449_suffix_002, ridgeSupport449_suffix_003, ridgeSupport449_suffix_004, ridgeSupport449_suffix_005, ridgeSupport449_suffix_006, ridgeSupport449_suffix_007, ridgeSupport449_suffix_008, ridgeSupport449_suffix_009, ridgeSupport449_suffix_010, List.all_append, List.all_nil, ridgeSupport449_000_checked, ridgeSupport449_001_checked, ridgeSupport449_002_checked, ridgeSupport449_003_checked, ridgeSupport449_004_checked, ridgeSupport449_005_checked, ridgeSupport449_006_checked, ridgeSupport449_007_checked, ridgeSupport449_008_checked, ridgeSupport449_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
