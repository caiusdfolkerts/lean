module
prelude
public import RootedSixBase00GrowthCacheRidgeSupport928Part000
public import RootedSixBase00GrowthCacheRidgeSupport928Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport928_suffix_decode_010 : PackedRawNatGrowth.readList 15 0 ridgeSupport928_rest_010 =
    (ridgeSupport928_suffix_010, ridgeSupport928_rest_010) := by rfl
theorem ridgeSupport928_suffix_decode_009 : PackedRawNatGrowth.readList 15 3 ridgeSupport928_rest_009 =
    (ridgeSupport928_suffix_009, ridgeSupport928_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 3 0
    ridgeSupport928_rest_009 ridgeSupport928_rest_010 ridgeSupport928_rest_010
    ridgeSupport928_009 ridgeSupport928_suffix_010 ridgeSupport928_009_decode ridgeSupport928_suffix_decode_010
theorem ridgeSupport928_suffix_decode_008 : PackedRawNatGrowth.readList 15 35 ridgeSupport928_rest_008 =
    (ridgeSupport928_suffix_008, ridgeSupport928_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 3
    ridgeSupport928_rest_008 ridgeSupport928_rest_009 ridgeSupport928_rest_010
    ridgeSupport928_008 ridgeSupport928_suffix_009 ridgeSupport928_008_decode ridgeSupport928_suffix_decode_009
theorem ridgeSupport928_suffix_decode_007 : PackedRawNatGrowth.readList 15 67 ridgeSupport928_rest_007 =
    (ridgeSupport928_suffix_007, ridgeSupport928_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 35
    ridgeSupport928_rest_007 ridgeSupport928_rest_008 ridgeSupport928_rest_010
    ridgeSupport928_007 ridgeSupport928_suffix_008 ridgeSupport928_007_decode ridgeSupport928_suffix_decode_008
theorem ridgeSupport928_suffix_decode_006 : PackedRawNatGrowth.readList 15 99 ridgeSupport928_rest_006 =
    (ridgeSupport928_suffix_006, ridgeSupport928_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 67
    ridgeSupport928_rest_006 ridgeSupport928_rest_007 ridgeSupport928_rest_010
    ridgeSupport928_006 ridgeSupport928_suffix_007 ridgeSupport928_006_decode ridgeSupport928_suffix_decode_007
theorem ridgeSupport928_suffix_decode_005 : PackedRawNatGrowth.readList 15 131 ridgeSupport928_rest_005 =
    (ridgeSupport928_suffix_005, ridgeSupport928_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 99
    ridgeSupport928_rest_005 ridgeSupport928_rest_006 ridgeSupport928_rest_010
    ridgeSupport928_005 ridgeSupport928_suffix_006 ridgeSupport928_005_decode ridgeSupport928_suffix_decode_006
theorem ridgeSupport928_suffix_decode_004 : PackedRawNatGrowth.readList 15 163 ridgeSupport928_rest_004 =
    (ridgeSupport928_suffix_004, ridgeSupport928_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 131
    ridgeSupport928_rest_004 ridgeSupport928_rest_005 ridgeSupport928_rest_010
    ridgeSupport928_004 ridgeSupport928_suffix_005 ridgeSupport928_004_decode ridgeSupport928_suffix_decode_005
theorem ridgeSupport928_suffix_decode_003 : PackedRawNatGrowth.readList 15 195 ridgeSupport928_rest_003 =
    (ridgeSupport928_suffix_003, ridgeSupport928_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 163
    ridgeSupport928_rest_003 ridgeSupport928_rest_004 ridgeSupport928_rest_010
    ridgeSupport928_003 ridgeSupport928_suffix_004 ridgeSupport928_003_decode ridgeSupport928_suffix_decode_004
theorem ridgeSupport928_suffix_decode_002 : PackedRawNatGrowth.readList 15 227 ridgeSupport928_rest_002 =
    (ridgeSupport928_suffix_002, ridgeSupport928_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 195
    ridgeSupport928_rest_002 ridgeSupport928_rest_003 ridgeSupport928_rest_010
    ridgeSupport928_002 ridgeSupport928_suffix_003 ridgeSupport928_002_decode ridgeSupport928_suffix_decode_003
theorem ridgeSupport928_suffix_decode_001 : PackedRawNatGrowth.readList 15 259 ridgeSupport928_rest_001 =
    (ridgeSupport928_suffix_001, ridgeSupport928_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 227
    ridgeSupport928_rest_001 ridgeSupport928_rest_002 ridgeSupport928_rest_010
    ridgeSupport928_001 ridgeSupport928_suffix_002 ridgeSupport928_001_decode ridgeSupport928_suffix_decode_002
theorem ridgeSupport928_suffix_decode_000 : PackedRawNatGrowth.readList 15 291 ridgeSupport928_rest_000 =
    (ridgeSupport928_suffix_000, ridgeSupport928_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 259
    ridgeSupport928_rest_000 ridgeSupport928_rest_001 ridgeSupport928_rest_010
    ridgeSupport928_000 ridgeSupport928_suffix_001 ridgeSupport928_000_decode ridgeSupport928_suffix_decode_001
theorem ridgeSupport928_eq : candidateRows 928 = ridgeSupport928_suffix_000 := by
  rw [ridgeSupport928_source]
  exact congrArg Prod.fst ridgeSupport928_suffix_decode_000
theorem ridgeTest_large_928 : ridgeTest 928 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport928_eq]
    simp only [ridgeSupport928_suffix_000, ridgeSupport928_suffix_001, ridgeSupport928_suffix_002, ridgeSupport928_suffix_003, ridgeSupport928_suffix_004, ridgeSupport928_suffix_005, ridgeSupport928_suffix_006, ridgeSupport928_suffix_007, ridgeSupport928_suffix_008, ridgeSupport928_suffix_009, ridgeSupport928_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport928_000_mask, ridgeSupport928_001_mask, ridgeSupport928_002_mask, ridgeSupport928_003_mask, ridgeSupport928_004_mask, ridgeSupport928_005_mask, ridgeSupport928_006_mask, ridgeSupport928_007_mask, ridgeSupport928_008_mask, ridgeSupport928_009_mask]
    decide +kernel
  · rw [ridgeSupport928_eq]
    simp only [ridgeSupport928_suffix_000, ridgeSupport928_suffix_001, ridgeSupport928_suffix_002, ridgeSupport928_suffix_003, ridgeSupport928_suffix_004, ridgeSupport928_suffix_005, ridgeSupport928_suffix_006, ridgeSupport928_suffix_007, ridgeSupport928_suffix_008, ridgeSupport928_suffix_009, ridgeSupport928_suffix_010, List.all_append, List.all_nil, ridgeSupport928_000_checked, ridgeSupport928_001_checked, ridgeSupport928_002_checked, ridgeSupport928_003_checked, ridgeSupport928_004_checked, ridgeSupport928_005_checked, ridgeSupport928_006_checked, ridgeSupport928_007_checked, ridgeSupport928_008_checked, ridgeSupport928_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
