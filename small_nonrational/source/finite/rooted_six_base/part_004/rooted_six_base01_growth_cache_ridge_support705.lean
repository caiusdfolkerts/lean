module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport705Part000
public import RootedSixBase01GrowthCacheRidgeSupport705Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport705_suffix_decode_010 : PackedRawNatGrowth.readList 14 0 ridgeSupport705_rest_010 =
    (ridgeSupport705_suffix_010, ridgeSupport705_rest_010) := by rfl
theorem ridgeSupport705_suffix_decode_009 : PackedRawNatGrowth.readList 14 3 ridgeSupport705_rest_009 =
    (ridgeSupport705_suffix_009, ridgeSupport705_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 3 0
    ridgeSupport705_rest_009 ridgeSupport705_rest_010 ridgeSupport705_rest_010
    ridgeSupport705_009 ridgeSupport705_suffix_010 ridgeSupport705_009_decode ridgeSupport705_suffix_decode_010
theorem ridgeSupport705_suffix_decode_008 : PackedRawNatGrowth.readList 14 35 ridgeSupport705_rest_008 =
    (ridgeSupport705_suffix_008, ridgeSupport705_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 3
    ridgeSupport705_rest_008 ridgeSupport705_rest_009 ridgeSupport705_rest_010
    ridgeSupport705_008 ridgeSupport705_suffix_009 ridgeSupport705_008_decode ridgeSupport705_suffix_decode_009
theorem ridgeSupport705_suffix_decode_007 : PackedRawNatGrowth.readList 14 67 ridgeSupport705_rest_007 =
    (ridgeSupport705_suffix_007, ridgeSupport705_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 35
    ridgeSupport705_rest_007 ridgeSupport705_rest_008 ridgeSupport705_rest_010
    ridgeSupport705_007 ridgeSupport705_suffix_008 ridgeSupport705_007_decode ridgeSupport705_suffix_decode_008
theorem ridgeSupport705_suffix_decode_006 : PackedRawNatGrowth.readList 14 99 ridgeSupport705_rest_006 =
    (ridgeSupport705_suffix_006, ridgeSupport705_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 67
    ridgeSupport705_rest_006 ridgeSupport705_rest_007 ridgeSupport705_rest_010
    ridgeSupport705_006 ridgeSupport705_suffix_007 ridgeSupport705_006_decode ridgeSupport705_suffix_decode_007
theorem ridgeSupport705_suffix_decode_005 : PackedRawNatGrowth.readList 14 131 ridgeSupport705_rest_005 =
    (ridgeSupport705_suffix_005, ridgeSupport705_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 99
    ridgeSupport705_rest_005 ridgeSupport705_rest_006 ridgeSupport705_rest_010
    ridgeSupport705_005 ridgeSupport705_suffix_006 ridgeSupport705_005_decode ridgeSupport705_suffix_decode_006
theorem ridgeSupport705_suffix_decode_004 : PackedRawNatGrowth.readList 14 163 ridgeSupport705_rest_004 =
    (ridgeSupport705_suffix_004, ridgeSupport705_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 131
    ridgeSupport705_rest_004 ridgeSupport705_rest_005 ridgeSupport705_rest_010
    ridgeSupport705_004 ridgeSupport705_suffix_005 ridgeSupport705_004_decode ridgeSupport705_suffix_decode_005
theorem ridgeSupport705_suffix_decode_003 : PackedRawNatGrowth.readList 14 195 ridgeSupport705_rest_003 =
    (ridgeSupport705_suffix_003, ridgeSupport705_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 163
    ridgeSupport705_rest_003 ridgeSupport705_rest_004 ridgeSupport705_rest_010
    ridgeSupport705_003 ridgeSupport705_suffix_004 ridgeSupport705_003_decode ridgeSupport705_suffix_decode_004
theorem ridgeSupport705_suffix_decode_002 : PackedRawNatGrowth.readList 14 227 ridgeSupport705_rest_002 =
    (ridgeSupport705_suffix_002, ridgeSupport705_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 195
    ridgeSupport705_rest_002 ridgeSupport705_rest_003 ridgeSupport705_rest_010
    ridgeSupport705_002 ridgeSupport705_suffix_003 ridgeSupport705_002_decode ridgeSupport705_suffix_decode_003
theorem ridgeSupport705_suffix_decode_001 : PackedRawNatGrowth.readList 14 259 ridgeSupport705_rest_001 =
    (ridgeSupport705_suffix_001, ridgeSupport705_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 227
    ridgeSupport705_rest_001 ridgeSupport705_rest_002 ridgeSupport705_rest_010
    ridgeSupport705_001 ridgeSupport705_suffix_002 ridgeSupport705_001_decode ridgeSupport705_suffix_decode_002
theorem ridgeSupport705_suffix_decode_000 : PackedRawNatGrowth.readList 14 291 ridgeSupport705_rest_000 =
    (ridgeSupport705_suffix_000, ridgeSupport705_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 259
    ridgeSupport705_rest_000 ridgeSupport705_rest_001 ridgeSupport705_rest_010
    ridgeSupport705_000 ridgeSupport705_suffix_001 ridgeSupport705_000_decode ridgeSupport705_suffix_decode_001
theorem ridgeSupport705_eq : candidateRows 705 = ridgeSupport705_suffix_000 := by
  rw [ridgeSupport705_source]
  exact congrArg Prod.fst ridgeSupport705_suffix_decode_000
theorem ridgeTest_large_705 : ridgeTest 705 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport705_eq]
    simp only [ridgeSupport705_suffix_000, ridgeSupport705_suffix_001, ridgeSupport705_suffix_002, ridgeSupport705_suffix_003, ridgeSupport705_suffix_004, ridgeSupport705_suffix_005, ridgeSupport705_suffix_006, ridgeSupport705_suffix_007, ridgeSupport705_suffix_008, ridgeSupport705_suffix_009, ridgeSupport705_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport705_000_mask, ridgeSupport705_001_mask, ridgeSupport705_002_mask, ridgeSupport705_003_mask, ridgeSupport705_004_mask, ridgeSupport705_005_mask, ridgeSupport705_006_mask, ridgeSupport705_007_mask, ridgeSupport705_008_mask, ridgeSupport705_009_mask]
    decide +kernel
  · rw [ridgeSupport705_eq]
    simp only [ridgeSupport705_suffix_000, ridgeSupport705_suffix_001, ridgeSupport705_suffix_002, ridgeSupport705_suffix_003, ridgeSupport705_suffix_004, ridgeSupport705_suffix_005, ridgeSupport705_suffix_006, ridgeSupport705_suffix_007, ridgeSupport705_suffix_008, ridgeSupport705_suffix_009, ridgeSupport705_suffix_010, List.all_append, List.all_nil, ridgeSupport705_000_checked, ridgeSupport705_001_checked, ridgeSupport705_002_checked, ridgeSupport705_003_checked, ridgeSupport705_004_checked, ridgeSupport705_005_checked, ridgeSupport705_006_checked, ridgeSupport705_007_checked, ridgeSupport705_008_checked, ridgeSupport705_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
