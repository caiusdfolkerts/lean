module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport464Part000
public import RootedSixBase01GrowthCacheRidgeSupport464Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport464_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport464_rest_009 =
    (ridgeSupport464_suffix_009, ridgeSupport464_rest_009) := by rfl
theorem ridgeSupport464_suffix_decode_008 : PackedRawNatGrowth.readList 14 5 ridgeSupport464_rest_008 =
    (ridgeSupport464_suffix_008, ridgeSupport464_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 5 0
    ridgeSupport464_rest_008 ridgeSupport464_rest_009 ridgeSupport464_rest_009
    ridgeSupport464_008 ridgeSupport464_suffix_009 ridgeSupport464_008_decode ridgeSupport464_suffix_decode_009
theorem ridgeSupport464_suffix_decode_007 : PackedRawNatGrowth.readList 14 37 ridgeSupport464_rest_007 =
    (ridgeSupport464_suffix_007, ridgeSupport464_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 5
    ridgeSupport464_rest_007 ridgeSupport464_rest_008 ridgeSupport464_rest_009
    ridgeSupport464_007 ridgeSupport464_suffix_008 ridgeSupport464_007_decode ridgeSupport464_suffix_decode_008
theorem ridgeSupport464_suffix_decode_006 : PackedRawNatGrowth.readList 14 69 ridgeSupport464_rest_006 =
    (ridgeSupport464_suffix_006, ridgeSupport464_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 37
    ridgeSupport464_rest_006 ridgeSupport464_rest_007 ridgeSupport464_rest_009
    ridgeSupport464_006 ridgeSupport464_suffix_007 ridgeSupport464_006_decode ridgeSupport464_suffix_decode_007
theorem ridgeSupport464_suffix_decode_005 : PackedRawNatGrowth.readList 14 101 ridgeSupport464_rest_005 =
    (ridgeSupport464_suffix_005, ridgeSupport464_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 69
    ridgeSupport464_rest_005 ridgeSupport464_rest_006 ridgeSupport464_rest_009
    ridgeSupport464_005 ridgeSupport464_suffix_006 ridgeSupport464_005_decode ridgeSupport464_suffix_decode_006
theorem ridgeSupport464_suffix_decode_004 : PackedRawNatGrowth.readList 14 133 ridgeSupport464_rest_004 =
    (ridgeSupport464_suffix_004, ridgeSupport464_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 101
    ridgeSupport464_rest_004 ridgeSupport464_rest_005 ridgeSupport464_rest_009
    ridgeSupport464_004 ridgeSupport464_suffix_005 ridgeSupport464_004_decode ridgeSupport464_suffix_decode_005
theorem ridgeSupport464_suffix_decode_003 : PackedRawNatGrowth.readList 14 165 ridgeSupport464_rest_003 =
    (ridgeSupport464_suffix_003, ridgeSupport464_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 133
    ridgeSupport464_rest_003 ridgeSupport464_rest_004 ridgeSupport464_rest_009
    ridgeSupport464_003 ridgeSupport464_suffix_004 ridgeSupport464_003_decode ridgeSupport464_suffix_decode_004
theorem ridgeSupport464_suffix_decode_002 : PackedRawNatGrowth.readList 14 197 ridgeSupport464_rest_002 =
    (ridgeSupport464_suffix_002, ridgeSupport464_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 165
    ridgeSupport464_rest_002 ridgeSupport464_rest_003 ridgeSupport464_rest_009
    ridgeSupport464_002 ridgeSupport464_suffix_003 ridgeSupport464_002_decode ridgeSupport464_suffix_decode_003
theorem ridgeSupport464_suffix_decode_001 : PackedRawNatGrowth.readList 14 229 ridgeSupport464_rest_001 =
    (ridgeSupport464_suffix_001, ridgeSupport464_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 197
    ridgeSupport464_rest_001 ridgeSupport464_rest_002 ridgeSupport464_rest_009
    ridgeSupport464_001 ridgeSupport464_suffix_002 ridgeSupport464_001_decode ridgeSupport464_suffix_decode_002
theorem ridgeSupport464_suffix_decode_000 : PackedRawNatGrowth.readList 14 261 ridgeSupport464_rest_000 =
    (ridgeSupport464_suffix_000, ridgeSupport464_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 229
    ridgeSupport464_rest_000 ridgeSupport464_rest_001 ridgeSupport464_rest_009
    ridgeSupport464_000 ridgeSupport464_suffix_001 ridgeSupport464_000_decode ridgeSupport464_suffix_decode_001
theorem ridgeSupport464_eq : candidateRows 464 = ridgeSupport464_suffix_000 := by
  rw [ridgeSupport464_source]
  exact congrArg Prod.fst ridgeSupport464_suffix_decode_000
theorem ridgeTest_large_464 : ridgeTest 464 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport464_eq]
    simp only [ridgeSupport464_suffix_000, ridgeSupport464_suffix_001, ridgeSupport464_suffix_002, ridgeSupport464_suffix_003, ridgeSupport464_suffix_004, ridgeSupport464_suffix_005, ridgeSupport464_suffix_006, ridgeSupport464_suffix_007, ridgeSupport464_suffix_008, ridgeSupport464_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport464_000_mask, ridgeSupport464_001_mask, ridgeSupport464_002_mask, ridgeSupport464_003_mask, ridgeSupport464_004_mask, ridgeSupport464_005_mask, ridgeSupport464_006_mask, ridgeSupport464_007_mask, ridgeSupport464_008_mask]
    decide +kernel
  · rw [ridgeSupport464_eq]
    simp only [ridgeSupport464_suffix_000, ridgeSupport464_suffix_001, ridgeSupport464_suffix_002, ridgeSupport464_suffix_003, ridgeSupport464_suffix_004, ridgeSupport464_suffix_005, ridgeSupport464_suffix_006, ridgeSupport464_suffix_007, ridgeSupport464_suffix_008, ridgeSupport464_suffix_009, List.all_append, List.all_nil, ridgeSupport464_000_checked, ridgeSupport464_001_checked, ridgeSupport464_002_checked, ridgeSupport464_003_checked, ridgeSupport464_004_checked, ridgeSupport464_005_checked, ridgeSupport464_006_checked, ridgeSupport464_007_checked, ridgeSupport464_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
