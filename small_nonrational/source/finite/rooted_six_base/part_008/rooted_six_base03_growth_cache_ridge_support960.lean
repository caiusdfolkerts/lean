module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport960Part000
public import RootedSixBase03GrowthCacheRidgeSupport960Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport960_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport960_rest_009 =
    (ridgeSupport960_suffix_009, ridgeSupport960_rest_009) := by rfl
theorem ridgeSupport960_suffix_decode_008 : PackedRawNatGrowth.readList 13 26 ridgeSupport960_rest_008 =
    (ridgeSupport960_suffix_008, ridgeSupport960_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport960_rest_008 ridgeSupport960_rest_009 ridgeSupport960_rest_009
    ridgeSupport960_008 ridgeSupport960_suffix_009 ridgeSupport960_008_decode ridgeSupport960_suffix_decode_009
theorem ridgeSupport960_suffix_decode_007 : PackedRawNatGrowth.readList 13 58 ridgeSupport960_rest_007 =
    (ridgeSupport960_suffix_007, ridgeSupport960_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport960_rest_007 ridgeSupport960_rest_008 ridgeSupport960_rest_009
    ridgeSupport960_007 ridgeSupport960_suffix_008 ridgeSupport960_007_decode ridgeSupport960_suffix_decode_008
theorem ridgeSupport960_suffix_decode_006 : PackedRawNatGrowth.readList 13 90 ridgeSupport960_rest_006 =
    (ridgeSupport960_suffix_006, ridgeSupport960_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport960_rest_006 ridgeSupport960_rest_007 ridgeSupport960_rest_009
    ridgeSupport960_006 ridgeSupport960_suffix_007 ridgeSupport960_006_decode ridgeSupport960_suffix_decode_007
theorem ridgeSupport960_suffix_decode_005 : PackedRawNatGrowth.readList 13 122 ridgeSupport960_rest_005 =
    (ridgeSupport960_suffix_005, ridgeSupport960_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport960_rest_005 ridgeSupport960_rest_006 ridgeSupport960_rest_009
    ridgeSupport960_005 ridgeSupport960_suffix_006 ridgeSupport960_005_decode ridgeSupport960_suffix_decode_006
theorem ridgeSupport960_suffix_decode_004 : PackedRawNatGrowth.readList 13 154 ridgeSupport960_rest_004 =
    (ridgeSupport960_suffix_004, ridgeSupport960_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport960_rest_004 ridgeSupport960_rest_005 ridgeSupport960_rest_009
    ridgeSupport960_004 ridgeSupport960_suffix_005 ridgeSupport960_004_decode ridgeSupport960_suffix_decode_005
theorem ridgeSupport960_suffix_decode_003 : PackedRawNatGrowth.readList 13 186 ridgeSupport960_rest_003 =
    (ridgeSupport960_suffix_003, ridgeSupport960_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport960_rest_003 ridgeSupport960_rest_004 ridgeSupport960_rest_009
    ridgeSupport960_003 ridgeSupport960_suffix_004 ridgeSupport960_003_decode ridgeSupport960_suffix_decode_004
theorem ridgeSupport960_suffix_decode_002 : PackedRawNatGrowth.readList 13 218 ridgeSupport960_rest_002 =
    (ridgeSupport960_suffix_002, ridgeSupport960_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport960_rest_002 ridgeSupport960_rest_003 ridgeSupport960_rest_009
    ridgeSupport960_002 ridgeSupport960_suffix_003 ridgeSupport960_002_decode ridgeSupport960_suffix_decode_003
theorem ridgeSupport960_suffix_decode_001 : PackedRawNatGrowth.readList 13 250 ridgeSupport960_rest_001 =
    (ridgeSupport960_suffix_001, ridgeSupport960_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport960_rest_001 ridgeSupport960_rest_002 ridgeSupport960_rest_009
    ridgeSupport960_001 ridgeSupport960_suffix_002 ridgeSupport960_001_decode ridgeSupport960_suffix_decode_002
theorem ridgeSupport960_suffix_decode_000 : PackedRawNatGrowth.readList 13 282 ridgeSupport960_rest_000 =
    (ridgeSupport960_suffix_000, ridgeSupport960_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport960_rest_000 ridgeSupport960_rest_001 ridgeSupport960_rest_009
    ridgeSupport960_000 ridgeSupport960_suffix_001 ridgeSupport960_000_decode ridgeSupport960_suffix_decode_001
theorem ridgeSupport960_eq : candidateSupports 960 = ridgeSupport960_suffix_000 := by
  rw [ridgeSupport960_source]
  exact congrArg Prod.fst ridgeSupport960_suffix_decode_000
theorem ridgeTest_large_960 : ridgeTest 960 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 960 = ridgeSupport960_suffix_000 from ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport960_000_mask, ridgeSupport960_001_mask, ridgeSupport960_002_mask, ridgeSupport960_003_mask, ridgeSupport960_004_mask, ridgeSupport960_005_mask, ridgeSupport960_006_mask, ridgeSupport960_007_mask, ridgeSupport960_008_mask]
    decide +kernel
  · rw [show candidateRows 960 = ridgeSupport960_suffix_000 from ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, List.all_append, List.all_nil, ridgeSupport960_000_checked, ridgeSupport960_001_checked, ridgeSupport960_002_checked, ridgeSupport960_003_checked, ridgeSupport960_004_checked, ridgeSupport960_005_checked, ridgeSupport960_006_checked, ridgeSupport960_007_checked, ridgeSupport960_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
