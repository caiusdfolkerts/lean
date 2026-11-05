module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport736Part000
public import RootedSixBase01GrowthCacheRidgeSupport736Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport736_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport736_rest_009 =
    (ridgeSupport736_suffix_009, ridgeSupport736_rest_009) := by rfl
theorem ridgeSupport736_suffix_decode_008 : PackedRawNatGrowth.readList 14 5 ridgeSupport736_rest_008 =
    (ridgeSupport736_suffix_008, ridgeSupport736_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 5 0
    ridgeSupport736_rest_008 ridgeSupport736_rest_009 ridgeSupport736_rest_009
    ridgeSupport736_008 ridgeSupport736_suffix_009 ridgeSupport736_008_decode ridgeSupport736_suffix_decode_009
theorem ridgeSupport736_suffix_decode_007 : PackedRawNatGrowth.readList 14 37 ridgeSupport736_rest_007 =
    (ridgeSupport736_suffix_007, ridgeSupport736_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 5
    ridgeSupport736_rest_007 ridgeSupport736_rest_008 ridgeSupport736_rest_009
    ridgeSupport736_007 ridgeSupport736_suffix_008 ridgeSupport736_007_decode ridgeSupport736_suffix_decode_008
theorem ridgeSupport736_suffix_decode_006 : PackedRawNatGrowth.readList 14 69 ridgeSupport736_rest_006 =
    (ridgeSupport736_suffix_006, ridgeSupport736_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 37
    ridgeSupport736_rest_006 ridgeSupport736_rest_007 ridgeSupport736_rest_009
    ridgeSupport736_006 ridgeSupport736_suffix_007 ridgeSupport736_006_decode ridgeSupport736_suffix_decode_007
theorem ridgeSupport736_suffix_decode_005 : PackedRawNatGrowth.readList 14 101 ridgeSupport736_rest_005 =
    (ridgeSupport736_suffix_005, ridgeSupport736_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 69
    ridgeSupport736_rest_005 ridgeSupport736_rest_006 ridgeSupport736_rest_009
    ridgeSupport736_005 ridgeSupport736_suffix_006 ridgeSupport736_005_decode ridgeSupport736_suffix_decode_006
theorem ridgeSupport736_suffix_decode_004 : PackedRawNatGrowth.readList 14 133 ridgeSupport736_rest_004 =
    (ridgeSupport736_suffix_004, ridgeSupport736_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 101
    ridgeSupport736_rest_004 ridgeSupport736_rest_005 ridgeSupport736_rest_009
    ridgeSupport736_004 ridgeSupport736_suffix_005 ridgeSupport736_004_decode ridgeSupport736_suffix_decode_005
theorem ridgeSupport736_suffix_decode_003 : PackedRawNatGrowth.readList 14 165 ridgeSupport736_rest_003 =
    (ridgeSupport736_suffix_003, ridgeSupport736_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 133
    ridgeSupport736_rest_003 ridgeSupport736_rest_004 ridgeSupport736_rest_009
    ridgeSupport736_003 ridgeSupport736_suffix_004 ridgeSupport736_003_decode ridgeSupport736_suffix_decode_004
theorem ridgeSupport736_suffix_decode_002 : PackedRawNatGrowth.readList 14 197 ridgeSupport736_rest_002 =
    (ridgeSupport736_suffix_002, ridgeSupport736_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 165
    ridgeSupport736_rest_002 ridgeSupport736_rest_003 ridgeSupport736_rest_009
    ridgeSupport736_002 ridgeSupport736_suffix_003 ridgeSupport736_002_decode ridgeSupport736_suffix_decode_003
theorem ridgeSupport736_suffix_decode_001 : PackedRawNatGrowth.readList 14 229 ridgeSupport736_rest_001 =
    (ridgeSupport736_suffix_001, ridgeSupport736_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 197
    ridgeSupport736_rest_001 ridgeSupport736_rest_002 ridgeSupport736_rest_009
    ridgeSupport736_001 ridgeSupport736_suffix_002 ridgeSupport736_001_decode ridgeSupport736_suffix_decode_002
theorem ridgeSupport736_suffix_decode_000 : PackedRawNatGrowth.readList 14 261 ridgeSupport736_rest_000 =
    (ridgeSupport736_suffix_000, ridgeSupport736_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 229
    ridgeSupport736_rest_000 ridgeSupport736_rest_001 ridgeSupport736_rest_009
    ridgeSupport736_000 ridgeSupport736_suffix_001 ridgeSupport736_000_decode ridgeSupport736_suffix_decode_001
theorem ridgeSupport736_eq : candidateRows 736 = ridgeSupport736_suffix_000 := by
  rw [ridgeSupport736_source]
  exact congrArg Prod.fst ridgeSupport736_suffix_decode_000
theorem ridgeTest_large_736 : ridgeTest 736 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport736_eq]
    simp only [ridgeSupport736_suffix_000, ridgeSupport736_suffix_001, ridgeSupport736_suffix_002, ridgeSupport736_suffix_003, ridgeSupport736_suffix_004, ridgeSupport736_suffix_005, ridgeSupport736_suffix_006, ridgeSupport736_suffix_007, ridgeSupport736_suffix_008, ridgeSupport736_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport736_000_mask, ridgeSupport736_001_mask, ridgeSupport736_002_mask, ridgeSupport736_003_mask, ridgeSupport736_004_mask, ridgeSupport736_005_mask, ridgeSupport736_006_mask, ridgeSupport736_007_mask, ridgeSupport736_008_mask]
    decide +kernel
  · rw [ridgeSupport736_eq]
    simp only [ridgeSupport736_suffix_000, ridgeSupport736_suffix_001, ridgeSupport736_suffix_002, ridgeSupport736_suffix_003, ridgeSupport736_suffix_004, ridgeSupport736_suffix_005, ridgeSupport736_suffix_006, ridgeSupport736_suffix_007, ridgeSupport736_suffix_008, ridgeSupport736_suffix_009, List.all_append, List.all_nil, ridgeSupport736_000_checked, ridgeSupport736_001_checked, ridgeSupport736_002_checked, ridgeSupport736_003_checked, ridgeSupport736_004_checked, ridgeSupport736_005_checked, ridgeSupport736_006_checked, ridgeSupport736_007_checked, ridgeSupport736_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
