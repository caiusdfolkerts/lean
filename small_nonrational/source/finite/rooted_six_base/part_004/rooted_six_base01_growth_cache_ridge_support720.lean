module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport720Part000
public import RootedSixBase01GrowthCacheRidgeSupport720Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport720_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport720_rest_009 =
    (ridgeSupport720_suffix_009, ridgeSupport720_rest_009) := by rfl
theorem ridgeSupport720_suffix_decode_008 : PackedRawNatGrowth.readList 14 5 ridgeSupport720_rest_008 =
    (ridgeSupport720_suffix_008, ridgeSupport720_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 5 0
    ridgeSupport720_rest_008 ridgeSupport720_rest_009 ridgeSupport720_rest_009
    ridgeSupport720_008 ridgeSupport720_suffix_009 ridgeSupport720_008_decode ridgeSupport720_suffix_decode_009
theorem ridgeSupport720_suffix_decode_007 : PackedRawNatGrowth.readList 14 37 ridgeSupport720_rest_007 =
    (ridgeSupport720_suffix_007, ridgeSupport720_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 5
    ridgeSupport720_rest_007 ridgeSupport720_rest_008 ridgeSupport720_rest_009
    ridgeSupport720_007 ridgeSupport720_suffix_008 ridgeSupport720_007_decode ridgeSupport720_suffix_decode_008
theorem ridgeSupport720_suffix_decode_006 : PackedRawNatGrowth.readList 14 69 ridgeSupport720_rest_006 =
    (ridgeSupport720_suffix_006, ridgeSupport720_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 37
    ridgeSupport720_rest_006 ridgeSupport720_rest_007 ridgeSupport720_rest_009
    ridgeSupport720_006 ridgeSupport720_suffix_007 ridgeSupport720_006_decode ridgeSupport720_suffix_decode_007
theorem ridgeSupport720_suffix_decode_005 : PackedRawNatGrowth.readList 14 101 ridgeSupport720_rest_005 =
    (ridgeSupport720_suffix_005, ridgeSupport720_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 69
    ridgeSupport720_rest_005 ridgeSupport720_rest_006 ridgeSupport720_rest_009
    ridgeSupport720_005 ridgeSupport720_suffix_006 ridgeSupport720_005_decode ridgeSupport720_suffix_decode_006
theorem ridgeSupport720_suffix_decode_004 : PackedRawNatGrowth.readList 14 133 ridgeSupport720_rest_004 =
    (ridgeSupport720_suffix_004, ridgeSupport720_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 101
    ridgeSupport720_rest_004 ridgeSupport720_rest_005 ridgeSupport720_rest_009
    ridgeSupport720_004 ridgeSupport720_suffix_005 ridgeSupport720_004_decode ridgeSupport720_suffix_decode_005
theorem ridgeSupport720_suffix_decode_003 : PackedRawNatGrowth.readList 14 165 ridgeSupport720_rest_003 =
    (ridgeSupport720_suffix_003, ridgeSupport720_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 133
    ridgeSupport720_rest_003 ridgeSupport720_rest_004 ridgeSupport720_rest_009
    ridgeSupport720_003 ridgeSupport720_suffix_004 ridgeSupport720_003_decode ridgeSupport720_suffix_decode_004
theorem ridgeSupport720_suffix_decode_002 : PackedRawNatGrowth.readList 14 197 ridgeSupport720_rest_002 =
    (ridgeSupport720_suffix_002, ridgeSupport720_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 165
    ridgeSupport720_rest_002 ridgeSupport720_rest_003 ridgeSupport720_rest_009
    ridgeSupport720_002 ridgeSupport720_suffix_003 ridgeSupport720_002_decode ridgeSupport720_suffix_decode_003
theorem ridgeSupport720_suffix_decode_001 : PackedRawNatGrowth.readList 14 229 ridgeSupport720_rest_001 =
    (ridgeSupport720_suffix_001, ridgeSupport720_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 197
    ridgeSupport720_rest_001 ridgeSupport720_rest_002 ridgeSupport720_rest_009
    ridgeSupport720_001 ridgeSupport720_suffix_002 ridgeSupport720_001_decode ridgeSupport720_suffix_decode_002
theorem ridgeSupport720_suffix_decode_000 : PackedRawNatGrowth.readList 14 261 ridgeSupport720_rest_000 =
    (ridgeSupport720_suffix_000, ridgeSupport720_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 229
    ridgeSupport720_rest_000 ridgeSupport720_rest_001 ridgeSupport720_rest_009
    ridgeSupport720_000 ridgeSupport720_suffix_001 ridgeSupport720_000_decode ridgeSupport720_suffix_decode_001
theorem ridgeSupport720_eq : candidateRows 720 = ridgeSupport720_suffix_000 := by
  rw [ridgeSupport720_source]
  exact congrArg Prod.fst ridgeSupport720_suffix_decode_000
theorem ridgeTest_large_720 : ridgeTest 720 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport720_eq]
    simp only [ridgeSupport720_suffix_000, ridgeSupport720_suffix_001, ridgeSupport720_suffix_002, ridgeSupport720_suffix_003, ridgeSupport720_suffix_004, ridgeSupport720_suffix_005, ridgeSupport720_suffix_006, ridgeSupport720_suffix_007, ridgeSupport720_suffix_008, ridgeSupport720_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport720_000_mask, ridgeSupport720_001_mask, ridgeSupport720_002_mask, ridgeSupport720_003_mask, ridgeSupport720_004_mask, ridgeSupport720_005_mask, ridgeSupport720_006_mask, ridgeSupport720_007_mask, ridgeSupport720_008_mask]
    decide +kernel
  · rw [ridgeSupport720_eq]
    simp only [ridgeSupport720_suffix_000, ridgeSupport720_suffix_001, ridgeSupport720_suffix_002, ridgeSupport720_suffix_003, ridgeSupport720_suffix_004, ridgeSupport720_suffix_005, ridgeSupport720_suffix_006, ridgeSupport720_suffix_007, ridgeSupport720_suffix_008, ridgeSupport720_suffix_009, List.all_append, List.all_nil, ridgeSupport720_000_checked, ridgeSupport720_001_checked, ridgeSupport720_002_checked, ridgeSupport720_003_checked, ridgeSupport720_004_checked, ridgeSupport720_005_checked, ridgeSupport720_006_checked, ridgeSupport720_007_checked, ridgeSupport720_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
