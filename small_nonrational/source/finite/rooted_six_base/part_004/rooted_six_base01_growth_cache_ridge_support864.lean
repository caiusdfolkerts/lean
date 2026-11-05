module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport864Part000
public import RootedSixBase01GrowthCacheRidgeSupport864Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport864_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport864_rest_009 =
    (ridgeSupport864_suffix_009, ridgeSupport864_rest_009) := by rfl
theorem ridgeSupport864_suffix_decode_008 : PackedRawNatGrowth.readList 14 5 ridgeSupport864_rest_008 =
    (ridgeSupport864_suffix_008, ridgeSupport864_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 5 0
    ridgeSupport864_rest_008 ridgeSupport864_rest_009 ridgeSupport864_rest_009
    ridgeSupport864_008 ridgeSupport864_suffix_009 ridgeSupport864_008_decode ridgeSupport864_suffix_decode_009
theorem ridgeSupport864_suffix_decode_007 : PackedRawNatGrowth.readList 14 37 ridgeSupport864_rest_007 =
    (ridgeSupport864_suffix_007, ridgeSupport864_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 5
    ridgeSupport864_rest_007 ridgeSupport864_rest_008 ridgeSupport864_rest_009
    ridgeSupport864_007 ridgeSupport864_suffix_008 ridgeSupport864_007_decode ridgeSupport864_suffix_decode_008
theorem ridgeSupport864_suffix_decode_006 : PackedRawNatGrowth.readList 14 69 ridgeSupport864_rest_006 =
    (ridgeSupport864_suffix_006, ridgeSupport864_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 37
    ridgeSupport864_rest_006 ridgeSupport864_rest_007 ridgeSupport864_rest_009
    ridgeSupport864_006 ridgeSupport864_suffix_007 ridgeSupport864_006_decode ridgeSupport864_suffix_decode_007
theorem ridgeSupport864_suffix_decode_005 : PackedRawNatGrowth.readList 14 101 ridgeSupport864_rest_005 =
    (ridgeSupport864_suffix_005, ridgeSupport864_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 69
    ridgeSupport864_rest_005 ridgeSupport864_rest_006 ridgeSupport864_rest_009
    ridgeSupport864_005 ridgeSupport864_suffix_006 ridgeSupport864_005_decode ridgeSupport864_suffix_decode_006
theorem ridgeSupport864_suffix_decode_004 : PackedRawNatGrowth.readList 14 133 ridgeSupport864_rest_004 =
    (ridgeSupport864_suffix_004, ridgeSupport864_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 101
    ridgeSupport864_rest_004 ridgeSupport864_rest_005 ridgeSupport864_rest_009
    ridgeSupport864_004 ridgeSupport864_suffix_005 ridgeSupport864_004_decode ridgeSupport864_suffix_decode_005
theorem ridgeSupport864_suffix_decode_003 : PackedRawNatGrowth.readList 14 165 ridgeSupport864_rest_003 =
    (ridgeSupport864_suffix_003, ridgeSupport864_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 133
    ridgeSupport864_rest_003 ridgeSupport864_rest_004 ridgeSupport864_rest_009
    ridgeSupport864_003 ridgeSupport864_suffix_004 ridgeSupport864_003_decode ridgeSupport864_suffix_decode_004
theorem ridgeSupport864_suffix_decode_002 : PackedRawNatGrowth.readList 14 197 ridgeSupport864_rest_002 =
    (ridgeSupport864_suffix_002, ridgeSupport864_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 165
    ridgeSupport864_rest_002 ridgeSupport864_rest_003 ridgeSupport864_rest_009
    ridgeSupport864_002 ridgeSupport864_suffix_003 ridgeSupport864_002_decode ridgeSupport864_suffix_decode_003
theorem ridgeSupport864_suffix_decode_001 : PackedRawNatGrowth.readList 14 229 ridgeSupport864_rest_001 =
    (ridgeSupport864_suffix_001, ridgeSupport864_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 197
    ridgeSupport864_rest_001 ridgeSupport864_rest_002 ridgeSupport864_rest_009
    ridgeSupport864_001 ridgeSupport864_suffix_002 ridgeSupport864_001_decode ridgeSupport864_suffix_decode_002
theorem ridgeSupport864_suffix_decode_000 : PackedRawNatGrowth.readList 14 261 ridgeSupport864_rest_000 =
    (ridgeSupport864_suffix_000, ridgeSupport864_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 229
    ridgeSupport864_rest_000 ridgeSupport864_rest_001 ridgeSupport864_rest_009
    ridgeSupport864_000 ridgeSupport864_suffix_001 ridgeSupport864_000_decode ridgeSupport864_suffix_decode_001
theorem ridgeSupport864_eq : candidateRows 864 = ridgeSupport864_suffix_000 := by
  rw [ridgeSupport864_source]
  exact congrArg Prod.fst ridgeSupport864_suffix_decode_000
theorem ridgeTest_large_864 : ridgeTest 864 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport864_eq]
    simp only [ridgeSupport864_suffix_000, ridgeSupport864_suffix_001, ridgeSupport864_suffix_002, ridgeSupport864_suffix_003, ridgeSupport864_suffix_004, ridgeSupport864_suffix_005, ridgeSupport864_suffix_006, ridgeSupport864_suffix_007, ridgeSupport864_suffix_008, ridgeSupport864_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport864_000_mask, ridgeSupport864_001_mask, ridgeSupport864_002_mask, ridgeSupport864_003_mask, ridgeSupport864_004_mask, ridgeSupport864_005_mask, ridgeSupport864_006_mask, ridgeSupport864_007_mask, ridgeSupport864_008_mask]
    decide +kernel
  · rw [ridgeSupport864_eq]
    simp only [ridgeSupport864_suffix_000, ridgeSupport864_suffix_001, ridgeSupport864_suffix_002, ridgeSupport864_suffix_003, ridgeSupport864_suffix_004, ridgeSupport864_suffix_005, ridgeSupport864_suffix_006, ridgeSupport864_suffix_007, ridgeSupport864_suffix_008, ridgeSupport864_suffix_009, List.all_append, List.all_nil, ridgeSupport864_000_checked, ridgeSupport864_001_checked, ridgeSupport864_002_checked, ridgeSupport864_003_checked, ridgeSupport864_004_checked, ridgeSupport864_005_checked, ridgeSupport864_006_checked, ridgeSupport864_007_checked, ridgeSupport864_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
