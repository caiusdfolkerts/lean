module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport928Part000
public import RootedSixBase01GrowthCacheRidgeSupport928Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport928_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport928_rest_009 =
    (ridgeSupport928_suffix_009, ridgeSupport928_rest_009) := by rfl
theorem ridgeSupport928_suffix_decode_008 : PackedRawNatGrowth.readList 14 5 ridgeSupport928_rest_008 =
    (ridgeSupport928_suffix_008, ridgeSupport928_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 5 0
    ridgeSupport928_rest_008 ridgeSupport928_rest_009 ridgeSupport928_rest_009
    ridgeSupport928_008 ridgeSupport928_suffix_009 ridgeSupport928_008_decode ridgeSupport928_suffix_decode_009
theorem ridgeSupport928_suffix_decode_007 : PackedRawNatGrowth.readList 14 37 ridgeSupport928_rest_007 =
    (ridgeSupport928_suffix_007, ridgeSupport928_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 5
    ridgeSupport928_rest_007 ridgeSupport928_rest_008 ridgeSupport928_rest_009
    ridgeSupport928_007 ridgeSupport928_suffix_008 ridgeSupport928_007_decode ridgeSupport928_suffix_decode_008
theorem ridgeSupport928_suffix_decode_006 : PackedRawNatGrowth.readList 14 69 ridgeSupport928_rest_006 =
    (ridgeSupport928_suffix_006, ridgeSupport928_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 37
    ridgeSupport928_rest_006 ridgeSupport928_rest_007 ridgeSupport928_rest_009
    ridgeSupport928_006 ridgeSupport928_suffix_007 ridgeSupport928_006_decode ridgeSupport928_suffix_decode_007
theorem ridgeSupport928_suffix_decode_005 : PackedRawNatGrowth.readList 14 101 ridgeSupport928_rest_005 =
    (ridgeSupport928_suffix_005, ridgeSupport928_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 69
    ridgeSupport928_rest_005 ridgeSupport928_rest_006 ridgeSupport928_rest_009
    ridgeSupport928_005 ridgeSupport928_suffix_006 ridgeSupport928_005_decode ridgeSupport928_suffix_decode_006
theorem ridgeSupport928_suffix_decode_004 : PackedRawNatGrowth.readList 14 133 ridgeSupport928_rest_004 =
    (ridgeSupport928_suffix_004, ridgeSupport928_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 101
    ridgeSupport928_rest_004 ridgeSupport928_rest_005 ridgeSupport928_rest_009
    ridgeSupport928_004 ridgeSupport928_suffix_005 ridgeSupport928_004_decode ridgeSupport928_suffix_decode_005
theorem ridgeSupport928_suffix_decode_003 : PackedRawNatGrowth.readList 14 165 ridgeSupport928_rest_003 =
    (ridgeSupport928_suffix_003, ridgeSupport928_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 133
    ridgeSupport928_rest_003 ridgeSupport928_rest_004 ridgeSupport928_rest_009
    ridgeSupport928_003 ridgeSupport928_suffix_004 ridgeSupport928_003_decode ridgeSupport928_suffix_decode_004
theorem ridgeSupport928_suffix_decode_002 : PackedRawNatGrowth.readList 14 197 ridgeSupport928_rest_002 =
    (ridgeSupport928_suffix_002, ridgeSupport928_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 165
    ridgeSupport928_rest_002 ridgeSupport928_rest_003 ridgeSupport928_rest_009
    ridgeSupport928_002 ridgeSupport928_suffix_003 ridgeSupport928_002_decode ridgeSupport928_suffix_decode_003
theorem ridgeSupport928_suffix_decode_001 : PackedRawNatGrowth.readList 14 229 ridgeSupport928_rest_001 =
    (ridgeSupport928_suffix_001, ridgeSupport928_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 197
    ridgeSupport928_rest_001 ridgeSupport928_rest_002 ridgeSupport928_rest_009
    ridgeSupport928_001 ridgeSupport928_suffix_002 ridgeSupport928_001_decode ridgeSupport928_suffix_decode_002
theorem ridgeSupport928_suffix_decode_000 : PackedRawNatGrowth.readList 14 261 ridgeSupport928_rest_000 =
    (ridgeSupport928_suffix_000, ridgeSupport928_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 229
    ridgeSupport928_rest_000 ridgeSupport928_rest_001 ridgeSupport928_rest_009
    ridgeSupport928_000 ridgeSupport928_suffix_001 ridgeSupport928_000_decode ridgeSupport928_suffix_decode_001
theorem ridgeSupport928_eq : candidateRows 928 = ridgeSupport928_suffix_000 := by
  rw [ridgeSupport928_source]
  exact congrArg Prod.fst ridgeSupport928_suffix_decode_000
theorem ridgeTest_large_928 : ridgeTest 928 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport928_eq]
    simp only [ridgeSupport928_suffix_000, ridgeSupport928_suffix_001, ridgeSupport928_suffix_002, ridgeSupport928_suffix_003, ridgeSupport928_suffix_004, ridgeSupport928_suffix_005, ridgeSupport928_suffix_006, ridgeSupport928_suffix_007, ridgeSupport928_suffix_008, ridgeSupport928_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport928_000_mask, ridgeSupport928_001_mask, ridgeSupport928_002_mask, ridgeSupport928_003_mask, ridgeSupport928_004_mask, ridgeSupport928_005_mask, ridgeSupport928_006_mask, ridgeSupport928_007_mask, ridgeSupport928_008_mask]
    decide +kernel
  · rw [ridgeSupport928_eq]
    simp only [ridgeSupport928_suffix_000, ridgeSupport928_suffix_001, ridgeSupport928_suffix_002, ridgeSupport928_suffix_003, ridgeSupport928_suffix_004, ridgeSupport928_suffix_005, ridgeSupport928_suffix_006, ridgeSupport928_suffix_007, ridgeSupport928_suffix_008, ridgeSupport928_suffix_009, List.all_append, List.all_nil, ridgeSupport928_000_checked, ridgeSupport928_001_checked, ridgeSupport928_002_checked, ridgeSupport928_003_checked, ridgeSupport928_004_checked, ridgeSupport928_005_checked, ridgeSupport928_006_checked, ridgeSupport928_007_checked, ridgeSupport928_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
