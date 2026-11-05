module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport480Part000
public import RootedSixBase01GrowthCacheRidgeSupport480Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport480_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport480_rest_009 =
    (ridgeSupport480_suffix_009, ridgeSupport480_rest_009) := by rfl
theorem ridgeSupport480_suffix_decode_008 : PackedRawNatGrowth.readList 14 5 ridgeSupport480_rest_008 =
    (ridgeSupport480_suffix_008, ridgeSupport480_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 5 0
    ridgeSupport480_rest_008 ridgeSupport480_rest_009 ridgeSupport480_rest_009
    ridgeSupport480_008 ridgeSupport480_suffix_009 ridgeSupport480_008_decode ridgeSupport480_suffix_decode_009
theorem ridgeSupport480_suffix_decode_007 : PackedRawNatGrowth.readList 14 37 ridgeSupport480_rest_007 =
    (ridgeSupport480_suffix_007, ridgeSupport480_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 5
    ridgeSupport480_rest_007 ridgeSupport480_rest_008 ridgeSupport480_rest_009
    ridgeSupport480_007 ridgeSupport480_suffix_008 ridgeSupport480_007_decode ridgeSupport480_suffix_decode_008
theorem ridgeSupport480_suffix_decode_006 : PackedRawNatGrowth.readList 14 69 ridgeSupport480_rest_006 =
    (ridgeSupport480_suffix_006, ridgeSupport480_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 37
    ridgeSupport480_rest_006 ridgeSupport480_rest_007 ridgeSupport480_rest_009
    ridgeSupport480_006 ridgeSupport480_suffix_007 ridgeSupport480_006_decode ridgeSupport480_suffix_decode_007
theorem ridgeSupport480_suffix_decode_005 : PackedRawNatGrowth.readList 14 101 ridgeSupport480_rest_005 =
    (ridgeSupport480_suffix_005, ridgeSupport480_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 69
    ridgeSupport480_rest_005 ridgeSupport480_rest_006 ridgeSupport480_rest_009
    ridgeSupport480_005 ridgeSupport480_suffix_006 ridgeSupport480_005_decode ridgeSupport480_suffix_decode_006
theorem ridgeSupport480_suffix_decode_004 : PackedRawNatGrowth.readList 14 133 ridgeSupport480_rest_004 =
    (ridgeSupport480_suffix_004, ridgeSupport480_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 101
    ridgeSupport480_rest_004 ridgeSupport480_rest_005 ridgeSupport480_rest_009
    ridgeSupport480_004 ridgeSupport480_suffix_005 ridgeSupport480_004_decode ridgeSupport480_suffix_decode_005
theorem ridgeSupport480_suffix_decode_003 : PackedRawNatGrowth.readList 14 165 ridgeSupport480_rest_003 =
    (ridgeSupport480_suffix_003, ridgeSupport480_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 133
    ridgeSupport480_rest_003 ridgeSupport480_rest_004 ridgeSupport480_rest_009
    ridgeSupport480_003 ridgeSupport480_suffix_004 ridgeSupport480_003_decode ridgeSupport480_suffix_decode_004
theorem ridgeSupport480_suffix_decode_002 : PackedRawNatGrowth.readList 14 197 ridgeSupport480_rest_002 =
    (ridgeSupport480_suffix_002, ridgeSupport480_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 165
    ridgeSupport480_rest_002 ridgeSupport480_rest_003 ridgeSupport480_rest_009
    ridgeSupport480_002 ridgeSupport480_suffix_003 ridgeSupport480_002_decode ridgeSupport480_suffix_decode_003
theorem ridgeSupport480_suffix_decode_001 : PackedRawNatGrowth.readList 14 229 ridgeSupport480_rest_001 =
    (ridgeSupport480_suffix_001, ridgeSupport480_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 197
    ridgeSupport480_rest_001 ridgeSupport480_rest_002 ridgeSupport480_rest_009
    ridgeSupport480_001 ridgeSupport480_suffix_002 ridgeSupport480_001_decode ridgeSupport480_suffix_decode_002
theorem ridgeSupport480_suffix_decode_000 : PackedRawNatGrowth.readList 14 261 ridgeSupport480_rest_000 =
    (ridgeSupport480_suffix_000, ridgeSupport480_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 229
    ridgeSupport480_rest_000 ridgeSupport480_rest_001 ridgeSupport480_rest_009
    ridgeSupport480_000 ridgeSupport480_suffix_001 ridgeSupport480_000_decode ridgeSupport480_suffix_decode_001
theorem ridgeSupport480_eq : candidateRows 480 = ridgeSupport480_suffix_000 := by
  rw [ridgeSupport480_source]
  exact congrArg Prod.fst ridgeSupport480_suffix_decode_000
theorem ridgeTest_large_480 : ridgeTest 480 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport480_eq]
    simp only [ridgeSupport480_suffix_000, ridgeSupport480_suffix_001, ridgeSupport480_suffix_002, ridgeSupport480_suffix_003, ridgeSupport480_suffix_004, ridgeSupport480_suffix_005, ridgeSupport480_suffix_006, ridgeSupport480_suffix_007, ridgeSupport480_suffix_008, ridgeSupport480_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport480_000_mask, ridgeSupport480_001_mask, ridgeSupport480_002_mask, ridgeSupport480_003_mask, ridgeSupport480_004_mask, ridgeSupport480_005_mask, ridgeSupport480_006_mask, ridgeSupport480_007_mask, ridgeSupport480_008_mask]
    decide +kernel
  · rw [ridgeSupport480_eq]
    simp only [ridgeSupport480_suffix_000, ridgeSupport480_suffix_001, ridgeSupport480_suffix_002, ridgeSupport480_suffix_003, ridgeSupport480_suffix_004, ridgeSupport480_suffix_005, ridgeSupport480_suffix_006, ridgeSupport480_suffix_007, ridgeSupport480_suffix_008, ridgeSupport480_suffix_009, List.all_append, List.all_nil, ridgeSupport480_000_checked, ridgeSupport480_001_checked, ridgeSupport480_002_checked, ridgeSupport480_003_checked, ridgeSupport480_004_checked, ridgeSupport480_005_checked, ridgeSupport480_006_checked, ridgeSupport480_007_checked, ridgeSupport480_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
