module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport134Part000
public import RootedSixBase02GrowthCacheRidgeSupport134Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport134_suffix_decode_010 : PackedRawNatGrowth.readList 13 0 ridgeSupport134_rest_010 =
    (ridgeSupport134_suffix_010, ridgeSupport134_rest_010) := by rfl
theorem ridgeSupport134_suffix_decode_009 : PackedRawNatGrowth.readList 13 17 ridgeSupport134_rest_009 =
    (ridgeSupport134_suffix_009, ridgeSupport134_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 17 0
    ridgeSupport134_rest_009 ridgeSupport134_rest_010 ridgeSupport134_rest_010
    ridgeSupport134_009 ridgeSupport134_suffix_010 ridgeSupport134_009_decode ridgeSupport134_suffix_decode_010
theorem ridgeSupport134_suffix_decode_008 : PackedRawNatGrowth.readList 13 49 ridgeSupport134_rest_008 =
    (ridgeSupport134_suffix_008, ridgeSupport134_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 17
    ridgeSupport134_rest_008 ridgeSupport134_rest_009 ridgeSupport134_rest_010
    ridgeSupport134_008 ridgeSupport134_suffix_009 ridgeSupport134_008_decode ridgeSupport134_suffix_decode_009
theorem ridgeSupport134_suffix_decode_007 : PackedRawNatGrowth.readList 13 81 ridgeSupport134_rest_007 =
    (ridgeSupport134_suffix_007, ridgeSupport134_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 49
    ridgeSupport134_rest_007 ridgeSupport134_rest_008 ridgeSupport134_rest_010
    ridgeSupport134_007 ridgeSupport134_suffix_008 ridgeSupport134_007_decode ridgeSupport134_suffix_decode_008
theorem ridgeSupport134_suffix_decode_006 : PackedRawNatGrowth.readList 13 113 ridgeSupport134_rest_006 =
    (ridgeSupport134_suffix_006, ridgeSupport134_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 81
    ridgeSupport134_rest_006 ridgeSupport134_rest_007 ridgeSupport134_rest_010
    ridgeSupport134_006 ridgeSupport134_suffix_007 ridgeSupport134_006_decode ridgeSupport134_suffix_decode_007
theorem ridgeSupport134_suffix_decode_005 : PackedRawNatGrowth.readList 13 145 ridgeSupport134_rest_005 =
    (ridgeSupport134_suffix_005, ridgeSupport134_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 113
    ridgeSupport134_rest_005 ridgeSupport134_rest_006 ridgeSupport134_rest_010
    ridgeSupport134_005 ridgeSupport134_suffix_006 ridgeSupport134_005_decode ridgeSupport134_suffix_decode_006
theorem ridgeSupport134_suffix_decode_004 : PackedRawNatGrowth.readList 13 177 ridgeSupport134_rest_004 =
    (ridgeSupport134_suffix_004, ridgeSupport134_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 145
    ridgeSupport134_rest_004 ridgeSupport134_rest_005 ridgeSupport134_rest_010
    ridgeSupport134_004 ridgeSupport134_suffix_005 ridgeSupport134_004_decode ridgeSupport134_suffix_decode_005
theorem ridgeSupport134_suffix_decode_003 : PackedRawNatGrowth.readList 13 209 ridgeSupport134_rest_003 =
    (ridgeSupport134_suffix_003, ridgeSupport134_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 177
    ridgeSupport134_rest_003 ridgeSupport134_rest_004 ridgeSupport134_rest_010
    ridgeSupport134_003 ridgeSupport134_suffix_004 ridgeSupport134_003_decode ridgeSupport134_suffix_decode_004
theorem ridgeSupport134_suffix_decode_002 : PackedRawNatGrowth.readList 13 241 ridgeSupport134_rest_002 =
    (ridgeSupport134_suffix_002, ridgeSupport134_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 209
    ridgeSupport134_rest_002 ridgeSupport134_rest_003 ridgeSupport134_rest_010
    ridgeSupport134_002 ridgeSupport134_suffix_003 ridgeSupport134_002_decode ridgeSupport134_suffix_decode_003
theorem ridgeSupport134_suffix_decode_001 : PackedRawNatGrowth.readList 13 273 ridgeSupport134_rest_001 =
    (ridgeSupport134_suffix_001, ridgeSupport134_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 241
    ridgeSupport134_rest_001 ridgeSupport134_rest_002 ridgeSupport134_rest_010
    ridgeSupport134_001 ridgeSupport134_suffix_002 ridgeSupport134_001_decode ridgeSupport134_suffix_decode_002
theorem ridgeSupport134_suffix_decode_000 : PackedRawNatGrowth.readList 13 305 ridgeSupport134_rest_000 =
    (ridgeSupport134_suffix_000, ridgeSupport134_rest_010) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 273
    ridgeSupport134_rest_000 ridgeSupport134_rest_001 ridgeSupport134_rest_010
    ridgeSupport134_000 ridgeSupport134_suffix_001 ridgeSupport134_000_decode ridgeSupport134_suffix_decode_001
theorem ridgeSupport134_eq : candidateRows 134 = ridgeSupport134_suffix_000 := by
  change candidateSupports 134 = ridgeSupport134_suffix_000
  rw [ridgeSupport134_source]
  exact congrArg Prod.fst ridgeSupport134_suffix_decode_000
theorem ridgeTest_large_134 : ridgeTest 134 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport134_eq]
    simp only [ridgeSupport134_suffix_000, ridgeSupport134_suffix_001, ridgeSupport134_suffix_002, ridgeSupport134_suffix_003, ridgeSupport134_suffix_004, ridgeSupport134_suffix_005, ridgeSupport134_suffix_006, ridgeSupport134_suffix_007, ridgeSupport134_suffix_008, ridgeSupport134_suffix_009, ridgeSupport134_suffix_010, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport134_000_mask, ridgeSupport134_001_mask, ridgeSupport134_002_mask, ridgeSupport134_003_mask, ridgeSupport134_004_mask, ridgeSupport134_005_mask, ridgeSupport134_006_mask, ridgeSupport134_007_mask, ridgeSupport134_008_mask, ridgeSupport134_009_mask]
    decide +kernel
  · rw [ridgeSupport134_eq]
    simp only [ridgeSupport134_suffix_000, ridgeSupport134_suffix_001, ridgeSupport134_suffix_002, ridgeSupport134_suffix_003, ridgeSupport134_suffix_004, ridgeSupport134_suffix_005, ridgeSupport134_suffix_006, ridgeSupport134_suffix_007, ridgeSupport134_suffix_008, ridgeSupport134_suffix_009, ridgeSupport134_suffix_010, List.all_append, List.all_nil, ridgeSupport134_000_checked, ridgeSupport134_001_checked, ridgeSupport134_002_checked, ridgeSupport134_003_checked, ridgeSupport134_004_checked, ridgeSupport134_005_checked, ridgeSupport134_006_checked, ridgeSupport134_007_checked, ridgeSupport134_008_checked, ridgeSupport134_009_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
