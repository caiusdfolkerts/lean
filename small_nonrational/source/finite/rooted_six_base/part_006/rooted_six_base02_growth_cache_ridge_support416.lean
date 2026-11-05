module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport416Part000
public import RootedSixBase02GrowthCacheRidgeSupport416Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport416_suffix_decode_013 : PackedRawNatGrowth.readList 13 0 ridgeSupport416_rest_013 =
    (ridgeSupport416_suffix_013, ridgeSupport416_rest_013) := by rfl
theorem ridgeSupport416_suffix_decode_012 : PackedRawNatGrowth.readList 13 15 ridgeSupport416_rest_012 =
    (ridgeSupport416_suffix_012, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 15 0
    ridgeSupport416_rest_012 ridgeSupport416_rest_013 ridgeSupport416_rest_013
    ridgeSupport416_012 ridgeSupport416_suffix_013 ridgeSupport416_012_decode ridgeSupport416_suffix_decode_013
theorem ridgeSupport416_suffix_decode_011 : PackedRawNatGrowth.readList 13 47 ridgeSupport416_rest_011 =
    (ridgeSupport416_suffix_011, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 15
    ridgeSupport416_rest_011 ridgeSupport416_rest_012 ridgeSupport416_rest_013
    ridgeSupport416_011 ridgeSupport416_suffix_012 ridgeSupport416_011_decode ridgeSupport416_suffix_decode_012
theorem ridgeSupport416_suffix_decode_010 : PackedRawNatGrowth.readList 13 79 ridgeSupport416_rest_010 =
    (ridgeSupport416_suffix_010, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 47
    ridgeSupport416_rest_010 ridgeSupport416_rest_011 ridgeSupport416_rest_013
    ridgeSupport416_010 ridgeSupport416_suffix_011 ridgeSupport416_010_decode ridgeSupport416_suffix_decode_011
theorem ridgeSupport416_suffix_decode_009 : PackedRawNatGrowth.readList 13 111 ridgeSupport416_rest_009 =
    (ridgeSupport416_suffix_009, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 79
    ridgeSupport416_rest_009 ridgeSupport416_rest_010 ridgeSupport416_rest_013
    ridgeSupport416_009 ridgeSupport416_suffix_010 ridgeSupport416_009_decode ridgeSupport416_suffix_decode_010
theorem ridgeSupport416_suffix_decode_008 : PackedRawNatGrowth.readList 13 143 ridgeSupport416_rest_008 =
    (ridgeSupport416_suffix_008, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 111
    ridgeSupport416_rest_008 ridgeSupport416_rest_009 ridgeSupport416_rest_013
    ridgeSupport416_008 ridgeSupport416_suffix_009 ridgeSupport416_008_decode ridgeSupport416_suffix_decode_009
theorem ridgeSupport416_suffix_decode_007 : PackedRawNatGrowth.readList 13 175 ridgeSupport416_rest_007 =
    (ridgeSupport416_suffix_007, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 143
    ridgeSupport416_rest_007 ridgeSupport416_rest_008 ridgeSupport416_rest_013
    ridgeSupport416_007 ridgeSupport416_suffix_008 ridgeSupport416_007_decode ridgeSupport416_suffix_decode_008
theorem ridgeSupport416_suffix_decode_006 : PackedRawNatGrowth.readList 13 207 ridgeSupport416_rest_006 =
    (ridgeSupport416_suffix_006, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 175
    ridgeSupport416_rest_006 ridgeSupport416_rest_007 ridgeSupport416_rest_013
    ridgeSupport416_006 ridgeSupport416_suffix_007 ridgeSupport416_006_decode ridgeSupport416_suffix_decode_007
theorem ridgeSupport416_suffix_decode_005 : PackedRawNatGrowth.readList 13 239 ridgeSupport416_rest_005 =
    (ridgeSupport416_suffix_005, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 207
    ridgeSupport416_rest_005 ridgeSupport416_rest_006 ridgeSupport416_rest_013
    ridgeSupport416_005 ridgeSupport416_suffix_006 ridgeSupport416_005_decode ridgeSupport416_suffix_decode_006
theorem ridgeSupport416_suffix_decode_004 : PackedRawNatGrowth.readList 13 271 ridgeSupport416_rest_004 =
    (ridgeSupport416_suffix_004, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 239
    ridgeSupport416_rest_004 ridgeSupport416_rest_005 ridgeSupport416_rest_013
    ridgeSupport416_004 ridgeSupport416_suffix_005 ridgeSupport416_004_decode ridgeSupport416_suffix_decode_005
theorem ridgeSupport416_suffix_decode_003 : PackedRawNatGrowth.readList 13 303 ridgeSupport416_rest_003 =
    (ridgeSupport416_suffix_003, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 271
    ridgeSupport416_rest_003 ridgeSupport416_rest_004 ridgeSupport416_rest_013
    ridgeSupport416_003 ridgeSupport416_suffix_004 ridgeSupport416_003_decode ridgeSupport416_suffix_decode_004
theorem ridgeSupport416_suffix_decode_002 : PackedRawNatGrowth.readList 13 335 ridgeSupport416_rest_002 =
    (ridgeSupport416_suffix_002, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 303
    ridgeSupport416_rest_002 ridgeSupport416_rest_003 ridgeSupport416_rest_013
    ridgeSupport416_002 ridgeSupport416_suffix_003 ridgeSupport416_002_decode ridgeSupport416_suffix_decode_003
theorem ridgeSupport416_suffix_decode_001 : PackedRawNatGrowth.readList 13 367 ridgeSupport416_rest_001 =
    (ridgeSupport416_suffix_001, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 335
    ridgeSupport416_rest_001 ridgeSupport416_rest_002 ridgeSupport416_rest_013
    ridgeSupport416_001 ridgeSupport416_suffix_002 ridgeSupport416_001_decode ridgeSupport416_suffix_decode_002
theorem ridgeSupport416_suffix_decode_000 : PackedRawNatGrowth.readList 13 399 ridgeSupport416_rest_000 =
    (ridgeSupport416_suffix_000, ridgeSupport416_rest_013) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 367
    ridgeSupport416_rest_000 ridgeSupport416_rest_001 ridgeSupport416_rest_013
    ridgeSupport416_000 ridgeSupport416_suffix_001 ridgeSupport416_000_decode ridgeSupport416_suffix_decode_001
theorem ridgeSupport416_eq : candidateRows 416 = ridgeSupport416_suffix_000 := by
  change candidateSupports 416 = ridgeSupport416_suffix_000
  rw [ridgeSupport416_source]
  exact congrArg Prod.fst ridgeSupport416_suffix_decode_000
theorem ridgeTest_large_416 : ridgeTest 416 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport416_eq]
    simp only [ridgeSupport416_suffix_000, ridgeSupport416_suffix_001, ridgeSupport416_suffix_002, ridgeSupport416_suffix_003, ridgeSupport416_suffix_004, ridgeSupport416_suffix_005, ridgeSupport416_suffix_006, ridgeSupport416_suffix_007, ridgeSupport416_suffix_008, ridgeSupport416_suffix_009, ridgeSupport416_suffix_010, ridgeSupport416_suffix_011, ridgeSupport416_suffix_012, ridgeSupport416_suffix_013, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport416_000_mask, ridgeSupport416_001_mask, ridgeSupport416_002_mask, ridgeSupport416_003_mask, ridgeSupport416_004_mask, ridgeSupport416_005_mask, ridgeSupport416_006_mask, ridgeSupport416_007_mask, ridgeSupport416_008_mask, ridgeSupport416_009_mask, ridgeSupport416_010_mask, ridgeSupport416_011_mask, ridgeSupport416_012_mask]
    decide +kernel
  · rw [ridgeSupport416_eq]
    simp only [ridgeSupport416_suffix_000, ridgeSupport416_suffix_001, ridgeSupport416_suffix_002, ridgeSupport416_suffix_003, ridgeSupport416_suffix_004, ridgeSupport416_suffix_005, ridgeSupport416_suffix_006, ridgeSupport416_suffix_007, ridgeSupport416_suffix_008, ridgeSupport416_suffix_009, ridgeSupport416_suffix_010, ridgeSupport416_suffix_011, ridgeSupport416_suffix_012, ridgeSupport416_suffix_013, List.all_append, List.all_nil, ridgeSupport416_000_checked, ridgeSupport416_001_checked, ridgeSupport416_002_checked, ridgeSupport416_003_checked, ridgeSupport416_004_checked, ridgeSupport416_005_checked, ridgeSupport416_006_checked, ridgeSupport416_007_checked, ridgeSupport416_008_checked, ridgeSupport416_009_checked, ridgeSupport416_010_checked, ridgeSupport416_011_checked, ridgeSupport416_012_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
