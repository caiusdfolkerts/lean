module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport324Part000
public import RootedSixBase02GrowthCacheRidgeSupport324Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport324_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport324_rest_012 =
    (ridgeSupport324_suffix_012, ridgeSupport324_rest_012) := by rfl
theorem ridgeSupport324_suffix_decode_011 : PackedRawNatGrowth.readList 13 3 ridgeSupport324_rest_011 =
    (ridgeSupport324_suffix_011, ridgeSupport324_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 3 0
    ridgeSupport324_rest_011 ridgeSupport324_rest_012 ridgeSupport324_rest_012
    ridgeSupport324_011 ridgeSupport324_suffix_012 ridgeSupport324_011_decode ridgeSupport324_suffix_decode_012
theorem ridgeSupport324_suffix_decode_010 : PackedRawNatGrowth.readList 13 35 ridgeSupport324_rest_010 =
    (ridgeSupport324_suffix_010, ridgeSupport324_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3
    ridgeSupport324_rest_010 ridgeSupport324_rest_011 ridgeSupport324_rest_012
    ridgeSupport324_010 ridgeSupport324_suffix_011 ridgeSupport324_010_decode ridgeSupport324_suffix_decode_011
theorem ridgeSupport324_suffix_decode_009 : PackedRawNatGrowth.readList 13 67 ridgeSupport324_rest_009 =
    (ridgeSupport324_suffix_009, ridgeSupport324_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 35
    ridgeSupport324_rest_009 ridgeSupport324_rest_010 ridgeSupport324_rest_012
    ridgeSupport324_009 ridgeSupport324_suffix_010 ridgeSupport324_009_decode ridgeSupport324_suffix_decode_010
theorem ridgeSupport324_suffix_decode_008 : PackedRawNatGrowth.readList 13 99 ridgeSupport324_rest_008 =
    (ridgeSupport324_suffix_008, ridgeSupport324_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 67
    ridgeSupport324_rest_008 ridgeSupport324_rest_009 ridgeSupport324_rest_012
    ridgeSupport324_008 ridgeSupport324_suffix_009 ridgeSupport324_008_decode ridgeSupport324_suffix_decode_009
theorem ridgeSupport324_suffix_decode_007 : PackedRawNatGrowth.readList 13 131 ridgeSupport324_rest_007 =
    (ridgeSupport324_suffix_007, ridgeSupport324_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 99
    ridgeSupport324_rest_007 ridgeSupport324_rest_008 ridgeSupport324_rest_012
    ridgeSupport324_007 ridgeSupport324_suffix_008 ridgeSupport324_007_decode ridgeSupport324_suffix_decode_008
theorem ridgeSupport324_suffix_decode_006 : PackedRawNatGrowth.readList 13 163 ridgeSupport324_rest_006 =
    (ridgeSupport324_suffix_006, ridgeSupport324_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 131
    ridgeSupport324_rest_006 ridgeSupport324_rest_007 ridgeSupport324_rest_012
    ridgeSupport324_006 ridgeSupport324_suffix_007 ridgeSupport324_006_decode ridgeSupport324_suffix_decode_007
theorem ridgeSupport324_suffix_decode_005 : PackedRawNatGrowth.readList 13 195 ridgeSupport324_rest_005 =
    (ridgeSupport324_suffix_005, ridgeSupport324_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 163
    ridgeSupport324_rest_005 ridgeSupport324_rest_006 ridgeSupport324_rest_012
    ridgeSupport324_005 ridgeSupport324_suffix_006 ridgeSupport324_005_decode ridgeSupport324_suffix_decode_006
theorem ridgeSupport324_suffix_decode_004 : PackedRawNatGrowth.readList 13 227 ridgeSupport324_rest_004 =
    (ridgeSupport324_suffix_004, ridgeSupport324_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 195
    ridgeSupport324_rest_004 ridgeSupport324_rest_005 ridgeSupport324_rest_012
    ridgeSupport324_004 ridgeSupport324_suffix_005 ridgeSupport324_004_decode ridgeSupport324_suffix_decode_005
theorem ridgeSupport324_suffix_decode_003 : PackedRawNatGrowth.readList 13 259 ridgeSupport324_rest_003 =
    (ridgeSupport324_suffix_003, ridgeSupport324_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 227
    ridgeSupport324_rest_003 ridgeSupport324_rest_004 ridgeSupport324_rest_012
    ridgeSupport324_003 ridgeSupport324_suffix_004 ridgeSupport324_003_decode ridgeSupport324_suffix_decode_004
theorem ridgeSupport324_suffix_decode_002 : PackedRawNatGrowth.readList 13 291 ridgeSupport324_rest_002 =
    (ridgeSupport324_suffix_002, ridgeSupport324_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 259
    ridgeSupport324_rest_002 ridgeSupport324_rest_003 ridgeSupport324_rest_012
    ridgeSupport324_002 ridgeSupport324_suffix_003 ridgeSupport324_002_decode ridgeSupport324_suffix_decode_003
theorem ridgeSupport324_suffix_decode_001 : PackedRawNatGrowth.readList 13 323 ridgeSupport324_rest_001 =
    (ridgeSupport324_suffix_001, ridgeSupport324_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 291
    ridgeSupport324_rest_001 ridgeSupport324_rest_002 ridgeSupport324_rest_012
    ridgeSupport324_001 ridgeSupport324_suffix_002 ridgeSupport324_001_decode ridgeSupport324_suffix_decode_002
theorem ridgeSupport324_suffix_decode_000 : PackedRawNatGrowth.readList 13 355 ridgeSupport324_rest_000 =
    (ridgeSupport324_suffix_000, ridgeSupport324_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 323
    ridgeSupport324_rest_000 ridgeSupport324_rest_001 ridgeSupport324_rest_012
    ridgeSupport324_000 ridgeSupport324_suffix_001 ridgeSupport324_000_decode ridgeSupport324_suffix_decode_001
theorem ridgeSupport324_eq : candidateRows 324 = ridgeSupport324_suffix_000 := by
  change candidateSupports 324 = ridgeSupport324_suffix_000
  rw [ridgeSupport324_source]
  exact congrArg Prod.fst ridgeSupport324_suffix_decode_000
theorem ridgeTest_large_324 : ridgeTest 324 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport324_eq]
    simp only [ridgeSupport324_suffix_000, ridgeSupport324_suffix_001, ridgeSupport324_suffix_002, ridgeSupport324_suffix_003, ridgeSupport324_suffix_004, ridgeSupport324_suffix_005, ridgeSupport324_suffix_006, ridgeSupport324_suffix_007, ridgeSupport324_suffix_008, ridgeSupport324_suffix_009, ridgeSupport324_suffix_010, ridgeSupport324_suffix_011, ridgeSupport324_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport324_000_mask, ridgeSupport324_001_mask, ridgeSupport324_002_mask, ridgeSupport324_003_mask, ridgeSupport324_004_mask, ridgeSupport324_005_mask, ridgeSupport324_006_mask, ridgeSupport324_007_mask, ridgeSupport324_008_mask, ridgeSupport324_009_mask, ridgeSupport324_010_mask, ridgeSupport324_011_mask]
    decide +kernel
  · rw [ridgeSupport324_eq]
    simp only [ridgeSupport324_suffix_000, ridgeSupport324_suffix_001, ridgeSupport324_suffix_002, ridgeSupport324_suffix_003, ridgeSupport324_suffix_004, ridgeSupport324_suffix_005, ridgeSupport324_suffix_006, ridgeSupport324_suffix_007, ridgeSupport324_suffix_008, ridgeSupport324_suffix_009, ridgeSupport324_suffix_010, ridgeSupport324_suffix_011, ridgeSupport324_suffix_012, List.all_append, List.all_nil, ridgeSupport324_000_checked, ridgeSupport324_001_checked, ridgeSupport324_002_checked, ridgeSupport324_003_checked, ridgeSupport324_004_checked, ridgeSupport324_005_checked, ridgeSupport324_006_checked, ridgeSupport324_007_checked, ridgeSupport324_008_checked, ridgeSupport324_009_checked, ridgeSupport324_010_checked, ridgeSupport324_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
