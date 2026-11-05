module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport196Part000
public import RootedSixBase02GrowthCacheRidgeSupport196Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport196_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport196_rest_012 =
    (ridgeSupport196_suffix_012, ridgeSupport196_rest_012) := by rfl
theorem ridgeSupport196_suffix_decode_011 : PackedRawNatGrowth.readList 13 3 ridgeSupport196_rest_011 =
    (ridgeSupport196_suffix_011, ridgeSupport196_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 3 0
    ridgeSupport196_rest_011 ridgeSupport196_rest_012 ridgeSupport196_rest_012
    ridgeSupport196_011 ridgeSupport196_suffix_012 ridgeSupport196_011_decode ridgeSupport196_suffix_decode_012
theorem ridgeSupport196_suffix_decode_010 : PackedRawNatGrowth.readList 13 35 ridgeSupport196_rest_010 =
    (ridgeSupport196_suffix_010, ridgeSupport196_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3
    ridgeSupport196_rest_010 ridgeSupport196_rest_011 ridgeSupport196_rest_012
    ridgeSupport196_010 ridgeSupport196_suffix_011 ridgeSupport196_010_decode ridgeSupport196_suffix_decode_011
theorem ridgeSupport196_suffix_decode_009 : PackedRawNatGrowth.readList 13 67 ridgeSupport196_rest_009 =
    (ridgeSupport196_suffix_009, ridgeSupport196_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 35
    ridgeSupport196_rest_009 ridgeSupport196_rest_010 ridgeSupport196_rest_012
    ridgeSupport196_009 ridgeSupport196_suffix_010 ridgeSupport196_009_decode ridgeSupport196_suffix_decode_010
theorem ridgeSupport196_suffix_decode_008 : PackedRawNatGrowth.readList 13 99 ridgeSupport196_rest_008 =
    (ridgeSupport196_suffix_008, ridgeSupport196_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 67
    ridgeSupport196_rest_008 ridgeSupport196_rest_009 ridgeSupport196_rest_012
    ridgeSupport196_008 ridgeSupport196_suffix_009 ridgeSupport196_008_decode ridgeSupport196_suffix_decode_009
theorem ridgeSupport196_suffix_decode_007 : PackedRawNatGrowth.readList 13 131 ridgeSupport196_rest_007 =
    (ridgeSupport196_suffix_007, ridgeSupport196_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 99
    ridgeSupport196_rest_007 ridgeSupport196_rest_008 ridgeSupport196_rest_012
    ridgeSupport196_007 ridgeSupport196_suffix_008 ridgeSupport196_007_decode ridgeSupport196_suffix_decode_008
theorem ridgeSupport196_suffix_decode_006 : PackedRawNatGrowth.readList 13 163 ridgeSupport196_rest_006 =
    (ridgeSupport196_suffix_006, ridgeSupport196_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 131
    ridgeSupport196_rest_006 ridgeSupport196_rest_007 ridgeSupport196_rest_012
    ridgeSupport196_006 ridgeSupport196_suffix_007 ridgeSupport196_006_decode ridgeSupport196_suffix_decode_007
theorem ridgeSupport196_suffix_decode_005 : PackedRawNatGrowth.readList 13 195 ridgeSupport196_rest_005 =
    (ridgeSupport196_suffix_005, ridgeSupport196_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 163
    ridgeSupport196_rest_005 ridgeSupport196_rest_006 ridgeSupport196_rest_012
    ridgeSupport196_005 ridgeSupport196_suffix_006 ridgeSupport196_005_decode ridgeSupport196_suffix_decode_006
theorem ridgeSupport196_suffix_decode_004 : PackedRawNatGrowth.readList 13 227 ridgeSupport196_rest_004 =
    (ridgeSupport196_suffix_004, ridgeSupport196_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 195
    ridgeSupport196_rest_004 ridgeSupport196_rest_005 ridgeSupport196_rest_012
    ridgeSupport196_004 ridgeSupport196_suffix_005 ridgeSupport196_004_decode ridgeSupport196_suffix_decode_005
theorem ridgeSupport196_suffix_decode_003 : PackedRawNatGrowth.readList 13 259 ridgeSupport196_rest_003 =
    (ridgeSupport196_suffix_003, ridgeSupport196_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 227
    ridgeSupport196_rest_003 ridgeSupport196_rest_004 ridgeSupport196_rest_012
    ridgeSupport196_003 ridgeSupport196_suffix_004 ridgeSupport196_003_decode ridgeSupport196_suffix_decode_004
theorem ridgeSupport196_suffix_decode_002 : PackedRawNatGrowth.readList 13 291 ridgeSupport196_rest_002 =
    (ridgeSupport196_suffix_002, ridgeSupport196_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 259
    ridgeSupport196_rest_002 ridgeSupport196_rest_003 ridgeSupport196_rest_012
    ridgeSupport196_002 ridgeSupport196_suffix_003 ridgeSupport196_002_decode ridgeSupport196_suffix_decode_003
theorem ridgeSupport196_suffix_decode_001 : PackedRawNatGrowth.readList 13 323 ridgeSupport196_rest_001 =
    (ridgeSupport196_suffix_001, ridgeSupport196_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 291
    ridgeSupport196_rest_001 ridgeSupport196_rest_002 ridgeSupport196_rest_012
    ridgeSupport196_001 ridgeSupport196_suffix_002 ridgeSupport196_001_decode ridgeSupport196_suffix_decode_002
theorem ridgeSupport196_suffix_decode_000 : PackedRawNatGrowth.readList 13 355 ridgeSupport196_rest_000 =
    (ridgeSupport196_suffix_000, ridgeSupport196_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 323
    ridgeSupport196_rest_000 ridgeSupport196_rest_001 ridgeSupport196_rest_012
    ridgeSupport196_000 ridgeSupport196_suffix_001 ridgeSupport196_000_decode ridgeSupport196_suffix_decode_001
theorem ridgeSupport196_eq : candidateRows 196 = ridgeSupport196_suffix_000 := by
  change candidateSupports 196 = ridgeSupport196_suffix_000
  rw [ridgeSupport196_source]
  exact congrArg Prod.fst ridgeSupport196_suffix_decode_000
theorem ridgeTest_large_196 : ridgeTest 196 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport196_eq]
    simp only [ridgeSupport196_suffix_000, ridgeSupport196_suffix_001, ridgeSupport196_suffix_002, ridgeSupport196_suffix_003, ridgeSupport196_suffix_004, ridgeSupport196_suffix_005, ridgeSupport196_suffix_006, ridgeSupport196_suffix_007, ridgeSupport196_suffix_008, ridgeSupport196_suffix_009, ridgeSupport196_suffix_010, ridgeSupport196_suffix_011, ridgeSupport196_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport196_000_mask, ridgeSupport196_001_mask, ridgeSupport196_002_mask, ridgeSupport196_003_mask, ridgeSupport196_004_mask, ridgeSupport196_005_mask, ridgeSupport196_006_mask, ridgeSupport196_007_mask, ridgeSupport196_008_mask, ridgeSupport196_009_mask, ridgeSupport196_010_mask, ridgeSupport196_011_mask]
    decide +kernel
  · rw [ridgeSupport196_eq]
    simp only [ridgeSupport196_suffix_000, ridgeSupport196_suffix_001, ridgeSupport196_suffix_002, ridgeSupport196_suffix_003, ridgeSupport196_suffix_004, ridgeSupport196_suffix_005, ridgeSupport196_suffix_006, ridgeSupport196_suffix_007, ridgeSupport196_suffix_008, ridgeSupport196_suffix_009, ridgeSupport196_suffix_010, ridgeSupport196_suffix_011, ridgeSupport196_suffix_012, List.all_append, List.all_nil, ridgeSupport196_000_checked, ridgeSupport196_001_checked, ridgeSupport196_002_checked, ridgeSupport196_003_checked, ridgeSupport196_004_checked, ridgeSupport196_005_checked, ridgeSupport196_006_checked, ridgeSupport196_007_checked, ridgeSupport196_008_checked, ridgeSupport196_009_checked, ridgeSupport196_010_checked, ridgeSupport196_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
