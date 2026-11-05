module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport656Part000
public import RootedSixBase02GrowthCacheRidgeSupport656Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport656_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport656_rest_012 =
    (ridgeSupport656_suffix_012, ridgeSupport656_rest_012) := by rfl
theorem ridgeSupport656_suffix_decode_011 : PackedRawNatGrowth.readList 13 3 ridgeSupport656_rest_011 =
    (ridgeSupport656_suffix_011, ridgeSupport656_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 3 0
    ridgeSupport656_rest_011 ridgeSupport656_rest_012 ridgeSupport656_rest_012
    ridgeSupport656_011 ridgeSupport656_suffix_012 ridgeSupport656_011_decode ridgeSupport656_suffix_decode_012
theorem ridgeSupport656_suffix_decode_010 : PackedRawNatGrowth.readList 13 35 ridgeSupport656_rest_010 =
    (ridgeSupport656_suffix_010, ridgeSupport656_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3
    ridgeSupport656_rest_010 ridgeSupport656_rest_011 ridgeSupport656_rest_012
    ridgeSupport656_010 ridgeSupport656_suffix_011 ridgeSupport656_010_decode ridgeSupport656_suffix_decode_011
theorem ridgeSupport656_suffix_decode_009 : PackedRawNatGrowth.readList 13 67 ridgeSupport656_rest_009 =
    (ridgeSupport656_suffix_009, ridgeSupport656_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 35
    ridgeSupport656_rest_009 ridgeSupport656_rest_010 ridgeSupport656_rest_012
    ridgeSupport656_009 ridgeSupport656_suffix_010 ridgeSupport656_009_decode ridgeSupport656_suffix_decode_010
theorem ridgeSupport656_suffix_decode_008 : PackedRawNatGrowth.readList 13 99 ridgeSupport656_rest_008 =
    (ridgeSupport656_suffix_008, ridgeSupport656_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 67
    ridgeSupport656_rest_008 ridgeSupport656_rest_009 ridgeSupport656_rest_012
    ridgeSupport656_008 ridgeSupport656_suffix_009 ridgeSupport656_008_decode ridgeSupport656_suffix_decode_009
theorem ridgeSupport656_suffix_decode_007 : PackedRawNatGrowth.readList 13 131 ridgeSupport656_rest_007 =
    (ridgeSupport656_suffix_007, ridgeSupport656_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 99
    ridgeSupport656_rest_007 ridgeSupport656_rest_008 ridgeSupport656_rest_012
    ridgeSupport656_007 ridgeSupport656_suffix_008 ridgeSupport656_007_decode ridgeSupport656_suffix_decode_008
theorem ridgeSupport656_suffix_decode_006 : PackedRawNatGrowth.readList 13 163 ridgeSupport656_rest_006 =
    (ridgeSupport656_suffix_006, ridgeSupport656_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 131
    ridgeSupport656_rest_006 ridgeSupport656_rest_007 ridgeSupport656_rest_012
    ridgeSupport656_006 ridgeSupport656_suffix_007 ridgeSupport656_006_decode ridgeSupport656_suffix_decode_007
theorem ridgeSupport656_suffix_decode_005 : PackedRawNatGrowth.readList 13 195 ridgeSupport656_rest_005 =
    (ridgeSupport656_suffix_005, ridgeSupport656_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 163
    ridgeSupport656_rest_005 ridgeSupport656_rest_006 ridgeSupport656_rest_012
    ridgeSupport656_005 ridgeSupport656_suffix_006 ridgeSupport656_005_decode ridgeSupport656_suffix_decode_006
theorem ridgeSupport656_suffix_decode_004 : PackedRawNatGrowth.readList 13 227 ridgeSupport656_rest_004 =
    (ridgeSupport656_suffix_004, ridgeSupport656_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 195
    ridgeSupport656_rest_004 ridgeSupport656_rest_005 ridgeSupport656_rest_012
    ridgeSupport656_004 ridgeSupport656_suffix_005 ridgeSupport656_004_decode ridgeSupport656_suffix_decode_005
theorem ridgeSupport656_suffix_decode_003 : PackedRawNatGrowth.readList 13 259 ridgeSupport656_rest_003 =
    (ridgeSupport656_suffix_003, ridgeSupport656_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 227
    ridgeSupport656_rest_003 ridgeSupport656_rest_004 ridgeSupport656_rest_012
    ridgeSupport656_003 ridgeSupport656_suffix_004 ridgeSupport656_003_decode ridgeSupport656_suffix_decode_004
theorem ridgeSupport656_suffix_decode_002 : PackedRawNatGrowth.readList 13 291 ridgeSupport656_rest_002 =
    (ridgeSupport656_suffix_002, ridgeSupport656_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 259
    ridgeSupport656_rest_002 ridgeSupport656_rest_003 ridgeSupport656_rest_012
    ridgeSupport656_002 ridgeSupport656_suffix_003 ridgeSupport656_002_decode ridgeSupport656_suffix_decode_003
theorem ridgeSupport656_suffix_decode_001 : PackedRawNatGrowth.readList 13 323 ridgeSupport656_rest_001 =
    (ridgeSupport656_suffix_001, ridgeSupport656_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 291
    ridgeSupport656_rest_001 ridgeSupport656_rest_002 ridgeSupport656_rest_012
    ridgeSupport656_001 ridgeSupport656_suffix_002 ridgeSupport656_001_decode ridgeSupport656_suffix_decode_002
theorem ridgeSupport656_suffix_decode_000 : PackedRawNatGrowth.readList 13 355 ridgeSupport656_rest_000 =
    (ridgeSupport656_suffix_000, ridgeSupport656_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 323
    ridgeSupport656_rest_000 ridgeSupport656_rest_001 ridgeSupport656_rest_012
    ridgeSupport656_000 ridgeSupport656_suffix_001 ridgeSupport656_000_decode ridgeSupport656_suffix_decode_001
theorem ridgeSupport656_eq : candidateRows 656 = ridgeSupport656_suffix_000 := by
  change candidateSupports 656 = ridgeSupport656_suffix_000
  rw [ridgeSupport656_source]
  exact congrArg Prod.fst ridgeSupport656_suffix_decode_000
theorem ridgeTest_large_656 : ridgeTest 656 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport656_eq]
    simp only [ridgeSupport656_suffix_000, ridgeSupport656_suffix_001, ridgeSupport656_suffix_002, ridgeSupport656_suffix_003, ridgeSupport656_suffix_004, ridgeSupport656_suffix_005, ridgeSupport656_suffix_006, ridgeSupport656_suffix_007, ridgeSupport656_suffix_008, ridgeSupport656_suffix_009, ridgeSupport656_suffix_010, ridgeSupport656_suffix_011, ridgeSupport656_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport656_000_mask, ridgeSupport656_001_mask, ridgeSupport656_002_mask, ridgeSupport656_003_mask, ridgeSupport656_004_mask, ridgeSupport656_005_mask, ridgeSupport656_006_mask, ridgeSupport656_007_mask, ridgeSupport656_008_mask, ridgeSupport656_009_mask, ridgeSupport656_010_mask, ridgeSupport656_011_mask]
    decide +kernel
  · rw [ridgeSupport656_eq]
    simp only [ridgeSupport656_suffix_000, ridgeSupport656_suffix_001, ridgeSupport656_suffix_002, ridgeSupport656_suffix_003, ridgeSupport656_suffix_004, ridgeSupport656_suffix_005, ridgeSupport656_suffix_006, ridgeSupport656_suffix_007, ridgeSupport656_suffix_008, ridgeSupport656_suffix_009, ridgeSupport656_suffix_010, ridgeSupport656_suffix_011, ridgeSupport656_suffix_012, List.all_append, List.all_nil, ridgeSupport656_000_checked, ridgeSupport656_001_checked, ridgeSupport656_002_checked, ridgeSupport656_003_checked, ridgeSupport656_004_checked, ridgeSupport656_005_checked, ridgeSupport656_006_checked, ridgeSupport656_007_checked, ridgeSupport656_008_checked, ridgeSupport656_009_checked, ridgeSupport656_010_checked, ridgeSupport656_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
