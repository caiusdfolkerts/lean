module
prelude
public import RootedSixBase02GrowthCacheRidgeSupport644Part000
public import RootedSixBase02GrowthCacheRidgeSupport644Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport644_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport644_rest_012 =
    (ridgeSupport644_suffix_012, ridgeSupport644_rest_012) := by rfl
theorem ridgeSupport644_suffix_decode_011 : PackedRawNatGrowth.readList 13 3 ridgeSupport644_rest_011 =
    (ridgeSupport644_suffix_011, ridgeSupport644_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 3 0
    ridgeSupport644_rest_011 ridgeSupport644_rest_012 ridgeSupport644_rest_012
    ridgeSupport644_011 ridgeSupport644_suffix_012 ridgeSupport644_011_decode ridgeSupport644_suffix_decode_012
theorem ridgeSupport644_suffix_decode_010 : PackedRawNatGrowth.readList 13 35 ridgeSupport644_rest_010 =
    (ridgeSupport644_suffix_010, ridgeSupport644_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 3
    ridgeSupport644_rest_010 ridgeSupport644_rest_011 ridgeSupport644_rest_012
    ridgeSupport644_010 ridgeSupport644_suffix_011 ridgeSupport644_010_decode ridgeSupport644_suffix_decode_011
theorem ridgeSupport644_suffix_decode_009 : PackedRawNatGrowth.readList 13 67 ridgeSupport644_rest_009 =
    (ridgeSupport644_suffix_009, ridgeSupport644_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 35
    ridgeSupport644_rest_009 ridgeSupport644_rest_010 ridgeSupport644_rest_012
    ridgeSupport644_009 ridgeSupport644_suffix_010 ridgeSupport644_009_decode ridgeSupport644_suffix_decode_010
theorem ridgeSupport644_suffix_decode_008 : PackedRawNatGrowth.readList 13 99 ridgeSupport644_rest_008 =
    (ridgeSupport644_suffix_008, ridgeSupport644_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 67
    ridgeSupport644_rest_008 ridgeSupport644_rest_009 ridgeSupport644_rest_012
    ridgeSupport644_008 ridgeSupport644_suffix_009 ridgeSupport644_008_decode ridgeSupport644_suffix_decode_009
theorem ridgeSupport644_suffix_decode_007 : PackedRawNatGrowth.readList 13 131 ridgeSupport644_rest_007 =
    (ridgeSupport644_suffix_007, ridgeSupport644_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 99
    ridgeSupport644_rest_007 ridgeSupport644_rest_008 ridgeSupport644_rest_012
    ridgeSupport644_007 ridgeSupport644_suffix_008 ridgeSupport644_007_decode ridgeSupport644_suffix_decode_008
theorem ridgeSupport644_suffix_decode_006 : PackedRawNatGrowth.readList 13 163 ridgeSupport644_rest_006 =
    (ridgeSupport644_suffix_006, ridgeSupport644_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 131
    ridgeSupport644_rest_006 ridgeSupport644_rest_007 ridgeSupport644_rest_012
    ridgeSupport644_006 ridgeSupport644_suffix_007 ridgeSupport644_006_decode ridgeSupport644_suffix_decode_007
theorem ridgeSupport644_suffix_decode_005 : PackedRawNatGrowth.readList 13 195 ridgeSupport644_rest_005 =
    (ridgeSupport644_suffix_005, ridgeSupport644_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 163
    ridgeSupport644_rest_005 ridgeSupport644_rest_006 ridgeSupport644_rest_012
    ridgeSupport644_005 ridgeSupport644_suffix_006 ridgeSupport644_005_decode ridgeSupport644_suffix_decode_006
theorem ridgeSupport644_suffix_decode_004 : PackedRawNatGrowth.readList 13 227 ridgeSupport644_rest_004 =
    (ridgeSupport644_suffix_004, ridgeSupport644_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 195
    ridgeSupport644_rest_004 ridgeSupport644_rest_005 ridgeSupport644_rest_012
    ridgeSupport644_004 ridgeSupport644_suffix_005 ridgeSupport644_004_decode ridgeSupport644_suffix_decode_005
theorem ridgeSupport644_suffix_decode_003 : PackedRawNatGrowth.readList 13 259 ridgeSupport644_rest_003 =
    (ridgeSupport644_suffix_003, ridgeSupport644_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 227
    ridgeSupport644_rest_003 ridgeSupport644_rest_004 ridgeSupport644_rest_012
    ridgeSupport644_003 ridgeSupport644_suffix_004 ridgeSupport644_003_decode ridgeSupport644_suffix_decode_004
theorem ridgeSupport644_suffix_decode_002 : PackedRawNatGrowth.readList 13 291 ridgeSupport644_rest_002 =
    (ridgeSupport644_suffix_002, ridgeSupport644_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 259
    ridgeSupport644_rest_002 ridgeSupport644_rest_003 ridgeSupport644_rest_012
    ridgeSupport644_002 ridgeSupport644_suffix_003 ridgeSupport644_002_decode ridgeSupport644_suffix_decode_003
theorem ridgeSupport644_suffix_decode_001 : PackedRawNatGrowth.readList 13 323 ridgeSupport644_rest_001 =
    (ridgeSupport644_suffix_001, ridgeSupport644_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 291
    ridgeSupport644_rest_001 ridgeSupport644_rest_002 ridgeSupport644_rest_012
    ridgeSupport644_001 ridgeSupport644_suffix_002 ridgeSupport644_001_decode ridgeSupport644_suffix_decode_002
theorem ridgeSupport644_suffix_decode_000 : PackedRawNatGrowth.readList 13 355 ridgeSupport644_rest_000 =
    (ridgeSupport644_suffix_000, ridgeSupport644_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 323
    ridgeSupport644_rest_000 ridgeSupport644_rest_001 ridgeSupport644_rest_012
    ridgeSupport644_000 ridgeSupport644_suffix_001 ridgeSupport644_000_decode ridgeSupport644_suffix_decode_001
theorem ridgeSupport644_eq : candidateRows 644 = ridgeSupport644_suffix_000 := by
  change candidateSupports 644 = ridgeSupport644_suffix_000
  rw [ridgeSupport644_source]
  exact congrArg Prod.fst ridgeSupport644_suffix_decode_000
theorem ridgeTest_large_644 : ridgeTest 644 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport644_eq]
    simp only [ridgeSupport644_suffix_000, ridgeSupport644_suffix_001, ridgeSupport644_suffix_002, ridgeSupport644_suffix_003, ridgeSupport644_suffix_004, ridgeSupport644_suffix_005, ridgeSupport644_suffix_006, ridgeSupport644_suffix_007, ridgeSupport644_suffix_008, ridgeSupport644_suffix_009, ridgeSupport644_suffix_010, ridgeSupport644_suffix_011, ridgeSupport644_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport644_000_mask, ridgeSupport644_001_mask, ridgeSupport644_002_mask, ridgeSupport644_003_mask, ridgeSupport644_004_mask, ridgeSupport644_005_mask, ridgeSupport644_006_mask, ridgeSupport644_007_mask, ridgeSupport644_008_mask, ridgeSupport644_009_mask, ridgeSupport644_010_mask, ridgeSupport644_011_mask]
    decide +kernel
  · rw [ridgeSupport644_eq]
    simp only [ridgeSupport644_suffix_000, ridgeSupport644_suffix_001, ridgeSupport644_suffix_002, ridgeSupport644_suffix_003, ridgeSupport644_suffix_004, ridgeSupport644_suffix_005, ridgeSupport644_suffix_006, ridgeSupport644_suffix_007, ridgeSupport644_suffix_008, ridgeSupport644_suffix_009, ridgeSupport644_suffix_010, ridgeSupport644_suffix_011, ridgeSupport644_suffix_012, List.all_append, List.all_nil, ridgeSupport644_000_checked, ridgeSupport644_001_checked, ridgeSupport644_002_checked, ridgeSupport644_003_checked, ridgeSupport644_004_checked, ridgeSupport644_005_checked, ridgeSupport644_006_checked, ridgeSupport644_007_checked, ridgeSupport644_008_checked, ridgeSupport644_009_checked, ridgeSupport644_010_checked, ridgeSupport644_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
