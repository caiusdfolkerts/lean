module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport386Part000
public import RootedSixBase03GrowthCacheRidgeSupport386Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport386_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport386_rest_012 =
    (ridgeSupport386_suffix_012, ridgeSupport386_rest_012) := by rfl
theorem ridgeSupport386_suffix_decode_011 : PackedRawNatGrowth.readList 13 26 ridgeSupport386_rest_011 =
    (ridgeSupport386_suffix_011, ridgeSupport386_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport386_rest_011 ridgeSupport386_rest_012 ridgeSupport386_rest_012
    ridgeSupport386_011 ridgeSupport386_suffix_012 ridgeSupport386_011_decode ridgeSupport386_suffix_decode_012
theorem ridgeSupport386_suffix_decode_010 : PackedRawNatGrowth.readList 13 58 ridgeSupport386_rest_010 =
    (ridgeSupport386_suffix_010, ridgeSupport386_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport386_rest_010 ridgeSupport386_rest_011 ridgeSupport386_rest_012
    ridgeSupport386_010 ridgeSupport386_suffix_011 ridgeSupport386_010_decode ridgeSupport386_suffix_decode_011
theorem ridgeSupport386_suffix_decode_009 : PackedRawNatGrowth.readList 13 90 ridgeSupport386_rest_009 =
    (ridgeSupport386_suffix_009, ridgeSupport386_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport386_rest_009 ridgeSupport386_rest_010 ridgeSupport386_rest_012
    ridgeSupport386_009 ridgeSupport386_suffix_010 ridgeSupport386_009_decode ridgeSupport386_suffix_decode_010
theorem ridgeSupport386_suffix_decode_008 : PackedRawNatGrowth.readList 13 122 ridgeSupport386_rest_008 =
    (ridgeSupport386_suffix_008, ridgeSupport386_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport386_rest_008 ridgeSupport386_rest_009 ridgeSupport386_rest_012
    ridgeSupport386_008 ridgeSupport386_suffix_009 ridgeSupport386_008_decode ridgeSupport386_suffix_decode_009
theorem ridgeSupport386_suffix_decode_007 : PackedRawNatGrowth.readList 13 154 ridgeSupport386_rest_007 =
    (ridgeSupport386_suffix_007, ridgeSupport386_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport386_rest_007 ridgeSupport386_rest_008 ridgeSupport386_rest_012
    ridgeSupport386_007 ridgeSupport386_suffix_008 ridgeSupport386_007_decode ridgeSupport386_suffix_decode_008
theorem ridgeSupport386_suffix_decode_006 : PackedRawNatGrowth.readList 13 186 ridgeSupport386_rest_006 =
    (ridgeSupport386_suffix_006, ridgeSupport386_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport386_rest_006 ridgeSupport386_rest_007 ridgeSupport386_rest_012
    ridgeSupport386_006 ridgeSupport386_suffix_007 ridgeSupport386_006_decode ridgeSupport386_suffix_decode_007
theorem ridgeSupport386_suffix_decode_005 : PackedRawNatGrowth.readList 13 218 ridgeSupport386_rest_005 =
    (ridgeSupport386_suffix_005, ridgeSupport386_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport386_rest_005 ridgeSupport386_rest_006 ridgeSupport386_rest_012
    ridgeSupport386_005 ridgeSupport386_suffix_006 ridgeSupport386_005_decode ridgeSupport386_suffix_decode_006
theorem ridgeSupport386_suffix_decode_004 : PackedRawNatGrowth.readList 13 250 ridgeSupport386_rest_004 =
    (ridgeSupport386_suffix_004, ridgeSupport386_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport386_rest_004 ridgeSupport386_rest_005 ridgeSupport386_rest_012
    ridgeSupport386_004 ridgeSupport386_suffix_005 ridgeSupport386_004_decode ridgeSupport386_suffix_decode_005
theorem ridgeSupport386_suffix_decode_003 : PackedRawNatGrowth.readList 13 282 ridgeSupport386_rest_003 =
    (ridgeSupport386_suffix_003, ridgeSupport386_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport386_rest_003 ridgeSupport386_rest_004 ridgeSupport386_rest_012
    ridgeSupport386_003 ridgeSupport386_suffix_004 ridgeSupport386_003_decode ridgeSupport386_suffix_decode_004
theorem ridgeSupport386_suffix_decode_002 : PackedRawNatGrowth.readList 13 314 ridgeSupport386_rest_002 =
    (ridgeSupport386_suffix_002, ridgeSupport386_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 282
    ridgeSupport386_rest_002 ridgeSupport386_rest_003 ridgeSupport386_rest_012
    ridgeSupport386_002 ridgeSupport386_suffix_003 ridgeSupport386_002_decode ridgeSupport386_suffix_decode_003
theorem ridgeSupport386_suffix_decode_001 : PackedRawNatGrowth.readList 13 346 ridgeSupport386_rest_001 =
    (ridgeSupport386_suffix_001, ridgeSupport386_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 314
    ridgeSupport386_rest_001 ridgeSupport386_rest_002 ridgeSupport386_rest_012
    ridgeSupport386_001 ridgeSupport386_suffix_002 ridgeSupport386_001_decode ridgeSupport386_suffix_decode_002
theorem ridgeSupport386_suffix_decode_000 : PackedRawNatGrowth.readList 13 378 ridgeSupport386_rest_000 =
    (ridgeSupport386_suffix_000, ridgeSupport386_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 346
    ridgeSupport386_rest_000 ridgeSupport386_rest_001 ridgeSupport386_rest_012
    ridgeSupport386_000 ridgeSupport386_suffix_001 ridgeSupport386_000_decode ridgeSupport386_suffix_decode_001
theorem ridgeSupport386_eq : candidateSupports 386 = ridgeSupport386_suffix_000 := by
  rw [ridgeSupport386_source]
  exact congrArg Prod.fst ridgeSupport386_suffix_decode_000
theorem ridgeTest_large_386 : ridgeTest 386 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 386 = ridgeSupport386_suffix_000 from ridgeSupport386_eq]
    simp only [ridgeSupport386_suffix_000, ridgeSupport386_suffix_001, ridgeSupport386_suffix_002, ridgeSupport386_suffix_003, ridgeSupport386_suffix_004, ridgeSupport386_suffix_005, ridgeSupport386_suffix_006, ridgeSupport386_suffix_007, ridgeSupport386_suffix_008, ridgeSupport386_suffix_009, ridgeSupport386_suffix_010, ridgeSupport386_suffix_011, ridgeSupport386_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport386_000_mask, ridgeSupport386_001_mask, ridgeSupport386_002_mask, ridgeSupport386_003_mask, ridgeSupport386_004_mask, ridgeSupport386_005_mask, ridgeSupport386_006_mask, ridgeSupport386_007_mask, ridgeSupport386_008_mask, ridgeSupport386_009_mask, ridgeSupport386_010_mask, ridgeSupport386_011_mask]
    decide +kernel
  · rw [show candidateRows 386 = ridgeSupport386_suffix_000 from ridgeSupport386_eq]
    simp only [ridgeSupport386_suffix_000, ridgeSupport386_suffix_001, ridgeSupport386_suffix_002, ridgeSupport386_suffix_003, ridgeSupport386_suffix_004, ridgeSupport386_suffix_005, ridgeSupport386_suffix_006, ridgeSupport386_suffix_007, ridgeSupport386_suffix_008, ridgeSupport386_suffix_009, ridgeSupport386_suffix_010, ridgeSupport386_suffix_011, ridgeSupport386_suffix_012, List.all_append, List.all_nil, ridgeSupport386_000_checked, ridgeSupport386_001_checked, ridgeSupport386_002_checked, ridgeSupport386_003_checked, ridgeSupport386_004_checked, ridgeSupport386_005_checked, ridgeSupport386_006_checked, ridgeSupport386_007_checked, ridgeSupport386_008_checked, ridgeSupport386_009_checked, ridgeSupport386_010_checked, ridgeSupport386_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
