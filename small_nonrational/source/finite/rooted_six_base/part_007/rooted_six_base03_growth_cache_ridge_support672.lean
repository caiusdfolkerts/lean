module
prelude
public import RootedSixBase03GrowthCacheRidgeSupport672Part000
public import RootedSixBase03GrowthCacheRidgeSupport672Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport672_suffix_decode_012 : PackedRawNatGrowth.readList 13 0 ridgeSupport672_rest_012 =
    (ridgeSupport672_suffix_012, ridgeSupport672_rest_012) := by rfl
theorem ridgeSupport672_suffix_decode_011 : PackedRawNatGrowth.readList 13 26 ridgeSupport672_rest_011 =
    (ridgeSupport672_suffix_011, ridgeSupport672_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 26 0
    ridgeSupport672_rest_011 ridgeSupport672_rest_012 ridgeSupport672_rest_012
    ridgeSupport672_011 ridgeSupport672_suffix_012 ridgeSupport672_011_decode ridgeSupport672_suffix_decode_012
theorem ridgeSupport672_suffix_decode_010 : PackedRawNatGrowth.readList 13 58 ridgeSupport672_rest_010 =
    (ridgeSupport672_suffix_010, ridgeSupport672_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 26
    ridgeSupport672_rest_010 ridgeSupport672_rest_011 ridgeSupport672_rest_012
    ridgeSupport672_010 ridgeSupport672_suffix_011 ridgeSupport672_010_decode ridgeSupport672_suffix_decode_011
theorem ridgeSupport672_suffix_decode_009 : PackedRawNatGrowth.readList 13 90 ridgeSupport672_rest_009 =
    (ridgeSupport672_suffix_009, ridgeSupport672_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 58
    ridgeSupport672_rest_009 ridgeSupport672_rest_010 ridgeSupport672_rest_012
    ridgeSupport672_009 ridgeSupport672_suffix_010 ridgeSupport672_009_decode ridgeSupport672_suffix_decode_010
theorem ridgeSupport672_suffix_decode_008 : PackedRawNatGrowth.readList 13 122 ridgeSupport672_rest_008 =
    (ridgeSupport672_suffix_008, ridgeSupport672_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 90
    ridgeSupport672_rest_008 ridgeSupport672_rest_009 ridgeSupport672_rest_012
    ridgeSupport672_008 ridgeSupport672_suffix_009 ridgeSupport672_008_decode ridgeSupport672_suffix_decode_009
theorem ridgeSupport672_suffix_decode_007 : PackedRawNatGrowth.readList 13 154 ridgeSupport672_rest_007 =
    (ridgeSupport672_suffix_007, ridgeSupport672_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 122
    ridgeSupport672_rest_007 ridgeSupport672_rest_008 ridgeSupport672_rest_012
    ridgeSupport672_007 ridgeSupport672_suffix_008 ridgeSupport672_007_decode ridgeSupport672_suffix_decode_008
theorem ridgeSupport672_suffix_decode_006 : PackedRawNatGrowth.readList 13 186 ridgeSupport672_rest_006 =
    (ridgeSupport672_suffix_006, ridgeSupport672_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 154
    ridgeSupport672_rest_006 ridgeSupport672_rest_007 ridgeSupport672_rest_012
    ridgeSupport672_006 ridgeSupport672_suffix_007 ridgeSupport672_006_decode ridgeSupport672_suffix_decode_007
theorem ridgeSupport672_suffix_decode_005 : PackedRawNatGrowth.readList 13 218 ridgeSupport672_rest_005 =
    (ridgeSupport672_suffix_005, ridgeSupport672_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 186
    ridgeSupport672_rest_005 ridgeSupport672_rest_006 ridgeSupport672_rest_012
    ridgeSupport672_005 ridgeSupport672_suffix_006 ridgeSupport672_005_decode ridgeSupport672_suffix_decode_006
theorem ridgeSupport672_suffix_decode_004 : PackedRawNatGrowth.readList 13 250 ridgeSupport672_rest_004 =
    (ridgeSupport672_suffix_004, ridgeSupport672_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 218
    ridgeSupport672_rest_004 ridgeSupport672_rest_005 ridgeSupport672_rest_012
    ridgeSupport672_004 ridgeSupport672_suffix_005 ridgeSupport672_004_decode ridgeSupport672_suffix_decode_005
theorem ridgeSupport672_suffix_decode_003 : PackedRawNatGrowth.readList 13 282 ridgeSupport672_rest_003 =
    (ridgeSupport672_suffix_003, ridgeSupport672_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 250
    ridgeSupport672_rest_003 ridgeSupport672_rest_004 ridgeSupport672_rest_012
    ridgeSupport672_003 ridgeSupport672_suffix_004 ridgeSupport672_003_decode ridgeSupport672_suffix_decode_004
theorem ridgeSupport672_suffix_decode_002 : PackedRawNatGrowth.readList 13 314 ridgeSupport672_rest_002 =
    (ridgeSupport672_suffix_002, ridgeSupport672_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 282
    ridgeSupport672_rest_002 ridgeSupport672_rest_003 ridgeSupport672_rest_012
    ridgeSupport672_002 ridgeSupport672_suffix_003 ridgeSupport672_002_decode ridgeSupport672_suffix_decode_003
theorem ridgeSupport672_suffix_decode_001 : PackedRawNatGrowth.readList 13 346 ridgeSupport672_rest_001 =
    (ridgeSupport672_suffix_001, ridgeSupport672_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 314
    ridgeSupport672_rest_001 ridgeSupport672_rest_002 ridgeSupport672_rest_012
    ridgeSupport672_001 ridgeSupport672_suffix_002 ridgeSupport672_001_decode ridgeSupport672_suffix_decode_002
theorem ridgeSupport672_suffix_decode_000 : PackedRawNatGrowth.readList 13 378 ridgeSupport672_rest_000 =
    (ridgeSupport672_suffix_000, ridgeSupport672_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 346
    ridgeSupport672_rest_000 ridgeSupport672_rest_001 ridgeSupport672_rest_012
    ridgeSupport672_000 ridgeSupport672_suffix_001 ridgeSupport672_000_decode ridgeSupport672_suffix_decode_001
theorem ridgeSupport672_eq : candidateSupports 672 = ridgeSupport672_suffix_000 := by
  rw [ridgeSupport672_source]
  exact congrArg Prod.fst ridgeSupport672_suffix_decode_000
theorem ridgeTest_large_672 : ridgeTest 672 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 672 = ridgeSupport672_suffix_000 from ridgeSupport672_eq]
    simp only [ridgeSupport672_suffix_000, ridgeSupport672_suffix_001, ridgeSupport672_suffix_002, ridgeSupport672_suffix_003, ridgeSupport672_suffix_004, ridgeSupport672_suffix_005, ridgeSupport672_suffix_006, ridgeSupport672_suffix_007, ridgeSupport672_suffix_008, ridgeSupport672_suffix_009, ridgeSupport672_suffix_010, ridgeSupport672_suffix_011, ridgeSupport672_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport672_000_mask, ridgeSupport672_001_mask, ridgeSupport672_002_mask, ridgeSupport672_003_mask, ridgeSupport672_004_mask, ridgeSupport672_005_mask, ridgeSupport672_006_mask, ridgeSupport672_007_mask, ridgeSupport672_008_mask, ridgeSupport672_009_mask, ridgeSupport672_010_mask, ridgeSupport672_011_mask]
    decide +kernel
  · rw [show candidateRows 672 = ridgeSupport672_suffix_000 from ridgeSupport672_eq]
    simp only [ridgeSupport672_suffix_000, ridgeSupport672_suffix_001, ridgeSupport672_suffix_002, ridgeSupport672_suffix_003, ridgeSupport672_suffix_004, ridgeSupport672_suffix_005, ridgeSupport672_suffix_006, ridgeSupport672_suffix_007, ridgeSupport672_suffix_008, ridgeSupport672_suffix_009, ridgeSupport672_suffix_010, ridgeSupport672_suffix_011, ridgeSupport672_suffix_012, List.all_append, List.all_nil, ridgeSupport672_000_checked, ridgeSupport672_001_checked, ridgeSupport672_002_checked, ridgeSupport672_003_checked, ridgeSupport672_004_checked, ridgeSupport672_005_checked, ridgeSupport672_006_checked, ridgeSupport672_007_checked, ridgeSupport672_008_checked, ridgeSupport672_009_checked, ridgeSupport672_010_checked, ridgeSupport672_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
