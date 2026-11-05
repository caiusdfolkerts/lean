module
prelude
public import RootedSevenPure001GrowthCacheKindSupport3Part000
public import RootedSevenPure001GrowthCacheKindSupport3Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure001
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_suffix_decode_012 : PackedRawNatGrowth.readList 10 0 kindSupport3_rest_012 =
    (kindSupport3_suffix_012, kindSupport3_rest_012) := by rfl
theorem kindSupport3_suffix_decode_011 : PackedRawNatGrowth.readList 10 8 kindSupport3_rest_011 =
    (kindSupport3_suffix_011, kindSupport3_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 10 8 0
    kindSupport3_rest_011 kindSupport3_rest_012 kindSupport3_rest_012
    kindSupport3_011 kindSupport3_suffix_012 kindSupport3_011_decode kindSupport3_suffix_decode_012
theorem kindSupport3_suffix_decode_010 : PackedRawNatGrowth.readList 10 40 kindSupport3_rest_010 =
    (kindSupport3_suffix_010, kindSupport3_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 8
    kindSupport3_rest_010 kindSupport3_rest_011 kindSupport3_rest_012
    kindSupport3_010 kindSupport3_suffix_011 kindSupport3_010_decode kindSupport3_suffix_decode_011
theorem kindSupport3_suffix_decode_009 : PackedRawNatGrowth.readList 10 72 kindSupport3_rest_009 =
    (kindSupport3_suffix_009, kindSupport3_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 40
    kindSupport3_rest_009 kindSupport3_rest_010 kindSupport3_rest_012
    kindSupport3_009 kindSupport3_suffix_010 kindSupport3_009_decode kindSupport3_suffix_decode_010
theorem kindSupport3_suffix_decode_008 : PackedRawNatGrowth.readList 10 104 kindSupport3_rest_008 =
    (kindSupport3_suffix_008, kindSupport3_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 72
    kindSupport3_rest_008 kindSupport3_rest_009 kindSupport3_rest_012
    kindSupport3_008 kindSupport3_suffix_009 kindSupport3_008_decode kindSupport3_suffix_decode_009
theorem kindSupport3_suffix_decode_007 : PackedRawNatGrowth.readList 10 136 kindSupport3_rest_007 =
    (kindSupport3_suffix_007, kindSupport3_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 104
    kindSupport3_rest_007 kindSupport3_rest_008 kindSupport3_rest_012
    kindSupport3_007 kindSupport3_suffix_008 kindSupport3_007_decode kindSupport3_suffix_decode_008
theorem kindSupport3_suffix_decode_006 : PackedRawNatGrowth.readList 10 168 kindSupport3_rest_006 =
    (kindSupport3_suffix_006, kindSupport3_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 136
    kindSupport3_rest_006 kindSupport3_rest_007 kindSupport3_rest_012
    kindSupport3_006 kindSupport3_suffix_007 kindSupport3_006_decode kindSupport3_suffix_decode_007
theorem kindSupport3_suffix_decode_005 : PackedRawNatGrowth.readList 10 200 kindSupport3_rest_005 =
    (kindSupport3_suffix_005, kindSupport3_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 168
    kindSupport3_rest_005 kindSupport3_rest_006 kindSupport3_rest_012
    kindSupport3_005 kindSupport3_suffix_006 kindSupport3_005_decode kindSupport3_suffix_decode_006
theorem kindSupport3_suffix_decode_004 : PackedRawNatGrowth.readList 10 232 kindSupport3_rest_004 =
    (kindSupport3_suffix_004, kindSupport3_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 200
    kindSupport3_rest_004 kindSupport3_rest_005 kindSupport3_rest_012
    kindSupport3_004 kindSupport3_suffix_005 kindSupport3_004_decode kindSupport3_suffix_decode_005
theorem kindSupport3_suffix_decode_003 : PackedRawNatGrowth.readList 10 264 kindSupport3_rest_003 =
    (kindSupport3_suffix_003, kindSupport3_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 232
    kindSupport3_rest_003 kindSupport3_rest_004 kindSupport3_rest_012
    kindSupport3_003 kindSupport3_suffix_004 kindSupport3_003_decode kindSupport3_suffix_decode_004
theorem kindSupport3_suffix_decode_002 : PackedRawNatGrowth.readList 10 296 kindSupport3_rest_002 =
    (kindSupport3_suffix_002, kindSupport3_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 264
    kindSupport3_rest_002 kindSupport3_rest_003 kindSupport3_rest_012
    kindSupport3_002 kindSupport3_suffix_003 kindSupport3_002_decode kindSupport3_suffix_decode_003
theorem kindSupport3_suffix_decode_001 : PackedRawNatGrowth.readList 10 328 kindSupport3_rest_001 =
    (kindSupport3_suffix_001, kindSupport3_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 296
    kindSupport3_rest_001 kindSupport3_rest_002 kindSupport3_rest_012
    kindSupport3_001 kindSupport3_suffix_002 kindSupport3_001_decode kindSupport3_suffix_decode_002
theorem kindSupport3_suffix_decode_000 : PackedRawNatGrowth.readList 10 360 kindSupport3_rest_000 =
    (kindSupport3_suffix_000, kindSupport3_rest_012) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 328
    kindSupport3_rest_000 kindSupport3_rest_001 kindSupport3_rest_012
    kindSupport3_000 kindSupport3_suffix_001 kindSupport3_000_decode kindSupport3_suffix_decode_001
theorem kindSupport3_eq : kindRows 3 = kindSupport3_suffix_000 := by
  rw [kindSupport3_source]
  exact congrArg Prod.fst kindSupport3_suffix_decode_000
theorem kindTest_large_3 : kindTest 3 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport3_000_mask, kindSupport3_001_mask, kindSupport3_002_mask, kindSupport3_003_mask, kindSupport3_004_mask, kindSupport3_005_mask, kindSupport3_006_mask, kindSupport3_007_mask, kindSupport3_008_mask, kindSupport3_009_mask, kindSupport3_010_mask, kindSupport3_011_mask]
    decide +kernel
  · rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, List.all_append, List.all_nil, kindSupport3_000_checked, kindSupport3_001_checked, kindSupport3_002_checked, kindSupport3_003_checked, kindSupport3_004_checked, kindSupport3_005_checked, kindSupport3_006_checked, kindSupport3_007_checked, kindSupport3_008_checked, kindSupport3_009_checked, kindSupport3_010_checked, kindSupport3_011_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSevenPure001
