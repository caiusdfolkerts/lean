module
prelude
public import RootedSixBase00GrowthCacheKindSupport8Part000
public import RootedSixBase00GrowthCacheKindSupport8Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport8_suffix_decode_011 : PackedRawNatGrowth.readList 15 0 kindSupport8_rest_011 =
    (kindSupport8_suffix_011, kindSupport8_rest_011) := by rfl
theorem kindSupport8_suffix_decode_010 : PackedRawNatGrowth.readList 15 16 kindSupport8_rest_010 =
    (kindSupport8_suffix_010, kindSupport8_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 15 16 0
    kindSupport8_rest_010 kindSupport8_rest_011 kindSupport8_rest_011
    kindSupport8_010 kindSupport8_suffix_011 kindSupport8_010_decode kindSupport8_suffix_decode_011
theorem kindSupport8_suffix_decode_009 : PackedRawNatGrowth.readList 15 48 kindSupport8_rest_009 =
    (kindSupport8_suffix_009, kindSupport8_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 16
    kindSupport8_rest_009 kindSupport8_rest_010 kindSupport8_rest_011
    kindSupport8_009 kindSupport8_suffix_010 kindSupport8_009_decode kindSupport8_suffix_decode_010
theorem kindSupport8_suffix_decode_008 : PackedRawNatGrowth.readList 15 80 kindSupport8_rest_008 =
    (kindSupport8_suffix_008, kindSupport8_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 48
    kindSupport8_rest_008 kindSupport8_rest_009 kindSupport8_rest_011
    kindSupport8_008 kindSupport8_suffix_009 kindSupport8_008_decode kindSupport8_suffix_decode_009
theorem kindSupport8_suffix_decode_007 : PackedRawNatGrowth.readList 15 112 kindSupport8_rest_007 =
    (kindSupport8_suffix_007, kindSupport8_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 80
    kindSupport8_rest_007 kindSupport8_rest_008 kindSupport8_rest_011
    kindSupport8_007 kindSupport8_suffix_008 kindSupport8_007_decode kindSupport8_suffix_decode_008
theorem kindSupport8_suffix_decode_006 : PackedRawNatGrowth.readList 15 144 kindSupport8_rest_006 =
    (kindSupport8_suffix_006, kindSupport8_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 112
    kindSupport8_rest_006 kindSupport8_rest_007 kindSupport8_rest_011
    kindSupport8_006 kindSupport8_suffix_007 kindSupport8_006_decode kindSupport8_suffix_decode_007
theorem kindSupport8_suffix_decode_005 : PackedRawNatGrowth.readList 15 176 kindSupport8_rest_005 =
    (kindSupport8_suffix_005, kindSupport8_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 144
    kindSupport8_rest_005 kindSupport8_rest_006 kindSupport8_rest_011
    kindSupport8_005 kindSupport8_suffix_006 kindSupport8_005_decode kindSupport8_suffix_decode_006
theorem kindSupport8_suffix_decode_004 : PackedRawNatGrowth.readList 15 208 kindSupport8_rest_004 =
    (kindSupport8_suffix_004, kindSupport8_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 176
    kindSupport8_rest_004 kindSupport8_rest_005 kindSupport8_rest_011
    kindSupport8_004 kindSupport8_suffix_005 kindSupport8_004_decode kindSupport8_suffix_decode_005
theorem kindSupport8_suffix_decode_003 : PackedRawNatGrowth.readList 15 240 kindSupport8_rest_003 =
    (kindSupport8_suffix_003, kindSupport8_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 208
    kindSupport8_rest_003 kindSupport8_rest_004 kindSupport8_rest_011
    kindSupport8_003 kindSupport8_suffix_004 kindSupport8_003_decode kindSupport8_suffix_decode_004
theorem kindSupport8_suffix_decode_002 : PackedRawNatGrowth.readList 15 272 kindSupport8_rest_002 =
    (kindSupport8_suffix_002, kindSupport8_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 240
    kindSupport8_rest_002 kindSupport8_rest_003 kindSupport8_rest_011
    kindSupport8_002 kindSupport8_suffix_003 kindSupport8_002_decode kindSupport8_suffix_decode_003
theorem kindSupport8_suffix_decode_001 : PackedRawNatGrowth.readList 15 304 kindSupport8_rest_001 =
    (kindSupport8_suffix_001, kindSupport8_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 272
    kindSupport8_rest_001 kindSupport8_rest_002 kindSupport8_rest_011
    kindSupport8_001 kindSupport8_suffix_002 kindSupport8_001_decode kindSupport8_suffix_decode_002
theorem kindSupport8_suffix_decode_000 : PackedRawNatGrowth.readList 15 336 kindSupport8_rest_000 =
    (kindSupport8_suffix_000, kindSupport8_rest_011) :=
  PackedRawNatGrowth.readList_append_of_eq 15 32 304
    kindSupport8_rest_000 kindSupport8_rest_001 kindSupport8_rest_011
    kindSupport8_000 kindSupport8_suffix_001 kindSupport8_000_decode kindSupport8_suffix_decode_001
theorem kindSupport8_eq : kindRows 8 = kindSupport8_suffix_000 := by
  rw [kindSupport8_source]
  exact congrArg Prod.fst kindSupport8_suffix_decode_000
theorem kindTest_large_8 : kindTest 8 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport8_eq]
    simp only [kindSupport8_suffix_000, kindSupport8_suffix_001, kindSupport8_suffix_002, kindSupport8_suffix_003, kindSupport8_suffix_004, kindSupport8_suffix_005, kindSupport8_suffix_006, kindSupport8_suffix_007, kindSupport8_suffix_008, kindSupport8_suffix_009, kindSupport8_suffix_010, kindSupport8_suffix_011, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport8_000_mask, kindSupport8_001_mask, kindSupport8_002_mask, kindSupport8_003_mask, kindSupport8_004_mask, kindSupport8_005_mask, kindSupport8_006_mask, kindSupport8_007_mask, kindSupport8_008_mask, kindSupport8_009_mask, kindSupport8_010_mask]
    decide +kernel
  · rw [kindSupport8_eq]
    simp only [kindSupport8_suffix_000, kindSupport8_suffix_001, kindSupport8_suffix_002, kindSupport8_suffix_003, kindSupport8_suffix_004, kindSupport8_suffix_005, kindSupport8_suffix_006, kindSupport8_suffix_007, kindSupport8_suffix_008, kindSupport8_suffix_009, kindSupport8_suffix_010, kindSupport8_suffix_011, List.all_append, List.all_nil, kindSupport8_000_checked, kindSupport8_001_checked, kindSupport8_002_checked, kindSupport8_003_checked, kindSupport8_004_checked, kindSupport8_005_checked, kindSupport8_006_checked, kindSupport8_007_checked, kindSupport8_008_checked, kindSupport8_009_checked, kindSupport8_010_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
