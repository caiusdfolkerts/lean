module
prelude
public import RootedSixBase03GrowthCacheKindSupport8Part000
public import RootedSixBase03GrowthCacheKindSupport8Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport8_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 kindSupport8_rest_009 =
    (kindSupport8_suffix_009, kindSupport8_rest_009) := by rfl
theorem kindSupport8_suffix_decode_008 : PackedRawNatGrowth.readList 13 20 kindSupport8_rest_008 =
    (kindSupport8_suffix_008, kindSupport8_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 20 0
    kindSupport8_rest_008 kindSupport8_rest_009 kindSupport8_rest_009
    kindSupport8_008 kindSupport8_suffix_009 kindSupport8_008_decode kindSupport8_suffix_decode_009
theorem kindSupport8_suffix_decode_007 : PackedRawNatGrowth.readList 13 52 kindSupport8_rest_007 =
    (kindSupport8_suffix_007, kindSupport8_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 20
    kindSupport8_rest_007 kindSupport8_rest_008 kindSupport8_rest_009
    kindSupport8_007 kindSupport8_suffix_008 kindSupport8_007_decode kindSupport8_suffix_decode_008
theorem kindSupport8_suffix_decode_006 : PackedRawNatGrowth.readList 13 84 kindSupport8_rest_006 =
    (kindSupport8_suffix_006, kindSupport8_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 52
    kindSupport8_rest_006 kindSupport8_rest_007 kindSupport8_rest_009
    kindSupport8_006 kindSupport8_suffix_007 kindSupport8_006_decode kindSupport8_suffix_decode_007
theorem kindSupport8_suffix_decode_005 : PackedRawNatGrowth.readList 13 116 kindSupport8_rest_005 =
    (kindSupport8_suffix_005, kindSupport8_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 84
    kindSupport8_rest_005 kindSupport8_rest_006 kindSupport8_rest_009
    kindSupport8_005 kindSupport8_suffix_006 kindSupport8_005_decode kindSupport8_suffix_decode_006
theorem kindSupport8_suffix_decode_004 : PackedRawNatGrowth.readList 13 148 kindSupport8_rest_004 =
    (kindSupport8_suffix_004, kindSupport8_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 116
    kindSupport8_rest_004 kindSupport8_rest_005 kindSupport8_rest_009
    kindSupport8_004 kindSupport8_suffix_005 kindSupport8_004_decode kindSupport8_suffix_decode_005
theorem kindSupport8_suffix_decode_003 : PackedRawNatGrowth.readList 13 180 kindSupport8_rest_003 =
    (kindSupport8_suffix_003, kindSupport8_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 148
    kindSupport8_rest_003 kindSupport8_rest_004 kindSupport8_rest_009
    kindSupport8_003 kindSupport8_suffix_004 kindSupport8_003_decode kindSupport8_suffix_decode_004
theorem kindSupport8_suffix_decode_002 : PackedRawNatGrowth.readList 13 212 kindSupport8_rest_002 =
    (kindSupport8_suffix_002, kindSupport8_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 180
    kindSupport8_rest_002 kindSupport8_rest_003 kindSupport8_rest_009
    kindSupport8_002 kindSupport8_suffix_003 kindSupport8_002_decode kindSupport8_suffix_decode_003
theorem kindSupport8_suffix_decode_001 : PackedRawNatGrowth.readList 13 244 kindSupport8_rest_001 =
    (kindSupport8_suffix_001, kindSupport8_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 212
    kindSupport8_rest_001 kindSupport8_rest_002 kindSupport8_rest_009
    kindSupport8_001 kindSupport8_suffix_002 kindSupport8_001_decode kindSupport8_suffix_decode_002
theorem kindSupport8_suffix_decode_000 : PackedRawNatGrowth.readList 13 276 kindSupport8_rest_000 =
    (kindSupport8_suffix_000, kindSupport8_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 244
    kindSupport8_rest_000 kindSupport8_rest_001 kindSupport8_rest_009
    kindSupport8_000 kindSupport8_suffix_001 kindSupport8_000_decode kindSupport8_suffix_decode_001
theorem kindSupport8_eq : kindSupports 8 = kindSupport8_suffix_000 := by
  rw [kindSupport8_source]
  exact congrArg Prod.fst kindSupport8_suffix_decode_000
theorem kindTest_large_8 : kindTest 8 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show kindRows 8 = kindSupport8_suffix_000 from kindSupport8_eq]
    simp only [kindSupport8_suffix_000, kindSupport8_suffix_001, kindSupport8_suffix_002, kindSupport8_suffix_003, kindSupport8_suffix_004, kindSupport8_suffix_005, kindSupport8_suffix_006, kindSupport8_suffix_007, kindSupport8_suffix_008, kindSupport8_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport8_000_mask, kindSupport8_001_mask, kindSupport8_002_mask, kindSupport8_003_mask, kindSupport8_004_mask, kindSupport8_005_mask, kindSupport8_006_mask, kindSupport8_007_mask, kindSupport8_008_mask]
    decide +kernel
  · rw [show kindRows 8 = kindSupport8_suffix_000 from kindSupport8_eq]
    simp only [kindSupport8_suffix_000, kindSupport8_suffix_001, kindSupport8_suffix_002, kindSupport8_suffix_003, kindSupport8_suffix_004, kindSupport8_suffix_005, kindSupport8_suffix_006, kindSupport8_suffix_007, kindSupport8_suffix_008, kindSupport8_suffix_009, List.all_append, List.all_nil, kindSupport8_000_checked, kindSupport8_001_checked, kindSupport8_002_checked, kindSupport8_003_checked, kindSupport8_004_checked, kindSupport8_005_checked, kindSupport8_006_checked, kindSupport8_007_checked, kindSupport8_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
