module
prelude
public import RootedSevenPure043GrowthCacheKindSupport3Part000
public import RootedSevenPure043GrowthCacheKindSupport3Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure043
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_suffix_decode_009 : PackedRawNatGrowth.readList 9 0 kindSupport3_rest_009 =
    (kindSupport3_suffix_009, kindSupport3_rest_009) := by rfl
theorem kindSupport3_suffix_decode_008 : PackedRawNatGrowth.readList 9 14 kindSupport3_rest_008 =
    (kindSupport3_suffix_008, kindSupport3_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 9 14 0
    kindSupport3_rest_008 kindSupport3_rest_009 kindSupport3_rest_009
    kindSupport3_008 kindSupport3_suffix_009 kindSupport3_008_decode kindSupport3_suffix_decode_009
theorem kindSupport3_suffix_decode_007 : PackedRawNatGrowth.readList 9 46 kindSupport3_rest_007 =
    (kindSupport3_suffix_007, kindSupport3_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 9 32 14
    kindSupport3_rest_007 kindSupport3_rest_008 kindSupport3_rest_009
    kindSupport3_007 kindSupport3_suffix_008 kindSupport3_007_decode kindSupport3_suffix_decode_008
theorem kindSupport3_suffix_decode_006 : PackedRawNatGrowth.readList 9 78 kindSupport3_rest_006 =
    (kindSupport3_suffix_006, kindSupport3_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 9 32 46
    kindSupport3_rest_006 kindSupport3_rest_007 kindSupport3_rest_009
    kindSupport3_006 kindSupport3_suffix_007 kindSupport3_006_decode kindSupport3_suffix_decode_007
theorem kindSupport3_suffix_decode_005 : PackedRawNatGrowth.readList 9 110 kindSupport3_rest_005 =
    (kindSupport3_suffix_005, kindSupport3_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 9 32 78
    kindSupport3_rest_005 kindSupport3_rest_006 kindSupport3_rest_009
    kindSupport3_005 kindSupport3_suffix_006 kindSupport3_005_decode kindSupport3_suffix_decode_006
theorem kindSupport3_suffix_decode_004 : PackedRawNatGrowth.readList 9 142 kindSupport3_rest_004 =
    (kindSupport3_suffix_004, kindSupport3_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 9 32 110
    kindSupport3_rest_004 kindSupport3_rest_005 kindSupport3_rest_009
    kindSupport3_004 kindSupport3_suffix_005 kindSupport3_004_decode kindSupport3_suffix_decode_005
theorem kindSupport3_suffix_decode_003 : PackedRawNatGrowth.readList 9 174 kindSupport3_rest_003 =
    (kindSupport3_suffix_003, kindSupport3_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 9 32 142
    kindSupport3_rest_003 kindSupport3_rest_004 kindSupport3_rest_009
    kindSupport3_003 kindSupport3_suffix_004 kindSupport3_003_decode kindSupport3_suffix_decode_004
theorem kindSupport3_suffix_decode_002 : PackedRawNatGrowth.readList 9 206 kindSupport3_rest_002 =
    (kindSupport3_suffix_002, kindSupport3_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 9 32 174
    kindSupport3_rest_002 kindSupport3_rest_003 kindSupport3_rest_009
    kindSupport3_002 kindSupport3_suffix_003 kindSupport3_002_decode kindSupport3_suffix_decode_003
theorem kindSupport3_suffix_decode_001 : PackedRawNatGrowth.readList 9 238 kindSupport3_rest_001 =
    (kindSupport3_suffix_001, kindSupport3_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 9 32 206
    kindSupport3_rest_001 kindSupport3_rest_002 kindSupport3_rest_009
    kindSupport3_001 kindSupport3_suffix_002 kindSupport3_001_decode kindSupport3_suffix_decode_002
theorem kindSupport3_suffix_decode_000 : PackedRawNatGrowth.readList 9 270 kindSupport3_rest_000 =
    (kindSupport3_suffix_000, kindSupport3_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 9 32 238
    kindSupport3_rest_000 kindSupport3_rest_001 kindSupport3_rest_009
    kindSupport3_000 kindSupport3_suffix_001 kindSupport3_000_decode kindSupport3_suffix_decode_001
theorem kindSupport3_eq : kindRows 3 = kindSupport3_suffix_000 := by
  rw [kindSupport3_source]
  exact congrArg Prod.fst kindSupport3_suffix_decode_000
theorem kindTest_large_3 : kindTest 3 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport3_000_mask, kindSupport3_001_mask, kindSupport3_002_mask, kindSupport3_003_mask, kindSupport3_004_mask, kindSupport3_005_mask, kindSupport3_006_mask, kindSupport3_007_mask, kindSupport3_008_mask]
    decide +kernel
  · rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, List.all_append, List.all_nil, kindSupport3_000_checked, kindSupport3_001_checked, kindSupport3_002_checked, kindSupport3_003_checked, kindSupport3_004_checked, kindSupport3_005_checked, kindSupport3_006_checked, kindSupport3_007_checked, kindSupport3_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSevenPure043
