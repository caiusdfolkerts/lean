module
prelude
public import RootedSevenPure036GrowthCacheKindSupport2Part000
public import RootedSevenPure036GrowthCacheKindSupport2Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure036
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_suffix_decode_009 : PackedRawNatGrowth.readList 10 0 kindSupport2_rest_009 =
    (kindSupport2_suffix_009, kindSupport2_rest_009) := by rfl
theorem kindSupport2_suffix_decode_008 : PackedRawNatGrowth.readList 10 14 kindSupport2_rest_008 =
    (kindSupport2_suffix_008, kindSupport2_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 10 14 0
    kindSupport2_rest_008 kindSupport2_rest_009 kindSupport2_rest_009
    kindSupport2_008 kindSupport2_suffix_009 kindSupport2_008_decode kindSupport2_suffix_decode_009
theorem kindSupport2_suffix_decode_007 : PackedRawNatGrowth.readList 10 46 kindSupport2_rest_007 =
    (kindSupport2_suffix_007, kindSupport2_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 14
    kindSupport2_rest_007 kindSupport2_rest_008 kindSupport2_rest_009
    kindSupport2_007 kindSupport2_suffix_008 kindSupport2_007_decode kindSupport2_suffix_decode_008
theorem kindSupport2_suffix_decode_006 : PackedRawNatGrowth.readList 10 78 kindSupport2_rest_006 =
    (kindSupport2_suffix_006, kindSupport2_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 46
    kindSupport2_rest_006 kindSupport2_rest_007 kindSupport2_rest_009
    kindSupport2_006 kindSupport2_suffix_007 kindSupport2_006_decode kindSupport2_suffix_decode_007
theorem kindSupport2_suffix_decode_005 : PackedRawNatGrowth.readList 10 110 kindSupport2_rest_005 =
    (kindSupport2_suffix_005, kindSupport2_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 78
    kindSupport2_rest_005 kindSupport2_rest_006 kindSupport2_rest_009
    kindSupport2_005 kindSupport2_suffix_006 kindSupport2_005_decode kindSupport2_suffix_decode_006
theorem kindSupport2_suffix_decode_004 : PackedRawNatGrowth.readList 10 142 kindSupport2_rest_004 =
    (kindSupport2_suffix_004, kindSupport2_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 110
    kindSupport2_rest_004 kindSupport2_rest_005 kindSupport2_rest_009
    kindSupport2_004 kindSupport2_suffix_005 kindSupport2_004_decode kindSupport2_suffix_decode_005
theorem kindSupport2_suffix_decode_003 : PackedRawNatGrowth.readList 10 174 kindSupport2_rest_003 =
    (kindSupport2_suffix_003, kindSupport2_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 142
    kindSupport2_rest_003 kindSupport2_rest_004 kindSupport2_rest_009
    kindSupport2_003 kindSupport2_suffix_004 kindSupport2_003_decode kindSupport2_suffix_decode_004
theorem kindSupport2_suffix_decode_002 : PackedRawNatGrowth.readList 10 206 kindSupport2_rest_002 =
    (kindSupport2_suffix_002, kindSupport2_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 174
    kindSupport2_rest_002 kindSupport2_rest_003 kindSupport2_rest_009
    kindSupport2_002 kindSupport2_suffix_003 kindSupport2_002_decode kindSupport2_suffix_decode_003
theorem kindSupport2_suffix_decode_001 : PackedRawNatGrowth.readList 10 238 kindSupport2_rest_001 =
    (kindSupport2_suffix_001, kindSupport2_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 206
    kindSupport2_rest_001 kindSupport2_rest_002 kindSupport2_rest_009
    kindSupport2_001 kindSupport2_suffix_002 kindSupport2_001_decode kindSupport2_suffix_decode_002
theorem kindSupport2_suffix_decode_000 : PackedRawNatGrowth.readList 10 270 kindSupport2_rest_000 =
    (kindSupport2_suffix_000, kindSupport2_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 10 32 238
    kindSupport2_rest_000 kindSupport2_rest_001 kindSupport2_rest_009
    kindSupport2_000 kindSupport2_suffix_001 kindSupport2_000_decode kindSupport2_suffix_decode_001
theorem kindSupport2_eq : kindRows 2 = kindSupport2_suffix_000 := by
  rw [kindSupport2_source]
  exact congrArg Prod.fst kindSupport2_suffix_decode_000
theorem kindTest_large_2 : kindTest 2 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport2_000_mask, kindSupport2_001_mask, kindSupport2_002_mask, kindSupport2_003_mask, kindSupport2_004_mask, kindSupport2_005_mask, kindSupport2_006_mask, kindSupport2_007_mask, kindSupport2_008_mask]
    decide +kernel
  · rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, List.all_append, List.all_nil, kindSupport2_000_checked, kindSupport2_001_checked, kindSupport2_002_checked, kindSupport2_003_checked, kindSupport2_004_checked, kindSupport2_005_checked, kindSupport2_006_checked, kindSupport2_007_checked, kindSupport2_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSevenPure036
