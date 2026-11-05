module
prelude
public import RootedSixBase01GrowthCacheRidgeSupport848Part000
public import RootedSixBase01GrowthCacheRidgeSupport848Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport848_suffix_decode_009 : PackedRawNatGrowth.readList 14 0 ridgeSupport848_rest_009 =
    (ridgeSupport848_suffix_009, ridgeSupport848_rest_009) := by rfl
theorem ridgeSupport848_suffix_decode_008 : PackedRawNatGrowth.readList 14 5 ridgeSupport848_rest_008 =
    (ridgeSupport848_suffix_008, ridgeSupport848_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 5 0
    ridgeSupport848_rest_008 ridgeSupport848_rest_009 ridgeSupport848_rest_009
    ridgeSupport848_008 ridgeSupport848_suffix_009 ridgeSupport848_008_decode ridgeSupport848_suffix_decode_009
theorem ridgeSupport848_suffix_decode_007 : PackedRawNatGrowth.readList 14 37 ridgeSupport848_rest_007 =
    (ridgeSupport848_suffix_007, ridgeSupport848_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 5
    ridgeSupport848_rest_007 ridgeSupport848_rest_008 ridgeSupport848_rest_009
    ridgeSupport848_007 ridgeSupport848_suffix_008 ridgeSupport848_007_decode ridgeSupport848_suffix_decode_008
theorem ridgeSupport848_suffix_decode_006 : PackedRawNatGrowth.readList 14 69 ridgeSupport848_rest_006 =
    (ridgeSupport848_suffix_006, ridgeSupport848_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 37
    ridgeSupport848_rest_006 ridgeSupport848_rest_007 ridgeSupport848_rest_009
    ridgeSupport848_006 ridgeSupport848_suffix_007 ridgeSupport848_006_decode ridgeSupport848_suffix_decode_007
theorem ridgeSupport848_suffix_decode_005 : PackedRawNatGrowth.readList 14 101 ridgeSupport848_rest_005 =
    (ridgeSupport848_suffix_005, ridgeSupport848_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 69
    ridgeSupport848_rest_005 ridgeSupport848_rest_006 ridgeSupport848_rest_009
    ridgeSupport848_005 ridgeSupport848_suffix_006 ridgeSupport848_005_decode ridgeSupport848_suffix_decode_006
theorem ridgeSupport848_suffix_decode_004 : PackedRawNatGrowth.readList 14 133 ridgeSupport848_rest_004 =
    (ridgeSupport848_suffix_004, ridgeSupport848_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 101
    ridgeSupport848_rest_004 ridgeSupport848_rest_005 ridgeSupport848_rest_009
    ridgeSupport848_004 ridgeSupport848_suffix_005 ridgeSupport848_004_decode ridgeSupport848_suffix_decode_005
theorem ridgeSupport848_suffix_decode_003 : PackedRawNatGrowth.readList 14 165 ridgeSupport848_rest_003 =
    (ridgeSupport848_suffix_003, ridgeSupport848_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 133
    ridgeSupport848_rest_003 ridgeSupport848_rest_004 ridgeSupport848_rest_009
    ridgeSupport848_003 ridgeSupport848_suffix_004 ridgeSupport848_003_decode ridgeSupport848_suffix_decode_004
theorem ridgeSupport848_suffix_decode_002 : PackedRawNatGrowth.readList 14 197 ridgeSupport848_rest_002 =
    (ridgeSupport848_suffix_002, ridgeSupport848_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 165
    ridgeSupport848_rest_002 ridgeSupport848_rest_003 ridgeSupport848_rest_009
    ridgeSupport848_002 ridgeSupport848_suffix_003 ridgeSupport848_002_decode ridgeSupport848_suffix_decode_003
theorem ridgeSupport848_suffix_decode_001 : PackedRawNatGrowth.readList 14 229 ridgeSupport848_rest_001 =
    (ridgeSupport848_suffix_001, ridgeSupport848_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 197
    ridgeSupport848_rest_001 ridgeSupport848_rest_002 ridgeSupport848_rest_009
    ridgeSupport848_001 ridgeSupport848_suffix_002 ridgeSupport848_001_decode ridgeSupport848_suffix_decode_002
theorem ridgeSupport848_suffix_decode_000 : PackedRawNatGrowth.readList 14 261 ridgeSupport848_rest_000 =
    (ridgeSupport848_suffix_000, ridgeSupport848_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 14 32 229
    ridgeSupport848_rest_000 ridgeSupport848_rest_001 ridgeSupport848_rest_009
    ridgeSupport848_000 ridgeSupport848_suffix_001 ridgeSupport848_000_decode ridgeSupport848_suffix_decode_001
theorem ridgeSupport848_eq : candidateRows 848 = ridgeSupport848_suffix_000 := by
  rw [ridgeSupport848_source]
  exact congrArg Prod.fst ridgeSupport848_suffix_decode_000
theorem ridgeTest_large_848 : ridgeTest 848 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport848_eq]
    simp only [ridgeSupport848_suffix_000, ridgeSupport848_suffix_001, ridgeSupport848_suffix_002, ridgeSupport848_suffix_003, ridgeSupport848_suffix_004, ridgeSupport848_suffix_005, ridgeSupport848_suffix_006, ridgeSupport848_suffix_007, ridgeSupport848_suffix_008, ridgeSupport848_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport848_000_mask, ridgeSupport848_001_mask, ridgeSupport848_002_mask, ridgeSupport848_003_mask, ridgeSupport848_004_mask, ridgeSupport848_005_mask, ridgeSupport848_006_mask, ridgeSupport848_007_mask, ridgeSupport848_008_mask]
    decide +kernel
  · rw [ridgeSupport848_eq]
    simp only [ridgeSupport848_suffix_000, ridgeSupport848_suffix_001, ridgeSupport848_suffix_002, ridgeSupport848_suffix_003, ridgeSupport848_suffix_004, ridgeSupport848_suffix_005, ridgeSupport848_suffix_006, ridgeSupport848_suffix_007, ridgeSupport848_suffix_008, ridgeSupport848_suffix_009, List.all_append, List.all_nil, ridgeSupport848_000_checked, ridgeSupport848_001_checked, ridgeSupport848_002_checked, ridgeSupport848_003_checked, ridgeSupport848_004_checked, ridgeSupport848_005_checked, ridgeSupport848_006_checked, ridgeSupport848_007_checked, ridgeSupport848_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
