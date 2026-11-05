module
prelude
public import RootedSixExtra02GrowthCacheRidgeSupport104Part000
public import RootedSixExtra02GrowthCacheRidgeSupport104Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport104_suffix_decode_009 : PackedRawNatGrowth.readList 13 0 ridgeSupport104_rest_009 =
    (ridgeSupport104_suffix_009, ridgeSupport104_rest_009) := by rfl
theorem ridgeSupport104_suffix_decode_008 : PackedRawNatGrowth.readList 13 25 ridgeSupport104_rest_008 =
    (ridgeSupport104_suffix_008, ridgeSupport104_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 25 0
    ridgeSupport104_rest_008 ridgeSupport104_rest_009 ridgeSupport104_rest_009
    ridgeSupport104_008 ridgeSupport104_suffix_009 ridgeSupport104_008_decode ridgeSupport104_suffix_decode_009
theorem ridgeSupport104_suffix_decode_007 : PackedRawNatGrowth.readList 13 57 ridgeSupport104_rest_007 =
    (ridgeSupport104_suffix_007, ridgeSupport104_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 25
    ridgeSupport104_rest_007 ridgeSupport104_rest_008 ridgeSupport104_rest_009
    ridgeSupport104_007 ridgeSupport104_suffix_008 ridgeSupport104_007_decode ridgeSupport104_suffix_decode_008
theorem ridgeSupport104_suffix_decode_006 : PackedRawNatGrowth.readList 13 89 ridgeSupport104_rest_006 =
    (ridgeSupport104_suffix_006, ridgeSupport104_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 57
    ridgeSupport104_rest_006 ridgeSupport104_rest_007 ridgeSupport104_rest_009
    ridgeSupport104_006 ridgeSupport104_suffix_007 ridgeSupport104_006_decode ridgeSupport104_suffix_decode_007
theorem ridgeSupport104_suffix_decode_005 : PackedRawNatGrowth.readList 13 121 ridgeSupport104_rest_005 =
    (ridgeSupport104_suffix_005, ridgeSupport104_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 89
    ridgeSupport104_rest_005 ridgeSupport104_rest_006 ridgeSupport104_rest_009
    ridgeSupport104_005 ridgeSupport104_suffix_006 ridgeSupport104_005_decode ridgeSupport104_suffix_decode_006
theorem ridgeSupport104_suffix_decode_004 : PackedRawNatGrowth.readList 13 153 ridgeSupport104_rest_004 =
    (ridgeSupport104_suffix_004, ridgeSupport104_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 121
    ridgeSupport104_rest_004 ridgeSupport104_rest_005 ridgeSupport104_rest_009
    ridgeSupport104_004 ridgeSupport104_suffix_005 ridgeSupport104_004_decode ridgeSupport104_suffix_decode_005
theorem ridgeSupport104_suffix_decode_003 : PackedRawNatGrowth.readList 13 185 ridgeSupport104_rest_003 =
    (ridgeSupport104_suffix_003, ridgeSupport104_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 153
    ridgeSupport104_rest_003 ridgeSupport104_rest_004 ridgeSupport104_rest_009
    ridgeSupport104_003 ridgeSupport104_suffix_004 ridgeSupport104_003_decode ridgeSupport104_suffix_decode_004
theorem ridgeSupport104_suffix_decode_002 : PackedRawNatGrowth.readList 13 217 ridgeSupport104_rest_002 =
    (ridgeSupport104_suffix_002, ridgeSupport104_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 185
    ridgeSupport104_rest_002 ridgeSupport104_rest_003 ridgeSupport104_rest_009
    ridgeSupport104_002 ridgeSupport104_suffix_003 ridgeSupport104_002_decode ridgeSupport104_suffix_decode_003
theorem ridgeSupport104_suffix_decode_001 : PackedRawNatGrowth.readList 13 249 ridgeSupport104_rest_001 =
    (ridgeSupport104_suffix_001, ridgeSupport104_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 217
    ridgeSupport104_rest_001 ridgeSupport104_rest_002 ridgeSupport104_rest_009
    ridgeSupport104_001 ridgeSupport104_suffix_002 ridgeSupport104_001_decode ridgeSupport104_suffix_decode_002
theorem ridgeSupport104_suffix_decode_000 : PackedRawNatGrowth.readList 13 281 ridgeSupport104_rest_000 =
    (ridgeSupport104_suffix_000, ridgeSupport104_rest_009) :=
  PackedRawNatGrowth.readList_append_of_eq 13 32 249
    ridgeSupport104_rest_000 ridgeSupport104_rest_001 ridgeSupport104_rest_009
    ridgeSupport104_000 ridgeSupport104_suffix_001 ridgeSupport104_000_decode ridgeSupport104_suffix_decode_001
theorem ridgeSupport104_eq : candidateRows 104 = ridgeSupport104_suffix_000 := by
  change candidateSupports 104 = ridgeSupport104_suffix_000
  rw [ridgeSupport104_source]
  exact congrArg Prod.fst ridgeSupport104_suffix_decode_000
theorem ridgeTest_large_104 : ridgeTest 104 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport104_eq]
    simp only [ridgeSupport104_suffix_000, ridgeSupport104_suffix_001, ridgeSupport104_suffix_002, ridgeSupport104_suffix_003, ridgeSupport104_suffix_004, ridgeSupport104_suffix_005, ridgeSupport104_suffix_006, ridgeSupport104_suffix_007, ridgeSupport104_suffix_008, ridgeSupport104_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport104_000_mask, ridgeSupport104_001_mask, ridgeSupport104_002_mask, ridgeSupport104_003_mask, ridgeSupport104_004_mask, ridgeSupport104_005_mask, ridgeSupport104_006_mask, ridgeSupport104_007_mask, ridgeSupport104_008_mask]
    decide +kernel
  · rw [ridgeSupport104_eq]
    simp only [ridgeSupport104_suffix_000, ridgeSupport104_suffix_001, ridgeSupport104_suffix_002, ridgeSupport104_suffix_003, ridgeSupport104_suffix_004, ridgeSupport104_suffix_005, ridgeSupport104_suffix_006, ridgeSupport104_suffix_007, ridgeSupport104_suffix_008, ridgeSupport104_suffix_009, List.all_append, List.all_nil, ridgeSupport104_000_checked, ridgeSupport104_001_checked, ridgeSupport104_002_checked, ridgeSupport104_003_checked, ridgeSupport104_004_checked, ridgeSupport104_005_checked, ridgeSupport104_006_checked, ridgeSupport104_007_checked, ridgeSupport104_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
