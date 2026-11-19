module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase03GrowthCacheRidgeSupport960Part000
public import RootedSixBase03GrowthCacheRidgeSupport960Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 960 009 13
cert_ridgeSupport_suffix_decode_2 960 008 13 26 26 009 009 0
cert_ridgeSupport_suffix_decode_2 960 007 13 58 32 009 008 26
cert_ridgeSupport_suffix_decode_2 960 006 13 90 32 009 007 58
cert_ridgeSupport_suffix_decode_2 960 005 13 122 32 009 006 90
cert_ridgeSupport_suffix_decode_2 960 004 13 154 32 009 005 122
cert_ridgeSupport_suffix_decode_2 960 003 13 186 32 009 004 154
cert_ridgeSupport_suffix_decode_2 960 002 13 218 32 009 003 186
cert_ridgeSupport_suffix_decode_2 960 001 13 250 32 009 002 218
cert_ridgeSupport_suffix_decode_2 960 000 13 282 32 009 001 250
cert_ridgeSupport_eq_2 960
theorem ridgeTest_large_960 : ridgeTest 960 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show candidateRows 960 = ridgeSupport960_suffix_000 from ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport960_000_mask, ridgeSupport960_001_mask, ridgeSupport960_002_mask, ridgeSupport960_003_mask, ridgeSupport960_004_mask, ridgeSupport960_005_mask, ridgeSupport960_006_mask, ridgeSupport960_007_mask, ridgeSupport960_008_mask]
    decide +kernel
  · rw [show candidateRows 960 = ridgeSupport960_suffix_000 from ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, List.all_append, List.all_nil, ridgeSupport960_000_checked, ridgeSupport960_001_checked, ridgeSupport960_002_checked, ridgeSupport960_003_checked, ridgeSupport960_004_checked, ridgeSupport960_005_checked, ridgeSupport960_006_checked, ridgeSupport960_007_checked, ridgeSupport960_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
