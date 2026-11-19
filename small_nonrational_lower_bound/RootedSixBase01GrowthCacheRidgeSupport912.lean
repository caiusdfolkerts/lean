module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase01GrowthCacheRidgeSupport912Part000
public import RootedSixBase01GrowthCacheRidgeSupport912Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 912 009 14
cert_ridgeSupport_suffix_decode_2 912 008 14 5 5 009 009 0
cert_ridgeSupport_suffix_decode_2 912 007 14 37 32 009 008 5
cert_ridgeSupport_suffix_decode_2 912 006 14 69 32 009 007 37
cert_ridgeSupport_suffix_decode_2 912 005 14 101 32 009 006 69
cert_ridgeSupport_suffix_decode_2 912 004 14 133 32 009 005 101
cert_ridgeSupport_suffix_decode_2 912 003 14 165 32 009 004 133
cert_ridgeSupport_suffix_decode_2 912 002 14 197 32 009 003 165
cert_ridgeSupport_suffix_decode_2 912 001 14 229 32 009 002 197
cert_ridgeSupport_suffix_decode_2 912 000 14 261 32 009 001 229
cert_ridgeSupport_eq_3 912
theorem ridgeTest_large_912 : ridgeTest 912 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport912_eq]
    simp only [ridgeSupport912_suffix_000, ridgeSupport912_suffix_001, ridgeSupport912_suffix_002, ridgeSupport912_suffix_003, ridgeSupport912_suffix_004, ridgeSupport912_suffix_005, ridgeSupport912_suffix_006, ridgeSupport912_suffix_007, ridgeSupport912_suffix_008, ridgeSupport912_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport912_000_mask, ridgeSupport912_001_mask, ridgeSupport912_002_mask, ridgeSupport912_003_mask, ridgeSupport912_004_mask, ridgeSupport912_005_mask, ridgeSupport912_006_mask, ridgeSupport912_007_mask, ridgeSupport912_008_mask]
    decide +kernel
  · rw [ridgeSupport912_eq]
    simp only [ridgeSupport912_suffix_000, ridgeSupport912_suffix_001, ridgeSupport912_suffix_002, ridgeSupport912_suffix_003, ridgeSupport912_suffix_004, ridgeSupport912_suffix_005, ridgeSupport912_suffix_006, ridgeSupport912_suffix_007, ridgeSupport912_suffix_008, ridgeSupport912_suffix_009, List.all_append, List.all_nil, ridgeSupport912_000_checked, ridgeSupport912_001_checked, ridgeSupport912_002_checked, ridgeSupport912_003_checked, ridgeSupport912_004_checked, ridgeSupport912_005_checked, ridgeSupport912_006_checked, ridgeSupport912_007_checked, ridgeSupport912_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
