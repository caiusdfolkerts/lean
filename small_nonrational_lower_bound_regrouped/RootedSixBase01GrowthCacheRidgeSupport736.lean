module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport736PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 736 009 14
cert_ridgeSupport_suffix_decode_2 736 008 14 5 5 009 009 0
cert_ridgeSupport_suffix_decode_2 736 007 14 37 32 009 008 5
cert_ridgeSupport_suffix_decode_2 736 006 14 69 32 009 007 37
cert_ridgeSupport_suffix_decode_2 736 005 14 101 32 009 006 69
cert_ridgeSupport_suffix_decode_2 736 004 14 133 32 009 005 101
cert_ridgeSupport_suffix_decode_2 736 003 14 165 32 009 004 133
cert_ridgeSupport_suffix_decode_2 736 002 14 197 32 009 003 165
cert_ridgeSupport_suffix_decode_2 736 001 14 229 32 009 002 197
cert_ridgeSupport_suffix_decode_2 736 000 14 261 32 009 001 229
cert_ridgeSupport_eq_3 736
theorem ridgeTest_large_736 : ridgeTest 736 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport736_eq]
    simp only [ridgeSupport736_suffix_000, ridgeSupport736_suffix_001, ridgeSupport736_suffix_002, ridgeSupport736_suffix_003, ridgeSupport736_suffix_004, ridgeSupport736_suffix_005, ridgeSupport736_suffix_006, ridgeSupport736_suffix_007, ridgeSupport736_suffix_008, ridgeSupport736_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport736_000_mask, ridgeSupport736_001_mask, ridgeSupport736_002_mask, ridgeSupport736_003_mask, ridgeSupport736_004_mask, ridgeSupport736_005_mask, ridgeSupport736_006_mask, ridgeSupport736_007_mask, ridgeSupport736_008_mask]
    decide +kernel
  · rw [ridgeSupport736_eq]
    simp only [ridgeSupport736_suffix_000, ridgeSupport736_suffix_001, ridgeSupport736_suffix_002, ridgeSupport736_suffix_003, ridgeSupport736_suffix_004, ridgeSupport736_suffix_005, ridgeSupport736_suffix_006, ridgeSupport736_suffix_007, ridgeSupport736_suffix_008, ridgeSupport736_suffix_009, List.all_append, List.all_nil, ridgeSupport736_000_checked, ridgeSupport736_001_checked, ridgeSupport736_002_checked, ridgeSupport736_003_checked, ridgeSupport736_004_checked, ridgeSupport736_005_checked, ridgeSupport736_006_checked, ridgeSupport736_007_checked, ridgeSupport736_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
