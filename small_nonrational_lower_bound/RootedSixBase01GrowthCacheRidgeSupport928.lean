module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase01GrowthCacheRidgeSupport928Part000
public import RootedSixBase01GrowthCacheRidgeSupport928Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 928 009 14
cert_ridgeSupport_suffix_decode_2 928 008 14 5 5 009 009 0
cert_ridgeSupport_suffix_decode_2 928 007 14 37 32 009 008 5
cert_ridgeSupport_suffix_decode_2 928 006 14 69 32 009 007 37
cert_ridgeSupport_suffix_decode_2 928 005 14 101 32 009 006 69
cert_ridgeSupport_suffix_decode_2 928 004 14 133 32 009 005 101
cert_ridgeSupport_suffix_decode_2 928 003 14 165 32 009 004 133
cert_ridgeSupport_suffix_decode_2 928 002 14 197 32 009 003 165
cert_ridgeSupport_suffix_decode_2 928 001 14 229 32 009 002 197
cert_ridgeSupport_suffix_decode_2 928 000 14 261 32 009 001 229
cert_ridgeSupport_eq_3 928
theorem ridgeTest_large_928 : ridgeTest 928 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport928_eq]
    simp only [ridgeSupport928_suffix_000, ridgeSupport928_suffix_001, ridgeSupport928_suffix_002, ridgeSupport928_suffix_003, ridgeSupport928_suffix_004, ridgeSupport928_suffix_005, ridgeSupport928_suffix_006, ridgeSupport928_suffix_007, ridgeSupport928_suffix_008, ridgeSupport928_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport928_000_mask, ridgeSupport928_001_mask, ridgeSupport928_002_mask, ridgeSupport928_003_mask, ridgeSupport928_004_mask, ridgeSupport928_005_mask, ridgeSupport928_006_mask, ridgeSupport928_007_mask, ridgeSupport928_008_mask]
    decide +kernel
  · rw [ridgeSupport928_eq]
    simp only [ridgeSupport928_suffix_000, ridgeSupport928_suffix_001, ridgeSupport928_suffix_002, ridgeSupport928_suffix_003, ridgeSupport928_suffix_004, ridgeSupport928_suffix_005, ridgeSupport928_suffix_006, ridgeSupport928_suffix_007, ridgeSupport928_suffix_008, ridgeSupport928_suffix_009, List.all_append, List.all_nil, ridgeSupport928_000_checked, ridgeSupport928_001_checked, ridgeSupport928_002_checked, ridgeSupport928_003_checked, ridgeSupport928_004_checked, ridgeSupport928_005_checked, ridgeSupport928_006_checked, ridgeSupport928_007_checked, ridgeSupport928_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
