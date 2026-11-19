module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase01GrowthCacheRidgeSupport464Part000
public import RootedSixBase01GrowthCacheRidgeSupport464Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 464 009 14
cert_ridgeSupport_suffix_decode_2 464 008 14 5 5 009 009 0
cert_ridgeSupport_suffix_decode_2 464 007 14 37 32 009 008 5
cert_ridgeSupport_suffix_decode_2 464 006 14 69 32 009 007 37
cert_ridgeSupport_suffix_decode_2 464 005 14 101 32 009 006 69
cert_ridgeSupport_suffix_decode_2 464 004 14 133 32 009 005 101
cert_ridgeSupport_suffix_decode_2 464 003 14 165 32 009 004 133
cert_ridgeSupport_suffix_decode_2 464 002 14 197 32 009 003 165
cert_ridgeSupport_suffix_decode_2 464 001 14 229 32 009 002 197
cert_ridgeSupport_suffix_decode_2 464 000 14 261 32 009 001 229
cert_ridgeSupport_eq_3 464
theorem ridgeTest_large_464 : ridgeTest 464 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport464_eq]
    simp only [ridgeSupport464_suffix_000, ridgeSupport464_suffix_001, ridgeSupport464_suffix_002, ridgeSupport464_suffix_003, ridgeSupport464_suffix_004, ridgeSupport464_suffix_005, ridgeSupport464_suffix_006, ridgeSupport464_suffix_007, ridgeSupport464_suffix_008, ridgeSupport464_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport464_000_mask, ridgeSupport464_001_mask, ridgeSupport464_002_mask, ridgeSupport464_003_mask, ridgeSupport464_004_mask, ridgeSupport464_005_mask, ridgeSupport464_006_mask, ridgeSupport464_007_mask, ridgeSupport464_008_mask]
    decide +kernel
  · rw [ridgeSupport464_eq]
    simp only [ridgeSupport464_suffix_000, ridgeSupport464_suffix_001, ridgeSupport464_suffix_002, ridgeSupport464_suffix_003, ridgeSupport464_suffix_004, ridgeSupport464_suffix_005, ridgeSupport464_suffix_006, ridgeSupport464_suffix_007, ridgeSupport464_suffix_008, ridgeSupport464_suffix_009, List.all_append, List.all_nil, ridgeSupport464_000_checked, ridgeSupport464_001_checked, ridgeSupport464_002_checked, ridgeSupport464_003_checked, ridgeSupport464_004_checked, ridgeSupport464_005_checked, ridgeSupport464_006_checked, ridgeSupport464_007_checked, ridgeSupport464_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
