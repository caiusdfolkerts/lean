module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport480PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 480 009 14
cert_ridgeSupport_suffix_decode_2 480 008 14 5 5 009 009 0
cert_ridgeSupport_suffix_decode_2 480 007 14 37 32 009 008 5
cert_ridgeSupport_suffix_decode_2 480 006 14 69 32 009 007 37
cert_ridgeSupport_suffix_decode_2 480 005 14 101 32 009 006 69
cert_ridgeSupport_suffix_decode_2 480 004 14 133 32 009 005 101
cert_ridgeSupport_suffix_decode_2 480 003 14 165 32 009 004 133
cert_ridgeSupport_suffix_decode_2 480 002 14 197 32 009 003 165
cert_ridgeSupport_suffix_decode_2 480 001 14 229 32 009 002 197
cert_ridgeSupport_suffix_decode_2 480 000 14 261 32 009 001 229
cert_ridgeSupport_eq_3 480
theorem ridgeTest_large_480 : ridgeTest 480 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport480_eq]
    simp only [ridgeSupport480_suffix_000, ridgeSupport480_suffix_001, ridgeSupport480_suffix_002, ridgeSupport480_suffix_003, ridgeSupport480_suffix_004, ridgeSupport480_suffix_005, ridgeSupport480_suffix_006, ridgeSupport480_suffix_007, ridgeSupport480_suffix_008, ridgeSupport480_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport480_000_mask, ridgeSupport480_001_mask, ridgeSupport480_002_mask, ridgeSupport480_003_mask, ridgeSupport480_004_mask, ridgeSupport480_005_mask, ridgeSupport480_006_mask, ridgeSupport480_007_mask, ridgeSupport480_008_mask]
    decide +kernel
  · rw [ridgeSupport480_eq]
    simp only [ridgeSupport480_suffix_000, ridgeSupport480_suffix_001, ridgeSupport480_suffix_002, ridgeSupport480_suffix_003, ridgeSupport480_suffix_004, ridgeSupport480_suffix_005, ridgeSupport480_suffix_006, ridgeSupport480_suffix_007, ridgeSupport480_suffix_008, ridgeSupport480_suffix_009, List.all_append, List.all_nil, ridgeSupport480_000_checked, ridgeSupport480_001_checked, ridgeSupport480_002_checked, ridgeSupport480_003_checked, ridgeSupport480_004_checked, ridgeSupport480_005_checked, ridgeSupport480_006_checked, ridgeSupport480_007_checked, ridgeSupport480_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
