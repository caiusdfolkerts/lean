module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase04GrowthCacheRidgeSupport448Part000
public import RootedSixBase04GrowthCacheRidgeSupport448Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 448 015 12
cert_ridgeSupport_suffix_decode_2 448 014 12 15 15 015 015 0
cert_ridgeSupport_suffix_decode_2 448 013 12 47 32 015 014 15
cert_ridgeSupport_suffix_decode_2 448 012 12 79 32 015 013 47
cert_ridgeSupport_suffix_decode_2 448 011 12 111 32 015 012 79
cert_ridgeSupport_suffix_decode_2 448 010 12 143 32 015 011 111
cert_ridgeSupport_suffix_decode_2 448 009 12 175 32 015 010 143
cert_ridgeSupport_suffix_decode_2 448 008 12 207 32 015 009 175
cert_ridgeSupport_suffix_decode_2 448 007 12 239 32 015 008 207
cert_ridgeSupport_suffix_decode_2 448 006 12 271 32 015 007 239
cert_ridgeSupport_suffix_decode_2 448 005 12 303 32 015 006 271
cert_ridgeSupport_suffix_decode_2 448 004 12 335 32 015 005 303
cert_ridgeSupport_suffix_decode_2 448 003 12 367 32 015 004 335
cert_ridgeSupport_suffix_decode_2 448 002 12 399 32 015 003 367
cert_ridgeSupport_suffix_decode_2 448 001 12 431 32 015 002 399
cert_ridgeSupport_suffix_decode_2 448 000 12 463 32 015 001 431
cert_ridgeSupport_eq 448
theorem ridgeTest_large_448 : ridgeTest 448 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport448_000_mask, ridgeSupport448_001_mask, ridgeSupport448_002_mask, ridgeSupport448_003_mask, ridgeSupport448_004_mask, ridgeSupport448_005_mask, ridgeSupport448_006_mask, ridgeSupport448_007_mask, ridgeSupport448_008_mask, ridgeSupport448_009_mask, ridgeSupport448_010_mask, ridgeSupport448_011_mask, ridgeSupport448_012_mask, ridgeSupport448_013_mask, ridgeSupport448_014_mask]
    decide +kernel
  · rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, List.all_append, List.all_nil, ridgeSupport448_000_checked, ridgeSupport448_001_checked, ridgeSupport448_002_checked, ridgeSupport448_003_checked, ridgeSupport448_004_checked, ridgeSupport448_005_checked, ridgeSupport448_006_checked, ridgeSupport448_007_checked, ridgeSupport448_008_checked, ridgeSupport448_009_checked, ridgeSupport448_010_checked, ridgeSupport448_011_checked, ridgeSupport448_012_checked, ridgeSupport448_013_checked, ridgeSupport448_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase04
