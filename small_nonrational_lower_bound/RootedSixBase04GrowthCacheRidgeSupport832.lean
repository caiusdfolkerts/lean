module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase04GrowthCacheRidgeSupport832Part000
public import RootedSixBase04GrowthCacheRidgeSupport832Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 832 015 12
cert_ridgeSupport_suffix_decode_2 832 014 12 15 15 015 015 0
cert_ridgeSupport_suffix_decode_2 832 013 12 47 32 015 014 15
cert_ridgeSupport_suffix_decode_2 832 012 12 79 32 015 013 47
cert_ridgeSupport_suffix_decode_2 832 011 12 111 32 015 012 79
cert_ridgeSupport_suffix_decode_2 832 010 12 143 32 015 011 111
cert_ridgeSupport_suffix_decode_2 832 009 12 175 32 015 010 143
cert_ridgeSupport_suffix_decode_2 832 008 12 207 32 015 009 175
cert_ridgeSupport_suffix_decode_2 832 007 12 239 32 015 008 207
cert_ridgeSupport_suffix_decode_2 832 006 12 271 32 015 007 239
cert_ridgeSupport_suffix_decode_2 832 005 12 303 32 015 006 271
cert_ridgeSupport_suffix_decode_2 832 004 12 335 32 015 005 303
cert_ridgeSupport_suffix_decode_2 832 003 12 367 32 015 004 335
cert_ridgeSupport_suffix_decode_2 832 002 12 399 32 015 003 367
cert_ridgeSupport_suffix_decode_2 832 001 12 431 32 015 002 399
cert_ridgeSupport_suffix_decode_2 832 000 12 463 32 015 001 431
cert_ridgeSupport_eq 832
theorem ridgeTest_large_832 : ridgeTest 832 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, ridgeSupport832_suffix_015, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport832_000_mask, ridgeSupport832_001_mask, ridgeSupport832_002_mask, ridgeSupport832_003_mask, ridgeSupport832_004_mask, ridgeSupport832_005_mask, ridgeSupport832_006_mask, ridgeSupport832_007_mask, ridgeSupport832_008_mask, ridgeSupport832_009_mask, ridgeSupport832_010_mask, ridgeSupport832_011_mask, ridgeSupport832_012_mask, ridgeSupport832_013_mask, ridgeSupport832_014_mask]
    decide +kernel
  · rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, ridgeSupport832_suffix_015, List.all_append, List.all_nil, ridgeSupport832_000_checked, ridgeSupport832_001_checked, ridgeSupport832_002_checked, ridgeSupport832_003_checked, ridgeSupport832_004_checked, ridgeSupport832_005_checked, ridgeSupport832_006_checked, ridgeSupport832_007_checked, ridgeSupport832_008_checked, ridgeSupport832_009_checked, ridgeSupport832_010_checked, ridgeSupport832_011_checked, ridgeSupport832_012_checked, ridgeSupport832_013_checked, ridgeSupport832_014_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase04
