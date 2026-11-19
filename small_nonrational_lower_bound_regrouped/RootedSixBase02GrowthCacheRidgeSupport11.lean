module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase02GrowthCacheRidgeSupport11PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 11 020 13
cert_ridgeSupport_suffix_decode_2 11 019 13 21 21 020 020 0
cert_ridgeSupport_suffix_decode_2 11 018 13 53 32 020 019 21
cert_ridgeSupport_suffix_decode_2 11 017 13 85 32 020 018 53
cert_ridgeSupport_suffix_decode_2 11 016 13 117 32 020 017 85
cert_ridgeSupport_suffix_decode_2 11 015 13 149 32 020 016 117
cert_ridgeSupport_suffix_decode_2 11 014 13 181 32 020 015 149
cert_ridgeSupport_suffix_decode_2 11 013 13 213 32 020 014 181
cert_ridgeSupport_suffix_decode_2 11 012 13 245 32 020 013 213
cert_ridgeSupport_suffix_decode_2 11 011 13 277 32 020 012 245
cert_ridgeSupport_suffix_decode_2 11 010 13 309 32 020 011 277
cert_ridgeSupport_suffix_decode_2 11 009 13 341 32 020 010 309
cert_ridgeSupport_suffix_decode_2 11 008 13 373 32 020 009 341
cert_ridgeSupport_suffix_decode_2 11 007 13 405 32 020 008 373
cert_ridgeSupport_suffix_decode_2 11 006 13 437 32 020 007 405
cert_ridgeSupport_suffix_decode_2 11 005 13 469 32 020 006 437
cert_ridgeSupport_suffix_decode_2 11 004 13 501 32 020 005 469
cert_ridgeSupport_suffix_decode_2 11 003 13 533 32 020 004 501
cert_ridgeSupport_suffix_decode_2 11 002 13 565 32 020 003 533
cert_ridgeSupport_suffix_decode_2 11 001 13 597 32 020 002 565
cert_ridgeSupport_suffix_decode_2 11 000 13 629 32 020 001 597
cert_ridgeSupport_eq 11
theorem ridgeTest_large_11 : ridgeTest 11 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, ridgeSupport11_suffix_012, ridgeSupport11_suffix_013, ridgeSupport11_suffix_014, ridgeSupport11_suffix_015, ridgeSupport11_suffix_016, ridgeSupport11_suffix_017, ridgeSupport11_suffix_018, ridgeSupport11_suffix_019, ridgeSupport11_suffix_020, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport11_000_mask, ridgeSupport11_001_mask, ridgeSupport11_002_mask, ridgeSupport11_003_mask, ridgeSupport11_004_mask, ridgeSupport11_005_mask, ridgeSupport11_006_mask, ridgeSupport11_007_mask, ridgeSupport11_008_mask, ridgeSupport11_009_mask, ridgeSupport11_010_mask, ridgeSupport11_011_mask, ridgeSupport11_012_mask, ridgeSupport11_013_mask, ridgeSupport11_014_mask, ridgeSupport11_015_mask, ridgeSupport11_016_mask, ridgeSupport11_017_mask, ridgeSupport11_018_mask, ridgeSupport11_019_mask]
    decide +kernel
  · rw [ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, ridgeSupport11_suffix_012, ridgeSupport11_suffix_013, ridgeSupport11_suffix_014, ridgeSupport11_suffix_015, ridgeSupport11_suffix_016, ridgeSupport11_suffix_017, ridgeSupport11_suffix_018, ridgeSupport11_suffix_019, ridgeSupport11_suffix_020, List.all_append, List.all_nil, ridgeSupport11_000_checked, ridgeSupport11_001_checked, ridgeSupport11_002_checked, ridgeSupport11_003_checked, ridgeSupport11_004_checked, ridgeSupport11_005_checked, ridgeSupport11_006_checked, ridgeSupport11_007_checked, ridgeSupport11_008_checked, ridgeSupport11_009_checked, ridgeSupport11_010_checked, ridgeSupport11_011_checked, ridgeSupport11_012_checked, ridgeSupport11_013_checked, ridgeSupport11_014_checked, ridgeSupport11_015_checked, ridgeSupport11_016_checked, ridgeSupport11_017_checked, ridgeSupport11_018_checked, ridgeSupport11_019_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
