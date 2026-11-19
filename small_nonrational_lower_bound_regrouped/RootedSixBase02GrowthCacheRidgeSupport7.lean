module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase02GrowthCacheRidgeSupport7PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 7 020 13
cert_ridgeSupport_suffix_decode_2 7 019 13 21 21 020 020 0
cert_ridgeSupport_suffix_decode_2 7 018 13 53 32 020 019 21
cert_ridgeSupport_suffix_decode_2 7 017 13 85 32 020 018 53
cert_ridgeSupport_suffix_decode_2 7 016 13 117 32 020 017 85
cert_ridgeSupport_suffix_decode_2 7 015 13 149 32 020 016 117
cert_ridgeSupport_suffix_decode_2 7 014 13 181 32 020 015 149
cert_ridgeSupport_suffix_decode_2 7 013 13 213 32 020 014 181
cert_ridgeSupport_suffix_decode_2 7 012 13 245 32 020 013 213
cert_ridgeSupport_suffix_decode_2 7 011 13 277 32 020 012 245
cert_ridgeSupport_suffix_decode_2 7 010 13 309 32 020 011 277
cert_ridgeSupport_suffix_decode_2 7 009 13 341 32 020 010 309
cert_ridgeSupport_suffix_decode_2 7 008 13 373 32 020 009 341
cert_ridgeSupport_suffix_decode_2 7 007 13 405 32 020 008 373
cert_ridgeSupport_suffix_decode_2 7 006 13 437 32 020 007 405
cert_ridgeSupport_suffix_decode_2 7 005 13 469 32 020 006 437
cert_ridgeSupport_suffix_decode_2 7 004 13 501 32 020 005 469
cert_ridgeSupport_suffix_decode_2 7 003 13 533 32 020 004 501
cert_ridgeSupport_suffix_decode_2 7 002 13 565 32 020 003 533
cert_ridgeSupport_suffix_decode_2 7 001 13 597 32 020 002 565
cert_ridgeSupport_suffix_decode_2 7 000 13 629 32 020 001 597
cert_ridgeSupport_eq 7
theorem ridgeTest_large_7 : ridgeTest 7 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport7_eq]
    simp only [ridgeSupport7_suffix_000, ridgeSupport7_suffix_001, ridgeSupport7_suffix_002, ridgeSupport7_suffix_003, ridgeSupport7_suffix_004, ridgeSupport7_suffix_005, ridgeSupport7_suffix_006, ridgeSupport7_suffix_007, ridgeSupport7_suffix_008, ridgeSupport7_suffix_009, ridgeSupport7_suffix_010, ridgeSupport7_suffix_011, ridgeSupport7_suffix_012, ridgeSupport7_suffix_013, ridgeSupport7_suffix_014, ridgeSupport7_suffix_015, ridgeSupport7_suffix_016, ridgeSupport7_suffix_017, ridgeSupport7_suffix_018, ridgeSupport7_suffix_019, ridgeSupport7_suffix_020, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport7_000_mask, ridgeSupport7_001_mask, ridgeSupport7_002_mask, ridgeSupport7_003_mask, ridgeSupport7_004_mask, ridgeSupport7_005_mask, ridgeSupport7_006_mask, ridgeSupport7_007_mask, ridgeSupport7_008_mask, ridgeSupport7_009_mask, ridgeSupport7_010_mask, ridgeSupport7_011_mask, ridgeSupport7_012_mask, ridgeSupport7_013_mask, ridgeSupport7_014_mask, ridgeSupport7_015_mask, ridgeSupport7_016_mask, ridgeSupport7_017_mask, ridgeSupport7_018_mask, ridgeSupport7_019_mask]
    decide +kernel
  · rw [ridgeSupport7_eq]
    simp only [ridgeSupport7_suffix_000, ridgeSupport7_suffix_001, ridgeSupport7_suffix_002, ridgeSupport7_suffix_003, ridgeSupport7_suffix_004, ridgeSupport7_suffix_005, ridgeSupport7_suffix_006, ridgeSupport7_suffix_007, ridgeSupport7_suffix_008, ridgeSupport7_suffix_009, ridgeSupport7_suffix_010, ridgeSupport7_suffix_011, ridgeSupport7_suffix_012, ridgeSupport7_suffix_013, ridgeSupport7_suffix_014, ridgeSupport7_suffix_015, ridgeSupport7_suffix_016, ridgeSupport7_suffix_017, ridgeSupport7_suffix_018, ridgeSupport7_suffix_019, ridgeSupport7_suffix_020, List.all_append, List.all_nil, ridgeSupport7_000_checked, ridgeSupport7_001_checked, ridgeSupport7_002_checked, ridgeSupport7_003_checked, ridgeSupport7_004_checked, ridgeSupport7_005_checked, ridgeSupport7_006_checked, ridgeSupport7_007_checked, ridgeSupport7_008_checked, ridgeSupport7_009_checked, ridgeSupport7_010_checked, ridgeSupport7_011_checked, ridgeSupport7_012_checked, ridgeSupport7_013_checked, ridgeSupport7_014_checked, ridgeSupport7_015_checked, ridgeSupport7_016_checked, ridgeSupport7_017_checked, ridgeSupport7_018_checked, ridgeSupport7_019_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
