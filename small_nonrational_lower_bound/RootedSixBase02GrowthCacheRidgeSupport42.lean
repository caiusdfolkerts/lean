module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase02GrowthCacheRidgeSupport42Part000
public import RootedSixBase02GrowthCacheRidgeSupport42Part001
public import RootedSixBase02GrowthCacheRidgeSupport42Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 42 020 13
cert_ridgeSupport_suffix_decode_2 42 019 13 21 21 020 020 0
cert_ridgeSupport_suffix_decode_2 42 018 13 53 32 020 019 21
cert_ridgeSupport_suffix_decode_2 42 017 13 85 32 020 018 53
cert_ridgeSupport_suffix_decode_2 42 016 13 117 32 020 017 85
cert_ridgeSupport_suffix_decode_2 42 015 13 149 32 020 016 117
cert_ridgeSupport_suffix_decode_2 42 014 13 181 32 020 015 149
cert_ridgeSupport_suffix_decode_2 42 013 13 213 32 020 014 181
cert_ridgeSupport_suffix_decode_2 42 012 13 245 32 020 013 213
cert_ridgeSupport_suffix_decode_2 42 011 13 277 32 020 012 245
cert_ridgeSupport_suffix_decode_2 42 010 13 309 32 020 011 277
cert_ridgeSupport_suffix_decode_2 42 009 13 341 32 020 010 309
cert_ridgeSupport_suffix_decode_2 42 008 13 373 32 020 009 341
cert_ridgeSupport_suffix_decode_2 42 007 13 405 32 020 008 373
cert_ridgeSupport_suffix_decode_2 42 006 13 437 32 020 007 405
cert_ridgeSupport_suffix_decode_2 42 005 13 469 32 020 006 437
cert_ridgeSupport_suffix_decode_2 42 004 13 501 32 020 005 469
cert_ridgeSupport_suffix_decode_2 42 003 13 533 32 020 004 501
cert_ridgeSupport_suffix_decode_2 42 002 13 565 32 020 003 533
cert_ridgeSupport_suffix_decode_2 42 001 13 597 32 020 002 565
cert_ridgeSupport_suffix_decode_2 42 000 13 629 32 020 001 597
cert_ridgeSupport_eq 42
theorem ridgeTest_large_42 : ridgeTest 42 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport42_eq]
    simp only [ridgeSupport42_suffix_000, ridgeSupport42_suffix_001, ridgeSupport42_suffix_002, ridgeSupport42_suffix_003, ridgeSupport42_suffix_004, ridgeSupport42_suffix_005, ridgeSupport42_suffix_006, ridgeSupport42_suffix_007, ridgeSupport42_suffix_008, ridgeSupport42_suffix_009, ridgeSupport42_suffix_010, ridgeSupport42_suffix_011, ridgeSupport42_suffix_012, ridgeSupport42_suffix_013, ridgeSupport42_suffix_014, ridgeSupport42_suffix_015, ridgeSupport42_suffix_016, ridgeSupport42_suffix_017, ridgeSupport42_suffix_018, ridgeSupport42_suffix_019, ridgeSupport42_suffix_020, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport42_000_mask, ridgeSupport42_001_mask, ridgeSupport42_002_mask, ridgeSupport42_003_mask, ridgeSupport42_004_mask, ridgeSupport42_005_mask, ridgeSupport42_006_mask, ridgeSupport42_007_mask, ridgeSupport42_008_mask, ridgeSupport42_009_mask, ridgeSupport42_010_mask, ridgeSupport42_011_mask, ridgeSupport42_012_mask, ridgeSupport42_013_mask, ridgeSupport42_014_mask, ridgeSupport42_015_mask, ridgeSupport42_016_mask, ridgeSupport42_017_mask, ridgeSupport42_018_mask, ridgeSupport42_019_mask]
    decide +kernel
  · rw [ridgeSupport42_eq]
    simp only [ridgeSupport42_suffix_000, ridgeSupport42_suffix_001, ridgeSupport42_suffix_002, ridgeSupport42_suffix_003, ridgeSupport42_suffix_004, ridgeSupport42_suffix_005, ridgeSupport42_suffix_006, ridgeSupport42_suffix_007, ridgeSupport42_suffix_008, ridgeSupport42_suffix_009, ridgeSupport42_suffix_010, ridgeSupport42_suffix_011, ridgeSupport42_suffix_012, ridgeSupport42_suffix_013, ridgeSupport42_suffix_014, ridgeSupport42_suffix_015, ridgeSupport42_suffix_016, ridgeSupport42_suffix_017, ridgeSupport42_suffix_018, ridgeSupport42_suffix_019, ridgeSupport42_suffix_020, List.all_append, List.all_nil, ridgeSupport42_000_checked, ridgeSupport42_001_checked, ridgeSupport42_002_checked, ridgeSupport42_003_checked, ridgeSupport42_004_checked, ridgeSupport42_005_checked, ridgeSupport42_006_checked, ridgeSupport42_007_checked, ridgeSupport42_008_checked, ridgeSupport42_009_checked, ridgeSupport42_010_checked, ridgeSupport42_011_checked, ridgeSupport42_012_checked, ridgeSupport42_013_checked, ridgeSupport42_014_checked, ridgeSupport42_015_checked, ridgeSupport42_016_checked, ridgeSupport42_017_checked, ridgeSupport42_018_checked, ridgeSupport42_019_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
