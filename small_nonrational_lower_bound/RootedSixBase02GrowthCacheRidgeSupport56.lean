module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase02GrowthCacheRidgeSupport56Part000
public import RootedSixBase02GrowthCacheRidgeSupport56Part001
public import RootedSixBase02GrowthCacheRidgeSupport56Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 56 020 13
cert_ridgeSupport_suffix_decode_2 56 019 13 21 21 020 020 0
cert_ridgeSupport_suffix_decode_2 56 018 13 53 32 020 019 21
cert_ridgeSupport_suffix_decode_2 56 017 13 85 32 020 018 53
cert_ridgeSupport_suffix_decode_2 56 016 13 117 32 020 017 85
cert_ridgeSupport_suffix_decode_2 56 015 13 149 32 020 016 117
cert_ridgeSupport_suffix_decode_2 56 014 13 181 32 020 015 149
cert_ridgeSupport_suffix_decode_2 56 013 13 213 32 020 014 181
cert_ridgeSupport_suffix_decode_2 56 012 13 245 32 020 013 213
cert_ridgeSupport_suffix_decode_2 56 011 13 277 32 020 012 245
cert_ridgeSupport_suffix_decode_2 56 010 13 309 32 020 011 277
cert_ridgeSupport_suffix_decode_2 56 009 13 341 32 020 010 309
cert_ridgeSupport_suffix_decode_2 56 008 13 373 32 020 009 341
cert_ridgeSupport_suffix_decode_2 56 007 13 405 32 020 008 373
cert_ridgeSupport_suffix_decode_2 56 006 13 437 32 020 007 405
cert_ridgeSupport_suffix_decode_2 56 005 13 469 32 020 006 437
cert_ridgeSupport_suffix_decode_2 56 004 13 501 32 020 005 469
cert_ridgeSupport_suffix_decode_2 56 003 13 533 32 020 004 501
cert_ridgeSupport_suffix_decode_2 56 002 13 565 32 020 003 533
cert_ridgeSupport_suffix_decode_2 56 001 13 597 32 020 002 565
cert_ridgeSupport_suffix_decode_2 56 000 13 629 32 020 001 597
cert_ridgeSupport_eq 56
theorem ridgeTest_large_56 : ridgeTest 56 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport56_eq]
    simp only [ridgeSupport56_suffix_000, ridgeSupport56_suffix_001, ridgeSupport56_suffix_002, ridgeSupport56_suffix_003, ridgeSupport56_suffix_004, ridgeSupport56_suffix_005, ridgeSupport56_suffix_006, ridgeSupport56_suffix_007, ridgeSupport56_suffix_008, ridgeSupport56_suffix_009, ridgeSupport56_suffix_010, ridgeSupport56_suffix_011, ridgeSupport56_suffix_012, ridgeSupport56_suffix_013, ridgeSupport56_suffix_014, ridgeSupport56_suffix_015, ridgeSupport56_suffix_016, ridgeSupport56_suffix_017, ridgeSupport56_suffix_018, ridgeSupport56_suffix_019, ridgeSupport56_suffix_020, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport56_000_mask, ridgeSupport56_001_mask, ridgeSupport56_002_mask, ridgeSupport56_003_mask, ridgeSupport56_004_mask, ridgeSupport56_005_mask, ridgeSupport56_006_mask, ridgeSupport56_007_mask, ridgeSupport56_008_mask, ridgeSupport56_009_mask, ridgeSupport56_010_mask, ridgeSupport56_011_mask, ridgeSupport56_012_mask, ridgeSupport56_013_mask, ridgeSupport56_014_mask, ridgeSupport56_015_mask, ridgeSupport56_016_mask, ridgeSupport56_017_mask, ridgeSupport56_018_mask, ridgeSupport56_019_mask]
    decide +kernel
  · rw [ridgeSupport56_eq]
    simp only [ridgeSupport56_suffix_000, ridgeSupport56_suffix_001, ridgeSupport56_suffix_002, ridgeSupport56_suffix_003, ridgeSupport56_suffix_004, ridgeSupport56_suffix_005, ridgeSupport56_suffix_006, ridgeSupport56_suffix_007, ridgeSupport56_suffix_008, ridgeSupport56_suffix_009, ridgeSupport56_suffix_010, ridgeSupport56_suffix_011, ridgeSupport56_suffix_012, ridgeSupport56_suffix_013, ridgeSupport56_suffix_014, ridgeSupport56_suffix_015, ridgeSupport56_suffix_016, ridgeSupport56_suffix_017, ridgeSupport56_suffix_018, ridgeSupport56_suffix_019, ridgeSupport56_suffix_020, List.all_append, List.all_nil, ridgeSupport56_000_checked, ridgeSupport56_001_checked, ridgeSupport56_002_checked, ridgeSupport56_003_checked, ridgeSupport56_004_checked, ridgeSupport56_005_checked, ridgeSupport56_006_checked, ridgeSupport56_007_checked, ridgeSupport56_008_checked, ridgeSupport56_009_checked, ridgeSupport56_010_checked, ridgeSupport56_011_checked, ridgeSupport56_012_checked, ridgeSupport56_013_checked, ridgeSupport56_014_checked, ridgeSupport56_015_checked, ridgeSupport56_016_checked, ridgeSupport56_017_checked, ridgeSupport56_018_checked, ridgeSupport56_019_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
