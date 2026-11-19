module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport521Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 521 028 15
cert_ridgeSupport_suffix_decode_2 521 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 521 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 521 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 521 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 521 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 521 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 521 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 521 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 521 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 521 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 521 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 521 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 521 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 521 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 521 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 521 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 521 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 521 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 521 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 521 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 521 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 521 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 521 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 521 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 521 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 521 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 521 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 521 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 521
theorem ridgeTest_large_521 : ridgeTest 521 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport521_eq]
    simp only [ridgeSupport521_suffix_000, ridgeSupport521_suffix_001, ridgeSupport521_suffix_002, ridgeSupport521_suffix_003, ridgeSupport521_suffix_004, ridgeSupport521_suffix_005, ridgeSupport521_suffix_006, ridgeSupport521_suffix_007, ridgeSupport521_suffix_008, ridgeSupport521_suffix_009, ridgeSupport521_suffix_010, ridgeSupport521_suffix_011, ridgeSupport521_suffix_012, ridgeSupport521_suffix_013, ridgeSupport521_suffix_014, ridgeSupport521_suffix_015, ridgeSupport521_suffix_016, ridgeSupport521_suffix_017, ridgeSupport521_suffix_018, ridgeSupport521_suffix_019, ridgeSupport521_suffix_020, ridgeSupport521_suffix_021, ridgeSupport521_suffix_022, ridgeSupport521_suffix_023, ridgeSupport521_suffix_024, ridgeSupport521_suffix_025, ridgeSupport521_suffix_026, ridgeSupport521_suffix_027, ridgeSupport521_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport521_000_mask, ridgeSupport521_001_mask, ridgeSupport521_002_mask, ridgeSupport521_003_mask, ridgeSupport521_004_mask, ridgeSupport521_005_mask, ridgeSupport521_006_mask, ridgeSupport521_007_mask, ridgeSupport521_008_mask, ridgeSupport521_009_mask, ridgeSupport521_010_mask, ridgeSupport521_011_mask, ridgeSupport521_012_mask, ridgeSupport521_013_mask, ridgeSupport521_014_mask, ridgeSupport521_015_mask, ridgeSupport521_016_mask, ridgeSupport521_017_mask, ridgeSupport521_018_mask, ridgeSupport521_019_mask, ridgeSupport521_020_mask, ridgeSupport521_021_mask, ridgeSupport521_022_mask, ridgeSupport521_023_mask, ridgeSupport521_024_mask, ridgeSupport521_025_mask, ridgeSupport521_026_mask, ridgeSupport521_027_mask]
    decide +kernel
  · rw [ridgeSupport521_eq]
    simp only [ridgeSupport521_suffix_000, ridgeSupport521_suffix_001, ridgeSupport521_suffix_002, ridgeSupport521_suffix_003, ridgeSupport521_suffix_004, ridgeSupport521_suffix_005, ridgeSupport521_suffix_006, ridgeSupport521_suffix_007, ridgeSupport521_suffix_008, ridgeSupport521_suffix_009, ridgeSupport521_suffix_010, ridgeSupport521_suffix_011, ridgeSupport521_suffix_012, ridgeSupport521_suffix_013, ridgeSupport521_suffix_014, ridgeSupport521_suffix_015, ridgeSupport521_suffix_016, ridgeSupport521_suffix_017, ridgeSupport521_suffix_018, ridgeSupport521_suffix_019, ridgeSupport521_suffix_020, ridgeSupport521_suffix_021, ridgeSupport521_suffix_022, ridgeSupport521_suffix_023, ridgeSupport521_suffix_024, ridgeSupport521_suffix_025, ridgeSupport521_suffix_026, ridgeSupport521_suffix_027, ridgeSupport521_suffix_028, List.all_append, List.all_nil, ridgeSupport521_000_checked, ridgeSupport521_001_checked, ridgeSupport521_002_checked, ridgeSupport521_003_checked, ridgeSupport521_004_checked, ridgeSupport521_005_checked, ridgeSupport521_006_checked, ridgeSupport521_007_checked, ridgeSupport521_008_checked, ridgeSupport521_009_checked, ridgeSupport521_010_checked, ridgeSupport521_011_checked, ridgeSupport521_012_checked, ridgeSupport521_013_checked, ridgeSupport521_014_checked, ridgeSupport521_015_checked, ridgeSupport521_016_checked, ridgeSupport521_017_checked, ridgeSupport521_018_checked, ridgeSupport521_019_checked, ridgeSupport521_020_checked, ridgeSupport521_021_checked, ridgeSupport521_022_checked, ridgeSupport521_023_checked, ridgeSupport521_024_checked, ridgeSupport521_025_checked, ridgeSupport521_026_checked, ridgeSupport521_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
