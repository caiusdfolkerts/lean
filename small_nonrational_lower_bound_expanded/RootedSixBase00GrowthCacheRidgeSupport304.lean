module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport304Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 304 028 15
cert_ridgeSupport_suffix_decode_2 304 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 304 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 304 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 304 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 304 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 304 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 304 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 304 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 304 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 304 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 304 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 304 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 304 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 304 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 304 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 304 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 304 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 304 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 304 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 304 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 304 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 304 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 304 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 304 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 304 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 304 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 304 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 304 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 304
theorem ridgeTest_large_304 : ridgeTest 304 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport304_eq]
    simp only [ridgeSupport304_suffix_000, ridgeSupport304_suffix_001, ridgeSupport304_suffix_002, ridgeSupport304_suffix_003, ridgeSupport304_suffix_004, ridgeSupport304_suffix_005, ridgeSupport304_suffix_006, ridgeSupport304_suffix_007, ridgeSupport304_suffix_008, ridgeSupport304_suffix_009, ridgeSupport304_suffix_010, ridgeSupport304_suffix_011, ridgeSupport304_suffix_012, ridgeSupport304_suffix_013, ridgeSupport304_suffix_014, ridgeSupport304_suffix_015, ridgeSupport304_suffix_016, ridgeSupport304_suffix_017, ridgeSupport304_suffix_018, ridgeSupport304_suffix_019, ridgeSupport304_suffix_020, ridgeSupport304_suffix_021, ridgeSupport304_suffix_022, ridgeSupport304_suffix_023, ridgeSupport304_suffix_024, ridgeSupport304_suffix_025, ridgeSupport304_suffix_026, ridgeSupport304_suffix_027, ridgeSupport304_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport304_000_mask, ridgeSupport304_001_mask, ridgeSupport304_002_mask, ridgeSupport304_003_mask, ridgeSupport304_004_mask, ridgeSupport304_005_mask, ridgeSupport304_006_mask, ridgeSupport304_007_mask, ridgeSupport304_008_mask, ridgeSupport304_009_mask, ridgeSupport304_010_mask, ridgeSupport304_011_mask, ridgeSupport304_012_mask, ridgeSupport304_013_mask, ridgeSupport304_014_mask, ridgeSupport304_015_mask, ridgeSupport304_016_mask, ridgeSupport304_017_mask, ridgeSupport304_018_mask, ridgeSupport304_019_mask, ridgeSupport304_020_mask, ridgeSupport304_021_mask, ridgeSupport304_022_mask, ridgeSupport304_023_mask, ridgeSupport304_024_mask, ridgeSupport304_025_mask, ridgeSupport304_026_mask, ridgeSupport304_027_mask]
    decide +kernel
  · rw [ridgeSupport304_eq]
    simp only [ridgeSupport304_suffix_000, ridgeSupport304_suffix_001, ridgeSupport304_suffix_002, ridgeSupport304_suffix_003, ridgeSupport304_suffix_004, ridgeSupport304_suffix_005, ridgeSupport304_suffix_006, ridgeSupport304_suffix_007, ridgeSupport304_suffix_008, ridgeSupport304_suffix_009, ridgeSupport304_suffix_010, ridgeSupport304_suffix_011, ridgeSupport304_suffix_012, ridgeSupport304_suffix_013, ridgeSupport304_suffix_014, ridgeSupport304_suffix_015, ridgeSupport304_suffix_016, ridgeSupport304_suffix_017, ridgeSupport304_suffix_018, ridgeSupport304_suffix_019, ridgeSupport304_suffix_020, ridgeSupport304_suffix_021, ridgeSupport304_suffix_022, ridgeSupport304_suffix_023, ridgeSupport304_suffix_024, ridgeSupport304_suffix_025, ridgeSupport304_suffix_026, ridgeSupport304_suffix_027, ridgeSupport304_suffix_028, List.all_append, List.all_nil, ridgeSupport304_000_checked, ridgeSupport304_001_checked, ridgeSupport304_002_checked, ridgeSupport304_003_checked, ridgeSupport304_004_checked, ridgeSupport304_005_checked, ridgeSupport304_006_checked, ridgeSupport304_007_checked, ridgeSupport304_008_checked, ridgeSupport304_009_checked, ridgeSupport304_010_checked, ridgeSupport304_011_checked, ridgeSupport304_012_checked, ridgeSupport304_013_checked, ridgeSupport304_014_checked, ridgeSupport304_015_checked, ridgeSupport304_016_checked, ridgeSupport304_017_checked, ridgeSupport304_018_checked, ridgeSupport304_019_checked, ridgeSupport304_020_checked, ridgeSupport304_021_checked, ridgeSupport304_022_checked, ridgeSupport304_023_checked, ridgeSupport304_024_checked, ridgeSupport304_025_checked, ridgeSupport304_026_checked, ridgeSupport304_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
