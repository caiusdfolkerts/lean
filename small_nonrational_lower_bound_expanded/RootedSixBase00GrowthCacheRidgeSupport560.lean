module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport560Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 560 028 15
cert_ridgeSupport_suffix_decode_2 560 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 560 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 560 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 560 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 560 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 560 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 560 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 560 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 560 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 560 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 560 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 560 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 560 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 560 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 560 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 560 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 560 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 560 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 560 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 560 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 560 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 560 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 560 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 560 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 560 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 560 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 560 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 560 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 560
theorem ridgeTest_large_560 : ridgeTest 560 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport560_eq]
    simp only [ridgeSupport560_suffix_000, ridgeSupport560_suffix_001, ridgeSupport560_suffix_002, ridgeSupport560_suffix_003, ridgeSupport560_suffix_004, ridgeSupport560_suffix_005, ridgeSupport560_suffix_006, ridgeSupport560_suffix_007, ridgeSupport560_suffix_008, ridgeSupport560_suffix_009, ridgeSupport560_suffix_010, ridgeSupport560_suffix_011, ridgeSupport560_suffix_012, ridgeSupport560_suffix_013, ridgeSupport560_suffix_014, ridgeSupport560_suffix_015, ridgeSupport560_suffix_016, ridgeSupport560_suffix_017, ridgeSupport560_suffix_018, ridgeSupport560_suffix_019, ridgeSupport560_suffix_020, ridgeSupport560_suffix_021, ridgeSupport560_suffix_022, ridgeSupport560_suffix_023, ridgeSupport560_suffix_024, ridgeSupport560_suffix_025, ridgeSupport560_suffix_026, ridgeSupport560_suffix_027, ridgeSupport560_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport560_000_mask, ridgeSupport560_001_mask, ridgeSupport560_002_mask, ridgeSupport560_003_mask, ridgeSupport560_004_mask, ridgeSupport560_005_mask, ridgeSupport560_006_mask, ridgeSupport560_007_mask, ridgeSupport560_008_mask, ridgeSupport560_009_mask, ridgeSupport560_010_mask, ridgeSupport560_011_mask, ridgeSupport560_012_mask, ridgeSupport560_013_mask, ridgeSupport560_014_mask, ridgeSupport560_015_mask, ridgeSupport560_016_mask, ridgeSupport560_017_mask, ridgeSupport560_018_mask, ridgeSupport560_019_mask, ridgeSupport560_020_mask, ridgeSupport560_021_mask, ridgeSupport560_022_mask, ridgeSupport560_023_mask, ridgeSupport560_024_mask, ridgeSupport560_025_mask, ridgeSupport560_026_mask, ridgeSupport560_027_mask]
    decide +kernel
  · rw [ridgeSupport560_eq]
    simp only [ridgeSupport560_suffix_000, ridgeSupport560_suffix_001, ridgeSupport560_suffix_002, ridgeSupport560_suffix_003, ridgeSupport560_suffix_004, ridgeSupport560_suffix_005, ridgeSupport560_suffix_006, ridgeSupport560_suffix_007, ridgeSupport560_suffix_008, ridgeSupport560_suffix_009, ridgeSupport560_suffix_010, ridgeSupport560_suffix_011, ridgeSupport560_suffix_012, ridgeSupport560_suffix_013, ridgeSupport560_suffix_014, ridgeSupport560_suffix_015, ridgeSupport560_suffix_016, ridgeSupport560_suffix_017, ridgeSupport560_suffix_018, ridgeSupport560_suffix_019, ridgeSupport560_suffix_020, ridgeSupport560_suffix_021, ridgeSupport560_suffix_022, ridgeSupport560_suffix_023, ridgeSupport560_suffix_024, ridgeSupport560_suffix_025, ridgeSupport560_suffix_026, ridgeSupport560_suffix_027, ridgeSupport560_suffix_028, List.all_append, List.all_nil, ridgeSupport560_000_checked, ridgeSupport560_001_checked, ridgeSupport560_002_checked, ridgeSupport560_003_checked, ridgeSupport560_004_checked, ridgeSupport560_005_checked, ridgeSupport560_006_checked, ridgeSupport560_007_checked, ridgeSupport560_008_checked, ridgeSupport560_009_checked, ridgeSupport560_010_checked, ridgeSupport560_011_checked, ridgeSupport560_012_checked, ridgeSupport560_013_checked, ridgeSupport560_014_checked, ridgeSupport560_015_checked, ridgeSupport560_016_checked, ridgeSupport560_017_checked, ridgeSupport560_018_checked, ridgeSupport560_019_checked, ridgeSupport560_020_checked, ridgeSupport560_021_checked, ridgeSupport560_022_checked, ridgeSupport560_023_checked, ridgeSupport560_024_checked, ridgeSupport560_025_checked, ridgeSupport560_026_checked, ridgeSupport560_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
