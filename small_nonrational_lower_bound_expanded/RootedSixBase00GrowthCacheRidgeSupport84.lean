module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport84Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 84 028 15
cert_ridgeSupport_suffix_decode_2 84 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 84 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 84 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 84 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 84 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 84 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 84 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 84 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 84 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 84 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 84 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 84 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 84 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 84 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 84 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 84 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 84 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 84 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 84 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 84 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 84 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 84 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 84 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 84 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 84 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 84 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 84 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 84 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 84
theorem ridgeTest_large_84 : ridgeTest 84 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport84_eq]
    simp only [ridgeSupport84_suffix_000, ridgeSupport84_suffix_001, ridgeSupport84_suffix_002, ridgeSupport84_suffix_003, ridgeSupport84_suffix_004, ridgeSupport84_suffix_005, ridgeSupport84_suffix_006, ridgeSupport84_suffix_007, ridgeSupport84_suffix_008, ridgeSupport84_suffix_009, ridgeSupport84_suffix_010, ridgeSupport84_suffix_011, ridgeSupport84_suffix_012, ridgeSupport84_suffix_013, ridgeSupport84_suffix_014, ridgeSupport84_suffix_015, ridgeSupport84_suffix_016, ridgeSupport84_suffix_017, ridgeSupport84_suffix_018, ridgeSupport84_suffix_019, ridgeSupport84_suffix_020, ridgeSupport84_suffix_021, ridgeSupport84_suffix_022, ridgeSupport84_suffix_023, ridgeSupport84_suffix_024, ridgeSupport84_suffix_025, ridgeSupport84_suffix_026, ridgeSupport84_suffix_027, ridgeSupport84_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport84_000_mask, ridgeSupport84_001_mask, ridgeSupport84_002_mask, ridgeSupport84_003_mask, ridgeSupport84_004_mask, ridgeSupport84_005_mask, ridgeSupport84_006_mask, ridgeSupport84_007_mask, ridgeSupport84_008_mask, ridgeSupport84_009_mask, ridgeSupport84_010_mask, ridgeSupport84_011_mask, ridgeSupport84_012_mask, ridgeSupport84_013_mask, ridgeSupport84_014_mask, ridgeSupport84_015_mask, ridgeSupport84_016_mask, ridgeSupport84_017_mask, ridgeSupport84_018_mask, ridgeSupport84_019_mask, ridgeSupport84_020_mask, ridgeSupport84_021_mask, ridgeSupport84_022_mask, ridgeSupport84_023_mask, ridgeSupport84_024_mask, ridgeSupport84_025_mask, ridgeSupport84_026_mask, ridgeSupport84_027_mask]
    decide +kernel
  · rw [ridgeSupport84_eq]
    simp only [ridgeSupport84_suffix_000, ridgeSupport84_suffix_001, ridgeSupport84_suffix_002, ridgeSupport84_suffix_003, ridgeSupport84_suffix_004, ridgeSupport84_suffix_005, ridgeSupport84_suffix_006, ridgeSupport84_suffix_007, ridgeSupport84_suffix_008, ridgeSupport84_suffix_009, ridgeSupport84_suffix_010, ridgeSupport84_suffix_011, ridgeSupport84_suffix_012, ridgeSupport84_suffix_013, ridgeSupport84_suffix_014, ridgeSupport84_suffix_015, ridgeSupport84_suffix_016, ridgeSupport84_suffix_017, ridgeSupport84_suffix_018, ridgeSupport84_suffix_019, ridgeSupport84_suffix_020, ridgeSupport84_suffix_021, ridgeSupport84_suffix_022, ridgeSupport84_suffix_023, ridgeSupport84_suffix_024, ridgeSupport84_suffix_025, ridgeSupport84_suffix_026, ridgeSupport84_suffix_027, ridgeSupport84_suffix_028, List.all_append, List.all_nil, ridgeSupport84_000_checked, ridgeSupport84_001_checked, ridgeSupport84_002_checked, ridgeSupport84_003_checked, ridgeSupport84_004_checked, ridgeSupport84_005_checked, ridgeSupport84_006_checked, ridgeSupport84_007_checked, ridgeSupport84_008_checked, ridgeSupport84_009_checked, ridgeSupport84_010_checked, ridgeSupport84_011_checked, ridgeSupport84_012_checked, ridgeSupport84_013_checked, ridgeSupport84_014_checked, ridgeSupport84_015_checked, ridgeSupport84_016_checked, ridgeSupport84_017_checked, ridgeSupport84_018_checked, ridgeSupport84_019_checked, ridgeSupport84_020_checked, ridgeSupport84_021_checked, ridgeSupport84_022_checked, ridgeSupport84_023_checked, ridgeSupport84_024_checked, ridgeSupport84_025_checked, ridgeSupport84_026_checked, ridgeSupport84_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
