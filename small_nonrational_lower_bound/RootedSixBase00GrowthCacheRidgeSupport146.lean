module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport146Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 146 028 15
cert_ridgeSupport_suffix_decode_2 146 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 146 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 146 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 146 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 146 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 146 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 146 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 146 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 146 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 146 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 146 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 146 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 146 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 146 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 146 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 146 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 146 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 146 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 146 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 146 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 146 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 146 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 146 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 146 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 146 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 146 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 146 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 146 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 146
theorem ridgeTest_large_146 : ridgeTest 146 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport146_eq]
    simp only [ridgeSupport146_suffix_000, ridgeSupport146_suffix_001, ridgeSupport146_suffix_002, ridgeSupport146_suffix_003, ridgeSupport146_suffix_004, ridgeSupport146_suffix_005, ridgeSupport146_suffix_006, ridgeSupport146_suffix_007, ridgeSupport146_suffix_008, ridgeSupport146_suffix_009, ridgeSupport146_suffix_010, ridgeSupport146_suffix_011, ridgeSupport146_suffix_012, ridgeSupport146_suffix_013, ridgeSupport146_suffix_014, ridgeSupport146_suffix_015, ridgeSupport146_suffix_016, ridgeSupport146_suffix_017, ridgeSupport146_suffix_018, ridgeSupport146_suffix_019, ridgeSupport146_suffix_020, ridgeSupport146_suffix_021, ridgeSupport146_suffix_022, ridgeSupport146_suffix_023, ridgeSupport146_suffix_024, ridgeSupport146_suffix_025, ridgeSupport146_suffix_026, ridgeSupport146_suffix_027, ridgeSupport146_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport146_000_mask, ridgeSupport146_001_mask, ridgeSupport146_002_mask, ridgeSupport146_003_mask, ridgeSupport146_004_mask, ridgeSupport146_005_mask, ridgeSupport146_006_mask, ridgeSupport146_007_mask, ridgeSupport146_008_mask, ridgeSupport146_009_mask, ridgeSupport146_010_mask, ridgeSupport146_011_mask, ridgeSupport146_012_mask, ridgeSupport146_013_mask, ridgeSupport146_014_mask, ridgeSupport146_015_mask, ridgeSupport146_016_mask, ridgeSupport146_017_mask, ridgeSupport146_018_mask, ridgeSupport146_019_mask, ridgeSupport146_020_mask, ridgeSupport146_021_mask, ridgeSupport146_022_mask, ridgeSupport146_023_mask, ridgeSupport146_024_mask, ridgeSupport146_025_mask, ridgeSupport146_026_mask, ridgeSupport146_027_mask]
    decide +kernel
  · rw [ridgeSupport146_eq]
    simp only [ridgeSupport146_suffix_000, ridgeSupport146_suffix_001, ridgeSupport146_suffix_002, ridgeSupport146_suffix_003, ridgeSupport146_suffix_004, ridgeSupport146_suffix_005, ridgeSupport146_suffix_006, ridgeSupport146_suffix_007, ridgeSupport146_suffix_008, ridgeSupport146_suffix_009, ridgeSupport146_suffix_010, ridgeSupport146_suffix_011, ridgeSupport146_suffix_012, ridgeSupport146_suffix_013, ridgeSupport146_suffix_014, ridgeSupport146_suffix_015, ridgeSupport146_suffix_016, ridgeSupport146_suffix_017, ridgeSupport146_suffix_018, ridgeSupport146_suffix_019, ridgeSupport146_suffix_020, ridgeSupport146_suffix_021, ridgeSupport146_suffix_022, ridgeSupport146_suffix_023, ridgeSupport146_suffix_024, ridgeSupport146_suffix_025, ridgeSupport146_suffix_026, ridgeSupport146_suffix_027, ridgeSupport146_suffix_028, List.all_append, List.all_nil, ridgeSupport146_000_checked, ridgeSupport146_001_checked, ridgeSupport146_002_checked, ridgeSupport146_003_checked, ridgeSupport146_004_checked, ridgeSupport146_005_checked, ridgeSupport146_006_checked, ridgeSupport146_007_checked, ridgeSupport146_008_checked, ridgeSupport146_009_checked, ridgeSupport146_010_checked, ridgeSupport146_011_checked, ridgeSupport146_012_checked, ridgeSupport146_013_checked, ridgeSupport146_014_checked, ridgeSupport146_015_checked, ridgeSupport146_016_checked, ridgeSupport146_017_checked, ridgeSupport146_018_checked, ridgeSupport146_019_checked, ridgeSupport146_020_checked, ridgeSupport146_021_checked, ridgeSupport146_022_checked, ridgeSupport146_023_checked, ridgeSupport146_024_checked, ridgeSupport146_025_checked, ridgeSupport146_026_checked, ridgeSupport146_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
