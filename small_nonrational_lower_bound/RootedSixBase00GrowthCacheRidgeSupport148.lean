module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport148Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 148 028 15
cert_ridgeSupport_suffix_decode_2 148 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 148 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 148 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 148 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 148 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 148 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 148 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 148 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 148 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 148 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 148 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 148 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 148 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 148 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 148 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 148 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 148 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 148 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 148 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 148 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 148 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 148 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 148 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 148 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 148 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 148 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 148 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 148 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 148
theorem ridgeTest_large_148 : ridgeTest 148 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport148_eq]
    simp only [ridgeSupport148_suffix_000, ridgeSupport148_suffix_001, ridgeSupport148_suffix_002, ridgeSupport148_suffix_003, ridgeSupport148_suffix_004, ridgeSupport148_suffix_005, ridgeSupport148_suffix_006, ridgeSupport148_suffix_007, ridgeSupport148_suffix_008, ridgeSupport148_suffix_009, ridgeSupport148_suffix_010, ridgeSupport148_suffix_011, ridgeSupport148_suffix_012, ridgeSupport148_suffix_013, ridgeSupport148_suffix_014, ridgeSupport148_suffix_015, ridgeSupport148_suffix_016, ridgeSupport148_suffix_017, ridgeSupport148_suffix_018, ridgeSupport148_suffix_019, ridgeSupport148_suffix_020, ridgeSupport148_suffix_021, ridgeSupport148_suffix_022, ridgeSupport148_suffix_023, ridgeSupport148_suffix_024, ridgeSupport148_suffix_025, ridgeSupport148_suffix_026, ridgeSupport148_suffix_027, ridgeSupport148_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport148_000_mask, ridgeSupport148_001_mask, ridgeSupport148_002_mask, ridgeSupport148_003_mask, ridgeSupport148_004_mask, ridgeSupport148_005_mask, ridgeSupport148_006_mask, ridgeSupport148_007_mask, ridgeSupport148_008_mask, ridgeSupport148_009_mask, ridgeSupport148_010_mask, ridgeSupport148_011_mask, ridgeSupport148_012_mask, ridgeSupport148_013_mask, ridgeSupport148_014_mask, ridgeSupport148_015_mask, ridgeSupport148_016_mask, ridgeSupport148_017_mask, ridgeSupport148_018_mask, ridgeSupport148_019_mask, ridgeSupport148_020_mask, ridgeSupport148_021_mask, ridgeSupport148_022_mask, ridgeSupport148_023_mask, ridgeSupport148_024_mask, ridgeSupport148_025_mask, ridgeSupport148_026_mask, ridgeSupport148_027_mask]
    decide +kernel
  · rw [ridgeSupport148_eq]
    simp only [ridgeSupport148_suffix_000, ridgeSupport148_suffix_001, ridgeSupport148_suffix_002, ridgeSupport148_suffix_003, ridgeSupport148_suffix_004, ridgeSupport148_suffix_005, ridgeSupport148_suffix_006, ridgeSupport148_suffix_007, ridgeSupport148_suffix_008, ridgeSupport148_suffix_009, ridgeSupport148_suffix_010, ridgeSupport148_suffix_011, ridgeSupport148_suffix_012, ridgeSupport148_suffix_013, ridgeSupport148_suffix_014, ridgeSupport148_suffix_015, ridgeSupport148_suffix_016, ridgeSupport148_suffix_017, ridgeSupport148_suffix_018, ridgeSupport148_suffix_019, ridgeSupport148_suffix_020, ridgeSupport148_suffix_021, ridgeSupport148_suffix_022, ridgeSupport148_suffix_023, ridgeSupport148_suffix_024, ridgeSupport148_suffix_025, ridgeSupport148_suffix_026, ridgeSupport148_suffix_027, ridgeSupport148_suffix_028, List.all_append, List.all_nil, ridgeSupport148_000_checked, ridgeSupport148_001_checked, ridgeSupport148_002_checked, ridgeSupport148_003_checked, ridgeSupport148_004_checked, ridgeSupport148_005_checked, ridgeSupport148_006_checked, ridgeSupport148_007_checked, ridgeSupport148_008_checked, ridgeSupport148_009_checked, ridgeSupport148_010_checked, ridgeSupport148_011_checked, ridgeSupport148_012_checked, ridgeSupport148_013_checked, ridgeSupport148_014_checked, ridgeSupport148_015_checked, ridgeSupport148_016_checked, ridgeSupport148_017_checked, ridgeSupport148_018_checked, ridgeSupport148_019_checked, ridgeSupport148_020_checked, ridgeSupport148_021_checked, ridgeSupport148_022_checked, ridgeSupport148_023_checked, ridgeSupport148_024_checked, ridgeSupport148_025_checked, ridgeSupport148_026_checked, ridgeSupport148_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
