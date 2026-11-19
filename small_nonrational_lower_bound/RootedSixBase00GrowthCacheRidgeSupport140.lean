module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport140Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 140 028 15
cert_ridgeSupport_suffix_decode_2 140 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 140 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 140 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 140 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 140 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 140 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 140 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 140 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 140 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 140 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 140 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 140 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 140 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 140 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 140 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 140 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 140 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 140 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 140 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 140 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 140 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 140 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 140 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 140 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 140 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 140 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 140 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 140 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 140
theorem ridgeTest_large_140 : ridgeTest 140 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport140_eq]
    simp only [ridgeSupport140_suffix_000, ridgeSupport140_suffix_001, ridgeSupport140_suffix_002, ridgeSupport140_suffix_003, ridgeSupport140_suffix_004, ridgeSupport140_suffix_005, ridgeSupport140_suffix_006, ridgeSupport140_suffix_007, ridgeSupport140_suffix_008, ridgeSupport140_suffix_009, ridgeSupport140_suffix_010, ridgeSupport140_suffix_011, ridgeSupport140_suffix_012, ridgeSupport140_suffix_013, ridgeSupport140_suffix_014, ridgeSupport140_suffix_015, ridgeSupport140_suffix_016, ridgeSupport140_suffix_017, ridgeSupport140_suffix_018, ridgeSupport140_suffix_019, ridgeSupport140_suffix_020, ridgeSupport140_suffix_021, ridgeSupport140_suffix_022, ridgeSupport140_suffix_023, ridgeSupport140_suffix_024, ridgeSupport140_suffix_025, ridgeSupport140_suffix_026, ridgeSupport140_suffix_027, ridgeSupport140_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport140_000_mask, ridgeSupport140_001_mask, ridgeSupport140_002_mask, ridgeSupport140_003_mask, ridgeSupport140_004_mask, ridgeSupport140_005_mask, ridgeSupport140_006_mask, ridgeSupport140_007_mask, ridgeSupport140_008_mask, ridgeSupport140_009_mask, ridgeSupport140_010_mask, ridgeSupport140_011_mask, ridgeSupport140_012_mask, ridgeSupport140_013_mask, ridgeSupport140_014_mask, ridgeSupport140_015_mask, ridgeSupport140_016_mask, ridgeSupport140_017_mask, ridgeSupport140_018_mask, ridgeSupport140_019_mask, ridgeSupport140_020_mask, ridgeSupport140_021_mask, ridgeSupport140_022_mask, ridgeSupport140_023_mask, ridgeSupport140_024_mask, ridgeSupport140_025_mask, ridgeSupport140_026_mask, ridgeSupport140_027_mask]
    decide +kernel
  · rw [ridgeSupport140_eq]
    simp only [ridgeSupport140_suffix_000, ridgeSupport140_suffix_001, ridgeSupport140_suffix_002, ridgeSupport140_suffix_003, ridgeSupport140_suffix_004, ridgeSupport140_suffix_005, ridgeSupport140_suffix_006, ridgeSupport140_suffix_007, ridgeSupport140_suffix_008, ridgeSupport140_suffix_009, ridgeSupport140_suffix_010, ridgeSupport140_suffix_011, ridgeSupport140_suffix_012, ridgeSupport140_suffix_013, ridgeSupport140_suffix_014, ridgeSupport140_suffix_015, ridgeSupport140_suffix_016, ridgeSupport140_suffix_017, ridgeSupport140_suffix_018, ridgeSupport140_suffix_019, ridgeSupport140_suffix_020, ridgeSupport140_suffix_021, ridgeSupport140_suffix_022, ridgeSupport140_suffix_023, ridgeSupport140_suffix_024, ridgeSupport140_suffix_025, ridgeSupport140_suffix_026, ridgeSupport140_suffix_027, ridgeSupport140_suffix_028, List.all_append, List.all_nil, ridgeSupport140_000_checked, ridgeSupport140_001_checked, ridgeSupport140_002_checked, ridgeSupport140_003_checked, ridgeSupport140_004_checked, ridgeSupport140_005_checked, ridgeSupport140_006_checked, ridgeSupport140_007_checked, ridgeSupport140_008_checked, ridgeSupport140_009_checked, ridgeSupport140_010_checked, ridgeSupport140_011_checked, ridgeSupport140_012_checked, ridgeSupport140_013_checked, ridgeSupport140_014_checked, ridgeSupport140_015_checked, ridgeSupport140_016_checked, ridgeSupport140_017_checked, ridgeSupport140_018_checked, ridgeSupport140_019_checked, ridgeSupport140_020_checked, ridgeSupport140_021_checked, ridgeSupport140_022_checked, ridgeSupport140_023_checked, ridgeSupport140_024_checked, ridgeSupport140_025_checked, ridgeSupport140_026_checked, ridgeSupport140_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
