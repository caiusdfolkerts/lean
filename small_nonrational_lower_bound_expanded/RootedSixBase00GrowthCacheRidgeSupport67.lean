module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport67Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 67 028 15
cert_ridgeSupport_suffix_decode_2 67 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 67 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 67 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 67 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 67 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 67 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 67 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 67 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 67 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 67 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 67 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 67 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 67 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 67 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 67 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 67 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 67 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 67 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 67 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 67 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 67 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 67 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 67 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 67 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 67 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 67 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 67 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 67 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 67
theorem ridgeTest_large_67 : ridgeTest 67 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport67_eq]
    simp only [ridgeSupport67_suffix_000, ridgeSupport67_suffix_001, ridgeSupport67_suffix_002, ridgeSupport67_suffix_003, ridgeSupport67_suffix_004, ridgeSupport67_suffix_005, ridgeSupport67_suffix_006, ridgeSupport67_suffix_007, ridgeSupport67_suffix_008, ridgeSupport67_suffix_009, ridgeSupport67_suffix_010, ridgeSupport67_suffix_011, ridgeSupport67_suffix_012, ridgeSupport67_suffix_013, ridgeSupport67_suffix_014, ridgeSupport67_suffix_015, ridgeSupport67_suffix_016, ridgeSupport67_suffix_017, ridgeSupport67_suffix_018, ridgeSupport67_suffix_019, ridgeSupport67_suffix_020, ridgeSupport67_suffix_021, ridgeSupport67_suffix_022, ridgeSupport67_suffix_023, ridgeSupport67_suffix_024, ridgeSupport67_suffix_025, ridgeSupport67_suffix_026, ridgeSupport67_suffix_027, ridgeSupport67_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport67_000_mask, ridgeSupport67_001_mask, ridgeSupport67_002_mask, ridgeSupport67_003_mask, ridgeSupport67_004_mask, ridgeSupport67_005_mask, ridgeSupport67_006_mask, ridgeSupport67_007_mask, ridgeSupport67_008_mask, ridgeSupport67_009_mask, ridgeSupport67_010_mask, ridgeSupport67_011_mask, ridgeSupport67_012_mask, ridgeSupport67_013_mask, ridgeSupport67_014_mask, ridgeSupport67_015_mask, ridgeSupport67_016_mask, ridgeSupport67_017_mask, ridgeSupport67_018_mask, ridgeSupport67_019_mask, ridgeSupport67_020_mask, ridgeSupport67_021_mask, ridgeSupport67_022_mask, ridgeSupport67_023_mask, ridgeSupport67_024_mask, ridgeSupport67_025_mask, ridgeSupport67_026_mask, ridgeSupport67_027_mask]
    decide +kernel
  · rw [ridgeSupport67_eq]
    simp only [ridgeSupport67_suffix_000, ridgeSupport67_suffix_001, ridgeSupport67_suffix_002, ridgeSupport67_suffix_003, ridgeSupport67_suffix_004, ridgeSupport67_suffix_005, ridgeSupport67_suffix_006, ridgeSupport67_suffix_007, ridgeSupport67_suffix_008, ridgeSupport67_suffix_009, ridgeSupport67_suffix_010, ridgeSupport67_suffix_011, ridgeSupport67_suffix_012, ridgeSupport67_suffix_013, ridgeSupport67_suffix_014, ridgeSupport67_suffix_015, ridgeSupport67_suffix_016, ridgeSupport67_suffix_017, ridgeSupport67_suffix_018, ridgeSupport67_suffix_019, ridgeSupport67_suffix_020, ridgeSupport67_suffix_021, ridgeSupport67_suffix_022, ridgeSupport67_suffix_023, ridgeSupport67_suffix_024, ridgeSupport67_suffix_025, ridgeSupport67_suffix_026, ridgeSupport67_suffix_027, ridgeSupport67_suffix_028, List.all_append, List.all_nil, ridgeSupport67_000_checked, ridgeSupport67_001_checked, ridgeSupport67_002_checked, ridgeSupport67_003_checked, ridgeSupport67_004_checked, ridgeSupport67_005_checked, ridgeSupport67_006_checked, ridgeSupport67_007_checked, ridgeSupport67_008_checked, ridgeSupport67_009_checked, ridgeSupport67_010_checked, ridgeSupport67_011_checked, ridgeSupport67_012_checked, ridgeSupport67_013_checked, ridgeSupport67_014_checked, ridgeSupport67_015_checked, ridgeSupport67_016_checked, ridgeSupport67_017_checked, ridgeSupport67_018_checked, ridgeSupport67_019_checked, ridgeSupport67_020_checked, ridgeSupport67_021_checked, ridgeSupport67_022_checked, ridgeSupport67_023_checked, ridgeSupport67_024_checked, ridgeSupport67_025_checked, ridgeSupport67_026_checked, ridgeSupport67_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
