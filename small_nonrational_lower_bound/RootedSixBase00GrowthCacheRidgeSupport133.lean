module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport133Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 133 028 15
cert_ridgeSupport_suffix_decode_2 133 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 133 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 133 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 133 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 133 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 133 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 133 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 133 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 133 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 133 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 133 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 133 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 133 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 133 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 133 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 133 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 133 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 133 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 133 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 133 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 133 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 133 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 133 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 133 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 133 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 133 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 133 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 133 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 133
theorem ridgeTest_large_133 : ridgeTest 133 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport133_eq]
    simp only [ridgeSupport133_suffix_000, ridgeSupport133_suffix_001, ridgeSupport133_suffix_002, ridgeSupport133_suffix_003, ridgeSupport133_suffix_004, ridgeSupport133_suffix_005, ridgeSupport133_suffix_006, ridgeSupport133_suffix_007, ridgeSupport133_suffix_008, ridgeSupport133_suffix_009, ridgeSupport133_suffix_010, ridgeSupport133_suffix_011, ridgeSupport133_suffix_012, ridgeSupport133_suffix_013, ridgeSupport133_suffix_014, ridgeSupport133_suffix_015, ridgeSupport133_suffix_016, ridgeSupport133_suffix_017, ridgeSupport133_suffix_018, ridgeSupport133_suffix_019, ridgeSupport133_suffix_020, ridgeSupport133_suffix_021, ridgeSupport133_suffix_022, ridgeSupport133_suffix_023, ridgeSupport133_suffix_024, ridgeSupport133_suffix_025, ridgeSupport133_suffix_026, ridgeSupport133_suffix_027, ridgeSupport133_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport133_000_mask, ridgeSupport133_001_mask, ridgeSupport133_002_mask, ridgeSupport133_003_mask, ridgeSupport133_004_mask, ridgeSupport133_005_mask, ridgeSupport133_006_mask, ridgeSupport133_007_mask, ridgeSupport133_008_mask, ridgeSupport133_009_mask, ridgeSupport133_010_mask, ridgeSupport133_011_mask, ridgeSupport133_012_mask, ridgeSupport133_013_mask, ridgeSupport133_014_mask, ridgeSupport133_015_mask, ridgeSupport133_016_mask, ridgeSupport133_017_mask, ridgeSupport133_018_mask, ridgeSupport133_019_mask, ridgeSupport133_020_mask, ridgeSupport133_021_mask, ridgeSupport133_022_mask, ridgeSupport133_023_mask, ridgeSupport133_024_mask, ridgeSupport133_025_mask, ridgeSupport133_026_mask, ridgeSupport133_027_mask]
    decide +kernel
  · rw [ridgeSupport133_eq]
    simp only [ridgeSupport133_suffix_000, ridgeSupport133_suffix_001, ridgeSupport133_suffix_002, ridgeSupport133_suffix_003, ridgeSupport133_suffix_004, ridgeSupport133_suffix_005, ridgeSupport133_suffix_006, ridgeSupport133_suffix_007, ridgeSupport133_suffix_008, ridgeSupport133_suffix_009, ridgeSupport133_suffix_010, ridgeSupport133_suffix_011, ridgeSupport133_suffix_012, ridgeSupport133_suffix_013, ridgeSupport133_suffix_014, ridgeSupport133_suffix_015, ridgeSupport133_suffix_016, ridgeSupport133_suffix_017, ridgeSupport133_suffix_018, ridgeSupport133_suffix_019, ridgeSupport133_suffix_020, ridgeSupport133_suffix_021, ridgeSupport133_suffix_022, ridgeSupport133_suffix_023, ridgeSupport133_suffix_024, ridgeSupport133_suffix_025, ridgeSupport133_suffix_026, ridgeSupport133_suffix_027, ridgeSupport133_suffix_028, List.all_append, List.all_nil, ridgeSupport133_000_checked, ridgeSupport133_001_checked, ridgeSupport133_002_checked, ridgeSupport133_003_checked, ridgeSupport133_004_checked, ridgeSupport133_005_checked, ridgeSupport133_006_checked, ridgeSupport133_007_checked, ridgeSupport133_008_checked, ridgeSupport133_009_checked, ridgeSupport133_010_checked, ridgeSupport133_011_checked, ridgeSupport133_012_checked, ridgeSupport133_013_checked, ridgeSupport133_014_checked, ridgeSupport133_015_checked, ridgeSupport133_016_checked, ridgeSupport133_017_checked, ridgeSupport133_018_checked, ridgeSupport133_019_checked, ridgeSupport133_020_checked, ridgeSupport133_021_checked, ridgeSupport133_022_checked, ridgeSupport133_023_checked, ridgeSupport133_024_checked, ridgeSupport133_025_checked, ridgeSupport133_026_checked, ridgeSupport133_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
