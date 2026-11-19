module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport131Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 131 028 15
cert_ridgeSupport_suffix_decode_2 131 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 131 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 131 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 131 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 131 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 131 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 131 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 131 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 131 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 131 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 131 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 131 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 131 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 131 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 131 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 131 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 131 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 131 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 131 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 131 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 131 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 131 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 131 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 131 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 131 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 131 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 131 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 131 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 131
theorem ridgeTest_large_131 : ridgeTest 131 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport131_eq]
    simp only [ridgeSupport131_suffix_000, ridgeSupport131_suffix_001, ridgeSupport131_suffix_002, ridgeSupport131_suffix_003, ridgeSupport131_suffix_004, ridgeSupport131_suffix_005, ridgeSupport131_suffix_006, ridgeSupport131_suffix_007, ridgeSupport131_suffix_008, ridgeSupport131_suffix_009, ridgeSupport131_suffix_010, ridgeSupport131_suffix_011, ridgeSupport131_suffix_012, ridgeSupport131_suffix_013, ridgeSupport131_suffix_014, ridgeSupport131_suffix_015, ridgeSupport131_suffix_016, ridgeSupport131_suffix_017, ridgeSupport131_suffix_018, ridgeSupport131_suffix_019, ridgeSupport131_suffix_020, ridgeSupport131_suffix_021, ridgeSupport131_suffix_022, ridgeSupport131_suffix_023, ridgeSupport131_suffix_024, ridgeSupport131_suffix_025, ridgeSupport131_suffix_026, ridgeSupport131_suffix_027, ridgeSupport131_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport131_000_mask, ridgeSupport131_001_mask, ridgeSupport131_002_mask, ridgeSupport131_003_mask, ridgeSupport131_004_mask, ridgeSupport131_005_mask, ridgeSupport131_006_mask, ridgeSupport131_007_mask, ridgeSupport131_008_mask, ridgeSupport131_009_mask, ridgeSupport131_010_mask, ridgeSupport131_011_mask, ridgeSupport131_012_mask, ridgeSupport131_013_mask, ridgeSupport131_014_mask, ridgeSupport131_015_mask, ridgeSupport131_016_mask, ridgeSupport131_017_mask, ridgeSupport131_018_mask, ridgeSupport131_019_mask, ridgeSupport131_020_mask, ridgeSupport131_021_mask, ridgeSupport131_022_mask, ridgeSupport131_023_mask, ridgeSupport131_024_mask, ridgeSupport131_025_mask, ridgeSupport131_026_mask, ridgeSupport131_027_mask]
    decide +kernel
  · rw [ridgeSupport131_eq]
    simp only [ridgeSupport131_suffix_000, ridgeSupport131_suffix_001, ridgeSupport131_suffix_002, ridgeSupport131_suffix_003, ridgeSupport131_suffix_004, ridgeSupport131_suffix_005, ridgeSupport131_suffix_006, ridgeSupport131_suffix_007, ridgeSupport131_suffix_008, ridgeSupport131_suffix_009, ridgeSupport131_suffix_010, ridgeSupport131_suffix_011, ridgeSupport131_suffix_012, ridgeSupport131_suffix_013, ridgeSupport131_suffix_014, ridgeSupport131_suffix_015, ridgeSupport131_suffix_016, ridgeSupport131_suffix_017, ridgeSupport131_suffix_018, ridgeSupport131_suffix_019, ridgeSupport131_suffix_020, ridgeSupport131_suffix_021, ridgeSupport131_suffix_022, ridgeSupport131_suffix_023, ridgeSupport131_suffix_024, ridgeSupport131_suffix_025, ridgeSupport131_suffix_026, ridgeSupport131_suffix_027, ridgeSupport131_suffix_028, List.all_append, List.all_nil, ridgeSupport131_000_checked, ridgeSupport131_001_checked, ridgeSupport131_002_checked, ridgeSupport131_003_checked, ridgeSupport131_004_checked, ridgeSupport131_005_checked, ridgeSupport131_006_checked, ridgeSupport131_007_checked, ridgeSupport131_008_checked, ridgeSupport131_009_checked, ridgeSupport131_010_checked, ridgeSupport131_011_checked, ridgeSupport131_012_checked, ridgeSupport131_013_checked, ridgeSupport131_014_checked, ridgeSupport131_015_checked, ridgeSupport131_016_checked, ridgeSupport131_017_checked, ridgeSupport131_018_checked, ridgeSupport131_019_checked, ridgeSupport131_020_checked, ridgeSupport131_021_checked, ridgeSupport131_022_checked, ridgeSupport131_023_checked, ridgeSupport131_024_checked, ridgeSupport131_025_checked, ridgeSupport131_026_checked, ridgeSupport131_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
