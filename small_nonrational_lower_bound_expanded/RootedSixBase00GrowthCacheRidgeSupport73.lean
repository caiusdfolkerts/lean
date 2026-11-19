module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport73Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 73 028 15
cert_ridgeSupport_suffix_decode_2 73 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 73 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 73 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 73 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 73 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 73 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 73 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 73 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 73 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 73 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 73 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 73 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 73 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 73 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 73 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 73 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 73 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 73 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 73 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 73 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 73 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 73 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 73 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 73 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 73 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 73 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 73 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 73 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 73
theorem ridgeTest_large_73 : ridgeTest 73 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport73_eq]
    simp only [ridgeSupport73_suffix_000, ridgeSupport73_suffix_001, ridgeSupport73_suffix_002, ridgeSupport73_suffix_003, ridgeSupport73_suffix_004, ridgeSupport73_suffix_005, ridgeSupport73_suffix_006, ridgeSupport73_suffix_007, ridgeSupport73_suffix_008, ridgeSupport73_suffix_009, ridgeSupport73_suffix_010, ridgeSupport73_suffix_011, ridgeSupport73_suffix_012, ridgeSupport73_suffix_013, ridgeSupport73_suffix_014, ridgeSupport73_suffix_015, ridgeSupport73_suffix_016, ridgeSupport73_suffix_017, ridgeSupport73_suffix_018, ridgeSupport73_suffix_019, ridgeSupport73_suffix_020, ridgeSupport73_suffix_021, ridgeSupport73_suffix_022, ridgeSupport73_suffix_023, ridgeSupport73_suffix_024, ridgeSupport73_suffix_025, ridgeSupport73_suffix_026, ridgeSupport73_suffix_027, ridgeSupport73_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport73_000_mask, ridgeSupport73_001_mask, ridgeSupport73_002_mask, ridgeSupport73_003_mask, ridgeSupport73_004_mask, ridgeSupport73_005_mask, ridgeSupport73_006_mask, ridgeSupport73_007_mask, ridgeSupport73_008_mask, ridgeSupport73_009_mask, ridgeSupport73_010_mask, ridgeSupport73_011_mask, ridgeSupport73_012_mask, ridgeSupport73_013_mask, ridgeSupport73_014_mask, ridgeSupport73_015_mask, ridgeSupport73_016_mask, ridgeSupport73_017_mask, ridgeSupport73_018_mask, ridgeSupport73_019_mask, ridgeSupport73_020_mask, ridgeSupport73_021_mask, ridgeSupport73_022_mask, ridgeSupport73_023_mask, ridgeSupport73_024_mask, ridgeSupport73_025_mask, ridgeSupport73_026_mask, ridgeSupport73_027_mask]
    decide +kernel
  · rw [ridgeSupport73_eq]
    simp only [ridgeSupport73_suffix_000, ridgeSupport73_suffix_001, ridgeSupport73_suffix_002, ridgeSupport73_suffix_003, ridgeSupport73_suffix_004, ridgeSupport73_suffix_005, ridgeSupport73_suffix_006, ridgeSupport73_suffix_007, ridgeSupport73_suffix_008, ridgeSupport73_suffix_009, ridgeSupport73_suffix_010, ridgeSupport73_suffix_011, ridgeSupport73_suffix_012, ridgeSupport73_suffix_013, ridgeSupport73_suffix_014, ridgeSupport73_suffix_015, ridgeSupport73_suffix_016, ridgeSupport73_suffix_017, ridgeSupport73_suffix_018, ridgeSupport73_suffix_019, ridgeSupport73_suffix_020, ridgeSupport73_suffix_021, ridgeSupport73_suffix_022, ridgeSupport73_suffix_023, ridgeSupport73_suffix_024, ridgeSupport73_suffix_025, ridgeSupport73_suffix_026, ridgeSupport73_suffix_027, ridgeSupport73_suffix_028, List.all_append, List.all_nil, ridgeSupport73_000_checked, ridgeSupport73_001_checked, ridgeSupport73_002_checked, ridgeSupport73_003_checked, ridgeSupport73_004_checked, ridgeSupport73_005_checked, ridgeSupport73_006_checked, ridgeSupport73_007_checked, ridgeSupport73_008_checked, ridgeSupport73_009_checked, ridgeSupport73_010_checked, ridgeSupport73_011_checked, ridgeSupport73_012_checked, ridgeSupport73_013_checked, ridgeSupport73_014_checked, ridgeSupport73_015_checked, ridgeSupport73_016_checked, ridgeSupport73_017_checked, ridgeSupport73_018_checked, ridgeSupport73_019_checked, ridgeSupport73_020_checked, ridgeSupport73_021_checked, ridgeSupport73_022_checked, ridgeSupport73_023_checked, ridgeSupport73_024_checked, ridgeSupport73_025_checked, ridgeSupport73_026_checked, ridgeSupport73_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
