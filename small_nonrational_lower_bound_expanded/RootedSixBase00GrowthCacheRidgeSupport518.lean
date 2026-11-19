module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport518Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 518 028 15
cert_ridgeSupport_suffix_decode_2 518 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 518 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 518 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 518 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 518 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 518 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 518 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 518 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 518 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 518 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 518 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 518 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 518 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 518 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 518 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 518 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 518 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 518 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 518 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 518 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 518 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 518 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 518 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 518 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 518 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 518 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 518 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 518 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 518
theorem ridgeTest_large_518 : ridgeTest 518 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport518_eq]
    simp only [ridgeSupport518_suffix_000, ridgeSupport518_suffix_001, ridgeSupport518_suffix_002, ridgeSupport518_suffix_003, ridgeSupport518_suffix_004, ridgeSupport518_suffix_005, ridgeSupport518_suffix_006, ridgeSupport518_suffix_007, ridgeSupport518_suffix_008, ridgeSupport518_suffix_009, ridgeSupport518_suffix_010, ridgeSupport518_suffix_011, ridgeSupport518_suffix_012, ridgeSupport518_suffix_013, ridgeSupport518_suffix_014, ridgeSupport518_suffix_015, ridgeSupport518_suffix_016, ridgeSupport518_suffix_017, ridgeSupport518_suffix_018, ridgeSupport518_suffix_019, ridgeSupport518_suffix_020, ridgeSupport518_suffix_021, ridgeSupport518_suffix_022, ridgeSupport518_suffix_023, ridgeSupport518_suffix_024, ridgeSupport518_suffix_025, ridgeSupport518_suffix_026, ridgeSupport518_suffix_027, ridgeSupport518_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport518_000_mask, ridgeSupport518_001_mask, ridgeSupport518_002_mask, ridgeSupport518_003_mask, ridgeSupport518_004_mask, ridgeSupport518_005_mask, ridgeSupport518_006_mask, ridgeSupport518_007_mask, ridgeSupport518_008_mask, ridgeSupport518_009_mask, ridgeSupport518_010_mask, ridgeSupport518_011_mask, ridgeSupport518_012_mask, ridgeSupport518_013_mask, ridgeSupport518_014_mask, ridgeSupport518_015_mask, ridgeSupport518_016_mask, ridgeSupport518_017_mask, ridgeSupport518_018_mask, ridgeSupport518_019_mask, ridgeSupport518_020_mask, ridgeSupport518_021_mask, ridgeSupport518_022_mask, ridgeSupport518_023_mask, ridgeSupport518_024_mask, ridgeSupport518_025_mask, ridgeSupport518_026_mask, ridgeSupport518_027_mask]
    decide +kernel
  · rw [ridgeSupport518_eq]
    simp only [ridgeSupport518_suffix_000, ridgeSupport518_suffix_001, ridgeSupport518_suffix_002, ridgeSupport518_suffix_003, ridgeSupport518_suffix_004, ridgeSupport518_suffix_005, ridgeSupport518_suffix_006, ridgeSupport518_suffix_007, ridgeSupport518_suffix_008, ridgeSupport518_suffix_009, ridgeSupport518_suffix_010, ridgeSupport518_suffix_011, ridgeSupport518_suffix_012, ridgeSupport518_suffix_013, ridgeSupport518_suffix_014, ridgeSupport518_suffix_015, ridgeSupport518_suffix_016, ridgeSupport518_suffix_017, ridgeSupport518_suffix_018, ridgeSupport518_suffix_019, ridgeSupport518_suffix_020, ridgeSupport518_suffix_021, ridgeSupport518_suffix_022, ridgeSupport518_suffix_023, ridgeSupport518_suffix_024, ridgeSupport518_suffix_025, ridgeSupport518_suffix_026, ridgeSupport518_suffix_027, ridgeSupport518_suffix_028, List.all_append, List.all_nil, ridgeSupport518_000_checked, ridgeSupport518_001_checked, ridgeSupport518_002_checked, ridgeSupport518_003_checked, ridgeSupport518_004_checked, ridgeSupport518_005_checked, ridgeSupport518_006_checked, ridgeSupport518_007_checked, ridgeSupport518_008_checked, ridgeSupport518_009_checked, ridgeSupport518_010_checked, ridgeSupport518_011_checked, ridgeSupport518_012_checked, ridgeSupport518_013_checked, ridgeSupport518_014_checked, ridgeSupport518_015_checked, ridgeSupport518_016_checked, ridgeSupport518_017_checked, ridgeSupport518_018_checked, ridgeSupport518_019_checked, ridgeSupport518_020_checked, ridgeSupport518_021_checked, ridgeSupport518_022_checked, ridgeSupport518_023_checked, ridgeSupport518_024_checked, ridgeSupport518_025_checked, ridgeSupport518_026_checked, ridgeSupport518_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
