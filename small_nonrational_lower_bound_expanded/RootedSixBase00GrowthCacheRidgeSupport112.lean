module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport112Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 112 028 15
cert_ridgeSupport_suffix_decode_2 112 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 112 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 112 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 112 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 112 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 112 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 112 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 112 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 112 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 112 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 112 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 112 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 112 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 112 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 112 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 112 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 112 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 112 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 112 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 112 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 112 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 112 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 112 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 112 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 112 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 112 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 112 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 112 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 112
theorem ridgeTest_large_112 : ridgeTest 112 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport112_eq]
    simp only [ridgeSupport112_suffix_000, ridgeSupport112_suffix_001, ridgeSupport112_suffix_002, ridgeSupport112_suffix_003, ridgeSupport112_suffix_004, ridgeSupport112_suffix_005, ridgeSupport112_suffix_006, ridgeSupport112_suffix_007, ridgeSupport112_suffix_008, ridgeSupport112_suffix_009, ridgeSupport112_suffix_010, ridgeSupport112_suffix_011, ridgeSupport112_suffix_012, ridgeSupport112_suffix_013, ridgeSupport112_suffix_014, ridgeSupport112_suffix_015, ridgeSupport112_suffix_016, ridgeSupport112_suffix_017, ridgeSupport112_suffix_018, ridgeSupport112_suffix_019, ridgeSupport112_suffix_020, ridgeSupport112_suffix_021, ridgeSupport112_suffix_022, ridgeSupport112_suffix_023, ridgeSupport112_suffix_024, ridgeSupport112_suffix_025, ridgeSupport112_suffix_026, ridgeSupport112_suffix_027, ridgeSupport112_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport112_000_mask, ridgeSupport112_001_mask, ridgeSupport112_002_mask, ridgeSupport112_003_mask, ridgeSupport112_004_mask, ridgeSupport112_005_mask, ridgeSupport112_006_mask, ridgeSupport112_007_mask, ridgeSupport112_008_mask, ridgeSupport112_009_mask, ridgeSupport112_010_mask, ridgeSupport112_011_mask, ridgeSupport112_012_mask, ridgeSupport112_013_mask, ridgeSupport112_014_mask, ridgeSupport112_015_mask, ridgeSupport112_016_mask, ridgeSupport112_017_mask, ridgeSupport112_018_mask, ridgeSupport112_019_mask, ridgeSupport112_020_mask, ridgeSupport112_021_mask, ridgeSupport112_022_mask, ridgeSupport112_023_mask, ridgeSupport112_024_mask, ridgeSupport112_025_mask, ridgeSupport112_026_mask, ridgeSupport112_027_mask]
    decide +kernel
  · rw [ridgeSupport112_eq]
    simp only [ridgeSupport112_suffix_000, ridgeSupport112_suffix_001, ridgeSupport112_suffix_002, ridgeSupport112_suffix_003, ridgeSupport112_suffix_004, ridgeSupport112_suffix_005, ridgeSupport112_suffix_006, ridgeSupport112_suffix_007, ridgeSupport112_suffix_008, ridgeSupport112_suffix_009, ridgeSupport112_suffix_010, ridgeSupport112_suffix_011, ridgeSupport112_suffix_012, ridgeSupport112_suffix_013, ridgeSupport112_suffix_014, ridgeSupport112_suffix_015, ridgeSupport112_suffix_016, ridgeSupport112_suffix_017, ridgeSupport112_suffix_018, ridgeSupport112_suffix_019, ridgeSupport112_suffix_020, ridgeSupport112_suffix_021, ridgeSupport112_suffix_022, ridgeSupport112_suffix_023, ridgeSupport112_suffix_024, ridgeSupport112_suffix_025, ridgeSupport112_suffix_026, ridgeSupport112_suffix_027, ridgeSupport112_suffix_028, List.all_append, List.all_nil, ridgeSupport112_000_checked, ridgeSupport112_001_checked, ridgeSupport112_002_checked, ridgeSupport112_003_checked, ridgeSupport112_004_checked, ridgeSupport112_005_checked, ridgeSupport112_006_checked, ridgeSupport112_007_checked, ridgeSupport112_008_checked, ridgeSupport112_009_checked, ridgeSupport112_010_checked, ridgeSupport112_011_checked, ridgeSupport112_012_checked, ridgeSupport112_013_checked, ridgeSupport112_014_checked, ridgeSupport112_015_checked, ridgeSupport112_016_checked, ridgeSupport112_017_checked, ridgeSupport112_018_checked, ridgeSupport112_019_checked, ridgeSupport112_020_checked, ridgeSupport112_021_checked, ridgeSupport112_022_checked, ridgeSupport112_023_checked, ridgeSupport112_024_checked, ridgeSupport112_025_checked, ridgeSupport112_026_checked, ridgeSupport112_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
