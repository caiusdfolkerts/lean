module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport82Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 82 028 15
cert_ridgeSupport_suffix_decode_2 82 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 82 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 82 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 82 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 82 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 82 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 82 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 82 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 82 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 82 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 82 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 82 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 82 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 82 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 82 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 82 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 82 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 82 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 82 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 82 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 82 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 82 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 82 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 82 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 82 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 82 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 82 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 82 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 82
theorem ridgeTest_large_82 : ridgeTest 82 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport82_eq]
    simp only [ridgeSupport82_suffix_000, ridgeSupport82_suffix_001, ridgeSupport82_suffix_002, ridgeSupport82_suffix_003, ridgeSupport82_suffix_004, ridgeSupport82_suffix_005, ridgeSupport82_suffix_006, ridgeSupport82_suffix_007, ridgeSupport82_suffix_008, ridgeSupport82_suffix_009, ridgeSupport82_suffix_010, ridgeSupport82_suffix_011, ridgeSupport82_suffix_012, ridgeSupport82_suffix_013, ridgeSupport82_suffix_014, ridgeSupport82_suffix_015, ridgeSupport82_suffix_016, ridgeSupport82_suffix_017, ridgeSupport82_suffix_018, ridgeSupport82_suffix_019, ridgeSupport82_suffix_020, ridgeSupport82_suffix_021, ridgeSupport82_suffix_022, ridgeSupport82_suffix_023, ridgeSupport82_suffix_024, ridgeSupport82_suffix_025, ridgeSupport82_suffix_026, ridgeSupport82_suffix_027, ridgeSupport82_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport82_000_mask, ridgeSupport82_001_mask, ridgeSupport82_002_mask, ridgeSupport82_003_mask, ridgeSupport82_004_mask, ridgeSupport82_005_mask, ridgeSupport82_006_mask, ridgeSupport82_007_mask, ridgeSupport82_008_mask, ridgeSupport82_009_mask, ridgeSupport82_010_mask, ridgeSupport82_011_mask, ridgeSupport82_012_mask, ridgeSupport82_013_mask, ridgeSupport82_014_mask, ridgeSupport82_015_mask, ridgeSupport82_016_mask, ridgeSupport82_017_mask, ridgeSupport82_018_mask, ridgeSupport82_019_mask, ridgeSupport82_020_mask, ridgeSupport82_021_mask, ridgeSupport82_022_mask, ridgeSupport82_023_mask, ridgeSupport82_024_mask, ridgeSupport82_025_mask, ridgeSupport82_026_mask, ridgeSupport82_027_mask]
    decide +kernel
  · rw [ridgeSupport82_eq]
    simp only [ridgeSupport82_suffix_000, ridgeSupport82_suffix_001, ridgeSupport82_suffix_002, ridgeSupport82_suffix_003, ridgeSupport82_suffix_004, ridgeSupport82_suffix_005, ridgeSupport82_suffix_006, ridgeSupport82_suffix_007, ridgeSupport82_suffix_008, ridgeSupport82_suffix_009, ridgeSupport82_suffix_010, ridgeSupport82_suffix_011, ridgeSupport82_suffix_012, ridgeSupport82_suffix_013, ridgeSupport82_suffix_014, ridgeSupport82_suffix_015, ridgeSupport82_suffix_016, ridgeSupport82_suffix_017, ridgeSupport82_suffix_018, ridgeSupport82_suffix_019, ridgeSupport82_suffix_020, ridgeSupport82_suffix_021, ridgeSupport82_suffix_022, ridgeSupport82_suffix_023, ridgeSupport82_suffix_024, ridgeSupport82_suffix_025, ridgeSupport82_suffix_026, ridgeSupport82_suffix_027, ridgeSupport82_suffix_028, List.all_append, List.all_nil, ridgeSupport82_000_checked, ridgeSupport82_001_checked, ridgeSupport82_002_checked, ridgeSupport82_003_checked, ridgeSupport82_004_checked, ridgeSupport82_005_checked, ridgeSupport82_006_checked, ridgeSupport82_007_checked, ridgeSupport82_008_checked, ridgeSupport82_009_checked, ridgeSupport82_010_checked, ridgeSupport82_011_checked, ridgeSupport82_012_checked, ridgeSupport82_013_checked, ridgeSupport82_014_checked, ridgeSupport82_015_checked, ridgeSupport82_016_checked, ridgeSupport82_017_checked, ridgeSupport82_018_checked, ridgeSupport82_019_checked, ridgeSupport82_020_checked, ridgeSupport82_021_checked, ridgeSupport82_022_checked, ridgeSupport82_023_checked, ridgeSupport82_024_checked, ridgeSupport82_025_checked, ridgeSupport82_026_checked, ridgeSupport82_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
