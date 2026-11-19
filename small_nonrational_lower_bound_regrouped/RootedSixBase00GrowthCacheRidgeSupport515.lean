module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport515Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 515 028 15
cert_ridgeSupport_suffix_decode_2 515 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 515 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 515 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 515 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 515 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 515 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 515 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 515 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 515 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 515 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 515 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 515 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 515 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 515 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 515 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 515 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 515 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 515 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 515 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 515 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 515 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 515 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 515 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 515 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 515 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 515 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 515 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 515 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 515
theorem ridgeTest_large_515 : ridgeTest 515 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport515_eq]
    simp only [ridgeSupport515_suffix_000, ridgeSupport515_suffix_001, ridgeSupport515_suffix_002, ridgeSupport515_suffix_003, ridgeSupport515_suffix_004, ridgeSupport515_suffix_005, ridgeSupport515_suffix_006, ridgeSupport515_suffix_007, ridgeSupport515_suffix_008, ridgeSupport515_suffix_009, ridgeSupport515_suffix_010, ridgeSupport515_suffix_011, ridgeSupport515_suffix_012, ridgeSupport515_suffix_013, ridgeSupport515_suffix_014, ridgeSupport515_suffix_015, ridgeSupport515_suffix_016, ridgeSupport515_suffix_017, ridgeSupport515_suffix_018, ridgeSupport515_suffix_019, ridgeSupport515_suffix_020, ridgeSupport515_suffix_021, ridgeSupport515_suffix_022, ridgeSupport515_suffix_023, ridgeSupport515_suffix_024, ridgeSupport515_suffix_025, ridgeSupport515_suffix_026, ridgeSupport515_suffix_027, ridgeSupport515_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport515_000_mask, ridgeSupport515_001_mask, ridgeSupport515_002_mask, ridgeSupport515_003_mask, ridgeSupport515_004_mask, ridgeSupport515_005_mask, ridgeSupport515_006_mask, ridgeSupport515_007_mask, ridgeSupport515_008_mask, ridgeSupport515_009_mask, ridgeSupport515_010_mask, ridgeSupport515_011_mask, ridgeSupport515_012_mask, ridgeSupport515_013_mask, ridgeSupport515_014_mask, ridgeSupport515_015_mask, ridgeSupport515_016_mask, ridgeSupport515_017_mask, ridgeSupport515_018_mask, ridgeSupport515_019_mask, ridgeSupport515_020_mask, ridgeSupport515_021_mask, ridgeSupport515_022_mask, ridgeSupport515_023_mask, ridgeSupport515_024_mask, ridgeSupport515_025_mask, ridgeSupport515_026_mask, ridgeSupport515_027_mask]
    decide +kernel
  · rw [ridgeSupport515_eq]
    simp only [ridgeSupport515_suffix_000, ridgeSupport515_suffix_001, ridgeSupport515_suffix_002, ridgeSupport515_suffix_003, ridgeSupport515_suffix_004, ridgeSupport515_suffix_005, ridgeSupport515_suffix_006, ridgeSupport515_suffix_007, ridgeSupport515_suffix_008, ridgeSupport515_suffix_009, ridgeSupport515_suffix_010, ridgeSupport515_suffix_011, ridgeSupport515_suffix_012, ridgeSupport515_suffix_013, ridgeSupport515_suffix_014, ridgeSupport515_suffix_015, ridgeSupport515_suffix_016, ridgeSupport515_suffix_017, ridgeSupport515_suffix_018, ridgeSupport515_suffix_019, ridgeSupport515_suffix_020, ridgeSupport515_suffix_021, ridgeSupport515_suffix_022, ridgeSupport515_suffix_023, ridgeSupport515_suffix_024, ridgeSupport515_suffix_025, ridgeSupport515_suffix_026, ridgeSupport515_suffix_027, ridgeSupport515_suffix_028, List.all_append, List.all_nil, ridgeSupport515_000_checked, ridgeSupport515_001_checked, ridgeSupport515_002_checked, ridgeSupport515_003_checked, ridgeSupport515_004_checked, ridgeSupport515_005_checked, ridgeSupport515_006_checked, ridgeSupport515_007_checked, ridgeSupport515_008_checked, ridgeSupport515_009_checked, ridgeSupport515_010_checked, ridgeSupport515_011_checked, ridgeSupport515_012_checked, ridgeSupport515_013_checked, ridgeSupport515_014_checked, ridgeSupport515_015_checked, ridgeSupport515_016_checked, ridgeSupport515_017_checked, ridgeSupport515_018_checked, ridgeSupport515_019_checked, ridgeSupport515_020_checked, ridgeSupport515_021_checked, ridgeSupport515_022_checked, ridgeSupport515_023_checked, ridgeSupport515_024_checked, ridgeSupport515_025_checked, ridgeSupport515_026_checked, ridgeSupport515_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
