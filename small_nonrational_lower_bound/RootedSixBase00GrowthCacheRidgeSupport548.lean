module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport548Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 548 028 15
cert_ridgeSupport_suffix_decode_2 548 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 548 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 548 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 548 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 548 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 548 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 548 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 548 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 548 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 548 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 548 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 548 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 548 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 548 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 548 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 548 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 548 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 548 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 548 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 548 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 548 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 548 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 548 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 548 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 548 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 548 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 548 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 548 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 548
theorem ridgeTest_large_548 : ridgeTest 548 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport548_eq]
    simp only [ridgeSupport548_suffix_000, ridgeSupport548_suffix_001, ridgeSupport548_suffix_002, ridgeSupport548_suffix_003, ridgeSupport548_suffix_004, ridgeSupport548_suffix_005, ridgeSupport548_suffix_006, ridgeSupport548_suffix_007, ridgeSupport548_suffix_008, ridgeSupport548_suffix_009, ridgeSupport548_suffix_010, ridgeSupport548_suffix_011, ridgeSupport548_suffix_012, ridgeSupport548_suffix_013, ridgeSupport548_suffix_014, ridgeSupport548_suffix_015, ridgeSupport548_suffix_016, ridgeSupport548_suffix_017, ridgeSupport548_suffix_018, ridgeSupport548_suffix_019, ridgeSupport548_suffix_020, ridgeSupport548_suffix_021, ridgeSupport548_suffix_022, ridgeSupport548_suffix_023, ridgeSupport548_suffix_024, ridgeSupport548_suffix_025, ridgeSupport548_suffix_026, ridgeSupport548_suffix_027, ridgeSupport548_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport548_000_mask, ridgeSupport548_001_mask, ridgeSupport548_002_mask, ridgeSupport548_003_mask, ridgeSupport548_004_mask, ridgeSupport548_005_mask, ridgeSupport548_006_mask, ridgeSupport548_007_mask, ridgeSupport548_008_mask, ridgeSupport548_009_mask, ridgeSupport548_010_mask, ridgeSupport548_011_mask, ridgeSupport548_012_mask, ridgeSupport548_013_mask, ridgeSupport548_014_mask, ridgeSupport548_015_mask, ridgeSupport548_016_mask, ridgeSupport548_017_mask, ridgeSupport548_018_mask, ridgeSupport548_019_mask, ridgeSupport548_020_mask, ridgeSupport548_021_mask, ridgeSupport548_022_mask, ridgeSupport548_023_mask, ridgeSupport548_024_mask, ridgeSupport548_025_mask, ridgeSupport548_026_mask, ridgeSupport548_027_mask]
    decide +kernel
  · rw [ridgeSupport548_eq]
    simp only [ridgeSupport548_suffix_000, ridgeSupport548_suffix_001, ridgeSupport548_suffix_002, ridgeSupport548_suffix_003, ridgeSupport548_suffix_004, ridgeSupport548_suffix_005, ridgeSupport548_suffix_006, ridgeSupport548_suffix_007, ridgeSupport548_suffix_008, ridgeSupport548_suffix_009, ridgeSupport548_suffix_010, ridgeSupport548_suffix_011, ridgeSupport548_suffix_012, ridgeSupport548_suffix_013, ridgeSupport548_suffix_014, ridgeSupport548_suffix_015, ridgeSupport548_suffix_016, ridgeSupport548_suffix_017, ridgeSupport548_suffix_018, ridgeSupport548_suffix_019, ridgeSupport548_suffix_020, ridgeSupport548_suffix_021, ridgeSupport548_suffix_022, ridgeSupport548_suffix_023, ridgeSupport548_suffix_024, ridgeSupport548_suffix_025, ridgeSupport548_suffix_026, ridgeSupport548_suffix_027, ridgeSupport548_suffix_028, List.all_append, List.all_nil, ridgeSupport548_000_checked, ridgeSupport548_001_checked, ridgeSupport548_002_checked, ridgeSupport548_003_checked, ridgeSupport548_004_checked, ridgeSupport548_005_checked, ridgeSupport548_006_checked, ridgeSupport548_007_checked, ridgeSupport548_008_checked, ridgeSupport548_009_checked, ridgeSupport548_010_checked, ridgeSupport548_011_checked, ridgeSupport548_012_checked, ridgeSupport548_013_checked, ridgeSupport548_014_checked, ridgeSupport548_015_checked, ridgeSupport548_016_checked, ridgeSupport548_017_checked, ridgeSupport548_018_checked, ridgeSupport548_019_checked, ridgeSupport548_020_checked, ridgeSupport548_021_checked, ridgeSupport548_022_checked, ridgeSupport548_023_checked, ridgeSupport548_024_checked, ridgeSupport548_025_checked, ridgeSupport548_026_checked, ridgeSupport548_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
