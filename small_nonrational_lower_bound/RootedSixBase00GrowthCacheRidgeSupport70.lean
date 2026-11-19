module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport70Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 70 028 15
cert_ridgeSupport_suffix_decode_2 70 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 70 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 70 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 70 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 70 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 70 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 70 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 70 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 70 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 70 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 70 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 70 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 70 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 70 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 70 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 70 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 70 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 70 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 70 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 70 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 70 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 70 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 70 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 70 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 70 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 70 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 70 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 70 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 70
theorem ridgeTest_large_70 : ridgeTest 70 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport70_eq]
    simp only [ridgeSupport70_suffix_000, ridgeSupport70_suffix_001, ridgeSupport70_suffix_002, ridgeSupport70_suffix_003, ridgeSupport70_suffix_004, ridgeSupport70_suffix_005, ridgeSupport70_suffix_006, ridgeSupport70_suffix_007, ridgeSupport70_suffix_008, ridgeSupport70_suffix_009, ridgeSupport70_suffix_010, ridgeSupport70_suffix_011, ridgeSupport70_suffix_012, ridgeSupport70_suffix_013, ridgeSupport70_suffix_014, ridgeSupport70_suffix_015, ridgeSupport70_suffix_016, ridgeSupport70_suffix_017, ridgeSupport70_suffix_018, ridgeSupport70_suffix_019, ridgeSupport70_suffix_020, ridgeSupport70_suffix_021, ridgeSupport70_suffix_022, ridgeSupport70_suffix_023, ridgeSupport70_suffix_024, ridgeSupport70_suffix_025, ridgeSupport70_suffix_026, ridgeSupport70_suffix_027, ridgeSupport70_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport70_000_mask, ridgeSupport70_001_mask, ridgeSupport70_002_mask, ridgeSupport70_003_mask, ridgeSupport70_004_mask, ridgeSupport70_005_mask, ridgeSupport70_006_mask, ridgeSupport70_007_mask, ridgeSupport70_008_mask, ridgeSupport70_009_mask, ridgeSupport70_010_mask, ridgeSupport70_011_mask, ridgeSupport70_012_mask, ridgeSupport70_013_mask, ridgeSupport70_014_mask, ridgeSupport70_015_mask, ridgeSupport70_016_mask, ridgeSupport70_017_mask, ridgeSupport70_018_mask, ridgeSupport70_019_mask, ridgeSupport70_020_mask, ridgeSupport70_021_mask, ridgeSupport70_022_mask, ridgeSupport70_023_mask, ridgeSupport70_024_mask, ridgeSupport70_025_mask, ridgeSupport70_026_mask, ridgeSupport70_027_mask]
    decide +kernel
  · rw [ridgeSupport70_eq]
    simp only [ridgeSupport70_suffix_000, ridgeSupport70_suffix_001, ridgeSupport70_suffix_002, ridgeSupport70_suffix_003, ridgeSupport70_suffix_004, ridgeSupport70_suffix_005, ridgeSupport70_suffix_006, ridgeSupport70_suffix_007, ridgeSupport70_suffix_008, ridgeSupport70_suffix_009, ridgeSupport70_suffix_010, ridgeSupport70_suffix_011, ridgeSupport70_suffix_012, ridgeSupport70_suffix_013, ridgeSupport70_suffix_014, ridgeSupport70_suffix_015, ridgeSupport70_suffix_016, ridgeSupport70_suffix_017, ridgeSupport70_suffix_018, ridgeSupport70_suffix_019, ridgeSupport70_suffix_020, ridgeSupport70_suffix_021, ridgeSupport70_suffix_022, ridgeSupport70_suffix_023, ridgeSupport70_suffix_024, ridgeSupport70_suffix_025, ridgeSupport70_suffix_026, ridgeSupport70_suffix_027, ridgeSupport70_suffix_028, List.all_append, List.all_nil, ridgeSupport70_000_checked, ridgeSupport70_001_checked, ridgeSupport70_002_checked, ridgeSupport70_003_checked, ridgeSupport70_004_checked, ridgeSupport70_005_checked, ridgeSupport70_006_checked, ridgeSupport70_007_checked, ridgeSupport70_008_checked, ridgeSupport70_009_checked, ridgeSupport70_010_checked, ridgeSupport70_011_checked, ridgeSupport70_012_checked, ridgeSupport70_013_checked, ridgeSupport70_014_checked, ridgeSupport70_015_checked, ridgeSupport70_016_checked, ridgeSupport70_017_checked, ridgeSupport70_018_checked, ridgeSupport70_019_checked, ridgeSupport70_020_checked, ridgeSupport70_021_checked, ridgeSupport70_022_checked, ridgeSupport70_023_checked, ridgeSupport70_024_checked, ridgeSupport70_025_checked, ridgeSupport70_026_checked, ridgeSupport70_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
