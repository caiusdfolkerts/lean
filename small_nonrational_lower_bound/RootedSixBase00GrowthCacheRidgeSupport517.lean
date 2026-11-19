module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport517Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 517 028 15
cert_ridgeSupport_suffix_decode_2 517 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 517 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 517 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 517 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 517 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 517 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 517 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 517 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 517 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 517 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 517 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 517 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 517 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 517 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 517 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 517 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 517 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 517 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 517 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 517 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 517 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 517 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 517 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 517 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 517 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 517 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 517 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 517 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 517
theorem ridgeTest_large_517 : ridgeTest 517 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport517_eq]
    simp only [ridgeSupport517_suffix_000, ridgeSupport517_suffix_001, ridgeSupport517_suffix_002, ridgeSupport517_suffix_003, ridgeSupport517_suffix_004, ridgeSupport517_suffix_005, ridgeSupport517_suffix_006, ridgeSupport517_suffix_007, ridgeSupport517_suffix_008, ridgeSupport517_suffix_009, ridgeSupport517_suffix_010, ridgeSupport517_suffix_011, ridgeSupport517_suffix_012, ridgeSupport517_suffix_013, ridgeSupport517_suffix_014, ridgeSupport517_suffix_015, ridgeSupport517_suffix_016, ridgeSupport517_suffix_017, ridgeSupport517_suffix_018, ridgeSupport517_suffix_019, ridgeSupport517_suffix_020, ridgeSupport517_suffix_021, ridgeSupport517_suffix_022, ridgeSupport517_suffix_023, ridgeSupport517_suffix_024, ridgeSupport517_suffix_025, ridgeSupport517_suffix_026, ridgeSupport517_suffix_027, ridgeSupport517_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport517_000_mask, ridgeSupport517_001_mask, ridgeSupport517_002_mask, ridgeSupport517_003_mask, ridgeSupport517_004_mask, ridgeSupport517_005_mask, ridgeSupport517_006_mask, ridgeSupport517_007_mask, ridgeSupport517_008_mask, ridgeSupport517_009_mask, ridgeSupport517_010_mask, ridgeSupport517_011_mask, ridgeSupport517_012_mask, ridgeSupport517_013_mask, ridgeSupport517_014_mask, ridgeSupport517_015_mask, ridgeSupport517_016_mask, ridgeSupport517_017_mask, ridgeSupport517_018_mask, ridgeSupport517_019_mask, ridgeSupport517_020_mask, ridgeSupport517_021_mask, ridgeSupport517_022_mask, ridgeSupport517_023_mask, ridgeSupport517_024_mask, ridgeSupport517_025_mask, ridgeSupport517_026_mask, ridgeSupport517_027_mask]
    decide +kernel
  · rw [ridgeSupport517_eq]
    simp only [ridgeSupport517_suffix_000, ridgeSupport517_suffix_001, ridgeSupport517_suffix_002, ridgeSupport517_suffix_003, ridgeSupport517_suffix_004, ridgeSupport517_suffix_005, ridgeSupport517_suffix_006, ridgeSupport517_suffix_007, ridgeSupport517_suffix_008, ridgeSupport517_suffix_009, ridgeSupport517_suffix_010, ridgeSupport517_suffix_011, ridgeSupport517_suffix_012, ridgeSupport517_suffix_013, ridgeSupport517_suffix_014, ridgeSupport517_suffix_015, ridgeSupport517_suffix_016, ridgeSupport517_suffix_017, ridgeSupport517_suffix_018, ridgeSupport517_suffix_019, ridgeSupport517_suffix_020, ridgeSupport517_suffix_021, ridgeSupport517_suffix_022, ridgeSupport517_suffix_023, ridgeSupport517_suffix_024, ridgeSupport517_suffix_025, ridgeSupport517_suffix_026, ridgeSupport517_suffix_027, ridgeSupport517_suffix_028, List.all_append, List.all_nil, ridgeSupport517_000_checked, ridgeSupport517_001_checked, ridgeSupport517_002_checked, ridgeSupport517_003_checked, ridgeSupport517_004_checked, ridgeSupport517_005_checked, ridgeSupport517_006_checked, ridgeSupport517_007_checked, ridgeSupport517_008_checked, ridgeSupport517_009_checked, ridgeSupport517_010_checked, ridgeSupport517_011_checked, ridgeSupport517_012_checked, ridgeSupport517_013_checked, ridgeSupport517_014_checked, ridgeSupport517_015_checked, ridgeSupport517_016_checked, ridgeSupport517_017_checked, ridgeSupport517_018_checked, ridgeSupport517_019_checked, ridgeSupport517_020_checked, ridgeSupport517_021_checked, ridgeSupport517_022_checked, ridgeSupport517_023_checked, ridgeSupport517_024_checked, ridgeSupport517_025_checked, ridgeSupport517_026_checked, ridgeSupport517_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
