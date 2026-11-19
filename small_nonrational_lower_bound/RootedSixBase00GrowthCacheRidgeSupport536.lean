module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport536Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 536 028 15
cert_ridgeSupport_suffix_decode_2 536 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 536 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 536 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 536 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 536 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 536 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 536 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 536 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 536 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 536 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 536 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 536 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 536 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 536 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 536 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 536 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 536 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 536 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 536 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 536 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 536 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 536 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 536 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 536 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 536 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 536 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 536 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 536 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 536
theorem ridgeTest_large_536 : ridgeTest 536 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport536_eq]
    simp only [ridgeSupport536_suffix_000, ridgeSupport536_suffix_001, ridgeSupport536_suffix_002, ridgeSupport536_suffix_003, ridgeSupport536_suffix_004, ridgeSupport536_suffix_005, ridgeSupport536_suffix_006, ridgeSupport536_suffix_007, ridgeSupport536_suffix_008, ridgeSupport536_suffix_009, ridgeSupport536_suffix_010, ridgeSupport536_suffix_011, ridgeSupport536_suffix_012, ridgeSupport536_suffix_013, ridgeSupport536_suffix_014, ridgeSupport536_suffix_015, ridgeSupport536_suffix_016, ridgeSupport536_suffix_017, ridgeSupport536_suffix_018, ridgeSupport536_suffix_019, ridgeSupport536_suffix_020, ridgeSupport536_suffix_021, ridgeSupport536_suffix_022, ridgeSupport536_suffix_023, ridgeSupport536_suffix_024, ridgeSupport536_suffix_025, ridgeSupport536_suffix_026, ridgeSupport536_suffix_027, ridgeSupport536_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport536_000_mask, ridgeSupport536_001_mask, ridgeSupport536_002_mask, ridgeSupport536_003_mask, ridgeSupport536_004_mask, ridgeSupport536_005_mask, ridgeSupport536_006_mask, ridgeSupport536_007_mask, ridgeSupport536_008_mask, ridgeSupport536_009_mask, ridgeSupport536_010_mask, ridgeSupport536_011_mask, ridgeSupport536_012_mask, ridgeSupport536_013_mask, ridgeSupport536_014_mask, ridgeSupport536_015_mask, ridgeSupport536_016_mask, ridgeSupport536_017_mask, ridgeSupport536_018_mask, ridgeSupport536_019_mask, ridgeSupport536_020_mask, ridgeSupport536_021_mask, ridgeSupport536_022_mask, ridgeSupport536_023_mask, ridgeSupport536_024_mask, ridgeSupport536_025_mask, ridgeSupport536_026_mask, ridgeSupport536_027_mask]
    decide +kernel
  · rw [ridgeSupport536_eq]
    simp only [ridgeSupport536_suffix_000, ridgeSupport536_suffix_001, ridgeSupport536_suffix_002, ridgeSupport536_suffix_003, ridgeSupport536_suffix_004, ridgeSupport536_suffix_005, ridgeSupport536_suffix_006, ridgeSupport536_suffix_007, ridgeSupport536_suffix_008, ridgeSupport536_suffix_009, ridgeSupport536_suffix_010, ridgeSupport536_suffix_011, ridgeSupport536_suffix_012, ridgeSupport536_suffix_013, ridgeSupport536_suffix_014, ridgeSupport536_suffix_015, ridgeSupport536_suffix_016, ridgeSupport536_suffix_017, ridgeSupport536_suffix_018, ridgeSupport536_suffix_019, ridgeSupport536_suffix_020, ridgeSupport536_suffix_021, ridgeSupport536_suffix_022, ridgeSupport536_suffix_023, ridgeSupport536_suffix_024, ridgeSupport536_suffix_025, ridgeSupport536_suffix_026, ridgeSupport536_suffix_027, ridgeSupport536_suffix_028, List.all_append, List.all_nil, ridgeSupport536_000_checked, ridgeSupport536_001_checked, ridgeSupport536_002_checked, ridgeSupport536_003_checked, ridgeSupport536_004_checked, ridgeSupport536_005_checked, ridgeSupport536_006_checked, ridgeSupport536_007_checked, ridgeSupport536_008_checked, ridgeSupport536_009_checked, ridgeSupport536_010_checked, ridgeSupport536_011_checked, ridgeSupport536_012_checked, ridgeSupport536_013_checked, ridgeSupport536_014_checked, ridgeSupport536_015_checked, ridgeSupport536_016_checked, ridgeSupport536_017_checked, ridgeSupport536_018_checked, ridgeSupport536_019_checked, ridgeSupport536_020_checked, ridgeSupport536_021_checked, ridgeSupport536_022_checked, ridgeSupport536_023_checked, ridgeSupport536_024_checked, ridgeSupport536_025_checked, ridgeSupport536_026_checked, ridgeSupport536_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
