module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport268Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 268 028 15
cert_ridgeSupport_suffix_decode_2 268 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 268 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 268 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 268 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 268 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 268 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 268 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 268 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 268 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 268 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 268 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 268 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 268 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 268 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 268 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 268 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 268 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 268 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 268 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 268 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 268 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 268 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 268 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 268 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 268 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 268 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 268 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 268 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 268
theorem ridgeTest_large_268 : ridgeTest 268 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport268_eq]
    simp only [ridgeSupport268_suffix_000, ridgeSupport268_suffix_001, ridgeSupport268_suffix_002, ridgeSupport268_suffix_003, ridgeSupport268_suffix_004, ridgeSupport268_suffix_005, ridgeSupport268_suffix_006, ridgeSupport268_suffix_007, ridgeSupport268_suffix_008, ridgeSupport268_suffix_009, ridgeSupport268_suffix_010, ridgeSupport268_suffix_011, ridgeSupport268_suffix_012, ridgeSupport268_suffix_013, ridgeSupport268_suffix_014, ridgeSupport268_suffix_015, ridgeSupport268_suffix_016, ridgeSupport268_suffix_017, ridgeSupport268_suffix_018, ridgeSupport268_suffix_019, ridgeSupport268_suffix_020, ridgeSupport268_suffix_021, ridgeSupport268_suffix_022, ridgeSupport268_suffix_023, ridgeSupport268_suffix_024, ridgeSupport268_suffix_025, ridgeSupport268_suffix_026, ridgeSupport268_suffix_027, ridgeSupport268_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport268_000_mask, ridgeSupport268_001_mask, ridgeSupport268_002_mask, ridgeSupport268_003_mask, ridgeSupport268_004_mask, ridgeSupport268_005_mask, ridgeSupport268_006_mask, ridgeSupport268_007_mask, ridgeSupport268_008_mask, ridgeSupport268_009_mask, ridgeSupport268_010_mask, ridgeSupport268_011_mask, ridgeSupport268_012_mask, ridgeSupport268_013_mask, ridgeSupport268_014_mask, ridgeSupport268_015_mask, ridgeSupport268_016_mask, ridgeSupport268_017_mask, ridgeSupport268_018_mask, ridgeSupport268_019_mask, ridgeSupport268_020_mask, ridgeSupport268_021_mask, ridgeSupport268_022_mask, ridgeSupport268_023_mask, ridgeSupport268_024_mask, ridgeSupport268_025_mask, ridgeSupport268_026_mask, ridgeSupport268_027_mask]
    decide +kernel
  · rw [ridgeSupport268_eq]
    simp only [ridgeSupport268_suffix_000, ridgeSupport268_suffix_001, ridgeSupport268_suffix_002, ridgeSupport268_suffix_003, ridgeSupport268_suffix_004, ridgeSupport268_suffix_005, ridgeSupport268_suffix_006, ridgeSupport268_suffix_007, ridgeSupport268_suffix_008, ridgeSupport268_suffix_009, ridgeSupport268_suffix_010, ridgeSupport268_suffix_011, ridgeSupport268_suffix_012, ridgeSupport268_suffix_013, ridgeSupport268_suffix_014, ridgeSupport268_suffix_015, ridgeSupport268_suffix_016, ridgeSupport268_suffix_017, ridgeSupport268_suffix_018, ridgeSupport268_suffix_019, ridgeSupport268_suffix_020, ridgeSupport268_suffix_021, ridgeSupport268_suffix_022, ridgeSupport268_suffix_023, ridgeSupport268_suffix_024, ridgeSupport268_suffix_025, ridgeSupport268_suffix_026, ridgeSupport268_suffix_027, ridgeSupport268_suffix_028, List.all_append, List.all_nil, ridgeSupport268_000_checked, ridgeSupport268_001_checked, ridgeSupport268_002_checked, ridgeSupport268_003_checked, ridgeSupport268_004_checked, ridgeSupport268_005_checked, ridgeSupport268_006_checked, ridgeSupport268_007_checked, ridgeSupport268_008_checked, ridgeSupport268_009_checked, ridgeSupport268_010_checked, ridgeSupport268_011_checked, ridgeSupport268_012_checked, ridgeSupport268_013_checked, ridgeSupport268_014_checked, ridgeSupport268_015_checked, ridgeSupport268_016_checked, ridgeSupport268_017_checked, ridgeSupport268_018_checked, ridgeSupport268_019_checked, ridgeSupport268_020_checked, ridgeSupport268_021_checked, ridgeSupport268_022_checked, ridgeSupport268_023_checked, ridgeSupport268_024_checked, ridgeSupport268_025_checked, ridgeSupport268_026_checked, ridgeSupport268_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
