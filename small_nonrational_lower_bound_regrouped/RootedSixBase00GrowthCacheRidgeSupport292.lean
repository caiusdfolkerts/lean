module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport292Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 292 028 15
cert_ridgeSupport_suffix_decode_2 292 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 292 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 292 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 292 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 292 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 292 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 292 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 292 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 292 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 292 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 292 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 292 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 292 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 292 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 292 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 292 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 292 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 292 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 292 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 292 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 292 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 292 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 292 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 292 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 292 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 292 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 292 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 292 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 292
theorem ridgeTest_large_292 : ridgeTest 292 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport292_eq]
    simp only [ridgeSupport292_suffix_000, ridgeSupport292_suffix_001, ridgeSupport292_suffix_002, ridgeSupport292_suffix_003, ridgeSupport292_suffix_004, ridgeSupport292_suffix_005, ridgeSupport292_suffix_006, ridgeSupport292_suffix_007, ridgeSupport292_suffix_008, ridgeSupport292_suffix_009, ridgeSupport292_suffix_010, ridgeSupport292_suffix_011, ridgeSupport292_suffix_012, ridgeSupport292_suffix_013, ridgeSupport292_suffix_014, ridgeSupport292_suffix_015, ridgeSupport292_suffix_016, ridgeSupport292_suffix_017, ridgeSupport292_suffix_018, ridgeSupport292_suffix_019, ridgeSupport292_suffix_020, ridgeSupport292_suffix_021, ridgeSupport292_suffix_022, ridgeSupport292_suffix_023, ridgeSupport292_suffix_024, ridgeSupport292_suffix_025, ridgeSupport292_suffix_026, ridgeSupport292_suffix_027, ridgeSupport292_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport292_000_mask, ridgeSupport292_001_mask, ridgeSupport292_002_mask, ridgeSupport292_003_mask, ridgeSupport292_004_mask, ridgeSupport292_005_mask, ridgeSupport292_006_mask, ridgeSupport292_007_mask, ridgeSupport292_008_mask, ridgeSupport292_009_mask, ridgeSupport292_010_mask, ridgeSupport292_011_mask, ridgeSupport292_012_mask, ridgeSupport292_013_mask, ridgeSupport292_014_mask, ridgeSupport292_015_mask, ridgeSupport292_016_mask, ridgeSupport292_017_mask, ridgeSupport292_018_mask, ridgeSupport292_019_mask, ridgeSupport292_020_mask, ridgeSupport292_021_mask, ridgeSupport292_022_mask, ridgeSupport292_023_mask, ridgeSupport292_024_mask, ridgeSupport292_025_mask, ridgeSupport292_026_mask, ridgeSupport292_027_mask]
    decide +kernel
  · rw [ridgeSupport292_eq]
    simp only [ridgeSupport292_suffix_000, ridgeSupport292_suffix_001, ridgeSupport292_suffix_002, ridgeSupport292_suffix_003, ridgeSupport292_suffix_004, ridgeSupport292_suffix_005, ridgeSupport292_suffix_006, ridgeSupport292_suffix_007, ridgeSupport292_suffix_008, ridgeSupport292_suffix_009, ridgeSupport292_suffix_010, ridgeSupport292_suffix_011, ridgeSupport292_suffix_012, ridgeSupport292_suffix_013, ridgeSupport292_suffix_014, ridgeSupport292_suffix_015, ridgeSupport292_suffix_016, ridgeSupport292_suffix_017, ridgeSupport292_suffix_018, ridgeSupport292_suffix_019, ridgeSupport292_suffix_020, ridgeSupport292_suffix_021, ridgeSupport292_suffix_022, ridgeSupport292_suffix_023, ridgeSupport292_suffix_024, ridgeSupport292_suffix_025, ridgeSupport292_suffix_026, ridgeSupport292_suffix_027, ridgeSupport292_suffix_028, List.all_append, List.all_nil, ridgeSupport292_000_checked, ridgeSupport292_001_checked, ridgeSupport292_002_checked, ridgeSupport292_003_checked, ridgeSupport292_004_checked, ridgeSupport292_005_checked, ridgeSupport292_006_checked, ridgeSupport292_007_checked, ridgeSupport292_008_checked, ridgeSupport292_009_checked, ridgeSupport292_010_checked, ridgeSupport292_011_checked, ridgeSupport292_012_checked, ridgeSupport292_013_checked, ridgeSupport292_014_checked, ridgeSupport292_015_checked, ridgeSupport292_016_checked, ridgeSupport292_017_checked, ridgeSupport292_018_checked, ridgeSupport292_019_checked, ridgeSupport292_020_checked, ridgeSupport292_021_checked, ridgeSupport292_022_checked, ridgeSupport292_023_checked, ridgeSupport292_024_checked, ridgeSupport292_025_checked, ridgeSupport292_026_checked, ridgeSupport292_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
