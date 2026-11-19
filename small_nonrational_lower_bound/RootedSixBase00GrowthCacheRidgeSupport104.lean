module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport104Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 104 028 15
cert_ridgeSupport_suffix_decode_2 104 027 15 5 5 028 028 0
cert_ridgeSupport_suffix_decode_2 104 026 15 37 32 028 027 5
cert_ridgeSupport_suffix_decode_2 104 025 15 69 32 028 026 37
cert_ridgeSupport_suffix_decode_2 104 024 15 101 32 028 025 69
cert_ridgeSupport_suffix_decode_2 104 023 15 133 32 028 024 101
cert_ridgeSupport_suffix_decode_2 104 022 15 165 32 028 023 133
cert_ridgeSupport_suffix_decode_2 104 021 15 197 32 028 022 165
cert_ridgeSupport_suffix_decode_2 104 020 15 229 32 028 021 197
cert_ridgeSupport_suffix_decode_2 104 019 15 261 32 028 020 229
cert_ridgeSupport_suffix_decode_2 104 018 15 293 32 028 019 261
cert_ridgeSupport_suffix_decode_2 104 017 15 325 32 028 018 293
cert_ridgeSupport_suffix_decode_2 104 016 15 357 32 028 017 325
cert_ridgeSupport_suffix_decode_2 104 015 15 389 32 028 016 357
cert_ridgeSupport_suffix_decode_2 104 014 15 421 32 028 015 389
cert_ridgeSupport_suffix_decode_2 104 013 15 453 32 028 014 421
cert_ridgeSupport_suffix_decode_2 104 012 15 485 32 028 013 453
cert_ridgeSupport_suffix_decode_2 104 011 15 517 32 028 012 485
cert_ridgeSupport_suffix_decode_2 104 010 15 549 32 028 011 517
cert_ridgeSupport_suffix_decode_2 104 009 15 581 32 028 010 549
cert_ridgeSupport_suffix_decode_2 104 008 15 613 32 028 009 581
cert_ridgeSupport_suffix_decode_2 104 007 15 645 32 028 008 613
cert_ridgeSupport_suffix_decode_2 104 006 15 677 32 028 007 645
cert_ridgeSupport_suffix_decode_2 104 005 15 709 32 028 006 677
cert_ridgeSupport_suffix_decode_2 104 004 15 741 32 028 005 709
cert_ridgeSupport_suffix_decode_2 104 003 15 773 32 028 004 741
cert_ridgeSupport_suffix_decode_2 104 002 15 805 32 028 003 773
cert_ridgeSupport_suffix_decode_2 104 001 15 837 32 028 002 805
cert_ridgeSupport_suffix_decode_2 104 000 15 869 32 028 001 837
cert_ridgeSupport_eq_3 104
theorem ridgeTest_large_104 : ridgeTest 104 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport104_eq]
    simp only [ridgeSupport104_suffix_000, ridgeSupport104_suffix_001, ridgeSupport104_suffix_002, ridgeSupport104_suffix_003, ridgeSupport104_suffix_004, ridgeSupport104_suffix_005, ridgeSupport104_suffix_006, ridgeSupport104_suffix_007, ridgeSupport104_suffix_008, ridgeSupport104_suffix_009, ridgeSupport104_suffix_010, ridgeSupport104_suffix_011, ridgeSupport104_suffix_012, ridgeSupport104_suffix_013, ridgeSupport104_suffix_014, ridgeSupport104_suffix_015, ridgeSupport104_suffix_016, ridgeSupport104_suffix_017, ridgeSupport104_suffix_018, ridgeSupport104_suffix_019, ridgeSupport104_suffix_020, ridgeSupport104_suffix_021, ridgeSupport104_suffix_022, ridgeSupport104_suffix_023, ridgeSupport104_suffix_024, ridgeSupport104_suffix_025, ridgeSupport104_suffix_026, ridgeSupport104_suffix_027, ridgeSupport104_suffix_028, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport104_000_mask, ridgeSupport104_001_mask, ridgeSupport104_002_mask, ridgeSupport104_003_mask, ridgeSupport104_004_mask, ridgeSupport104_005_mask, ridgeSupport104_006_mask, ridgeSupport104_007_mask, ridgeSupport104_008_mask, ridgeSupport104_009_mask, ridgeSupport104_010_mask, ridgeSupport104_011_mask, ridgeSupport104_012_mask, ridgeSupport104_013_mask, ridgeSupport104_014_mask, ridgeSupport104_015_mask, ridgeSupport104_016_mask, ridgeSupport104_017_mask, ridgeSupport104_018_mask, ridgeSupport104_019_mask, ridgeSupport104_020_mask, ridgeSupport104_021_mask, ridgeSupport104_022_mask, ridgeSupport104_023_mask, ridgeSupport104_024_mask, ridgeSupport104_025_mask, ridgeSupport104_026_mask, ridgeSupport104_027_mask]
    decide +kernel
  · rw [ridgeSupport104_eq]
    simp only [ridgeSupport104_suffix_000, ridgeSupport104_suffix_001, ridgeSupport104_suffix_002, ridgeSupport104_suffix_003, ridgeSupport104_suffix_004, ridgeSupport104_suffix_005, ridgeSupport104_suffix_006, ridgeSupport104_suffix_007, ridgeSupport104_suffix_008, ridgeSupport104_suffix_009, ridgeSupport104_suffix_010, ridgeSupport104_suffix_011, ridgeSupport104_suffix_012, ridgeSupport104_suffix_013, ridgeSupport104_suffix_014, ridgeSupport104_suffix_015, ridgeSupport104_suffix_016, ridgeSupport104_suffix_017, ridgeSupport104_suffix_018, ridgeSupport104_suffix_019, ridgeSupport104_suffix_020, ridgeSupport104_suffix_021, ridgeSupport104_suffix_022, ridgeSupport104_suffix_023, ridgeSupport104_suffix_024, ridgeSupport104_suffix_025, ridgeSupport104_suffix_026, ridgeSupport104_suffix_027, ridgeSupport104_suffix_028, List.all_append, List.all_nil, ridgeSupport104_000_checked, ridgeSupport104_001_checked, ridgeSupport104_002_checked, ridgeSupport104_003_checked, ridgeSupport104_004_checked, ridgeSupport104_005_checked, ridgeSupport104_006_checked, ridgeSupport104_007_checked, ridgeSupport104_008_checked, ridgeSupport104_009_checked, ridgeSupport104_010_checked, ridgeSupport104_011_checked, ridgeSupport104_012_checked, ridgeSupport104_013_checked, ridgeSupport104_014_checked, ridgeSupport104_015_checked, ridgeSupport104_016_checked, ridgeSupport104_017_checked, ridgeSupport104_018_checked, ridgeSupport104_019_checked, ridgeSupport104_020_checked, ridgeSupport104_021_checked, ridgeSupport104_022_checked, ridgeSupport104_023_checked, ridgeSupport104_024_checked, ridgeSupport104_025_checked, ridgeSupport104_026_checked, ridgeSupport104_027_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
