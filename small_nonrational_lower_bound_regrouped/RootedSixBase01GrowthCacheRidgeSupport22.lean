module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport22Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 22 034 14
cert_ridgeSupport_suffix_decode_2 22 033 14 5 5 034 034 0
cert_ridgeSupport_suffix_decode_2 22 032 14 37 32 034 033 5
cert_ridgeSupport_suffix_decode_2 22 031 14 69 32 034 032 37
cert_ridgeSupport_suffix_decode_2 22 030 14 101 32 034 031 69
cert_ridgeSupport_suffix_decode_2 22 029 14 133 32 034 030 101
cert_ridgeSupport_suffix_decode_2 22 028 14 165 32 034 029 133
cert_ridgeSupport_suffix_decode_2 22 027 14 197 32 034 028 165
cert_ridgeSupport_suffix_decode_2 22 026 14 229 32 034 027 197
cert_ridgeSupport_suffix_decode_2 22 025 14 261 32 034 026 229
cert_ridgeSupport_suffix_decode_2 22 024 14 293 32 034 025 261
cert_ridgeSupport_suffix_decode_2 22 023 14 325 32 034 024 293
cert_ridgeSupport_suffix_decode_2 22 022 14 357 32 034 023 325
cert_ridgeSupport_suffix_decode_2 22 021 14 389 32 034 022 357
cert_ridgeSupport_suffix_decode_2 22 020 14 421 32 034 021 389
cert_ridgeSupport_suffix_decode_2 22 019 14 453 32 034 020 421
cert_ridgeSupport_suffix_decode_2 22 018 14 485 32 034 019 453
cert_ridgeSupport_suffix_decode_2 22 017 14 517 32 034 018 485
cert_ridgeSupport_suffix_decode_2 22 016 14 549 32 034 017 517
cert_ridgeSupport_suffix_decode_2 22 015 14 581 32 034 016 549
cert_ridgeSupport_suffix_decode_2 22 014 14 613 32 034 015 581
cert_ridgeSupport_suffix_decode_2 22 013 14 645 32 034 014 613
cert_ridgeSupport_suffix_decode_2 22 012 14 677 32 034 013 645
cert_ridgeSupport_suffix_decode_2 22 011 14 709 32 034 012 677
cert_ridgeSupport_suffix_decode_2 22 010 14 741 32 034 011 709
cert_ridgeSupport_suffix_decode_2 22 009 14 773 32 034 010 741
cert_ridgeSupport_suffix_decode_2 22 008 14 805 32 034 009 773
cert_ridgeSupport_suffix_decode_2 22 007 14 837 32 034 008 805
cert_ridgeSupport_suffix_decode_2 22 006 14 869 32 034 007 837
cert_ridgeSupport_suffix_decode_2 22 005 14 901 32 034 006 869
cert_ridgeSupport_suffix_decode_2 22 004 14 933 32 034 005 901
cert_ridgeSupport_suffix_decode_2 22 003 14 965 32 034 004 933
cert_ridgeSupport_suffix_decode_2 22 002 14 997 32 034 003 965
cert_ridgeSupport_suffix_decode_2 22 001 14 1029 32 034 002 997
cert_ridgeSupport_suffix_decode_2 22 000 14 1061 32 034 001 1029
cert_ridgeSupport_eq_3 22
theorem ridgeTest_large_22 : ridgeTest 22 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport22_eq]
    simp only [ridgeSupport22_suffix_000, ridgeSupport22_suffix_001, ridgeSupport22_suffix_002, ridgeSupport22_suffix_003, ridgeSupport22_suffix_004, ridgeSupport22_suffix_005, ridgeSupport22_suffix_006, ridgeSupport22_suffix_007, ridgeSupport22_suffix_008, ridgeSupport22_suffix_009, ridgeSupport22_suffix_010, ridgeSupport22_suffix_011, ridgeSupport22_suffix_012, ridgeSupport22_suffix_013, ridgeSupport22_suffix_014, ridgeSupport22_suffix_015, ridgeSupport22_suffix_016, ridgeSupport22_suffix_017, ridgeSupport22_suffix_018, ridgeSupport22_suffix_019, ridgeSupport22_suffix_020, ridgeSupport22_suffix_021, ridgeSupport22_suffix_022, ridgeSupport22_suffix_023, ridgeSupport22_suffix_024, ridgeSupport22_suffix_025, ridgeSupport22_suffix_026, ridgeSupport22_suffix_027, ridgeSupport22_suffix_028, ridgeSupport22_suffix_029, ridgeSupport22_suffix_030, ridgeSupport22_suffix_031, ridgeSupport22_suffix_032, ridgeSupport22_suffix_033, ridgeSupport22_suffix_034, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport22_000_mask, ridgeSupport22_001_mask, ridgeSupport22_002_mask, ridgeSupport22_003_mask, ridgeSupport22_004_mask, ridgeSupport22_005_mask, ridgeSupport22_006_mask, ridgeSupport22_007_mask, ridgeSupport22_008_mask, ridgeSupport22_009_mask, ridgeSupport22_010_mask, ridgeSupport22_011_mask, ridgeSupport22_012_mask, ridgeSupport22_013_mask, ridgeSupport22_014_mask, ridgeSupport22_015_mask, ridgeSupport22_016_mask, ridgeSupport22_017_mask, ridgeSupport22_018_mask, ridgeSupport22_019_mask, ridgeSupport22_020_mask, ridgeSupport22_021_mask, ridgeSupport22_022_mask, ridgeSupport22_023_mask, ridgeSupport22_024_mask, ridgeSupport22_025_mask, ridgeSupport22_026_mask, ridgeSupport22_027_mask, ridgeSupport22_028_mask, ridgeSupport22_029_mask, ridgeSupport22_030_mask, ridgeSupport22_031_mask, ridgeSupport22_032_mask, ridgeSupport22_033_mask]
    decide +kernel
  · rw [ridgeSupport22_eq]
    simp only [ridgeSupport22_suffix_000, ridgeSupport22_suffix_001, ridgeSupport22_suffix_002, ridgeSupport22_suffix_003, ridgeSupport22_suffix_004, ridgeSupport22_suffix_005, ridgeSupport22_suffix_006, ridgeSupport22_suffix_007, ridgeSupport22_suffix_008, ridgeSupport22_suffix_009, ridgeSupport22_suffix_010, ridgeSupport22_suffix_011, ridgeSupport22_suffix_012, ridgeSupport22_suffix_013, ridgeSupport22_suffix_014, ridgeSupport22_suffix_015, ridgeSupport22_suffix_016, ridgeSupport22_suffix_017, ridgeSupport22_suffix_018, ridgeSupport22_suffix_019, ridgeSupport22_suffix_020, ridgeSupport22_suffix_021, ridgeSupport22_suffix_022, ridgeSupport22_suffix_023, ridgeSupport22_suffix_024, ridgeSupport22_suffix_025, ridgeSupport22_suffix_026, ridgeSupport22_suffix_027, ridgeSupport22_suffix_028, ridgeSupport22_suffix_029, ridgeSupport22_suffix_030, ridgeSupport22_suffix_031, ridgeSupport22_suffix_032, ridgeSupport22_suffix_033, ridgeSupport22_suffix_034, List.all_append, List.all_nil, ridgeSupport22_000_checked, ridgeSupport22_001_checked, ridgeSupport22_002_checked, ridgeSupport22_003_checked, ridgeSupport22_004_checked, ridgeSupport22_005_checked, ridgeSupport22_006_checked, ridgeSupport22_007_checked, ridgeSupport22_008_checked, ridgeSupport22_009_checked, ridgeSupport22_010_checked, ridgeSupport22_011_checked, ridgeSupport22_012_checked, ridgeSupport22_013_checked, ridgeSupport22_014_checked, ridgeSupport22_015_checked, ridgeSupport22_016_checked, ridgeSupport22_017_checked, ridgeSupport22_018_checked, ridgeSupport22_019_checked, ridgeSupport22_020_checked, ridgeSupport22_021_checked, ridgeSupport22_022_checked, ridgeSupport22_023_checked, ridgeSupport22_024_checked, ridgeSupport22_025_checked, ridgeSupport22_026_checked, ridgeSupport22_027_checked, ridgeSupport22_028_checked, ridgeSupport22_029_checked, ridgeSupport22_030_checked, ridgeSupport22_031_checked, ridgeSupport22_032_checked, ridgeSupport22_033_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
