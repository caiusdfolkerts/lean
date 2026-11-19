module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport11Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 11 034 14
cert_ridgeSupport_suffix_decode_2 11 033 14 5 5 034 034 0
cert_ridgeSupport_suffix_decode_2 11 032 14 37 32 034 033 5
cert_ridgeSupport_suffix_decode_2 11 031 14 69 32 034 032 37
cert_ridgeSupport_suffix_decode_2 11 030 14 101 32 034 031 69
cert_ridgeSupport_suffix_decode_2 11 029 14 133 32 034 030 101
cert_ridgeSupport_suffix_decode_2 11 028 14 165 32 034 029 133
cert_ridgeSupport_suffix_decode_2 11 027 14 197 32 034 028 165
cert_ridgeSupport_suffix_decode_2 11 026 14 229 32 034 027 197
cert_ridgeSupport_suffix_decode_2 11 025 14 261 32 034 026 229
cert_ridgeSupport_suffix_decode_2 11 024 14 293 32 034 025 261
cert_ridgeSupport_suffix_decode_2 11 023 14 325 32 034 024 293
cert_ridgeSupport_suffix_decode_2 11 022 14 357 32 034 023 325
cert_ridgeSupport_suffix_decode_2 11 021 14 389 32 034 022 357
cert_ridgeSupport_suffix_decode_2 11 020 14 421 32 034 021 389
cert_ridgeSupport_suffix_decode_2 11 019 14 453 32 034 020 421
cert_ridgeSupport_suffix_decode_2 11 018 14 485 32 034 019 453
cert_ridgeSupport_suffix_decode_2 11 017 14 517 32 034 018 485
cert_ridgeSupport_suffix_decode_2 11 016 14 549 32 034 017 517
cert_ridgeSupport_suffix_decode_2 11 015 14 581 32 034 016 549
cert_ridgeSupport_suffix_decode_2 11 014 14 613 32 034 015 581
cert_ridgeSupport_suffix_decode_2 11 013 14 645 32 034 014 613
cert_ridgeSupport_suffix_decode_2 11 012 14 677 32 034 013 645
cert_ridgeSupport_suffix_decode_2 11 011 14 709 32 034 012 677
cert_ridgeSupport_suffix_decode_2 11 010 14 741 32 034 011 709
cert_ridgeSupport_suffix_decode_2 11 009 14 773 32 034 010 741
cert_ridgeSupport_suffix_decode_2 11 008 14 805 32 034 009 773
cert_ridgeSupport_suffix_decode_2 11 007 14 837 32 034 008 805
cert_ridgeSupport_suffix_decode_2 11 006 14 869 32 034 007 837
cert_ridgeSupport_suffix_decode_2 11 005 14 901 32 034 006 869
cert_ridgeSupport_suffix_decode_2 11 004 14 933 32 034 005 901
cert_ridgeSupport_suffix_decode_2 11 003 14 965 32 034 004 933
cert_ridgeSupport_suffix_decode_2 11 002 14 997 32 034 003 965
cert_ridgeSupport_suffix_decode_2 11 001 14 1029 32 034 002 997
cert_ridgeSupport_suffix_decode_2 11 000 14 1061 32 034 001 1029
cert_ridgeSupport_eq_3 11
theorem ridgeTest_large_11 : ridgeTest 11 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, ridgeSupport11_suffix_012, ridgeSupport11_suffix_013, ridgeSupport11_suffix_014, ridgeSupport11_suffix_015, ridgeSupport11_suffix_016, ridgeSupport11_suffix_017, ridgeSupport11_suffix_018, ridgeSupport11_suffix_019, ridgeSupport11_suffix_020, ridgeSupport11_suffix_021, ridgeSupport11_suffix_022, ridgeSupport11_suffix_023, ridgeSupport11_suffix_024, ridgeSupport11_suffix_025, ridgeSupport11_suffix_026, ridgeSupport11_suffix_027, ridgeSupport11_suffix_028, ridgeSupport11_suffix_029, ridgeSupport11_suffix_030, ridgeSupport11_suffix_031, ridgeSupport11_suffix_032, ridgeSupport11_suffix_033, ridgeSupport11_suffix_034, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport11_000_mask, ridgeSupport11_001_mask, ridgeSupport11_002_mask, ridgeSupport11_003_mask, ridgeSupport11_004_mask, ridgeSupport11_005_mask, ridgeSupport11_006_mask, ridgeSupport11_007_mask, ridgeSupport11_008_mask, ridgeSupport11_009_mask, ridgeSupport11_010_mask, ridgeSupport11_011_mask, ridgeSupport11_012_mask, ridgeSupport11_013_mask, ridgeSupport11_014_mask, ridgeSupport11_015_mask, ridgeSupport11_016_mask, ridgeSupport11_017_mask, ridgeSupport11_018_mask, ridgeSupport11_019_mask, ridgeSupport11_020_mask, ridgeSupport11_021_mask, ridgeSupport11_022_mask, ridgeSupport11_023_mask, ridgeSupport11_024_mask, ridgeSupport11_025_mask, ridgeSupport11_026_mask, ridgeSupport11_027_mask, ridgeSupport11_028_mask, ridgeSupport11_029_mask, ridgeSupport11_030_mask, ridgeSupport11_031_mask, ridgeSupport11_032_mask, ridgeSupport11_033_mask]
    decide +kernel
  · rw [ridgeSupport11_eq]
    simp only [ridgeSupport11_suffix_000, ridgeSupport11_suffix_001, ridgeSupport11_suffix_002, ridgeSupport11_suffix_003, ridgeSupport11_suffix_004, ridgeSupport11_suffix_005, ridgeSupport11_suffix_006, ridgeSupport11_suffix_007, ridgeSupport11_suffix_008, ridgeSupport11_suffix_009, ridgeSupport11_suffix_010, ridgeSupport11_suffix_011, ridgeSupport11_suffix_012, ridgeSupport11_suffix_013, ridgeSupport11_suffix_014, ridgeSupport11_suffix_015, ridgeSupport11_suffix_016, ridgeSupport11_suffix_017, ridgeSupport11_suffix_018, ridgeSupport11_suffix_019, ridgeSupport11_suffix_020, ridgeSupport11_suffix_021, ridgeSupport11_suffix_022, ridgeSupport11_suffix_023, ridgeSupport11_suffix_024, ridgeSupport11_suffix_025, ridgeSupport11_suffix_026, ridgeSupport11_suffix_027, ridgeSupport11_suffix_028, ridgeSupport11_suffix_029, ridgeSupport11_suffix_030, ridgeSupport11_suffix_031, ridgeSupport11_suffix_032, ridgeSupport11_suffix_033, ridgeSupport11_suffix_034, List.all_append, List.all_nil, ridgeSupport11_000_checked, ridgeSupport11_001_checked, ridgeSupport11_002_checked, ridgeSupport11_003_checked, ridgeSupport11_004_checked, ridgeSupport11_005_checked, ridgeSupport11_006_checked, ridgeSupport11_007_checked, ridgeSupport11_008_checked, ridgeSupport11_009_checked, ridgeSupport11_010_checked, ridgeSupport11_011_checked, ridgeSupport11_012_checked, ridgeSupport11_013_checked, ridgeSupport11_014_checked, ridgeSupport11_015_checked, ridgeSupport11_016_checked, ridgeSupport11_017_checked, ridgeSupport11_018_checked, ridgeSupport11_019_checked, ridgeSupport11_020_checked, ridgeSupport11_021_checked, ridgeSupport11_022_checked, ridgeSupport11_023_checked, ridgeSupport11_024_checked, ridgeSupport11_025_checked, ridgeSupport11_026_checked, ridgeSupport11_027_checked, ridgeSupport11_028_checked, ridgeSupport11_029_checked, ridgeSupport11_030_checked, ridgeSupport11_031_checked, ridgeSupport11_032_checked, ridgeSupport11_033_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
