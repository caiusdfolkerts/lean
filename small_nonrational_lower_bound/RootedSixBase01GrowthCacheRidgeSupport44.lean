module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport44Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 44 034 14
cert_ridgeSupport_suffix_decode_2 44 033 14 5 5 034 034 0
cert_ridgeSupport_suffix_decode_2 44 032 14 37 32 034 033 5
cert_ridgeSupport_suffix_decode_2 44 031 14 69 32 034 032 37
cert_ridgeSupport_suffix_decode_2 44 030 14 101 32 034 031 69
cert_ridgeSupport_suffix_decode_2 44 029 14 133 32 034 030 101
cert_ridgeSupport_suffix_decode_2 44 028 14 165 32 034 029 133
cert_ridgeSupport_suffix_decode_2 44 027 14 197 32 034 028 165
cert_ridgeSupport_suffix_decode_2 44 026 14 229 32 034 027 197
cert_ridgeSupport_suffix_decode_2 44 025 14 261 32 034 026 229
cert_ridgeSupport_suffix_decode_2 44 024 14 293 32 034 025 261
cert_ridgeSupport_suffix_decode_2 44 023 14 325 32 034 024 293
cert_ridgeSupport_suffix_decode_2 44 022 14 357 32 034 023 325
cert_ridgeSupport_suffix_decode_2 44 021 14 389 32 034 022 357
cert_ridgeSupport_suffix_decode_2 44 020 14 421 32 034 021 389
cert_ridgeSupport_suffix_decode_2 44 019 14 453 32 034 020 421
cert_ridgeSupport_suffix_decode_2 44 018 14 485 32 034 019 453
cert_ridgeSupport_suffix_decode_2 44 017 14 517 32 034 018 485
cert_ridgeSupport_suffix_decode_2 44 016 14 549 32 034 017 517
cert_ridgeSupport_suffix_decode_2 44 015 14 581 32 034 016 549
cert_ridgeSupport_suffix_decode_2 44 014 14 613 32 034 015 581
cert_ridgeSupport_suffix_decode_2 44 013 14 645 32 034 014 613
cert_ridgeSupport_suffix_decode_2 44 012 14 677 32 034 013 645
cert_ridgeSupport_suffix_decode_2 44 011 14 709 32 034 012 677
cert_ridgeSupport_suffix_decode_2 44 010 14 741 32 034 011 709
cert_ridgeSupport_suffix_decode_2 44 009 14 773 32 034 010 741
cert_ridgeSupport_suffix_decode_2 44 008 14 805 32 034 009 773
cert_ridgeSupport_suffix_decode_2 44 007 14 837 32 034 008 805
cert_ridgeSupport_suffix_decode_2 44 006 14 869 32 034 007 837
cert_ridgeSupport_suffix_decode_2 44 005 14 901 32 034 006 869
cert_ridgeSupport_suffix_decode_2 44 004 14 933 32 034 005 901
cert_ridgeSupport_suffix_decode_2 44 003 14 965 32 034 004 933
cert_ridgeSupport_suffix_decode_2 44 002 14 997 32 034 003 965
cert_ridgeSupport_suffix_decode_2 44 001 14 1029 32 034 002 997
cert_ridgeSupport_suffix_decode_2 44 000 14 1061 32 034 001 1029
cert_ridgeSupport_eq_3 44
theorem ridgeTest_large_44 : ridgeTest 44 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport44_eq]
    simp only [ridgeSupport44_suffix_000, ridgeSupport44_suffix_001, ridgeSupport44_suffix_002, ridgeSupport44_suffix_003, ridgeSupport44_suffix_004, ridgeSupport44_suffix_005, ridgeSupport44_suffix_006, ridgeSupport44_suffix_007, ridgeSupport44_suffix_008, ridgeSupport44_suffix_009, ridgeSupport44_suffix_010, ridgeSupport44_suffix_011, ridgeSupport44_suffix_012, ridgeSupport44_suffix_013, ridgeSupport44_suffix_014, ridgeSupport44_suffix_015, ridgeSupport44_suffix_016, ridgeSupport44_suffix_017, ridgeSupport44_suffix_018, ridgeSupport44_suffix_019, ridgeSupport44_suffix_020, ridgeSupport44_suffix_021, ridgeSupport44_suffix_022, ridgeSupport44_suffix_023, ridgeSupport44_suffix_024, ridgeSupport44_suffix_025, ridgeSupport44_suffix_026, ridgeSupport44_suffix_027, ridgeSupport44_suffix_028, ridgeSupport44_suffix_029, ridgeSupport44_suffix_030, ridgeSupport44_suffix_031, ridgeSupport44_suffix_032, ridgeSupport44_suffix_033, ridgeSupport44_suffix_034, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport44_000_mask, ridgeSupport44_001_mask, ridgeSupport44_002_mask, ridgeSupport44_003_mask, ridgeSupport44_004_mask, ridgeSupport44_005_mask, ridgeSupport44_006_mask, ridgeSupport44_007_mask, ridgeSupport44_008_mask, ridgeSupport44_009_mask, ridgeSupport44_010_mask, ridgeSupport44_011_mask, ridgeSupport44_012_mask, ridgeSupport44_013_mask, ridgeSupport44_014_mask, ridgeSupport44_015_mask, ridgeSupport44_016_mask, ridgeSupport44_017_mask, ridgeSupport44_018_mask, ridgeSupport44_019_mask, ridgeSupport44_020_mask, ridgeSupport44_021_mask, ridgeSupport44_022_mask, ridgeSupport44_023_mask, ridgeSupport44_024_mask, ridgeSupport44_025_mask, ridgeSupport44_026_mask, ridgeSupport44_027_mask, ridgeSupport44_028_mask, ridgeSupport44_029_mask, ridgeSupport44_030_mask, ridgeSupport44_031_mask, ridgeSupport44_032_mask, ridgeSupport44_033_mask]
    decide +kernel
  · rw [ridgeSupport44_eq]
    simp only [ridgeSupport44_suffix_000, ridgeSupport44_suffix_001, ridgeSupport44_suffix_002, ridgeSupport44_suffix_003, ridgeSupport44_suffix_004, ridgeSupport44_suffix_005, ridgeSupport44_suffix_006, ridgeSupport44_suffix_007, ridgeSupport44_suffix_008, ridgeSupport44_suffix_009, ridgeSupport44_suffix_010, ridgeSupport44_suffix_011, ridgeSupport44_suffix_012, ridgeSupport44_suffix_013, ridgeSupport44_suffix_014, ridgeSupport44_suffix_015, ridgeSupport44_suffix_016, ridgeSupport44_suffix_017, ridgeSupport44_suffix_018, ridgeSupport44_suffix_019, ridgeSupport44_suffix_020, ridgeSupport44_suffix_021, ridgeSupport44_suffix_022, ridgeSupport44_suffix_023, ridgeSupport44_suffix_024, ridgeSupport44_suffix_025, ridgeSupport44_suffix_026, ridgeSupport44_suffix_027, ridgeSupport44_suffix_028, ridgeSupport44_suffix_029, ridgeSupport44_suffix_030, ridgeSupport44_suffix_031, ridgeSupport44_suffix_032, ridgeSupport44_suffix_033, ridgeSupport44_suffix_034, List.all_append, List.all_nil, ridgeSupport44_000_checked, ridgeSupport44_001_checked, ridgeSupport44_002_checked, ridgeSupport44_003_checked, ridgeSupport44_004_checked, ridgeSupport44_005_checked, ridgeSupport44_006_checked, ridgeSupport44_007_checked, ridgeSupport44_008_checked, ridgeSupport44_009_checked, ridgeSupport44_010_checked, ridgeSupport44_011_checked, ridgeSupport44_012_checked, ridgeSupport44_013_checked, ridgeSupport44_014_checked, ridgeSupport44_015_checked, ridgeSupport44_016_checked, ridgeSupport44_017_checked, ridgeSupport44_018_checked, ridgeSupport44_019_checked, ridgeSupport44_020_checked, ridgeSupport44_021_checked, ridgeSupport44_022_checked, ridgeSupport44_023_checked, ridgeSupport44_024_checked, ridgeSupport44_025_checked, ridgeSupport44_026_checked, ridgeSupport44_027_checked, ridgeSupport44_028_checked, ridgeSupport44_029_checked, ridgeSupport44_030_checked, ridgeSupport44_031_checked, ridgeSupport44_032_checked, ridgeSupport44_033_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
