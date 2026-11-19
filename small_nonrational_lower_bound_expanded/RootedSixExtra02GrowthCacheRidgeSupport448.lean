module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import BundledChecks.RootedSixExtra02GrowthCacheRidgeSupport448Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 448 039 13
cert_ridgeSupport_suffix_decode_4 448 038 13 15 15 039 039 0
cert_ridgeSupport_suffix_decode_4 448 037 13 47 32 039 038 15
cert_ridgeSupport_suffix_decode_4 448 036 13 79 32 039 037 47
cert_ridgeSupport_suffix_decode_4 448 035 13 111 32 039 036 79
cert_ridgeSupport_suffix_decode_4 448 034 13 143 32 039 035 111
cert_ridgeSupport_suffix_decode_4 448 033 13 175 32 039 034 143
cert_ridgeSupport_suffix_decode_4 448 032 13 207 32 039 033 175
cert_ridgeSupport_suffix_decode_4 448 031 13 239 32 039 032 207
cert_ridgeSupport_suffix_decode_4 448 030 13 271 32 039 031 239
cert_ridgeSupport_suffix_decode_4 448 029 13 303 32 039 030 271
cert_ridgeSupport_suffix_decode_4 448 028 13 335 32 039 029 303
cert_ridgeSupport_suffix_decode_4 448 027 13 367 32 039 028 335
cert_ridgeSupport_suffix_decode_4 448 026 13 399 32 039 027 367
cert_ridgeSupport_suffix_decode_4 448 025 13 431 32 039 026 399
cert_ridgeSupport_suffix_decode_4 448 024 13 463 32 039 025 431
cert_ridgeSupport_suffix_decode_4 448 023 13 495 32 039 024 463
cert_ridgeSupport_suffix_decode_4 448 022 13 527 32 039 023 495
cert_ridgeSupport_suffix_decode_4 448 021 13 559 32 039 022 527
cert_ridgeSupport_suffix_decode_4 448 020 13 591 32 039 021 559
cert_ridgeSupport_suffix_decode_4 448 019 13 623 32 039 020 591
cert_ridgeSupport_suffix_decode_4 448 018 13 655 32 039 019 623
cert_ridgeSupport_suffix_decode_4 448 017 13 687 32 039 018 655
cert_ridgeSupport_suffix_decode_4 448 016 13 719 32 039 017 687
cert_ridgeSupport_suffix_decode_4 448 015 13 751 32 039 016 719
cert_ridgeSupport_suffix_decode_4 448 014 13 783 32 039 015 751
cert_ridgeSupport_suffix_decode_4 448 013 13 815 32 039 014 783
cert_ridgeSupport_suffix_decode_4 448 012 13 847 32 039 013 815
cert_ridgeSupport_suffix_decode_4 448 011 13 879 32 039 012 847
cert_ridgeSupport_suffix_decode_4 448 010 13 911 32 039 011 879
cert_ridgeSupport_suffix_decode_4 448 009 13 943 32 039 010 911
cert_ridgeSupport_suffix_decode_4 448 008 13 975 32 039 009 943
cert_ridgeSupport_suffix_decode_4 448 007 13 1007 32 039 008 975
cert_ridgeSupport_suffix_decode_4 448 006 13 1039 32 039 007 1007
cert_ridgeSupport_suffix_decode_4 448 005 13 1071 32 039 006 1039
cert_ridgeSupport_suffix_decode_4 448 004 13 1103 32 039 005 1071
cert_ridgeSupport_suffix_decode_4 448 003 13 1135 32 039 004 1103
cert_ridgeSupport_suffix_decode_4 448 002 13 1167 32 039 003 1135
cert_ridgeSupport_suffix_decode_4 448 001 13 1199 32 039 002 1167
cert_ridgeSupport_suffix_decode_4 448 000 13 1231 32 039 001 1199
cert_ridgeSupport_eq_4 448
theorem ridgeTest_large_448 : ridgeTest 448 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, ridgeSupport448_suffix_016, ridgeSupport448_suffix_017, ridgeSupport448_suffix_018, ridgeSupport448_suffix_019, ridgeSupport448_suffix_020, ridgeSupport448_suffix_021, ridgeSupport448_suffix_022, ridgeSupport448_suffix_023, ridgeSupport448_suffix_024, ridgeSupport448_suffix_025, ridgeSupport448_suffix_026, ridgeSupport448_suffix_027, ridgeSupport448_suffix_028, ridgeSupport448_suffix_029, ridgeSupport448_suffix_030, ridgeSupport448_suffix_031, ridgeSupport448_suffix_032, ridgeSupport448_suffix_033, ridgeSupport448_suffix_034, ridgeSupport448_suffix_035, ridgeSupport448_suffix_036, ridgeSupport448_suffix_037, ridgeSupport448_suffix_038, ridgeSupport448_suffix_039, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport448_000_mask, ridgeSupport448_001_mask, ridgeSupport448_002_mask, ridgeSupport448_003_mask, ridgeSupport448_004_mask, ridgeSupport448_005_mask, ridgeSupport448_006_mask, ridgeSupport448_007_mask, ridgeSupport448_008_mask, ridgeSupport448_009_mask, ridgeSupport448_010_mask, ridgeSupport448_011_mask, ridgeSupport448_012_mask, ridgeSupport448_013_mask, ridgeSupport448_014_mask, ridgeSupport448_015_mask, ridgeSupport448_016_mask, ridgeSupport448_017_mask, ridgeSupport448_018_mask, ridgeSupport448_019_mask, ridgeSupport448_020_mask, ridgeSupport448_021_mask, ridgeSupport448_022_mask, ridgeSupport448_023_mask, ridgeSupport448_024_mask, ridgeSupport448_025_mask, ridgeSupport448_026_mask, ridgeSupport448_027_mask, ridgeSupport448_028_mask, ridgeSupport448_029_mask, ridgeSupport448_030_mask, ridgeSupport448_031_mask, ridgeSupport448_032_mask, ridgeSupport448_033_mask, ridgeSupport448_034_mask, ridgeSupport448_035_mask, ridgeSupport448_036_mask, ridgeSupport448_037_mask, ridgeSupport448_038_mask]
    decide +kernel
  · rw [ridgeSupport448_eq]
    simp only [ridgeSupport448_suffix_000, ridgeSupport448_suffix_001, ridgeSupport448_suffix_002, ridgeSupport448_suffix_003, ridgeSupport448_suffix_004, ridgeSupport448_suffix_005, ridgeSupport448_suffix_006, ridgeSupport448_suffix_007, ridgeSupport448_suffix_008, ridgeSupport448_suffix_009, ridgeSupport448_suffix_010, ridgeSupport448_suffix_011, ridgeSupport448_suffix_012, ridgeSupport448_suffix_013, ridgeSupport448_suffix_014, ridgeSupport448_suffix_015, ridgeSupport448_suffix_016, ridgeSupport448_suffix_017, ridgeSupport448_suffix_018, ridgeSupport448_suffix_019, ridgeSupport448_suffix_020, ridgeSupport448_suffix_021, ridgeSupport448_suffix_022, ridgeSupport448_suffix_023, ridgeSupport448_suffix_024, ridgeSupport448_suffix_025, ridgeSupport448_suffix_026, ridgeSupport448_suffix_027, ridgeSupport448_suffix_028, ridgeSupport448_suffix_029, ridgeSupport448_suffix_030, ridgeSupport448_suffix_031, ridgeSupport448_suffix_032, ridgeSupport448_suffix_033, ridgeSupport448_suffix_034, ridgeSupport448_suffix_035, ridgeSupport448_suffix_036, ridgeSupport448_suffix_037, ridgeSupport448_suffix_038, ridgeSupport448_suffix_039, List.all_append, List.all_nil, ridgeSupport448_000_checked, ridgeSupport448_001_checked, ridgeSupport448_002_checked, ridgeSupport448_003_checked, ridgeSupport448_004_checked, ridgeSupport448_005_checked, ridgeSupport448_006_checked, ridgeSupport448_007_checked, ridgeSupport448_008_checked, ridgeSupport448_009_checked, ridgeSupport448_010_checked, ridgeSupport448_011_checked, ridgeSupport448_012_checked, ridgeSupport448_013_checked, ridgeSupport448_014_checked, ridgeSupport448_015_checked, ridgeSupport448_016_checked, ridgeSupport448_017_checked, ridgeSupport448_018_checked, ridgeSupport448_019_checked, ridgeSupport448_020_checked, ridgeSupport448_021_checked, ridgeSupport448_022_checked, ridgeSupport448_023_checked, ridgeSupport448_024_checked, ridgeSupport448_025_checked, ridgeSupport448_026_checked, ridgeSupport448_027_checked, ridgeSupport448_028_checked, ridgeSupport448_029_checked, ridgeSupport448_030_checked, ridgeSupport448_031_checked, ridgeSupport448_032_checked, ridgeSupport448_033_checked, ridgeSupport448_034_checked, ridgeSupport448_035_checked, ridgeSupport448_036_checked, ridgeSupport448_037_checked, ridgeSupport448_038_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
