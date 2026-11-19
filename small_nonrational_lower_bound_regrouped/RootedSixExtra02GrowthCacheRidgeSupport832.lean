module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import BundledChecks.RootedSixExtra02GrowthCacheRidgeSupport832Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 832 039 13
cert_ridgeSupport_suffix_decode_4 832 038 13 15 15 039 039 0
cert_ridgeSupport_suffix_decode_4 832 037 13 47 32 039 038 15
cert_ridgeSupport_suffix_decode_4 832 036 13 79 32 039 037 47
cert_ridgeSupport_suffix_decode_4 832 035 13 111 32 039 036 79
cert_ridgeSupport_suffix_decode_4 832 034 13 143 32 039 035 111
cert_ridgeSupport_suffix_decode_4 832 033 13 175 32 039 034 143
cert_ridgeSupport_suffix_decode_4 832 032 13 207 32 039 033 175
cert_ridgeSupport_suffix_decode_4 832 031 13 239 32 039 032 207
cert_ridgeSupport_suffix_decode_4 832 030 13 271 32 039 031 239
cert_ridgeSupport_suffix_decode_4 832 029 13 303 32 039 030 271
cert_ridgeSupport_suffix_decode_4 832 028 13 335 32 039 029 303
cert_ridgeSupport_suffix_decode_4 832 027 13 367 32 039 028 335
cert_ridgeSupport_suffix_decode_4 832 026 13 399 32 039 027 367
cert_ridgeSupport_suffix_decode_4 832 025 13 431 32 039 026 399
cert_ridgeSupport_suffix_decode_4 832 024 13 463 32 039 025 431
cert_ridgeSupport_suffix_decode_4 832 023 13 495 32 039 024 463
cert_ridgeSupport_suffix_decode_4 832 022 13 527 32 039 023 495
cert_ridgeSupport_suffix_decode_4 832 021 13 559 32 039 022 527
cert_ridgeSupport_suffix_decode_4 832 020 13 591 32 039 021 559
cert_ridgeSupport_suffix_decode_4 832 019 13 623 32 039 020 591
cert_ridgeSupport_suffix_decode_4 832 018 13 655 32 039 019 623
cert_ridgeSupport_suffix_decode_4 832 017 13 687 32 039 018 655
cert_ridgeSupport_suffix_decode_4 832 016 13 719 32 039 017 687
cert_ridgeSupport_suffix_decode_4 832 015 13 751 32 039 016 719
cert_ridgeSupport_suffix_decode_4 832 014 13 783 32 039 015 751
cert_ridgeSupport_suffix_decode_4 832 013 13 815 32 039 014 783
cert_ridgeSupport_suffix_decode_4 832 012 13 847 32 039 013 815
cert_ridgeSupport_suffix_decode_4 832 011 13 879 32 039 012 847
cert_ridgeSupport_suffix_decode_4 832 010 13 911 32 039 011 879
cert_ridgeSupport_suffix_decode_4 832 009 13 943 32 039 010 911
cert_ridgeSupport_suffix_decode_4 832 008 13 975 32 039 009 943
cert_ridgeSupport_suffix_decode_4 832 007 13 1007 32 039 008 975
cert_ridgeSupport_suffix_decode_4 832 006 13 1039 32 039 007 1007
cert_ridgeSupport_suffix_decode_4 832 005 13 1071 32 039 006 1039
cert_ridgeSupport_suffix_decode_4 832 004 13 1103 32 039 005 1071
cert_ridgeSupport_suffix_decode_4 832 003 13 1135 32 039 004 1103
cert_ridgeSupport_suffix_decode_4 832 002 13 1167 32 039 003 1135
cert_ridgeSupport_suffix_decode_4 832 001 13 1199 32 039 002 1167
cert_ridgeSupport_suffix_decode_4 832 000 13 1231 32 039 001 1199
cert_ridgeSupport_eq_4 832
theorem ridgeTest_large_832 : ridgeTest 832 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, ridgeSupport832_suffix_015, ridgeSupport832_suffix_016, ridgeSupport832_suffix_017, ridgeSupport832_suffix_018, ridgeSupport832_suffix_019, ridgeSupport832_suffix_020, ridgeSupport832_suffix_021, ridgeSupport832_suffix_022, ridgeSupport832_suffix_023, ridgeSupport832_suffix_024, ridgeSupport832_suffix_025, ridgeSupport832_suffix_026, ridgeSupport832_suffix_027, ridgeSupport832_suffix_028, ridgeSupport832_suffix_029, ridgeSupport832_suffix_030, ridgeSupport832_suffix_031, ridgeSupport832_suffix_032, ridgeSupport832_suffix_033, ridgeSupport832_suffix_034, ridgeSupport832_suffix_035, ridgeSupport832_suffix_036, ridgeSupport832_suffix_037, ridgeSupport832_suffix_038, ridgeSupport832_suffix_039, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport832_000_mask, ridgeSupport832_001_mask, ridgeSupport832_002_mask, ridgeSupport832_003_mask, ridgeSupport832_004_mask, ridgeSupport832_005_mask, ridgeSupport832_006_mask, ridgeSupport832_007_mask, ridgeSupport832_008_mask, ridgeSupport832_009_mask, ridgeSupport832_010_mask, ridgeSupport832_011_mask, ridgeSupport832_012_mask, ridgeSupport832_013_mask, ridgeSupport832_014_mask, ridgeSupport832_015_mask, ridgeSupport832_016_mask, ridgeSupport832_017_mask, ridgeSupport832_018_mask, ridgeSupport832_019_mask, ridgeSupport832_020_mask, ridgeSupport832_021_mask, ridgeSupport832_022_mask, ridgeSupport832_023_mask, ridgeSupport832_024_mask, ridgeSupport832_025_mask, ridgeSupport832_026_mask, ridgeSupport832_027_mask, ridgeSupport832_028_mask, ridgeSupport832_029_mask, ridgeSupport832_030_mask, ridgeSupport832_031_mask, ridgeSupport832_032_mask, ridgeSupport832_033_mask, ridgeSupport832_034_mask, ridgeSupport832_035_mask, ridgeSupport832_036_mask, ridgeSupport832_037_mask, ridgeSupport832_038_mask]
    decide +kernel
  · rw [ridgeSupport832_eq]
    simp only [ridgeSupport832_suffix_000, ridgeSupport832_suffix_001, ridgeSupport832_suffix_002, ridgeSupport832_suffix_003, ridgeSupport832_suffix_004, ridgeSupport832_suffix_005, ridgeSupport832_suffix_006, ridgeSupport832_suffix_007, ridgeSupport832_suffix_008, ridgeSupport832_suffix_009, ridgeSupport832_suffix_010, ridgeSupport832_suffix_011, ridgeSupport832_suffix_012, ridgeSupport832_suffix_013, ridgeSupport832_suffix_014, ridgeSupport832_suffix_015, ridgeSupport832_suffix_016, ridgeSupport832_suffix_017, ridgeSupport832_suffix_018, ridgeSupport832_suffix_019, ridgeSupport832_suffix_020, ridgeSupport832_suffix_021, ridgeSupport832_suffix_022, ridgeSupport832_suffix_023, ridgeSupport832_suffix_024, ridgeSupport832_suffix_025, ridgeSupport832_suffix_026, ridgeSupport832_suffix_027, ridgeSupport832_suffix_028, ridgeSupport832_suffix_029, ridgeSupport832_suffix_030, ridgeSupport832_suffix_031, ridgeSupport832_suffix_032, ridgeSupport832_suffix_033, ridgeSupport832_suffix_034, ridgeSupport832_suffix_035, ridgeSupport832_suffix_036, ridgeSupport832_suffix_037, ridgeSupport832_suffix_038, ridgeSupport832_suffix_039, List.all_append, List.all_nil, ridgeSupport832_000_checked, ridgeSupport832_001_checked, ridgeSupport832_002_checked, ridgeSupport832_003_checked, ridgeSupport832_004_checked, ridgeSupport832_005_checked, ridgeSupport832_006_checked, ridgeSupport832_007_checked, ridgeSupport832_008_checked, ridgeSupport832_009_checked, ridgeSupport832_010_checked, ridgeSupport832_011_checked, ridgeSupport832_012_checked, ridgeSupport832_013_checked, ridgeSupport832_014_checked, ridgeSupport832_015_checked, ridgeSupport832_016_checked, ridgeSupport832_017_checked, ridgeSupport832_018_checked, ridgeSupport832_019_checked, ridgeSupport832_020_checked, ridgeSupport832_021_checked, ridgeSupport832_022_checked, ridgeSupport832_023_checked, ridgeSupport832_024_checked, ridgeSupport832_025_checked, ridgeSupport832_026_checked, ridgeSupport832_027_checked, ridgeSupport832_028_checked, ridgeSupport832_029_checked, ridgeSupport832_030_checked, ridgeSupport832_031_checked, ridgeSupport832_032_checked, ridgeSupport832_033_checked, ridgeSupport832_034_checked, ridgeSupport832_035_checked, ridgeSupport832_036_checked, ridgeSupport832_037_checked, ridgeSupport832_038_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
