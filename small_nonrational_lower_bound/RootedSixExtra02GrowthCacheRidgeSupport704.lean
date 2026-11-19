module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import BundledChecks.RootedSixExtra02GrowthCacheRidgeSupport704Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 704 039 13
cert_ridgeSupport_suffix_decode_4 704 038 13 15 15 039 039 0
cert_ridgeSupport_suffix_decode_4 704 037 13 47 32 039 038 15
cert_ridgeSupport_suffix_decode_4 704 036 13 79 32 039 037 47
cert_ridgeSupport_suffix_decode_4 704 035 13 111 32 039 036 79
cert_ridgeSupport_suffix_decode_4 704 034 13 143 32 039 035 111
cert_ridgeSupport_suffix_decode_4 704 033 13 175 32 039 034 143
cert_ridgeSupport_suffix_decode_4 704 032 13 207 32 039 033 175
cert_ridgeSupport_suffix_decode_4 704 031 13 239 32 039 032 207
cert_ridgeSupport_suffix_decode_4 704 030 13 271 32 039 031 239
cert_ridgeSupport_suffix_decode_4 704 029 13 303 32 039 030 271
cert_ridgeSupport_suffix_decode_4 704 028 13 335 32 039 029 303
cert_ridgeSupport_suffix_decode_4 704 027 13 367 32 039 028 335
cert_ridgeSupport_suffix_decode_4 704 026 13 399 32 039 027 367
cert_ridgeSupport_suffix_decode_4 704 025 13 431 32 039 026 399
cert_ridgeSupport_suffix_decode_4 704 024 13 463 32 039 025 431
cert_ridgeSupport_suffix_decode_4 704 023 13 495 32 039 024 463
cert_ridgeSupport_suffix_decode_4 704 022 13 527 32 039 023 495
cert_ridgeSupport_suffix_decode_4 704 021 13 559 32 039 022 527
cert_ridgeSupport_suffix_decode_4 704 020 13 591 32 039 021 559
cert_ridgeSupport_suffix_decode_4 704 019 13 623 32 039 020 591
cert_ridgeSupport_suffix_decode_4 704 018 13 655 32 039 019 623
cert_ridgeSupport_suffix_decode_4 704 017 13 687 32 039 018 655
cert_ridgeSupport_suffix_decode_4 704 016 13 719 32 039 017 687
cert_ridgeSupport_suffix_decode_4 704 015 13 751 32 039 016 719
cert_ridgeSupport_suffix_decode_4 704 014 13 783 32 039 015 751
cert_ridgeSupport_suffix_decode_4 704 013 13 815 32 039 014 783
cert_ridgeSupport_suffix_decode_4 704 012 13 847 32 039 013 815
cert_ridgeSupport_suffix_decode_4 704 011 13 879 32 039 012 847
cert_ridgeSupport_suffix_decode_4 704 010 13 911 32 039 011 879
cert_ridgeSupport_suffix_decode_4 704 009 13 943 32 039 010 911
cert_ridgeSupport_suffix_decode_4 704 008 13 975 32 039 009 943
cert_ridgeSupport_suffix_decode_4 704 007 13 1007 32 039 008 975
cert_ridgeSupport_suffix_decode_4 704 006 13 1039 32 039 007 1007
cert_ridgeSupport_suffix_decode_4 704 005 13 1071 32 039 006 1039
cert_ridgeSupport_suffix_decode_4 704 004 13 1103 32 039 005 1071
cert_ridgeSupport_suffix_decode_4 704 003 13 1135 32 039 004 1103
cert_ridgeSupport_suffix_decode_4 704 002 13 1167 32 039 003 1135
cert_ridgeSupport_suffix_decode_4 704 001 13 1199 32 039 002 1167
cert_ridgeSupport_suffix_decode_4 704 000 13 1231 32 039 001 1199
cert_ridgeSupport_eq_4 704
theorem ridgeTest_large_704 : ridgeTest 704 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, ridgeSupport704_suffix_015, ridgeSupport704_suffix_016, ridgeSupport704_suffix_017, ridgeSupport704_suffix_018, ridgeSupport704_suffix_019, ridgeSupport704_suffix_020, ridgeSupport704_suffix_021, ridgeSupport704_suffix_022, ridgeSupport704_suffix_023, ridgeSupport704_suffix_024, ridgeSupport704_suffix_025, ridgeSupport704_suffix_026, ridgeSupport704_suffix_027, ridgeSupport704_suffix_028, ridgeSupport704_suffix_029, ridgeSupport704_suffix_030, ridgeSupport704_suffix_031, ridgeSupport704_suffix_032, ridgeSupport704_suffix_033, ridgeSupport704_suffix_034, ridgeSupport704_suffix_035, ridgeSupport704_suffix_036, ridgeSupport704_suffix_037, ridgeSupport704_suffix_038, ridgeSupport704_suffix_039, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport704_000_mask, ridgeSupport704_001_mask, ridgeSupport704_002_mask, ridgeSupport704_003_mask, ridgeSupport704_004_mask, ridgeSupport704_005_mask, ridgeSupport704_006_mask, ridgeSupport704_007_mask, ridgeSupport704_008_mask, ridgeSupport704_009_mask, ridgeSupport704_010_mask, ridgeSupport704_011_mask, ridgeSupport704_012_mask, ridgeSupport704_013_mask, ridgeSupport704_014_mask, ridgeSupport704_015_mask, ridgeSupport704_016_mask, ridgeSupport704_017_mask, ridgeSupport704_018_mask, ridgeSupport704_019_mask, ridgeSupport704_020_mask, ridgeSupport704_021_mask, ridgeSupport704_022_mask, ridgeSupport704_023_mask, ridgeSupport704_024_mask, ridgeSupport704_025_mask, ridgeSupport704_026_mask, ridgeSupport704_027_mask, ridgeSupport704_028_mask, ridgeSupport704_029_mask, ridgeSupport704_030_mask, ridgeSupport704_031_mask, ridgeSupport704_032_mask, ridgeSupport704_033_mask, ridgeSupport704_034_mask, ridgeSupport704_035_mask, ridgeSupport704_036_mask, ridgeSupport704_037_mask, ridgeSupport704_038_mask]
    decide +kernel
  · rw [ridgeSupport704_eq]
    simp only [ridgeSupport704_suffix_000, ridgeSupport704_suffix_001, ridgeSupport704_suffix_002, ridgeSupport704_suffix_003, ridgeSupport704_suffix_004, ridgeSupport704_suffix_005, ridgeSupport704_suffix_006, ridgeSupport704_suffix_007, ridgeSupport704_suffix_008, ridgeSupport704_suffix_009, ridgeSupport704_suffix_010, ridgeSupport704_suffix_011, ridgeSupport704_suffix_012, ridgeSupport704_suffix_013, ridgeSupport704_suffix_014, ridgeSupport704_suffix_015, ridgeSupport704_suffix_016, ridgeSupport704_suffix_017, ridgeSupport704_suffix_018, ridgeSupport704_suffix_019, ridgeSupport704_suffix_020, ridgeSupport704_suffix_021, ridgeSupport704_suffix_022, ridgeSupport704_suffix_023, ridgeSupport704_suffix_024, ridgeSupport704_suffix_025, ridgeSupport704_suffix_026, ridgeSupport704_suffix_027, ridgeSupport704_suffix_028, ridgeSupport704_suffix_029, ridgeSupport704_suffix_030, ridgeSupport704_suffix_031, ridgeSupport704_suffix_032, ridgeSupport704_suffix_033, ridgeSupport704_suffix_034, ridgeSupport704_suffix_035, ridgeSupport704_suffix_036, ridgeSupport704_suffix_037, ridgeSupport704_suffix_038, ridgeSupport704_suffix_039, List.all_append, List.all_nil, ridgeSupport704_000_checked, ridgeSupport704_001_checked, ridgeSupport704_002_checked, ridgeSupport704_003_checked, ridgeSupport704_004_checked, ridgeSupport704_005_checked, ridgeSupport704_006_checked, ridgeSupport704_007_checked, ridgeSupport704_008_checked, ridgeSupport704_009_checked, ridgeSupport704_010_checked, ridgeSupport704_011_checked, ridgeSupport704_012_checked, ridgeSupport704_013_checked, ridgeSupport704_014_checked, ridgeSupport704_015_checked, ridgeSupport704_016_checked, ridgeSupport704_017_checked, ridgeSupport704_018_checked, ridgeSupport704_019_checked, ridgeSupport704_020_checked, ridgeSupport704_021_checked, ridgeSupport704_022_checked, ridgeSupport704_023_checked, ridgeSupport704_024_checked, ridgeSupport704_025_checked, ridgeSupport704_026_checked, ridgeSupport704_027_checked, ridgeSupport704_028_checked, ridgeSupport704_029_checked, ridgeSupport704_030_checked, ridgeSupport704_031_checked, ridgeSupport704_032_checked, ridgeSupport704_033_checked, ridgeSupport704_034_checked, ridgeSupport704_035_checked, ridgeSupport704_036_checked, ridgeSupport704_037_checked, ridgeSupport704_038_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
