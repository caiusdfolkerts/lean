module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport644Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 644 060 15
cert_ridgeSupport_suffix_decode_2 644 059 15 1 1 060 060 0
cert_ridgeSupport_suffix_decode_2 644 058 15 33 32 060 059 1
cert_ridgeSupport_suffix_decode_2 644 057 15 65 32 060 058 33
cert_ridgeSupport_suffix_decode_2 644 056 15 97 32 060 057 65
cert_ridgeSupport_suffix_decode_2 644 055 15 129 32 060 056 97
cert_ridgeSupport_suffix_decode_2 644 054 15 161 32 060 055 129
cert_ridgeSupport_suffix_decode_2 644 053 15 193 32 060 054 161
cert_ridgeSupport_suffix_decode_2 644 052 15 225 32 060 053 193
cert_ridgeSupport_suffix_decode_2 644 051 15 257 32 060 052 225
cert_ridgeSupport_suffix_decode_2 644 050 15 289 32 060 051 257
cert_ridgeSupport_suffix_decode_2 644 049 15 321 32 060 050 289
cert_ridgeSupport_suffix_decode_2 644 048 15 353 32 060 049 321
cert_ridgeSupport_suffix_decode_2 644 047 15 385 32 060 048 353
cert_ridgeSupport_suffix_decode_2 644 046 15 417 32 060 047 385
cert_ridgeSupport_suffix_decode_2 644 045 15 449 32 060 046 417
cert_ridgeSupport_suffix_decode_2 644 044 15 481 32 060 045 449
cert_ridgeSupport_suffix_decode_2 644 043 15 513 32 060 044 481
cert_ridgeSupport_suffix_decode_2 644 042 15 545 32 060 043 513
cert_ridgeSupport_suffix_decode_2 644 041 15 577 32 060 042 545
cert_ridgeSupport_suffix_decode_2 644 040 15 609 32 060 041 577
cert_ridgeSupport_suffix_decode_2 644 039 15 641 32 060 040 609
cert_ridgeSupport_suffix_decode_2 644 038 15 673 32 060 039 641
cert_ridgeSupport_suffix_decode_2 644 037 15 705 32 060 038 673
cert_ridgeSupport_suffix_decode_2 644 036 15 737 32 060 037 705
cert_ridgeSupport_suffix_decode_2 644 035 15 769 32 060 036 737
cert_ridgeSupport_suffix_decode_2 644 034 15 801 32 060 035 769
cert_ridgeSupport_suffix_decode_2 644 033 15 833 32 060 034 801
cert_ridgeSupport_suffix_decode_2 644 032 15 865 32 060 033 833
cert_ridgeSupport_suffix_decode_2 644 031 15 897 32 060 032 865
cert_ridgeSupport_suffix_decode_2 644 030 15 929 32 060 031 897
cert_ridgeSupport_suffix_decode_2 644 029 15 961 32 060 030 929
cert_ridgeSupport_suffix_decode_2 644 028 15 993 32 060 029 961
cert_ridgeSupport_suffix_decode_2 644 027 15 1025 32 060 028 993
cert_ridgeSupport_suffix_decode_2 644 026 15 1057 32 060 027 1025
cert_ridgeSupport_suffix_decode_2 644 025 15 1089 32 060 026 1057
cert_ridgeSupport_suffix_decode_2 644 024 15 1121 32 060 025 1089
cert_ridgeSupport_suffix_decode_2 644 023 15 1153 32 060 024 1121
cert_ridgeSupport_suffix_decode_2 644 022 15 1185 32 060 023 1153
cert_ridgeSupport_suffix_decode_2 644 021 15 1217 32 060 022 1185
cert_ridgeSupport_suffix_decode_2 644 020 15 1249 32 060 021 1217
cert_ridgeSupport_suffix_decode_2 644 019 15 1281 32 060 020 1249
cert_ridgeSupport_suffix_decode_2 644 018 15 1313 32 060 019 1281
cert_ridgeSupport_suffix_decode_2 644 017 15 1345 32 060 018 1313
cert_ridgeSupport_suffix_decode_2 644 016 15 1377 32 060 017 1345
cert_ridgeSupport_suffix_decode_2 644 015 15 1409 32 060 016 1377
cert_ridgeSupport_suffix_decode_2 644 014 15 1441 32 060 015 1409
cert_ridgeSupport_suffix_decode_2 644 013 15 1473 32 060 014 1441
cert_ridgeSupport_suffix_decode_2 644 012 15 1505 32 060 013 1473
cert_ridgeSupport_suffix_decode_2 644 011 15 1537 32 060 012 1505
cert_ridgeSupport_suffix_decode_2 644 010 15 1569 32 060 011 1537
cert_ridgeSupport_suffix_decode_2 644 009 15 1601 32 060 010 1569
cert_ridgeSupport_suffix_decode_2 644 008 15 1633 32 060 009 1601
cert_ridgeSupport_suffix_decode_2 644 007 15 1665 32 060 008 1633
cert_ridgeSupport_suffix_decode_2 644 006 15 1697 32 060 007 1665
cert_ridgeSupport_suffix_decode_2 644 005 15 1729 32 060 006 1697
cert_ridgeSupport_suffix_decode_2 644 004 15 1761 32 060 005 1729
cert_ridgeSupport_suffix_decode_2 644 003 15 1793 32 060 004 1761
cert_ridgeSupport_suffix_decode_2 644 002 15 1825 32 060 003 1793
cert_ridgeSupport_suffix_decode_2 644 001 15 1857 32 060 002 1825
cert_ridgeSupport_suffix_decode_2 644 000 15 1889 32 060 001 1857
cert_ridgeSupport_eq_3 644
theorem ridgeTest_large_644 : ridgeTest 644 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport644_eq]
    simp only [ridgeSupport644_suffix_000, ridgeSupport644_suffix_001, ridgeSupport644_suffix_002, ridgeSupport644_suffix_003, ridgeSupport644_suffix_004, ridgeSupport644_suffix_005, ridgeSupport644_suffix_006, ridgeSupport644_suffix_007, ridgeSupport644_suffix_008, ridgeSupport644_suffix_009, ridgeSupport644_suffix_010, ridgeSupport644_suffix_011, ridgeSupport644_suffix_012, ridgeSupport644_suffix_013, ridgeSupport644_suffix_014, ridgeSupport644_suffix_015, ridgeSupport644_suffix_016, ridgeSupport644_suffix_017, ridgeSupport644_suffix_018, ridgeSupport644_suffix_019, ridgeSupport644_suffix_020, ridgeSupport644_suffix_021, ridgeSupport644_suffix_022, ridgeSupport644_suffix_023, ridgeSupport644_suffix_024, ridgeSupport644_suffix_025, ridgeSupport644_suffix_026, ridgeSupport644_suffix_027, ridgeSupport644_suffix_028, ridgeSupport644_suffix_029, ridgeSupport644_suffix_030, ridgeSupport644_suffix_031, ridgeSupport644_suffix_032, ridgeSupport644_suffix_033, ridgeSupport644_suffix_034, ridgeSupport644_suffix_035, ridgeSupport644_suffix_036, ridgeSupport644_suffix_037, ridgeSupport644_suffix_038, ridgeSupport644_suffix_039, ridgeSupport644_suffix_040, ridgeSupport644_suffix_041, ridgeSupport644_suffix_042, ridgeSupport644_suffix_043, ridgeSupport644_suffix_044, ridgeSupport644_suffix_045, ridgeSupport644_suffix_046, ridgeSupport644_suffix_047, ridgeSupport644_suffix_048, ridgeSupport644_suffix_049, ridgeSupport644_suffix_050, ridgeSupport644_suffix_051, ridgeSupport644_suffix_052, ridgeSupport644_suffix_053, ridgeSupport644_suffix_054, ridgeSupport644_suffix_055, ridgeSupport644_suffix_056, ridgeSupport644_suffix_057, ridgeSupport644_suffix_058, ridgeSupport644_suffix_059, ridgeSupport644_suffix_060, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport644_000_mask, ridgeSupport644_001_mask, ridgeSupport644_002_mask, ridgeSupport644_003_mask, ridgeSupport644_004_mask, ridgeSupport644_005_mask, ridgeSupport644_006_mask, ridgeSupport644_007_mask, ridgeSupport644_008_mask, ridgeSupport644_009_mask, ridgeSupport644_010_mask, ridgeSupport644_011_mask, ridgeSupport644_012_mask, ridgeSupport644_013_mask, ridgeSupport644_014_mask, ridgeSupport644_015_mask, ridgeSupport644_016_mask, ridgeSupport644_017_mask, ridgeSupport644_018_mask, ridgeSupport644_019_mask, ridgeSupport644_020_mask, ridgeSupport644_021_mask, ridgeSupport644_022_mask, ridgeSupport644_023_mask, ridgeSupport644_024_mask, ridgeSupport644_025_mask, ridgeSupport644_026_mask, ridgeSupport644_027_mask, ridgeSupport644_028_mask, ridgeSupport644_029_mask, ridgeSupport644_030_mask, ridgeSupport644_031_mask, ridgeSupport644_032_mask, ridgeSupport644_033_mask, ridgeSupport644_034_mask, ridgeSupport644_035_mask, ridgeSupport644_036_mask, ridgeSupport644_037_mask, ridgeSupport644_038_mask, ridgeSupport644_039_mask, ridgeSupport644_040_mask, ridgeSupport644_041_mask, ridgeSupport644_042_mask, ridgeSupport644_043_mask, ridgeSupport644_044_mask, ridgeSupport644_045_mask, ridgeSupport644_046_mask, ridgeSupport644_047_mask, ridgeSupport644_048_mask, ridgeSupport644_049_mask, ridgeSupport644_050_mask, ridgeSupport644_051_mask, ridgeSupport644_052_mask, ridgeSupport644_053_mask, ridgeSupport644_054_mask, ridgeSupport644_055_mask, ridgeSupport644_056_mask, ridgeSupport644_057_mask, ridgeSupport644_058_mask, ridgeSupport644_059_mask]
    decide +kernel
  · rw [ridgeSupport644_eq]
    simp only [ridgeSupport644_suffix_000, ridgeSupport644_suffix_001, ridgeSupport644_suffix_002, ridgeSupport644_suffix_003, ridgeSupport644_suffix_004, ridgeSupport644_suffix_005, ridgeSupport644_suffix_006, ridgeSupport644_suffix_007, ridgeSupport644_suffix_008, ridgeSupport644_suffix_009, ridgeSupport644_suffix_010, ridgeSupport644_suffix_011, ridgeSupport644_suffix_012, ridgeSupport644_suffix_013, ridgeSupport644_suffix_014, ridgeSupport644_suffix_015, ridgeSupport644_suffix_016, ridgeSupport644_suffix_017, ridgeSupport644_suffix_018, ridgeSupport644_suffix_019, ridgeSupport644_suffix_020, ridgeSupport644_suffix_021, ridgeSupport644_suffix_022, ridgeSupport644_suffix_023, ridgeSupport644_suffix_024, ridgeSupport644_suffix_025, ridgeSupport644_suffix_026, ridgeSupport644_suffix_027, ridgeSupport644_suffix_028, ridgeSupport644_suffix_029, ridgeSupport644_suffix_030, ridgeSupport644_suffix_031, ridgeSupport644_suffix_032, ridgeSupport644_suffix_033, ridgeSupport644_suffix_034, ridgeSupport644_suffix_035, ridgeSupport644_suffix_036, ridgeSupport644_suffix_037, ridgeSupport644_suffix_038, ridgeSupport644_suffix_039, ridgeSupport644_suffix_040, ridgeSupport644_suffix_041, ridgeSupport644_suffix_042, ridgeSupport644_suffix_043, ridgeSupport644_suffix_044, ridgeSupport644_suffix_045, ridgeSupport644_suffix_046, ridgeSupport644_suffix_047, ridgeSupport644_suffix_048, ridgeSupport644_suffix_049, ridgeSupport644_suffix_050, ridgeSupport644_suffix_051, ridgeSupport644_suffix_052, ridgeSupport644_suffix_053, ridgeSupport644_suffix_054, ridgeSupport644_suffix_055, ridgeSupport644_suffix_056, ridgeSupport644_suffix_057, ridgeSupport644_suffix_058, ridgeSupport644_suffix_059, ridgeSupport644_suffix_060, List.all_append, List.all_nil, ridgeSupport644_000_checked, ridgeSupport644_001_checked, ridgeSupport644_002_checked, ridgeSupport644_003_checked, ridgeSupport644_004_checked, ridgeSupport644_005_checked, ridgeSupport644_006_checked, ridgeSupport644_007_checked, ridgeSupport644_008_checked, ridgeSupport644_009_checked, ridgeSupport644_010_checked, ridgeSupport644_011_checked, ridgeSupport644_012_checked, ridgeSupport644_013_checked, ridgeSupport644_014_checked, ridgeSupport644_015_checked, ridgeSupport644_016_checked, ridgeSupport644_017_checked, ridgeSupport644_018_checked, ridgeSupport644_019_checked, ridgeSupport644_020_checked, ridgeSupport644_021_checked, ridgeSupport644_022_checked, ridgeSupport644_023_checked, ridgeSupport644_024_checked, ridgeSupport644_025_checked, ridgeSupport644_026_checked, ridgeSupport644_027_checked, ridgeSupport644_028_checked, ridgeSupport644_029_checked, ridgeSupport644_030_checked, ridgeSupport644_031_checked, ridgeSupport644_032_checked, ridgeSupport644_033_checked, ridgeSupport644_034_checked, ridgeSupport644_035_checked, ridgeSupport644_036_checked, ridgeSupport644_037_checked, ridgeSupport644_038_checked, ridgeSupport644_039_checked, ridgeSupport644_040_checked, ridgeSupport644_041_checked, ridgeSupport644_042_checked, ridgeSupport644_043_checked, ridgeSupport644_044_checked, ridgeSupport644_045_checked, ridgeSupport644_046_checked, ridgeSupport644_047_checked, ridgeSupport644_048_checked, ridgeSupport644_049_checked, ridgeSupport644_050_checked, ridgeSupport644_051_checked, ridgeSupport644_052_checked, ridgeSupport644_053_checked, ridgeSupport644_054_checked, ridgeSupport644_055_checked, ridgeSupport644_056_checked, ridgeSupport644_057_checked, ridgeSupport644_058_checked, ridgeSupport644_059_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
