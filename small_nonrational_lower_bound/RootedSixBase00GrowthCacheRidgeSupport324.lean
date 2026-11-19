module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport324Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 324 060 15
cert_ridgeSupport_suffix_decode_2 324 059 15 1 1 060 060 0
cert_ridgeSupport_suffix_decode_2 324 058 15 33 32 060 059 1
cert_ridgeSupport_suffix_decode_2 324 057 15 65 32 060 058 33
cert_ridgeSupport_suffix_decode_2 324 056 15 97 32 060 057 65
cert_ridgeSupport_suffix_decode_2 324 055 15 129 32 060 056 97
cert_ridgeSupport_suffix_decode_2 324 054 15 161 32 060 055 129
cert_ridgeSupport_suffix_decode_2 324 053 15 193 32 060 054 161
cert_ridgeSupport_suffix_decode_2 324 052 15 225 32 060 053 193
cert_ridgeSupport_suffix_decode_2 324 051 15 257 32 060 052 225
cert_ridgeSupport_suffix_decode_2 324 050 15 289 32 060 051 257
cert_ridgeSupport_suffix_decode_2 324 049 15 321 32 060 050 289
cert_ridgeSupport_suffix_decode_2 324 048 15 353 32 060 049 321
cert_ridgeSupport_suffix_decode_2 324 047 15 385 32 060 048 353
cert_ridgeSupport_suffix_decode_2 324 046 15 417 32 060 047 385
cert_ridgeSupport_suffix_decode_2 324 045 15 449 32 060 046 417
cert_ridgeSupport_suffix_decode_2 324 044 15 481 32 060 045 449
cert_ridgeSupport_suffix_decode_2 324 043 15 513 32 060 044 481
cert_ridgeSupport_suffix_decode_2 324 042 15 545 32 060 043 513
cert_ridgeSupport_suffix_decode_2 324 041 15 577 32 060 042 545
cert_ridgeSupport_suffix_decode_2 324 040 15 609 32 060 041 577
cert_ridgeSupport_suffix_decode_2 324 039 15 641 32 060 040 609
cert_ridgeSupport_suffix_decode_2 324 038 15 673 32 060 039 641
cert_ridgeSupport_suffix_decode_2 324 037 15 705 32 060 038 673
cert_ridgeSupport_suffix_decode_2 324 036 15 737 32 060 037 705
cert_ridgeSupport_suffix_decode_2 324 035 15 769 32 060 036 737
cert_ridgeSupport_suffix_decode_2 324 034 15 801 32 060 035 769
cert_ridgeSupport_suffix_decode_2 324 033 15 833 32 060 034 801
cert_ridgeSupport_suffix_decode_2 324 032 15 865 32 060 033 833
cert_ridgeSupport_suffix_decode_2 324 031 15 897 32 060 032 865
cert_ridgeSupport_suffix_decode_2 324 030 15 929 32 060 031 897
cert_ridgeSupport_suffix_decode_2 324 029 15 961 32 060 030 929
cert_ridgeSupport_suffix_decode_2 324 028 15 993 32 060 029 961
cert_ridgeSupport_suffix_decode_2 324 027 15 1025 32 060 028 993
cert_ridgeSupport_suffix_decode_2 324 026 15 1057 32 060 027 1025
cert_ridgeSupport_suffix_decode_2 324 025 15 1089 32 060 026 1057
cert_ridgeSupport_suffix_decode_2 324 024 15 1121 32 060 025 1089
cert_ridgeSupport_suffix_decode_2 324 023 15 1153 32 060 024 1121
cert_ridgeSupport_suffix_decode_2 324 022 15 1185 32 060 023 1153
cert_ridgeSupport_suffix_decode_2 324 021 15 1217 32 060 022 1185
cert_ridgeSupport_suffix_decode_2 324 020 15 1249 32 060 021 1217
cert_ridgeSupport_suffix_decode_2 324 019 15 1281 32 060 020 1249
cert_ridgeSupport_suffix_decode_2 324 018 15 1313 32 060 019 1281
cert_ridgeSupport_suffix_decode_2 324 017 15 1345 32 060 018 1313
cert_ridgeSupport_suffix_decode_2 324 016 15 1377 32 060 017 1345
cert_ridgeSupport_suffix_decode_2 324 015 15 1409 32 060 016 1377
cert_ridgeSupport_suffix_decode_2 324 014 15 1441 32 060 015 1409
cert_ridgeSupport_suffix_decode_2 324 013 15 1473 32 060 014 1441
cert_ridgeSupport_suffix_decode_2 324 012 15 1505 32 060 013 1473
cert_ridgeSupport_suffix_decode_2 324 011 15 1537 32 060 012 1505
cert_ridgeSupport_suffix_decode_2 324 010 15 1569 32 060 011 1537
cert_ridgeSupport_suffix_decode_2 324 009 15 1601 32 060 010 1569
cert_ridgeSupport_suffix_decode_2 324 008 15 1633 32 060 009 1601
cert_ridgeSupport_suffix_decode_2 324 007 15 1665 32 060 008 1633
cert_ridgeSupport_suffix_decode_2 324 006 15 1697 32 060 007 1665
cert_ridgeSupport_suffix_decode_2 324 005 15 1729 32 060 006 1697
cert_ridgeSupport_suffix_decode_2 324 004 15 1761 32 060 005 1729
cert_ridgeSupport_suffix_decode_2 324 003 15 1793 32 060 004 1761
cert_ridgeSupport_suffix_decode_2 324 002 15 1825 32 060 003 1793
cert_ridgeSupport_suffix_decode_2 324 001 15 1857 32 060 002 1825
cert_ridgeSupport_suffix_decode_2 324 000 15 1889 32 060 001 1857
cert_ridgeSupport_eq_3 324
theorem ridgeTest_large_324 : ridgeTest 324 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport324_eq]
    simp only [ridgeSupport324_suffix_000, ridgeSupport324_suffix_001, ridgeSupport324_suffix_002, ridgeSupport324_suffix_003, ridgeSupport324_suffix_004, ridgeSupport324_suffix_005, ridgeSupport324_suffix_006, ridgeSupport324_suffix_007, ridgeSupport324_suffix_008, ridgeSupport324_suffix_009, ridgeSupport324_suffix_010, ridgeSupport324_suffix_011, ridgeSupport324_suffix_012, ridgeSupport324_suffix_013, ridgeSupport324_suffix_014, ridgeSupport324_suffix_015, ridgeSupport324_suffix_016, ridgeSupport324_suffix_017, ridgeSupport324_suffix_018, ridgeSupport324_suffix_019, ridgeSupport324_suffix_020, ridgeSupport324_suffix_021, ridgeSupport324_suffix_022, ridgeSupport324_suffix_023, ridgeSupport324_suffix_024, ridgeSupport324_suffix_025, ridgeSupport324_suffix_026, ridgeSupport324_suffix_027, ridgeSupport324_suffix_028, ridgeSupport324_suffix_029, ridgeSupport324_suffix_030, ridgeSupport324_suffix_031, ridgeSupport324_suffix_032, ridgeSupport324_suffix_033, ridgeSupport324_suffix_034, ridgeSupport324_suffix_035, ridgeSupport324_suffix_036, ridgeSupport324_suffix_037, ridgeSupport324_suffix_038, ridgeSupport324_suffix_039, ridgeSupport324_suffix_040, ridgeSupport324_suffix_041, ridgeSupport324_suffix_042, ridgeSupport324_suffix_043, ridgeSupport324_suffix_044, ridgeSupport324_suffix_045, ridgeSupport324_suffix_046, ridgeSupport324_suffix_047, ridgeSupport324_suffix_048, ridgeSupport324_suffix_049, ridgeSupport324_suffix_050, ridgeSupport324_suffix_051, ridgeSupport324_suffix_052, ridgeSupport324_suffix_053, ridgeSupport324_suffix_054, ridgeSupport324_suffix_055, ridgeSupport324_suffix_056, ridgeSupport324_suffix_057, ridgeSupport324_suffix_058, ridgeSupport324_suffix_059, ridgeSupport324_suffix_060, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport324_000_mask, ridgeSupport324_001_mask, ridgeSupport324_002_mask, ridgeSupport324_003_mask, ridgeSupport324_004_mask, ridgeSupport324_005_mask, ridgeSupport324_006_mask, ridgeSupport324_007_mask, ridgeSupport324_008_mask, ridgeSupport324_009_mask, ridgeSupport324_010_mask, ridgeSupport324_011_mask, ridgeSupport324_012_mask, ridgeSupport324_013_mask, ridgeSupport324_014_mask, ridgeSupport324_015_mask, ridgeSupport324_016_mask, ridgeSupport324_017_mask, ridgeSupport324_018_mask, ridgeSupport324_019_mask, ridgeSupport324_020_mask, ridgeSupport324_021_mask, ridgeSupport324_022_mask, ridgeSupport324_023_mask, ridgeSupport324_024_mask, ridgeSupport324_025_mask, ridgeSupport324_026_mask, ridgeSupport324_027_mask, ridgeSupport324_028_mask, ridgeSupport324_029_mask, ridgeSupport324_030_mask, ridgeSupport324_031_mask, ridgeSupport324_032_mask, ridgeSupport324_033_mask, ridgeSupport324_034_mask, ridgeSupport324_035_mask, ridgeSupport324_036_mask, ridgeSupport324_037_mask, ridgeSupport324_038_mask, ridgeSupport324_039_mask, ridgeSupport324_040_mask, ridgeSupport324_041_mask, ridgeSupport324_042_mask, ridgeSupport324_043_mask, ridgeSupport324_044_mask, ridgeSupport324_045_mask, ridgeSupport324_046_mask, ridgeSupport324_047_mask, ridgeSupport324_048_mask, ridgeSupport324_049_mask, ridgeSupport324_050_mask, ridgeSupport324_051_mask, ridgeSupport324_052_mask, ridgeSupport324_053_mask, ridgeSupport324_054_mask, ridgeSupport324_055_mask, ridgeSupport324_056_mask, ridgeSupport324_057_mask, ridgeSupport324_058_mask, ridgeSupport324_059_mask]
    decide +kernel
  · rw [ridgeSupport324_eq]
    simp only [ridgeSupport324_suffix_000, ridgeSupport324_suffix_001, ridgeSupport324_suffix_002, ridgeSupport324_suffix_003, ridgeSupport324_suffix_004, ridgeSupport324_suffix_005, ridgeSupport324_suffix_006, ridgeSupport324_suffix_007, ridgeSupport324_suffix_008, ridgeSupport324_suffix_009, ridgeSupport324_suffix_010, ridgeSupport324_suffix_011, ridgeSupport324_suffix_012, ridgeSupport324_suffix_013, ridgeSupport324_suffix_014, ridgeSupport324_suffix_015, ridgeSupport324_suffix_016, ridgeSupport324_suffix_017, ridgeSupport324_suffix_018, ridgeSupport324_suffix_019, ridgeSupport324_suffix_020, ridgeSupport324_suffix_021, ridgeSupport324_suffix_022, ridgeSupport324_suffix_023, ridgeSupport324_suffix_024, ridgeSupport324_suffix_025, ridgeSupport324_suffix_026, ridgeSupport324_suffix_027, ridgeSupport324_suffix_028, ridgeSupport324_suffix_029, ridgeSupport324_suffix_030, ridgeSupport324_suffix_031, ridgeSupport324_suffix_032, ridgeSupport324_suffix_033, ridgeSupport324_suffix_034, ridgeSupport324_suffix_035, ridgeSupport324_suffix_036, ridgeSupport324_suffix_037, ridgeSupport324_suffix_038, ridgeSupport324_suffix_039, ridgeSupport324_suffix_040, ridgeSupport324_suffix_041, ridgeSupport324_suffix_042, ridgeSupport324_suffix_043, ridgeSupport324_suffix_044, ridgeSupport324_suffix_045, ridgeSupport324_suffix_046, ridgeSupport324_suffix_047, ridgeSupport324_suffix_048, ridgeSupport324_suffix_049, ridgeSupport324_suffix_050, ridgeSupport324_suffix_051, ridgeSupport324_suffix_052, ridgeSupport324_suffix_053, ridgeSupport324_suffix_054, ridgeSupport324_suffix_055, ridgeSupport324_suffix_056, ridgeSupport324_suffix_057, ridgeSupport324_suffix_058, ridgeSupport324_suffix_059, ridgeSupport324_suffix_060, List.all_append, List.all_nil, ridgeSupport324_000_checked, ridgeSupport324_001_checked, ridgeSupport324_002_checked, ridgeSupport324_003_checked, ridgeSupport324_004_checked, ridgeSupport324_005_checked, ridgeSupport324_006_checked, ridgeSupport324_007_checked, ridgeSupport324_008_checked, ridgeSupport324_009_checked, ridgeSupport324_010_checked, ridgeSupport324_011_checked, ridgeSupport324_012_checked, ridgeSupport324_013_checked, ridgeSupport324_014_checked, ridgeSupport324_015_checked, ridgeSupport324_016_checked, ridgeSupport324_017_checked, ridgeSupport324_018_checked, ridgeSupport324_019_checked, ridgeSupport324_020_checked, ridgeSupport324_021_checked, ridgeSupport324_022_checked, ridgeSupport324_023_checked, ridgeSupport324_024_checked, ridgeSupport324_025_checked, ridgeSupport324_026_checked, ridgeSupport324_027_checked, ridgeSupport324_028_checked, ridgeSupport324_029_checked, ridgeSupport324_030_checked, ridgeSupport324_031_checked, ridgeSupport324_032_checked, ridgeSupport324_033_checked, ridgeSupport324_034_checked, ridgeSupport324_035_checked, ridgeSupport324_036_checked, ridgeSupport324_037_checked, ridgeSupport324_038_checked, ridgeSupport324_039_checked, ridgeSupport324_040_checked, ridgeSupport324_041_checked, ridgeSupport324_042_checked, ridgeSupport324_043_checked, ridgeSupport324_044_checked, ridgeSupport324_045_checked, ridgeSupport324_046_checked, ridgeSupport324_047_checked, ridgeSupport324_048_checked, ridgeSupport324_049_checked, ridgeSupport324_050_checked, ridgeSupport324_051_checked, ridgeSupport324_052_checked, ridgeSupport324_053_checked, ridgeSupport324_054_checked, ridgeSupport324_055_checked, ridgeSupport324_056_checked, ridgeSupport324_057_checked, ridgeSupport324_058_checked, ridgeSupport324_059_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
