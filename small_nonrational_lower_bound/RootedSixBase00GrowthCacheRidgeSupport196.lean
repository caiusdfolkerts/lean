module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport196Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 196 060 15
cert_ridgeSupport_suffix_decode_2 196 059 15 1 1 060 060 0
cert_ridgeSupport_suffix_decode_2 196 058 15 33 32 060 059 1
cert_ridgeSupport_suffix_decode_2 196 057 15 65 32 060 058 33
cert_ridgeSupport_suffix_decode_2 196 056 15 97 32 060 057 65
cert_ridgeSupport_suffix_decode_2 196 055 15 129 32 060 056 97
cert_ridgeSupport_suffix_decode_2 196 054 15 161 32 060 055 129
cert_ridgeSupport_suffix_decode_2 196 053 15 193 32 060 054 161
cert_ridgeSupport_suffix_decode_2 196 052 15 225 32 060 053 193
cert_ridgeSupport_suffix_decode_2 196 051 15 257 32 060 052 225
cert_ridgeSupport_suffix_decode_2 196 050 15 289 32 060 051 257
cert_ridgeSupport_suffix_decode_2 196 049 15 321 32 060 050 289
cert_ridgeSupport_suffix_decode_2 196 048 15 353 32 060 049 321
cert_ridgeSupport_suffix_decode_2 196 047 15 385 32 060 048 353
cert_ridgeSupport_suffix_decode_2 196 046 15 417 32 060 047 385
cert_ridgeSupport_suffix_decode_2 196 045 15 449 32 060 046 417
cert_ridgeSupport_suffix_decode_2 196 044 15 481 32 060 045 449
cert_ridgeSupport_suffix_decode_2 196 043 15 513 32 060 044 481
cert_ridgeSupport_suffix_decode_2 196 042 15 545 32 060 043 513
cert_ridgeSupport_suffix_decode_2 196 041 15 577 32 060 042 545
cert_ridgeSupport_suffix_decode_2 196 040 15 609 32 060 041 577
cert_ridgeSupport_suffix_decode_2 196 039 15 641 32 060 040 609
cert_ridgeSupport_suffix_decode_2 196 038 15 673 32 060 039 641
cert_ridgeSupport_suffix_decode_2 196 037 15 705 32 060 038 673
cert_ridgeSupport_suffix_decode_2 196 036 15 737 32 060 037 705
cert_ridgeSupport_suffix_decode_2 196 035 15 769 32 060 036 737
cert_ridgeSupport_suffix_decode_2 196 034 15 801 32 060 035 769
cert_ridgeSupport_suffix_decode_2 196 033 15 833 32 060 034 801
cert_ridgeSupport_suffix_decode_2 196 032 15 865 32 060 033 833
cert_ridgeSupport_suffix_decode_2 196 031 15 897 32 060 032 865
cert_ridgeSupport_suffix_decode_2 196 030 15 929 32 060 031 897
cert_ridgeSupport_suffix_decode_2 196 029 15 961 32 060 030 929
cert_ridgeSupport_suffix_decode_2 196 028 15 993 32 060 029 961
cert_ridgeSupport_suffix_decode_2 196 027 15 1025 32 060 028 993
cert_ridgeSupport_suffix_decode_2 196 026 15 1057 32 060 027 1025
cert_ridgeSupport_suffix_decode_2 196 025 15 1089 32 060 026 1057
cert_ridgeSupport_suffix_decode_2 196 024 15 1121 32 060 025 1089
cert_ridgeSupport_suffix_decode_2 196 023 15 1153 32 060 024 1121
cert_ridgeSupport_suffix_decode_2 196 022 15 1185 32 060 023 1153
cert_ridgeSupport_suffix_decode_2 196 021 15 1217 32 060 022 1185
cert_ridgeSupport_suffix_decode_2 196 020 15 1249 32 060 021 1217
cert_ridgeSupport_suffix_decode_2 196 019 15 1281 32 060 020 1249
cert_ridgeSupport_suffix_decode_2 196 018 15 1313 32 060 019 1281
cert_ridgeSupport_suffix_decode_2 196 017 15 1345 32 060 018 1313
cert_ridgeSupport_suffix_decode_2 196 016 15 1377 32 060 017 1345
cert_ridgeSupport_suffix_decode_2 196 015 15 1409 32 060 016 1377
cert_ridgeSupport_suffix_decode_2 196 014 15 1441 32 060 015 1409
cert_ridgeSupport_suffix_decode_2 196 013 15 1473 32 060 014 1441
cert_ridgeSupport_suffix_decode_2 196 012 15 1505 32 060 013 1473
cert_ridgeSupport_suffix_decode_2 196 011 15 1537 32 060 012 1505
cert_ridgeSupport_suffix_decode_2 196 010 15 1569 32 060 011 1537
cert_ridgeSupport_suffix_decode_2 196 009 15 1601 32 060 010 1569
cert_ridgeSupport_suffix_decode_2 196 008 15 1633 32 060 009 1601
cert_ridgeSupport_suffix_decode_2 196 007 15 1665 32 060 008 1633
cert_ridgeSupport_suffix_decode_2 196 006 15 1697 32 060 007 1665
cert_ridgeSupport_suffix_decode_2 196 005 15 1729 32 060 006 1697
cert_ridgeSupport_suffix_decode_2 196 004 15 1761 32 060 005 1729
cert_ridgeSupport_suffix_decode_2 196 003 15 1793 32 060 004 1761
cert_ridgeSupport_suffix_decode_2 196 002 15 1825 32 060 003 1793
cert_ridgeSupport_suffix_decode_2 196 001 15 1857 32 060 002 1825
cert_ridgeSupport_suffix_decode_2 196 000 15 1889 32 060 001 1857
cert_ridgeSupport_eq_3 196
theorem ridgeTest_large_196 : ridgeTest 196 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport196_eq]
    simp only [ridgeSupport196_suffix_000, ridgeSupport196_suffix_001, ridgeSupport196_suffix_002, ridgeSupport196_suffix_003, ridgeSupport196_suffix_004, ridgeSupport196_suffix_005, ridgeSupport196_suffix_006, ridgeSupport196_suffix_007, ridgeSupport196_suffix_008, ridgeSupport196_suffix_009, ridgeSupport196_suffix_010, ridgeSupport196_suffix_011, ridgeSupport196_suffix_012, ridgeSupport196_suffix_013, ridgeSupport196_suffix_014, ridgeSupport196_suffix_015, ridgeSupport196_suffix_016, ridgeSupport196_suffix_017, ridgeSupport196_suffix_018, ridgeSupport196_suffix_019, ridgeSupport196_suffix_020, ridgeSupport196_suffix_021, ridgeSupport196_suffix_022, ridgeSupport196_suffix_023, ridgeSupport196_suffix_024, ridgeSupport196_suffix_025, ridgeSupport196_suffix_026, ridgeSupport196_suffix_027, ridgeSupport196_suffix_028, ridgeSupport196_suffix_029, ridgeSupport196_suffix_030, ridgeSupport196_suffix_031, ridgeSupport196_suffix_032, ridgeSupport196_suffix_033, ridgeSupport196_suffix_034, ridgeSupport196_suffix_035, ridgeSupport196_suffix_036, ridgeSupport196_suffix_037, ridgeSupport196_suffix_038, ridgeSupport196_suffix_039, ridgeSupport196_suffix_040, ridgeSupport196_suffix_041, ridgeSupport196_suffix_042, ridgeSupport196_suffix_043, ridgeSupport196_suffix_044, ridgeSupport196_suffix_045, ridgeSupport196_suffix_046, ridgeSupport196_suffix_047, ridgeSupport196_suffix_048, ridgeSupport196_suffix_049, ridgeSupport196_suffix_050, ridgeSupport196_suffix_051, ridgeSupport196_suffix_052, ridgeSupport196_suffix_053, ridgeSupport196_suffix_054, ridgeSupport196_suffix_055, ridgeSupport196_suffix_056, ridgeSupport196_suffix_057, ridgeSupport196_suffix_058, ridgeSupport196_suffix_059, ridgeSupport196_suffix_060, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport196_000_mask, ridgeSupport196_001_mask, ridgeSupport196_002_mask, ridgeSupport196_003_mask, ridgeSupport196_004_mask, ridgeSupport196_005_mask, ridgeSupport196_006_mask, ridgeSupport196_007_mask, ridgeSupport196_008_mask, ridgeSupport196_009_mask, ridgeSupport196_010_mask, ridgeSupport196_011_mask, ridgeSupport196_012_mask, ridgeSupport196_013_mask, ridgeSupport196_014_mask, ridgeSupport196_015_mask, ridgeSupport196_016_mask, ridgeSupport196_017_mask, ridgeSupport196_018_mask, ridgeSupport196_019_mask, ridgeSupport196_020_mask, ridgeSupport196_021_mask, ridgeSupport196_022_mask, ridgeSupport196_023_mask, ridgeSupport196_024_mask, ridgeSupport196_025_mask, ridgeSupport196_026_mask, ridgeSupport196_027_mask, ridgeSupport196_028_mask, ridgeSupport196_029_mask, ridgeSupport196_030_mask, ridgeSupport196_031_mask, ridgeSupport196_032_mask, ridgeSupport196_033_mask, ridgeSupport196_034_mask, ridgeSupport196_035_mask, ridgeSupport196_036_mask, ridgeSupport196_037_mask, ridgeSupport196_038_mask, ridgeSupport196_039_mask, ridgeSupport196_040_mask, ridgeSupport196_041_mask, ridgeSupport196_042_mask, ridgeSupport196_043_mask, ridgeSupport196_044_mask, ridgeSupport196_045_mask, ridgeSupport196_046_mask, ridgeSupport196_047_mask, ridgeSupport196_048_mask, ridgeSupport196_049_mask, ridgeSupport196_050_mask, ridgeSupport196_051_mask, ridgeSupport196_052_mask, ridgeSupport196_053_mask, ridgeSupport196_054_mask, ridgeSupport196_055_mask, ridgeSupport196_056_mask, ridgeSupport196_057_mask, ridgeSupport196_058_mask, ridgeSupport196_059_mask]
    decide +kernel
  · rw [ridgeSupport196_eq]
    simp only [ridgeSupport196_suffix_000, ridgeSupport196_suffix_001, ridgeSupport196_suffix_002, ridgeSupport196_suffix_003, ridgeSupport196_suffix_004, ridgeSupport196_suffix_005, ridgeSupport196_suffix_006, ridgeSupport196_suffix_007, ridgeSupport196_suffix_008, ridgeSupport196_suffix_009, ridgeSupport196_suffix_010, ridgeSupport196_suffix_011, ridgeSupport196_suffix_012, ridgeSupport196_suffix_013, ridgeSupport196_suffix_014, ridgeSupport196_suffix_015, ridgeSupport196_suffix_016, ridgeSupport196_suffix_017, ridgeSupport196_suffix_018, ridgeSupport196_suffix_019, ridgeSupport196_suffix_020, ridgeSupport196_suffix_021, ridgeSupport196_suffix_022, ridgeSupport196_suffix_023, ridgeSupport196_suffix_024, ridgeSupport196_suffix_025, ridgeSupport196_suffix_026, ridgeSupport196_suffix_027, ridgeSupport196_suffix_028, ridgeSupport196_suffix_029, ridgeSupport196_suffix_030, ridgeSupport196_suffix_031, ridgeSupport196_suffix_032, ridgeSupport196_suffix_033, ridgeSupport196_suffix_034, ridgeSupport196_suffix_035, ridgeSupport196_suffix_036, ridgeSupport196_suffix_037, ridgeSupport196_suffix_038, ridgeSupport196_suffix_039, ridgeSupport196_suffix_040, ridgeSupport196_suffix_041, ridgeSupport196_suffix_042, ridgeSupport196_suffix_043, ridgeSupport196_suffix_044, ridgeSupport196_suffix_045, ridgeSupport196_suffix_046, ridgeSupport196_suffix_047, ridgeSupport196_suffix_048, ridgeSupport196_suffix_049, ridgeSupport196_suffix_050, ridgeSupport196_suffix_051, ridgeSupport196_suffix_052, ridgeSupport196_suffix_053, ridgeSupport196_suffix_054, ridgeSupport196_suffix_055, ridgeSupport196_suffix_056, ridgeSupport196_suffix_057, ridgeSupport196_suffix_058, ridgeSupport196_suffix_059, ridgeSupport196_suffix_060, List.all_append, List.all_nil, ridgeSupport196_000_checked, ridgeSupport196_001_checked, ridgeSupport196_002_checked, ridgeSupport196_003_checked, ridgeSupport196_004_checked, ridgeSupport196_005_checked, ridgeSupport196_006_checked, ridgeSupport196_007_checked, ridgeSupport196_008_checked, ridgeSupport196_009_checked, ridgeSupport196_010_checked, ridgeSupport196_011_checked, ridgeSupport196_012_checked, ridgeSupport196_013_checked, ridgeSupport196_014_checked, ridgeSupport196_015_checked, ridgeSupport196_016_checked, ridgeSupport196_017_checked, ridgeSupport196_018_checked, ridgeSupport196_019_checked, ridgeSupport196_020_checked, ridgeSupport196_021_checked, ridgeSupport196_022_checked, ridgeSupport196_023_checked, ridgeSupport196_024_checked, ridgeSupport196_025_checked, ridgeSupport196_026_checked, ridgeSupport196_027_checked, ridgeSupport196_028_checked, ridgeSupport196_029_checked, ridgeSupport196_030_checked, ridgeSupport196_031_checked, ridgeSupport196_032_checked, ridgeSupport196_033_checked, ridgeSupport196_034_checked, ridgeSupport196_035_checked, ridgeSupport196_036_checked, ridgeSupport196_037_checked, ridgeSupport196_038_checked, ridgeSupport196_039_checked, ridgeSupport196_040_checked, ridgeSupport196_041_checked, ridgeSupport196_042_checked, ridgeSupport196_043_checked, ridgeSupport196_044_checked, ridgeSupport196_045_checked, ridgeSupport196_046_checked, ridgeSupport196_047_checked, ridgeSupport196_048_checked, ridgeSupport196_049_checked, ridgeSupport196_050_checked, ridgeSupport196_051_checked, ridgeSupport196_052_checked, ridgeSupport196_053_checked, ridgeSupport196_054_checked, ridgeSupport196_055_checked, ridgeSupport196_056_checked, ridgeSupport196_057_checked, ridgeSupport196_058_checked, ridgeSupport196_059_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
