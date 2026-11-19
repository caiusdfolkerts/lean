module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport776Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 776 060 15
cert_ridgeSupport_suffix_decode_2 776 059 15 1 1 060 060 0
cert_ridgeSupport_suffix_decode_2 776 058 15 33 32 060 059 1
cert_ridgeSupport_suffix_decode_2 776 057 15 65 32 060 058 33
cert_ridgeSupport_suffix_decode_2 776 056 15 97 32 060 057 65
cert_ridgeSupport_suffix_decode_2 776 055 15 129 32 060 056 97
cert_ridgeSupport_suffix_decode_2 776 054 15 161 32 060 055 129
cert_ridgeSupport_suffix_decode_2 776 053 15 193 32 060 054 161
cert_ridgeSupport_suffix_decode_2 776 052 15 225 32 060 053 193
cert_ridgeSupport_suffix_decode_2 776 051 15 257 32 060 052 225
cert_ridgeSupport_suffix_decode_2 776 050 15 289 32 060 051 257
cert_ridgeSupport_suffix_decode_2 776 049 15 321 32 060 050 289
cert_ridgeSupport_suffix_decode_2 776 048 15 353 32 060 049 321
cert_ridgeSupport_suffix_decode_2 776 047 15 385 32 060 048 353
cert_ridgeSupport_suffix_decode_2 776 046 15 417 32 060 047 385
cert_ridgeSupport_suffix_decode_2 776 045 15 449 32 060 046 417
cert_ridgeSupport_suffix_decode_2 776 044 15 481 32 060 045 449
cert_ridgeSupport_suffix_decode_2 776 043 15 513 32 060 044 481
cert_ridgeSupport_suffix_decode_2 776 042 15 545 32 060 043 513
cert_ridgeSupport_suffix_decode_2 776 041 15 577 32 060 042 545
cert_ridgeSupport_suffix_decode_2 776 040 15 609 32 060 041 577
cert_ridgeSupport_suffix_decode_2 776 039 15 641 32 060 040 609
cert_ridgeSupport_suffix_decode_2 776 038 15 673 32 060 039 641
cert_ridgeSupport_suffix_decode_2 776 037 15 705 32 060 038 673
cert_ridgeSupport_suffix_decode_2 776 036 15 737 32 060 037 705
cert_ridgeSupport_suffix_decode_2 776 035 15 769 32 060 036 737
cert_ridgeSupport_suffix_decode_2 776 034 15 801 32 060 035 769
cert_ridgeSupport_suffix_decode_2 776 033 15 833 32 060 034 801
cert_ridgeSupport_suffix_decode_2 776 032 15 865 32 060 033 833
cert_ridgeSupport_suffix_decode_2 776 031 15 897 32 060 032 865
cert_ridgeSupport_suffix_decode_2 776 030 15 929 32 060 031 897
cert_ridgeSupport_suffix_decode_2 776 029 15 961 32 060 030 929
cert_ridgeSupport_suffix_decode_2 776 028 15 993 32 060 029 961
cert_ridgeSupport_suffix_decode_2 776 027 15 1025 32 060 028 993
cert_ridgeSupport_suffix_decode_2 776 026 15 1057 32 060 027 1025
cert_ridgeSupport_suffix_decode_2 776 025 15 1089 32 060 026 1057
cert_ridgeSupport_suffix_decode_2 776 024 15 1121 32 060 025 1089
cert_ridgeSupport_suffix_decode_2 776 023 15 1153 32 060 024 1121
cert_ridgeSupport_suffix_decode_2 776 022 15 1185 32 060 023 1153
cert_ridgeSupport_suffix_decode_2 776 021 15 1217 32 060 022 1185
cert_ridgeSupport_suffix_decode_2 776 020 15 1249 32 060 021 1217
cert_ridgeSupport_suffix_decode_2 776 019 15 1281 32 060 020 1249
cert_ridgeSupport_suffix_decode_2 776 018 15 1313 32 060 019 1281
cert_ridgeSupport_suffix_decode_2 776 017 15 1345 32 060 018 1313
cert_ridgeSupport_suffix_decode_2 776 016 15 1377 32 060 017 1345
cert_ridgeSupport_suffix_decode_2 776 015 15 1409 32 060 016 1377
cert_ridgeSupport_suffix_decode_2 776 014 15 1441 32 060 015 1409
cert_ridgeSupport_suffix_decode_2 776 013 15 1473 32 060 014 1441
cert_ridgeSupport_suffix_decode_2 776 012 15 1505 32 060 013 1473
cert_ridgeSupport_suffix_decode_2 776 011 15 1537 32 060 012 1505
cert_ridgeSupport_suffix_decode_2 776 010 15 1569 32 060 011 1537
cert_ridgeSupport_suffix_decode_2 776 009 15 1601 32 060 010 1569
cert_ridgeSupport_suffix_decode_2 776 008 15 1633 32 060 009 1601
cert_ridgeSupport_suffix_decode_2 776 007 15 1665 32 060 008 1633
cert_ridgeSupport_suffix_decode_2 776 006 15 1697 32 060 007 1665
cert_ridgeSupport_suffix_decode_2 776 005 15 1729 32 060 006 1697
cert_ridgeSupport_suffix_decode_2 776 004 15 1761 32 060 005 1729
cert_ridgeSupport_suffix_decode_2 776 003 15 1793 32 060 004 1761
cert_ridgeSupport_suffix_decode_2 776 002 15 1825 32 060 003 1793
cert_ridgeSupport_suffix_decode_2 776 001 15 1857 32 060 002 1825
cert_ridgeSupport_suffix_decode_2 776 000 15 1889 32 060 001 1857
cert_ridgeSupport_eq_3 776
theorem ridgeTest_large_776 : ridgeTest 776 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport776_eq]
    simp only [ridgeSupport776_suffix_000, ridgeSupport776_suffix_001, ridgeSupport776_suffix_002, ridgeSupport776_suffix_003, ridgeSupport776_suffix_004, ridgeSupport776_suffix_005, ridgeSupport776_suffix_006, ridgeSupport776_suffix_007, ridgeSupport776_suffix_008, ridgeSupport776_suffix_009, ridgeSupport776_suffix_010, ridgeSupport776_suffix_011, ridgeSupport776_suffix_012, ridgeSupport776_suffix_013, ridgeSupport776_suffix_014, ridgeSupport776_suffix_015, ridgeSupport776_suffix_016, ridgeSupport776_suffix_017, ridgeSupport776_suffix_018, ridgeSupport776_suffix_019, ridgeSupport776_suffix_020, ridgeSupport776_suffix_021, ridgeSupport776_suffix_022, ridgeSupport776_suffix_023, ridgeSupport776_suffix_024, ridgeSupport776_suffix_025, ridgeSupport776_suffix_026, ridgeSupport776_suffix_027, ridgeSupport776_suffix_028, ridgeSupport776_suffix_029, ridgeSupport776_suffix_030, ridgeSupport776_suffix_031, ridgeSupport776_suffix_032, ridgeSupport776_suffix_033, ridgeSupport776_suffix_034, ridgeSupport776_suffix_035, ridgeSupport776_suffix_036, ridgeSupport776_suffix_037, ridgeSupport776_suffix_038, ridgeSupport776_suffix_039, ridgeSupport776_suffix_040, ridgeSupport776_suffix_041, ridgeSupport776_suffix_042, ridgeSupport776_suffix_043, ridgeSupport776_suffix_044, ridgeSupport776_suffix_045, ridgeSupport776_suffix_046, ridgeSupport776_suffix_047, ridgeSupport776_suffix_048, ridgeSupport776_suffix_049, ridgeSupport776_suffix_050, ridgeSupport776_suffix_051, ridgeSupport776_suffix_052, ridgeSupport776_suffix_053, ridgeSupport776_suffix_054, ridgeSupport776_suffix_055, ridgeSupport776_suffix_056, ridgeSupport776_suffix_057, ridgeSupport776_suffix_058, ridgeSupport776_suffix_059, ridgeSupport776_suffix_060, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport776_000_mask, ridgeSupport776_001_mask, ridgeSupport776_002_mask, ridgeSupport776_003_mask, ridgeSupport776_004_mask, ridgeSupport776_005_mask, ridgeSupport776_006_mask, ridgeSupport776_007_mask, ridgeSupport776_008_mask, ridgeSupport776_009_mask, ridgeSupport776_010_mask, ridgeSupport776_011_mask, ridgeSupport776_012_mask, ridgeSupport776_013_mask, ridgeSupport776_014_mask, ridgeSupport776_015_mask, ridgeSupport776_016_mask, ridgeSupport776_017_mask, ridgeSupport776_018_mask, ridgeSupport776_019_mask, ridgeSupport776_020_mask, ridgeSupport776_021_mask, ridgeSupport776_022_mask, ridgeSupport776_023_mask, ridgeSupport776_024_mask, ridgeSupport776_025_mask, ridgeSupport776_026_mask, ridgeSupport776_027_mask, ridgeSupport776_028_mask, ridgeSupport776_029_mask, ridgeSupport776_030_mask, ridgeSupport776_031_mask, ridgeSupport776_032_mask, ridgeSupport776_033_mask, ridgeSupport776_034_mask, ridgeSupport776_035_mask, ridgeSupport776_036_mask, ridgeSupport776_037_mask, ridgeSupport776_038_mask, ridgeSupport776_039_mask, ridgeSupport776_040_mask, ridgeSupport776_041_mask, ridgeSupport776_042_mask, ridgeSupport776_043_mask, ridgeSupport776_044_mask, ridgeSupport776_045_mask, ridgeSupport776_046_mask, ridgeSupport776_047_mask, ridgeSupport776_048_mask, ridgeSupport776_049_mask, ridgeSupport776_050_mask, ridgeSupport776_051_mask, ridgeSupport776_052_mask, ridgeSupport776_053_mask, ridgeSupport776_054_mask, ridgeSupport776_055_mask, ridgeSupport776_056_mask, ridgeSupport776_057_mask, ridgeSupport776_058_mask, ridgeSupport776_059_mask]
    decide +kernel
  · rw [ridgeSupport776_eq]
    simp only [ridgeSupport776_suffix_000, ridgeSupport776_suffix_001, ridgeSupport776_suffix_002, ridgeSupport776_suffix_003, ridgeSupport776_suffix_004, ridgeSupport776_suffix_005, ridgeSupport776_suffix_006, ridgeSupport776_suffix_007, ridgeSupport776_suffix_008, ridgeSupport776_suffix_009, ridgeSupport776_suffix_010, ridgeSupport776_suffix_011, ridgeSupport776_suffix_012, ridgeSupport776_suffix_013, ridgeSupport776_suffix_014, ridgeSupport776_suffix_015, ridgeSupport776_suffix_016, ridgeSupport776_suffix_017, ridgeSupport776_suffix_018, ridgeSupport776_suffix_019, ridgeSupport776_suffix_020, ridgeSupport776_suffix_021, ridgeSupport776_suffix_022, ridgeSupport776_suffix_023, ridgeSupport776_suffix_024, ridgeSupport776_suffix_025, ridgeSupport776_suffix_026, ridgeSupport776_suffix_027, ridgeSupport776_suffix_028, ridgeSupport776_suffix_029, ridgeSupport776_suffix_030, ridgeSupport776_suffix_031, ridgeSupport776_suffix_032, ridgeSupport776_suffix_033, ridgeSupport776_suffix_034, ridgeSupport776_suffix_035, ridgeSupport776_suffix_036, ridgeSupport776_suffix_037, ridgeSupport776_suffix_038, ridgeSupport776_suffix_039, ridgeSupport776_suffix_040, ridgeSupport776_suffix_041, ridgeSupport776_suffix_042, ridgeSupport776_suffix_043, ridgeSupport776_suffix_044, ridgeSupport776_suffix_045, ridgeSupport776_suffix_046, ridgeSupport776_suffix_047, ridgeSupport776_suffix_048, ridgeSupport776_suffix_049, ridgeSupport776_suffix_050, ridgeSupport776_suffix_051, ridgeSupport776_suffix_052, ridgeSupport776_suffix_053, ridgeSupport776_suffix_054, ridgeSupport776_suffix_055, ridgeSupport776_suffix_056, ridgeSupport776_suffix_057, ridgeSupport776_suffix_058, ridgeSupport776_suffix_059, ridgeSupport776_suffix_060, List.all_append, List.all_nil, ridgeSupport776_000_checked, ridgeSupport776_001_checked, ridgeSupport776_002_checked, ridgeSupport776_003_checked, ridgeSupport776_004_checked, ridgeSupport776_005_checked, ridgeSupport776_006_checked, ridgeSupport776_007_checked, ridgeSupport776_008_checked, ridgeSupport776_009_checked, ridgeSupport776_010_checked, ridgeSupport776_011_checked, ridgeSupport776_012_checked, ridgeSupport776_013_checked, ridgeSupport776_014_checked, ridgeSupport776_015_checked, ridgeSupport776_016_checked, ridgeSupport776_017_checked, ridgeSupport776_018_checked, ridgeSupport776_019_checked, ridgeSupport776_020_checked, ridgeSupport776_021_checked, ridgeSupport776_022_checked, ridgeSupport776_023_checked, ridgeSupport776_024_checked, ridgeSupport776_025_checked, ridgeSupport776_026_checked, ridgeSupport776_027_checked, ridgeSupport776_028_checked, ridgeSupport776_029_checked, ridgeSupport776_030_checked, ridgeSupport776_031_checked, ridgeSupport776_032_checked, ridgeSupport776_033_checked, ridgeSupport776_034_checked, ridgeSupport776_035_checked, ridgeSupport776_036_checked, ridgeSupport776_037_checked, ridgeSupport776_038_checked, ridgeSupport776_039_checked, ridgeSupport776_040_checked, ridgeSupport776_041_checked, ridgeSupport776_042_checked, ridgeSupport776_043_checked, ridgeSupport776_044_checked, ridgeSupport776_045_checked, ridgeSupport776_046_checked, ridgeSupport776_047_checked, ridgeSupport776_048_checked, ridgeSupport776_049_checked, ridgeSupport776_050_checked, ridgeSupport776_051_checked, ridgeSupport776_052_checked, ridgeSupport776_053_checked, ridgeSupport776_054_checked, ridgeSupport776_055_checked, ridgeSupport776_056_checked, ridgeSupport776_057_checked, ridgeSupport776_058_checked, ridgeSupport776_059_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
