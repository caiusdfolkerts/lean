module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport584Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 584 060 15
cert_ridgeSupport_suffix_decode_2 584 059 15 1 1 060 060 0
cert_ridgeSupport_suffix_decode_2 584 058 15 33 32 060 059 1
cert_ridgeSupport_suffix_decode_2 584 057 15 65 32 060 058 33
cert_ridgeSupport_suffix_decode_2 584 056 15 97 32 060 057 65
cert_ridgeSupport_suffix_decode_2 584 055 15 129 32 060 056 97
cert_ridgeSupport_suffix_decode_2 584 054 15 161 32 060 055 129
cert_ridgeSupport_suffix_decode_2 584 053 15 193 32 060 054 161
cert_ridgeSupport_suffix_decode_2 584 052 15 225 32 060 053 193
cert_ridgeSupport_suffix_decode_2 584 051 15 257 32 060 052 225
cert_ridgeSupport_suffix_decode_2 584 050 15 289 32 060 051 257
cert_ridgeSupport_suffix_decode_2 584 049 15 321 32 060 050 289
cert_ridgeSupport_suffix_decode_2 584 048 15 353 32 060 049 321
cert_ridgeSupport_suffix_decode_2 584 047 15 385 32 060 048 353
cert_ridgeSupport_suffix_decode_2 584 046 15 417 32 060 047 385
cert_ridgeSupport_suffix_decode_2 584 045 15 449 32 060 046 417
cert_ridgeSupport_suffix_decode_2 584 044 15 481 32 060 045 449
cert_ridgeSupport_suffix_decode_2 584 043 15 513 32 060 044 481
cert_ridgeSupport_suffix_decode_2 584 042 15 545 32 060 043 513
cert_ridgeSupport_suffix_decode_2 584 041 15 577 32 060 042 545
cert_ridgeSupport_suffix_decode_2 584 040 15 609 32 060 041 577
cert_ridgeSupport_suffix_decode_2 584 039 15 641 32 060 040 609
cert_ridgeSupport_suffix_decode_2 584 038 15 673 32 060 039 641
cert_ridgeSupport_suffix_decode_2 584 037 15 705 32 060 038 673
cert_ridgeSupport_suffix_decode_2 584 036 15 737 32 060 037 705
cert_ridgeSupport_suffix_decode_2 584 035 15 769 32 060 036 737
cert_ridgeSupport_suffix_decode_2 584 034 15 801 32 060 035 769
cert_ridgeSupport_suffix_decode_2 584 033 15 833 32 060 034 801
cert_ridgeSupport_suffix_decode_2 584 032 15 865 32 060 033 833
cert_ridgeSupport_suffix_decode_2 584 031 15 897 32 060 032 865
cert_ridgeSupport_suffix_decode_2 584 030 15 929 32 060 031 897
cert_ridgeSupport_suffix_decode_2 584 029 15 961 32 060 030 929
cert_ridgeSupport_suffix_decode_2 584 028 15 993 32 060 029 961
cert_ridgeSupport_suffix_decode_2 584 027 15 1025 32 060 028 993
cert_ridgeSupport_suffix_decode_2 584 026 15 1057 32 060 027 1025
cert_ridgeSupport_suffix_decode_2 584 025 15 1089 32 060 026 1057
cert_ridgeSupport_suffix_decode_2 584 024 15 1121 32 060 025 1089
cert_ridgeSupport_suffix_decode_2 584 023 15 1153 32 060 024 1121
cert_ridgeSupport_suffix_decode_2 584 022 15 1185 32 060 023 1153
cert_ridgeSupport_suffix_decode_2 584 021 15 1217 32 060 022 1185
cert_ridgeSupport_suffix_decode_2 584 020 15 1249 32 060 021 1217
cert_ridgeSupport_suffix_decode_2 584 019 15 1281 32 060 020 1249
cert_ridgeSupport_suffix_decode_2 584 018 15 1313 32 060 019 1281
cert_ridgeSupport_suffix_decode_2 584 017 15 1345 32 060 018 1313
cert_ridgeSupport_suffix_decode_2 584 016 15 1377 32 060 017 1345
cert_ridgeSupport_suffix_decode_2 584 015 15 1409 32 060 016 1377
cert_ridgeSupport_suffix_decode_2 584 014 15 1441 32 060 015 1409
cert_ridgeSupport_suffix_decode_2 584 013 15 1473 32 060 014 1441
cert_ridgeSupport_suffix_decode_2 584 012 15 1505 32 060 013 1473
cert_ridgeSupport_suffix_decode_2 584 011 15 1537 32 060 012 1505
cert_ridgeSupport_suffix_decode_2 584 010 15 1569 32 060 011 1537
cert_ridgeSupport_suffix_decode_2 584 009 15 1601 32 060 010 1569
cert_ridgeSupport_suffix_decode_2 584 008 15 1633 32 060 009 1601
cert_ridgeSupport_suffix_decode_2 584 007 15 1665 32 060 008 1633
cert_ridgeSupport_suffix_decode_2 584 006 15 1697 32 060 007 1665
cert_ridgeSupport_suffix_decode_2 584 005 15 1729 32 060 006 1697
cert_ridgeSupport_suffix_decode_2 584 004 15 1761 32 060 005 1729
cert_ridgeSupport_suffix_decode_2 584 003 15 1793 32 060 004 1761
cert_ridgeSupport_suffix_decode_2 584 002 15 1825 32 060 003 1793
cert_ridgeSupport_suffix_decode_2 584 001 15 1857 32 060 002 1825
cert_ridgeSupport_suffix_decode_2 584 000 15 1889 32 060 001 1857
cert_ridgeSupport_eq_3 584
theorem ridgeTest_large_584 : ridgeTest 584 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport584_eq]
    simp only [ridgeSupport584_suffix_000, ridgeSupport584_suffix_001, ridgeSupport584_suffix_002, ridgeSupport584_suffix_003, ridgeSupport584_suffix_004, ridgeSupport584_suffix_005, ridgeSupport584_suffix_006, ridgeSupport584_suffix_007, ridgeSupport584_suffix_008, ridgeSupport584_suffix_009, ridgeSupport584_suffix_010, ridgeSupport584_suffix_011, ridgeSupport584_suffix_012, ridgeSupport584_suffix_013, ridgeSupport584_suffix_014, ridgeSupport584_suffix_015, ridgeSupport584_suffix_016, ridgeSupport584_suffix_017, ridgeSupport584_suffix_018, ridgeSupport584_suffix_019, ridgeSupport584_suffix_020, ridgeSupport584_suffix_021, ridgeSupport584_suffix_022, ridgeSupport584_suffix_023, ridgeSupport584_suffix_024, ridgeSupport584_suffix_025, ridgeSupport584_suffix_026, ridgeSupport584_suffix_027, ridgeSupport584_suffix_028, ridgeSupport584_suffix_029, ridgeSupport584_suffix_030, ridgeSupport584_suffix_031, ridgeSupport584_suffix_032, ridgeSupport584_suffix_033, ridgeSupport584_suffix_034, ridgeSupport584_suffix_035, ridgeSupport584_suffix_036, ridgeSupport584_suffix_037, ridgeSupport584_suffix_038, ridgeSupport584_suffix_039, ridgeSupport584_suffix_040, ridgeSupport584_suffix_041, ridgeSupport584_suffix_042, ridgeSupport584_suffix_043, ridgeSupport584_suffix_044, ridgeSupport584_suffix_045, ridgeSupport584_suffix_046, ridgeSupport584_suffix_047, ridgeSupport584_suffix_048, ridgeSupport584_suffix_049, ridgeSupport584_suffix_050, ridgeSupport584_suffix_051, ridgeSupport584_suffix_052, ridgeSupport584_suffix_053, ridgeSupport584_suffix_054, ridgeSupport584_suffix_055, ridgeSupport584_suffix_056, ridgeSupport584_suffix_057, ridgeSupport584_suffix_058, ridgeSupport584_suffix_059, ridgeSupport584_suffix_060, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport584_000_mask, ridgeSupport584_001_mask, ridgeSupport584_002_mask, ridgeSupport584_003_mask, ridgeSupport584_004_mask, ridgeSupport584_005_mask, ridgeSupport584_006_mask, ridgeSupport584_007_mask, ridgeSupport584_008_mask, ridgeSupport584_009_mask, ridgeSupport584_010_mask, ridgeSupport584_011_mask, ridgeSupport584_012_mask, ridgeSupport584_013_mask, ridgeSupport584_014_mask, ridgeSupport584_015_mask, ridgeSupport584_016_mask, ridgeSupport584_017_mask, ridgeSupport584_018_mask, ridgeSupport584_019_mask, ridgeSupport584_020_mask, ridgeSupport584_021_mask, ridgeSupport584_022_mask, ridgeSupport584_023_mask, ridgeSupport584_024_mask, ridgeSupport584_025_mask, ridgeSupport584_026_mask, ridgeSupport584_027_mask, ridgeSupport584_028_mask, ridgeSupport584_029_mask, ridgeSupport584_030_mask, ridgeSupport584_031_mask, ridgeSupport584_032_mask, ridgeSupport584_033_mask, ridgeSupport584_034_mask, ridgeSupport584_035_mask, ridgeSupport584_036_mask, ridgeSupport584_037_mask, ridgeSupport584_038_mask, ridgeSupport584_039_mask, ridgeSupport584_040_mask, ridgeSupport584_041_mask, ridgeSupport584_042_mask, ridgeSupport584_043_mask, ridgeSupport584_044_mask, ridgeSupport584_045_mask, ridgeSupport584_046_mask, ridgeSupport584_047_mask, ridgeSupport584_048_mask, ridgeSupport584_049_mask, ridgeSupport584_050_mask, ridgeSupport584_051_mask, ridgeSupport584_052_mask, ridgeSupport584_053_mask, ridgeSupport584_054_mask, ridgeSupport584_055_mask, ridgeSupport584_056_mask, ridgeSupport584_057_mask, ridgeSupport584_058_mask, ridgeSupport584_059_mask]
    decide +kernel
  · rw [ridgeSupport584_eq]
    simp only [ridgeSupport584_suffix_000, ridgeSupport584_suffix_001, ridgeSupport584_suffix_002, ridgeSupport584_suffix_003, ridgeSupport584_suffix_004, ridgeSupport584_suffix_005, ridgeSupport584_suffix_006, ridgeSupport584_suffix_007, ridgeSupport584_suffix_008, ridgeSupport584_suffix_009, ridgeSupport584_suffix_010, ridgeSupport584_suffix_011, ridgeSupport584_suffix_012, ridgeSupport584_suffix_013, ridgeSupport584_suffix_014, ridgeSupport584_suffix_015, ridgeSupport584_suffix_016, ridgeSupport584_suffix_017, ridgeSupport584_suffix_018, ridgeSupport584_suffix_019, ridgeSupport584_suffix_020, ridgeSupport584_suffix_021, ridgeSupport584_suffix_022, ridgeSupport584_suffix_023, ridgeSupport584_suffix_024, ridgeSupport584_suffix_025, ridgeSupport584_suffix_026, ridgeSupport584_suffix_027, ridgeSupport584_suffix_028, ridgeSupport584_suffix_029, ridgeSupport584_suffix_030, ridgeSupport584_suffix_031, ridgeSupport584_suffix_032, ridgeSupport584_suffix_033, ridgeSupport584_suffix_034, ridgeSupport584_suffix_035, ridgeSupport584_suffix_036, ridgeSupport584_suffix_037, ridgeSupport584_suffix_038, ridgeSupport584_suffix_039, ridgeSupport584_suffix_040, ridgeSupport584_suffix_041, ridgeSupport584_suffix_042, ridgeSupport584_suffix_043, ridgeSupport584_suffix_044, ridgeSupport584_suffix_045, ridgeSupport584_suffix_046, ridgeSupport584_suffix_047, ridgeSupport584_suffix_048, ridgeSupport584_suffix_049, ridgeSupport584_suffix_050, ridgeSupport584_suffix_051, ridgeSupport584_suffix_052, ridgeSupport584_suffix_053, ridgeSupport584_suffix_054, ridgeSupport584_suffix_055, ridgeSupport584_suffix_056, ridgeSupport584_suffix_057, ridgeSupport584_suffix_058, ridgeSupport584_suffix_059, ridgeSupport584_suffix_060, List.all_append, List.all_nil, ridgeSupport584_000_checked, ridgeSupport584_001_checked, ridgeSupport584_002_checked, ridgeSupport584_003_checked, ridgeSupport584_004_checked, ridgeSupport584_005_checked, ridgeSupport584_006_checked, ridgeSupport584_007_checked, ridgeSupport584_008_checked, ridgeSupport584_009_checked, ridgeSupport584_010_checked, ridgeSupport584_011_checked, ridgeSupport584_012_checked, ridgeSupport584_013_checked, ridgeSupport584_014_checked, ridgeSupport584_015_checked, ridgeSupport584_016_checked, ridgeSupport584_017_checked, ridgeSupport584_018_checked, ridgeSupport584_019_checked, ridgeSupport584_020_checked, ridgeSupport584_021_checked, ridgeSupport584_022_checked, ridgeSupport584_023_checked, ridgeSupport584_024_checked, ridgeSupport584_025_checked, ridgeSupport584_026_checked, ridgeSupport584_027_checked, ridgeSupport584_028_checked, ridgeSupport584_029_checked, ridgeSupport584_030_checked, ridgeSupport584_031_checked, ridgeSupport584_032_checked, ridgeSupport584_033_checked, ridgeSupport584_034_checked, ridgeSupport584_035_checked, ridgeSupport584_036_checked, ridgeSupport584_037_checked, ridgeSupport584_038_checked, ridgeSupport584_039_checked, ridgeSupport584_040_checked, ridgeSupport584_041_checked, ridgeSupport584_042_checked, ridgeSupport584_043_checked, ridgeSupport584_044_checked, ridgeSupport584_045_checked, ridgeSupport584_046_checked, ridgeSupport584_047_checked, ridgeSupport584_048_checked, ridgeSupport584_049_checked, ridgeSupport584_050_checked, ridgeSupport584_051_checked, ridgeSupport584_052_checked, ridgeSupport584_053_checked, ridgeSupport584_054_checked, ridgeSupport584_055_checked, ridgeSupport584_056_checked, ridgeSupport584_057_checked, ridgeSupport584_058_checked, ridgeSupport584_059_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
