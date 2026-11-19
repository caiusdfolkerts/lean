module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport386Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 386 048 15
cert_ridgeSupport_suffix_decode_2 386 047 15 10 10 048 048 0
cert_ridgeSupport_suffix_decode_2 386 046 15 42 32 048 047 10
cert_ridgeSupport_suffix_decode_2 386 045 15 74 32 048 046 42
cert_ridgeSupport_suffix_decode_2 386 044 15 106 32 048 045 74
cert_ridgeSupport_suffix_decode_2 386 043 15 138 32 048 044 106
cert_ridgeSupport_suffix_decode_2 386 042 15 170 32 048 043 138
cert_ridgeSupport_suffix_decode_2 386 041 15 202 32 048 042 170
cert_ridgeSupport_suffix_decode_2 386 040 15 234 32 048 041 202
cert_ridgeSupport_suffix_decode_2 386 039 15 266 32 048 040 234
cert_ridgeSupport_suffix_decode_2 386 038 15 298 32 048 039 266
cert_ridgeSupport_suffix_decode_2 386 037 15 330 32 048 038 298
cert_ridgeSupport_suffix_decode_2 386 036 15 362 32 048 037 330
cert_ridgeSupport_suffix_decode_2 386 035 15 394 32 048 036 362
cert_ridgeSupport_suffix_decode_2 386 034 15 426 32 048 035 394
cert_ridgeSupport_suffix_decode_2 386 033 15 458 32 048 034 426
cert_ridgeSupport_suffix_decode_2 386 032 15 490 32 048 033 458
cert_ridgeSupport_suffix_decode_2 386 031 15 522 32 048 032 490
cert_ridgeSupport_suffix_decode_2 386 030 15 554 32 048 031 522
cert_ridgeSupport_suffix_decode_2 386 029 15 586 32 048 030 554
cert_ridgeSupport_suffix_decode_2 386 028 15 618 32 048 029 586
cert_ridgeSupport_suffix_decode_2 386 027 15 650 32 048 028 618
cert_ridgeSupport_suffix_decode_2 386 026 15 682 32 048 027 650
cert_ridgeSupport_suffix_decode_2 386 025 15 714 32 048 026 682
cert_ridgeSupport_suffix_decode_2 386 024 15 746 32 048 025 714
cert_ridgeSupport_suffix_decode_2 386 023 15 778 32 048 024 746
cert_ridgeSupport_suffix_decode_2 386 022 15 810 32 048 023 778
cert_ridgeSupport_suffix_decode_2 386 021 15 842 32 048 022 810
cert_ridgeSupport_suffix_decode_2 386 020 15 874 32 048 021 842
cert_ridgeSupport_suffix_decode_2 386 019 15 906 32 048 020 874
cert_ridgeSupport_suffix_decode_2 386 018 15 938 32 048 019 906
cert_ridgeSupport_suffix_decode_2 386 017 15 970 32 048 018 938
cert_ridgeSupport_suffix_decode_2 386 016 15 1002 32 048 017 970
cert_ridgeSupport_suffix_decode_2 386 015 15 1034 32 048 016 1002
cert_ridgeSupport_suffix_decode_2 386 014 15 1066 32 048 015 1034
cert_ridgeSupport_suffix_decode_2 386 013 15 1098 32 048 014 1066
cert_ridgeSupport_suffix_decode_2 386 012 15 1130 32 048 013 1098
cert_ridgeSupport_suffix_decode_2 386 011 15 1162 32 048 012 1130
cert_ridgeSupport_suffix_decode_2 386 010 15 1194 32 048 011 1162
cert_ridgeSupport_suffix_decode_2 386 009 15 1226 32 048 010 1194
cert_ridgeSupport_suffix_decode_2 386 008 15 1258 32 048 009 1226
cert_ridgeSupport_suffix_decode_2 386 007 15 1290 32 048 008 1258
cert_ridgeSupport_suffix_decode_2 386 006 15 1322 32 048 007 1290
cert_ridgeSupport_suffix_decode_2 386 005 15 1354 32 048 006 1322
cert_ridgeSupport_suffix_decode_2 386 004 15 1386 32 048 005 1354
cert_ridgeSupport_suffix_decode_2 386 003 15 1418 32 048 004 1386
cert_ridgeSupport_suffix_decode_2 386 002 15 1450 32 048 003 1418
cert_ridgeSupport_suffix_decode_2 386 001 15 1482 32 048 002 1450
cert_ridgeSupport_suffix_decode_2 386 000 15 1514 32 048 001 1482
cert_ridgeSupport_eq_3 386
theorem ridgeTest_large_386 : ridgeTest 386 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport386_eq]
    simp only [ridgeSupport386_suffix_000, ridgeSupport386_suffix_001, ridgeSupport386_suffix_002, ridgeSupport386_suffix_003, ridgeSupport386_suffix_004, ridgeSupport386_suffix_005, ridgeSupport386_suffix_006, ridgeSupport386_suffix_007, ridgeSupport386_suffix_008, ridgeSupport386_suffix_009, ridgeSupport386_suffix_010, ridgeSupport386_suffix_011, ridgeSupport386_suffix_012, ridgeSupport386_suffix_013, ridgeSupport386_suffix_014, ridgeSupport386_suffix_015, ridgeSupport386_suffix_016, ridgeSupport386_suffix_017, ridgeSupport386_suffix_018, ridgeSupport386_suffix_019, ridgeSupport386_suffix_020, ridgeSupport386_suffix_021, ridgeSupport386_suffix_022, ridgeSupport386_suffix_023, ridgeSupport386_suffix_024, ridgeSupport386_suffix_025, ridgeSupport386_suffix_026, ridgeSupport386_suffix_027, ridgeSupport386_suffix_028, ridgeSupport386_suffix_029, ridgeSupport386_suffix_030, ridgeSupport386_suffix_031, ridgeSupport386_suffix_032, ridgeSupport386_suffix_033, ridgeSupport386_suffix_034, ridgeSupport386_suffix_035, ridgeSupport386_suffix_036, ridgeSupport386_suffix_037, ridgeSupport386_suffix_038, ridgeSupport386_suffix_039, ridgeSupport386_suffix_040, ridgeSupport386_suffix_041, ridgeSupport386_suffix_042, ridgeSupport386_suffix_043, ridgeSupport386_suffix_044, ridgeSupport386_suffix_045, ridgeSupport386_suffix_046, ridgeSupport386_suffix_047, ridgeSupport386_suffix_048, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport386_000_mask, ridgeSupport386_001_mask, ridgeSupport386_002_mask, ridgeSupport386_003_mask, ridgeSupport386_004_mask, ridgeSupport386_005_mask, ridgeSupport386_006_mask, ridgeSupport386_007_mask, ridgeSupport386_008_mask, ridgeSupport386_009_mask, ridgeSupport386_010_mask, ridgeSupport386_011_mask, ridgeSupport386_012_mask, ridgeSupport386_013_mask, ridgeSupport386_014_mask, ridgeSupport386_015_mask, ridgeSupport386_016_mask, ridgeSupport386_017_mask, ridgeSupport386_018_mask, ridgeSupport386_019_mask, ridgeSupport386_020_mask, ridgeSupport386_021_mask, ridgeSupport386_022_mask, ridgeSupport386_023_mask, ridgeSupport386_024_mask, ridgeSupport386_025_mask, ridgeSupport386_026_mask, ridgeSupport386_027_mask, ridgeSupport386_028_mask, ridgeSupport386_029_mask, ridgeSupport386_030_mask, ridgeSupport386_031_mask, ridgeSupport386_032_mask, ridgeSupport386_033_mask, ridgeSupport386_034_mask, ridgeSupport386_035_mask, ridgeSupport386_036_mask, ridgeSupport386_037_mask, ridgeSupport386_038_mask, ridgeSupport386_039_mask, ridgeSupport386_040_mask, ridgeSupport386_041_mask, ridgeSupport386_042_mask, ridgeSupport386_043_mask, ridgeSupport386_044_mask, ridgeSupport386_045_mask, ridgeSupport386_046_mask, ridgeSupport386_047_mask]
    decide +kernel
  · rw [ridgeSupport386_eq]
    simp only [ridgeSupport386_suffix_000, ridgeSupport386_suffix_001, ridgeSupport386_suffix_002, ridgeSupport386_suffix_003, ridgeSupport386_suffix_004, ridgeSupport386_suffix_005, ridgeSupport386_suffix_006, ridgeSupport386_suffix_007, ridgeSupport386_suffix_008, ridgeSupport386_suffix_009, ridgeSupport386_suffix_010, ridgeSupport386_suffix_011, ridgeSupport386_suffix_012, ridgeSupport386_suffix_013, ridgeSupport386_suffix_014, ridgeSupport386_suffix_015, ridgeSupport386_suffix_016, ridgeSupport386_suffix_017, ridgeSupport386_suffix_018, ridgeSupport386_suffix_019, ridgeSupport386_suffix_020, ridgeSupport386_suffix_021, ridgeSupport386_suffix_022, ridgeSupport386_suffix_023, ridgeSupport386_suffix_024, ridgeSupport386_suffix_025, ridgeSupport386_suffix_026, ridgeSupport386_suffix_027, ridgeSupport386_suffix_028, ridgeSupport386_suffix_029, ridgeSupport386_suffix_030, ridgeSupport386_suffix_031, ridgeSupport386_suffix_032, ridgeSupport386_suffix_033, ridgeSupport386_suffix_034, ridgeSupport386_suffix_035, ridgeSupport386_suffix_036, ridgeSupport386_suffix_037, ridgeSupport386_suffix_038, ridgeSupport386_suffix_039, ridgeSupport386_suffix_040, ridgeSupport386_suffix_041, ridgeSupport386_suffix_042, ridgeSupport386_suffix_043, ridgeSupport386_suffix_044, ridgeSupport386_suffix_045, ridgeSupport386_suffix_046, ridgeSupport386_suffix_047, ridgeSupport386_suffix_048, List.all_append, List.all_nil, ridgeSupport386_000_checked, ridgeSupport386_001_checked, ridgeSupport386_002_checked, ridgeSupport386_003_checked, ridgeSupport386_004_checked, ridgeSupport386_005_checked, ridgeSupport386_006_checked, ridgeSupport386_007_checked, ridgeSupport386_008_checked, ridgeSupport386_009_checked, ridgeSupport386_010_checked, ridgeSupport386_011_checked, ridgeSupport386_012_checked, ridgeSupport386_013_checked, ridgeSupport386_014_checked, ridgeSupport386_015_checked, ridgeSupport386_016_checked, ridgeSupport386_017_checked, ridgeSupport386_018_checked, ridgeSupport386_019_checked, ridgeSupport386_020_checked, ridgeSupport386_021_checked, ridgeSupport386_022_checked, ridgeSupport386_023_checked, ridgeSupport386_024_checked, ridgeSupport386_025_checked, ridgeSupport386_026_checked, ridgeSupport386_027_checked, ridgeSupport386_028_checked, ridgeSupport386_029_checked, ridgeSupport386_030_checked, ridgeSupport386_031_checked, ridgeSupport386_032_checked, ridgeSupport386_033_checked, ridgeSupport386_034_checked, ridgeSupport386_035_checked, ridgeSupport386_036_checked, ridgeSupport386_037_checked, ridgeSupport386_038_checked, ridgeSupport386_039_checked, ridgeSupport386_040_checked, ridgeSupport386_041_checked, ridgeSupport386_042_checked, ridgeSupport386_043_checked, ridgeSupport386_044_checked, ridgeSupport386_045_checked, ridgeSupport386_046_checked, ridgeSupport386_047_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
