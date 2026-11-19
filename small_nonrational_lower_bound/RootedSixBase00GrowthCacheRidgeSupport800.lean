module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport800Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 800 036 15
cert_ridgeSupport_suffix_decode_2 800 035 15 19 19 036 036 0
cert_ridgeSupport_suffix_decode_2 800 034 15 51 32 036 035 19
cert_ridgeSupport_suffix_decode_2 800 033 15 83 32 036 034 51
cert_ridgeSupport_suffix_decode_2 800 032 15 115 32 036 033 83
cert_ridgeSupport_suffix_decode_2 800 031 15 147 32 036 032 115
cert_ridgeSupport_suffix_decode_2 800 030 15 179 32 036 031 147
cert_ridgeSupport_suffix_decode_2 800 029 15 211 32 036 030 179
cert_ridgeSupport_suffix_decode_2 800 028 15 243 32 036 029 211
cert_ridgeSupport_suffix_decode_2 800 027 15 275 32 036 028 243
cert_ridgeSupport_suffix_decode_2 800 026 15 307 32 036 027 275
cert_ridgeSupport_suffix_decode_2 800 025 15 339 32 036 026 307
cert_ridgeSupport_suffix_decode_2 800 024 15 371 32 036 025 339
cert_ridgeSupport_suffix_decode_2 800 023 15 403 32 036 024 371
cert_ridgeSupport_suffix_decode_2 800 022 15 435 32 036 023 403
cert_ridgeSupport_suffix_decode_2 800 021 15 467 32 036 022 435
cert_ridgeSupport_suffix_decode_2 800 020 15 499 32 036 021 467
cert_ridgeSupport_suffix_decode_2 800 019 15 531 32 036 020 499
cert_ridgeSupport_suffix_decode_2 800 018 15 563 32 036 019 531
cert_ridgeSupport_suffix_decode_2 800 017 15 595 32 036 018 563
cert_ridgeSupport_suffix_decode_2 800 016 15 627 32 036 017 595
cert_ridgeSupport_suffix_decode_2 800 015 15 659 32 036 016 627
cert_ridgeSupport_suffix_decode_2 800 014 15 691 32 036 015 659
cert_ridgeSupport_suffix_decode_2 800 013 15 723 32 036 014 691
cert_ridgeSupport_suffix_decode_2 800 012 15 755 32 036 013 723
cert_ridgeSupport_suffix_decode_2 800 011 15 787 32 036 012 755
cert_ridgeSupport_suffix_decode_2 800 010 15 819 32 036 011 787
cert_ridgeSupport_suffix_decode_2 800 009 15 851 32 036 010 819
cert_ridgeSupport_suffix_decode_2 800 008 15 883 32 036 009 851
cert_ridgeSupport_suffix_decode_2 800 007 15 915 32 036 008 883
cert_ridgeSupport_suffix_decode_2 800 006 15 947 32 036 007 915
cert_ridgeSupport_suffix_decode_2 800 005 15 979 32 036 006 947
cert_ridgeSupport_suffix_decode_2 800 004 15 1011 32 036 005 979
cert_ridgeSupport_suffix_decode_2 800 003 15 1043 32 036 004 1011
cert_ridgeSupport_suffix_decode_2 800 002 15 1075 32 036 003 1043
cert_ridgeSupport_suffix_decode_2 800 001 15 1107 32 036 002 1075
cert_ridgeSupport_suffix_decode_2 800 000 15 1139 32 036 001 1107
cert_ridgeSupport_eq_3 800
theorem ridgeTest_large_800 : ridgeTest 800 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport800_eq]
    simp only [ridgeSupport800_suffix_000, ridgeSupport800_suffix_001, ridgeSupport800_suffix_002, ridgeSupport800_suffix_003, ridgeSupport800_suffix_004, ridgeSupport800_suffix_005, ridgeSupport800_suffix_006, ridgeSupport800_suffix_007, ridgeSupport800_suffix_008, ridgeSupport800_suffix_009, ridgeSupport800_suffix_010, ridgeSupport800_suffix_011, ridgeSupport800_suffix_012, ridgeSupport800_suffix_013, ridgeSupport800_suffix_014, ridgeSupport800_suffix_015, ridgeSupport800_suffix_016, ridgeSupport800_suffix_017, ridgeSupport800_suffix_018, ridgeSupport800_suffix_019, ridgeSupport800_suffix_020, ridgeSupport800_suffix_021, ridgeSupport800_suffix_022, ridgeSupport800_suffix_023, ridgeSupport800_suffix_024, ridgeSupport800_suffix_025, ridgeSupport800_suffix_026, ridgeSupport800_suffix_027, ridgeSupport800_suffix_028, ridgeSupport800_suffix_029, ridgeSupport800_suffix_030, ridgeSupport800_suffix_031, ridgeSupport800_suffix_032, ridgeSupport800_suffix_033, ridgeSupport800_suffix_034, ridgeSupport800_suffix_035, ridgeSupport800_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport800_000_mask, ridgeSupport800_001_mask, ridgeSupport800_002_mask, ridgeSupport800_003_mask, ridgeSupport800_004_mask, ridgeSupport800_005_mask, ridgeSupport800_006_mask, ridgeSupport800_007_mask, ridgeSupport800_008_mask, ridgeSupport800_009_mask, ridgeSupport800_010_mask, ridgeSupport800_011_mask, ridgeSupport800_012_mask, ridgeSupport800_013_mask, ridgeSupport800_014_mask, ridgeSupport800_015_mask, ridgeSupport800_016_mask, ridgeSupport800_017_mask, ridgeSupport800_018_mask, ridgeSupport800_019_mask, ridgeSupport800_020_mask, ridgeSupport800_021_mask, ridgeSupport800_022_mask, ridgeSupport800_023_mask, ridgeSupport800_024_mask, ridgeSupport800_025_mask, ridgeSupport800_026_mask, ridgeSupport800_027_mask, ridgeSupport800_028_mask, ridgeSupport800_029_mask, ridgeSupport800_030_mask, ridgeSupport800_031_mask, ridgeSupport800_032_mask, ridgeSupport800_033_mask, ridgeSupport800_034_mask, ridgeSupport800_035_mask]
    decide +kernel
  · rw [ridgeSupport800_eq]
    simp only [ridgeSupport800_suffix_000, ridgeSupport800_suffix_001, ridgeSupport800_suffix_002, ridgeSupport800_suffix_003, ridgeSupport800_suffix_004, ridgeSupport800_suffix_005, ridgeSupport800_suffix_006, ridgeSupport800_suffix_007, ridgeSupport800_suffix_008, ridgeSupport800_suffix_009, ridgeSupport800_suffix_010, ridgeSupport800_suffix_011, ridgeSupport800_suffix_012, ridgeSupport800_suffix_013, ridgeSupport800_suffix_014, ridgeSupport800_suffix_015, ridgeSupport800_suffix_016, ridgeSupport800_suffix_017, ridgeSupport800_suffix_018, ridgeSupport800_suffix_019, ridgeSupport800_suffix_020, ridgeSupport800_suffix_021, ridgeSupport800_suffix_022, ridgeSupport800_suffix_023, ridgeSupport800_suffix_024, ridgeSupport800_suffix_025, ridgeSupport800_suffix_026, ridgeSupport800_suffix_027, ridgeSupport800_suffix_028, ridgeSupport800_suffix_029, ridgeSupport800_suffix_030, ridgeSupport800_suffix_031, ridgeSupport800_suffix_032, ridgeSupport800_suffix_033, ridgeSupport800_suffix_034, ridgeSupport800_suffix_035, ridgeSupport800_suffix_036, List.all_append, List.all_nil, ridgeSupport800_000_checked, ridgeSupport800_001_checked, ridgeSupport800_002_checked, ridgeSupport800_003_checked, ridgeSupport800_004_checked, ridgeSupport800_005_checked, ridgeSupport800_006_checked, ridgeSupport800_007_checked, ridgeSupport800_008_checked, ridgeSupport800_009_checked, ridgeSupport800_010_checked, ridgeSupport800_011_checked, ridgeSupport800_012_checked, ridgeSupport800_013_checked, ridgeSupport800_014_checked, ridgeSupport800_015_checked, ridgeSupport800_016_checked, ridgeSupport800_017_checked, ridgeSupport800_018_checked, ridgeSupport800_019_checked, ridgeSupport800_020_checked, ridgeSupport800_021_checked, ridgeSupport800_022_checked, ridgeSupport800_023_checked, ridgeSupport800_024_checked, ridgeSupport800_025_checked, ridgeSupport800_026_checked, ridgeSupport800_027_checked, ridgeSupport800_028_checked, ridgeSupport800_029_checked, ridgeSupport800_030_checked, ridgeSupport800_031_checked, ridgeSupport800_032_checked, ridgeSupport800_033_checked, ridgeSupport800_034_checked, ridgeSupport800_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
