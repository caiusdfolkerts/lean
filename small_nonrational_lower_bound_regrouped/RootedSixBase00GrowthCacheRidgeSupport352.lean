module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport352Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 352 036 15
cert_ridgeSupport_suffix_decode_2 352 035 15 19 19 036 036 0
cert_ridgeSupport_suffix_decode_2 352 034 15 51 32 036 035 19
cert_ridgeSupport_suffix_decode_2 352 033 15 83 32 036 034 51
cert_ridgeSupport_suffix_decode_2 352 032 15 115 32 036 033 83
cert_ridgeSupport_suffix_decode_2 352 031 15 147 32 036 032 115
cert_ridgeSupport_suffix_decode_2 352 030 15 179 32 036 031 147
cert_ridgeSupport_suffix_decode_2 352 029 15 211 32 036 030 179
cert_ridgeSupport_suffix_decode_2 352 028 15 243 32 036 029 211
cert_ridgeSupport_suffix_decode_2 352 027 15 275 32 036 028 243
cert_ridgeSupport_suffix_decode_2 352 026 15 307 32 036 027 275
cert_ridgeSupport_suffix_decode_2 352 025 15 339 32 036 026 307
cert_ridgeSupport_suffix_decode_2 352 024 15 371 32 036 025 339
cert_ridgeSupport_suffix_decode_2 352 023 15 403 32 036 024 371
cert_ridgeSupport_suffix_decode_2 352 022 15 435 32 036 023 403
cert_ridgeSupport_suffix_decode_2 352 021 15 467 32 036 022 435
cert_ridgeSupport_suffix_decode_2 352 020 15 499 32 036 021 467
cert_ridgeSupport_suffix_decode_2 352 019 15 531 32 036 020 499
cert_ridgeSupport_suffix_decode_2 352 018 15 563 32 036 019 531
cert_ridgeSupport_suffix_decode_2 352 017 15 595 32 036 018 563
cert_ridgeSupport_suffix_decode_2 352 016 15 627 32 036 017 595
cert_ridgeSupport_suffix_decode_2 352 015 15 659 32 036 016 627
cert_ridgeSupport_suffix_decode_2 352 014 15 691 32 036 015 659
cert_ridgeSupport_suffix_decode_2 352 013 15 723 32 036 014 691
cert_ridgeSupport_suffix_decode_2 352 012 15 755 32 036 013 723
cert_ridgeSupport_suffix_decode_2 352 011 15 787 32 036 012 755
cert_ridgeSupport_suffix_decode_2 352 010 15 819 32 036 011 787
cert_ridgeSupport_suffix_decode_2 352 009 15 851 32 036 010 819
cert_ridgeSupport_suffix_decode_2 352 008 15 883 32 036 009 851
cert_ridgeSupport_suffix_decode_2 352 007 15 915 32 036 008 883
cert_ridgeSupport_suffix_decode_2 352 006 15 947 32 036 007 915
cert_ridgeSupport_suffix_decode_2 352 005 15 979 32 036 006 947
cert_ridgeSupport_suffix_decode_2 352 004 15 1011 32 036 005 979
cert_ridgeSupport_suffix_decode_2 352 003 15 1043 32 036 004 1011
cert_ridgeSupport_suffix_decode_2 352 002 15 1075 32 036 003 1043
cert_ridgeSupport_suffix_decode_2 352 001 15 1107 32 036 002 1075
cert_ridgeSupport_suffix_decode_2 352 000 15 1139 32 036 001 1107
cert_ridgeSupport_eq_3 352
theorem ridgeTest_large_352 : ridgeTest 352 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport352_eq]
    simp only [ridgeSupport352_suffix_000, ridgeSupport352_suffix_001, ridgeSupport352_suffix_002, ridgeSupport352_suffix_003, ridgeSupport352_suffix_004, ridgeSupport352_suffix_005, ridgeSupport352_suffix_006, ridgeSupport352_suffix_007, ridgeSupport352_suffix_008, ridgeSupport352_suffix_009, ridgeSupport352_suffix_010, ridgeSupport352_suffix_011, ridgeSupport352_suffix_012, ridgeSupport352_suffix_013, ridgeSupport352_suffix_014, ridgeSupport352_suffix_015, ridgeSupport352_suffix_016, ridgeSupport352_suffix_017, ridgeSupport352_suffix_018, ridgeSupport352_suffix_019, ridgeSupport352_suffix_020, ridgeSupport352_suffix_021, ridgeSupport352_suffix_022, ridgeSupport352_suffix_023, ridgeSupport352_suffix_024, ridgeSupport352_suffix_025, ridgeSupport352_suffix_026, ridgeSupport352_suffix_027, ridgeSupport352_suffix_028, ridgeSupport352_suffix_029, ridgeSupport352_suffix_030, ridgeSupport352_suffix_031, ridgeSupport352_suffix_032, ridgeSupport352_suffix_033, ridgeSupport352_suffix_034, ridgeSupport352_suffix_035, ridgeSupport352_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport352_000_mask, ridgeSupport352_001_mask, ridgeSupport352_002_mask, ridgeSupport352_003_mask, ridgeSupport352_004_mask, ridgeSupport352_005_mask, ridgeSupport352_006_mask, ridgeSupport352_007_mask, ridgeSupport352_008_mask, ridgeSupport352_009_mask, ridgeSupport352_010_mask, ridgeSupport352_011_mask, ridgeSupport352_012_mask, ridgeSupport352_013_mask, ridgeSupport352_014_mask, ridgeSupport352_015_mask, ridgeSupport352_016_mask, ridgeSupport352_017_mask, ridgeSupport352_018_mask, ridgeSupport352_019_mask, ridgeSupport352_020_mask, ridgeSupport352_021_mask, ridgeSupport352_022_mask, ridgeSupport352_023_mask, ridgeSupport352_024_mask, ridgeSupport352_025_mask, ridgeSupport352_026_mask, ridgeSupport352_027_mask, ridgeSupport352_028_mask, ridgeSupport352_029_mask, ridgeSupport352_030_mask, ridgeSupport352_031_mask, ridgeSupport352_032_mask, ridgeSupport352_033_mask, ridgeSupport352_034_mask, ridgeSupport352_035_mask]
    decide +kernel
  · rw [ridgeSupport352_eq]
    simp only [ridgeSupport352_suffix_000, ridgeSupport352_suffix_001, ridgeSupport352_suffix_002, ridgeSupport352_suffix_003, ridgeSupport352_suffix_004, ridgeSupport352_suffix_005, ridgeSupport352_suffix_006, ridgeSupport352_suffix_007, ridgeSupport352_suffix_008, ridgeSupport352_suffix_009, ridgeSupport352_suffix_010, ridgeSupport352_suffix_011, ridgeSupport352_suffix_012, ridgeSupport352_suffix_013, ridgeSupport352_suffix_014, ridgeSupport352_suffix_015, ridgeSupport352_suffix_016, ridgeSupport352_suffix_017, ridgeSupport352_suffix_018, ridgeSupport352_suffix_019, ridgeSupport352_suffix_020, ridgeSupport352_suffix_021, ridgeSupport352_suffix_022, ridgeSupport352_suffix_023, ridgeSupport352_suffix_024, ridgeSupport352_suffix_025, ridgeSupport352_suffix_026, ridgeSupport352_suffix_027, ridgeSupport352_suffix_028, ridgeSupport352_suffix_029, ridgeSupport352_suffix_030, ridgeSupport352_suffix_031, ridgeSupport352_suffix_032, ridgeSupport352_suffix_033, ridgeSupport352_suffix_034, ridgeSupport352_suffix_035, ridgeSupport352_suffix_036, List.all_append, List.all_nil, ridgeSupport352_000_checked, ridgeSupport352_001_checked, ridgeSupport352_002_checked, ridgeSupport352_003_checked, ridgeSupport352_004_checked, ridgeSupport352_005_checked, ridgeSupport352_006_checked, ridgeSupport352_007_checked, ridgeSupport352_008_checked, ridgeSupport352_009_checked, ridgeSupport352_010_checked, ridgeSupport352_011_checked, ridgeSupport352_012_checked, ridgeSupport352_013_checked, ridgeSupport352_014_checked, ridgeSupport352_015_checked, ridgeSupport352_016_checked, ridgeSupport352_017_checked, ridgeSupport352_018_checked, ridgeSupport352_019_checked, ridgeSupport352_020_checked, ridgeSupport352_021_checked, ridgeSupport352_022_checked, ridgeSupport352_023_checked, ridgeSupport352_024_checked, ridgeSupport352_025_checked, ridgeSupport352_026_checked, ridgeSupport352_027_checked, ridgeSupport352_028_checked, ridgeSupport352_029_checked, ridgeSupport352_030_checked, ridgeSupport352_031_checked, ridgeSupport352_032_checked, ridgeSupport352_033_checked, ridgeSupport352_034_checked, ridgeSupport352_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
