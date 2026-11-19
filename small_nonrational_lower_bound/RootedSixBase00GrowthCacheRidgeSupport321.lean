module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport321Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 321 036 15
cert_ridgeSupport_suffix_decode_2 321 035 15 19 19 036 036 0
cert_ridgeSupport_suffix_decode_2 321 034 15 51 32 036 035 19
cert_ridgeSupport_suffix_decode_2 321 033 15 83 32 036 034 51
cert_ridgeSupport_suffix_decode_2 321 032 15 115 32 036 033 83
cert_ridgeSupport_suffix_decode_2 321 031 15 147 32 036 032 115
cert_ridgeSupport_suffix_decode_2 321 030 15 179 32 036 031 147
cert_ridgeSupport_suffix_decode_2 321 029 15 211 32 036 030 179
cert_ridgeSupport_suffix_decode_2 321 028 15 243 32 036 029 211
cert_ridgeSupport_suffix_decode_2 321 027 15 275 32 036 028 243
cert_ridgeSupport_suffix_decode_2 321 026 15 307 32 036 027 275
cert_ridgeSupport_suffix_decode_2 321 025 15 339 32 036 026 307
cert_ridgeSupport_suffix_decode_2 321 024 15 371 32 036 025 339
cert_ridgeSupport_suffix_decode_2 321 023 15 403 32 036 024 371
cert_ridgeSupport_suffix_decode_2 321 022 15 435 32 036 023 403
cert_ridgeSupport_suffix_decode_2 321 021 15 467 32 036 022 435
cert_ridgeSupport_suffix_decode_2 321 020 15 499 32 036 021 467
cert_ridgeSupport_suffix_decode_2 321 019 15 531 32 036 020 499
cert_ridgeSupport_suffix_decode_2 321 018 15 563 32 036 019 531
cert_ridgeSupport_suffix_decode_2 321 017 15 595 32 036 018 563
cert_ridgeSupport_suffix_decode_2 321 016 15 627 32 036 017 595
cert_ridgeSupport_suffix_decode_2 321 015 15 659 32 036 016 627
cert_ridgeSupport_suffix_decode_2 321 014 15 691 32 036 015 659
cert_ridgeSupport_suffix_decode_2 321 013 15 723 32 036 014 691
cert_ridgeSupport_suffix_decode_2 321 012 15 755 32 036 013 723
cert_ridgeSupport_suffix_decode_2 321 011 15 787 32 036 012 755
cert_ridgeSupport_suffix_decode_2 321 010 15 819 32 036 011 787
cert_ridgeSupport_suffix_decode_2 321 009 15 851 32 036 010 819
cert_ridgeSupport_suffix_decode_2 321 008 15 883 32 036 009 851
cert_ridgeSupport_suffix_decode_2 321 007 15 915 32 036 008 883
cert_ridgeSupport_suffix_decode_2 321 006 15 947 32 036 007 915
cert_ridgeSupport_suffix_decode_2 321 005 15 979 32 036 006 947
cert_ridgeSupport_suffix_decode_2 321 004 15 1011 32 036 005 979
cert_ridgeSupport_suffix_decode_2 321 003 15 1043 32 036 004 1011
cert_ridgeSupport_suffix_decode_2 321 002 15 1075 32 036 003 1043
cert_ridgeSupport_suffix_decode_2 321 001 15 1107 32 036 002 1075
cert_ridgeSupport_suffix_decode_2 321 000 15 1139 32 036 001 1107
cert_ridgeSupport_eq_3 321
theorem ridgeTest_large_321 : ridgeTest 321 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport321_eq]
    simp only [ridgeSupport321_suffix_000, ridgeSupport321_suffix_001, ridgeSupport321_suffix_002, ridgeSupport321_suffix_003, ridgeSupport321_suffix_004, ridgeSupport321_suffix_005, ridgeSupport321_suffix_006, ridgeSupport321_suffix_007, ridgeSupport321_suffix_008, ridgeSupport321_suffix_009, ridgeSupport321_suffix_010, ridgeSupport321_suffix_011, ridgeSupport321_suffix_012, ridgeSupport321_suffix_013, ridgeSupport321_suffix_014, ridgeSupport321_suffix_015, ridgeSupport321_suffix_016, ridgeSupport321_suffix_017, ridgeSupport321_suffix_018, ridgeSupport321_suffix_019, ridgeSupport321_suffix_020, ridgeSupport321_suffix_021, ridgeSupport321_suffix_022, ridgeSupport321_suffix_023, ridgeSupport321_suffix_024, ridgeSupport321_suffix_025, ridgeSupport321_suffix_026, ridgeSupport321_suffix_027, ridgeSupport321_suffix_028, ridgeSupport321_suffix_029, ridgeSupport321_suffix_030, ridgeSupport321_suffix_031, ridgeSupport321_suffix_032, ridgeSupport321_suffix_033, ridgeSupport321_suffix_034, ridgeSupport321_suffix_035, ridgeSupport321_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport321_000_mask, ridgeSupport321_001_mask, ridgeSupport321_002_mask, ridgeSupport321_003_mask, ridgeSupport321_004_mask, ridgeSupport321_005_mask, ridgeSupport321_006_mask, ridgeSupport321_007_mask, ridgeSupport321_008_mask, ridgeSupport321_009_mask, ridgeSupport321_010_mask, ridgeSupport321_011_mask, ridgeSupport321_012_mask, ridgeSupport321_013_mask, ridgeSupport321_014_mask, ridgeSupport321_015_mask, ridgeSupport321_016_mask, ridgeSupport321_017_mask, ridgeSupport321_018_mask, ridgeSupport321_019_mask, ridgeSupport321_020_mask, ridgeSupport321_021_mask, ridgeSupport321_022_mask, ridgeSupport321_023_mask, ridgeSupport321_024_mask, ridgeSupport321_025_mask, ridgeSupport321_026_mask, ridgeSupport321_027_mask, ridgeSupport321_028_mask, ridgeSupport321_029_mask, ridgeSupport321_030_mask, ridgeSupport321_031_mask, ridgeSupport321_032_mask, ridgeSupport321_033_mask, ridgeSupport321_034_mask, ridgeSupport321_035_mask]
    decide +kernel
  · rw [ridgeSupport321_eq]
    simp only [ridgeSupport321_suffix_000, ridgeSupport321_suffix_001, ridgeSupport321_suffix_002, ridgeSupport321_suffix_003, ridgeSupport321_suffix_004, ridgeSupport321_suffix_005, ridgeSupport321_suffix_006, ridgeSupport321_suffix_007, ridgeSupport321_suffix_008, ridgeSupport321_suffix_009, ridgeSupport321_suffix_010, ridgeSupport321_suffix_011, ridgeSupport321_suffix_012, ridgeSupport321_suffix_013, ridgeSupport321_suffix_014, ridgeSupport321_suffix_015, ridgeSupport321_suffix_016, ridgeSupport321_suffix_017, ridgeSupport321_suffix_018, ridgeSupport321_suffix_019, ridgeSupport321_suffix_020, ridgeSupport321_suffix_021, ridgeSupport321_suffix_022, ridgeSupport321_suffix_023, ridgeSupport321_suffix_024, ridgeSupport321_suffix_025, ridgeSupport321_suffix_026, ridgeSupport321_suffix_027, ridgeSupport321_suffix_028, ridgeSupport321_suffix_029, ridgeSupport321_suffix_030, ridgeSupport321_suffix_031, ridgeSupport321_suffix_032, ridgeSupport321_suffix_033, ridgeSupport321_suffix_034, ridgeSupport321_suffix_035, ridgeSupport321_suffix_036, List.all_append, List.all_nil, ridgeSupport321_000_checked, ridgeSupport321_001_checked, ridgeSupport321_002_checked, ridgeSupport321_003_checked, ridgeSupport321_004_checked, ridgeSupport321_005_checked, ridgeSupport321_006_checked, ridgeSupport321_007_checked, ridgeSupport321_008_checked, ridgeSupport321_009_checked, ridgeSupport321_010_checked, ridgeSupport321_011_checked, ridgeSupport321_012_checked, ridgeSupport321_013_checked, ridgeSupport321_014_checked, ridgeSupport321_015_checked, ridgeSupport321_016_checked, ridgeSupport321_017_checked, ridgeSupport321_018_checked, ridgeSupport321_019_checked, ridgeSupport321_020_checked, ridgeSupport321_021_checked, ridgeSupport321_022_checked, ridgeSupport321_023_checked, ridgeSupport321_024_checked, ridgeSupport321_025_checked, ridgeSupport321_026_checked, ridgeSupport321_027_checked, ridgeSupport321_028_checked, ridgeSupport321_029_checked, ridgeSupport321_030_checked, ridgeSupport321_031_checked, ridgeSupport321_032_checked, ridgeSupport321_033_checked, ridgeSupport321_034_checked, ridgeSupport321_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
