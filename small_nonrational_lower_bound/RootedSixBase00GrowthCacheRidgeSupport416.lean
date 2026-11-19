module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport416Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 416 036 15
cert_ridgeSupport_suffix_decode_2 416 035 15 19 19 036 036 0
cert_ridgeSupport_suffix_decode_2 416 034 15 51 32 036 035 19
cert_ridgeSupport_suffix_decode_2 416 033 15 83 32 036 034 51
cert_ridgeSupport_suffix_decode_2 416 032 15 115 32 036 033 83
cert_ridgeSupport_suffix_decode_2 416 031 15 147 32 036 032 115
cert_ridgeSupport_suffix_decode_2 416 030 15 179 32 036 031 147
cert_ridgeSupport_suffix_decode_2 416 029 15 211 32 036 030 179
cert_ridgeSupport_suffix_decode_2 416 028 15 243 32 036 029 211
cert_ridgeSupport_suffix_decode_2 416 027 15 275 32 036 028 243
cert_ridgeSupport_suffix_decode_2 416 026 15 307 32 036 027 275
cert_ridgeSupport_suffix_decode_2 416 025 15 339 32 036 026 307
cert_ridgeSupport_suffix_decode_2 416 024 15 371 32 036 025 339
cert_ridgeSupport_suffix_decode_2 416 023 15 403 32 036 024 371
cert_ridgeSupport_suffix_decode_2 416 022 15 435 32 036 023 403
cert_ridgeSupport_suffix_decode_2 416 021 15 467 32 036 022 435
cert_ridgeSupport_suffix_decode_2 416 020 15 499 32 036 021 467
cert_ridgeSupport_suffix_decode_2 416 019 15 531 32 036 020 499
cert_ridgeSupport_suffix_decode_2 416 018 15 563 32 036 019 531
cert_ridgeSupport_suffix_decode_2 416 017 15 595 32 036 018 563
cert_ridgeSupport_suffix_decode_2 416 016 15 627 32 036 017 595
cert_ridgeSupport_suffix_decode_2 416 015 15 659 32 036 016 627
cert_ridgeSupport_suffix_decode_2 416 014 15 691 32 036 015 659
cert_ridgeSupport_suffix_decode_2 416 013 15 723 32 036 014 691
cert_ridgeSupport_suffix_decode_2 416 012 15 755 32 036 013 723
cert_ridgeSupport_suffix_decode_2 416 011 15 787 32 036 012 755
cert_ridgeSupport_suffix_decode_2 416 010 15 819 32 036 011 787
cert_ridgeSupport_suffix_decode_2 416 009 15 851 32 036 010 819
cert_ridgeSupport_suffix_decode_2 416 008 15 883 32 036 009 851
cert_ridgeSupport_suffix_decode_2 416 007 15 915 32 036 008 883
cert_ridgeSupport_suffix_decode_2 416 006 15 947 32 036 007 915
cert_ridgeSupport_suffix_decode_2 416 005 15 979 32 036 006 947
cert_ridgeSupport_suffix_decode_2 416 004 15 1011 32 036 005 979
cert_ridgeSupport_suffix_decode_2 416 003 15 1043 32 036 004 1011
cert_ridgeSupport_suffix_decode_2 416 002 15 1075 32 036 003 1043
cert_ridgeSupport_suffix_decode_2 416 001 15 1107 32 036 002 1075
cert_ridgeSupport_suffix_decode_2 416 000 15 1139 32 036 001 1107
cert_ridgeSupport_eq_3 416
theorem ridgeTest_large_416 : ridgeTest 416 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport416_eq]
    simp only [ridgeSupport416_suffix_000, ridgeSupport416_suffix_001, ridgeSupport416_suffix_002, ridgeSupport416_suffix_003, ridgeSupport416_suffix_004, ridgeSupport416_suffix_005, ridgeSupport416_suffix_006, ridgeSupport416_suffix_007, ridgeSupport416_suffix_008, ridgeSupport416_suffix_009, ridgeSupport416_suffix_010, ridgeSupport416_suffix_011, ridgeSupport416_suffix_012, ridgeSupport416_suffix_013, ridgeSupport416_suffix_014, ridgeSupport416_suffix_015, ridgeSupport416_suffix_016, ridgeSupport416_suffix_017, ridgeSupport416_suffix_018, ridgeSupport416_suffix_019, ridgeSupport416_suffix_020, ridgeSupport416_suffix_021, ridgeSupport416_suffix_022, ridgeSupport416_suffix_023, ridgeSupport416_suffix_024, ridgeSupport416_suffix_025, ridgeSupport416_suffix_026, ridgeSupport416_suffix_027, ridgeSupport416_suffix_028, ridgeSupport416_suffix_029, ridgeSupport416_suffix_030, ridgeSupport416_suffix_031, ridgeSupport416_suffix_032, ridgeSupport416_suffix_033, ridgeSupport416_suffix_034, ridgeSupport416_suffix_035, ridgeSupport416_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport416_000_mask, ridgeSupport416_001_mask, ridgeSupport416_002_mask, ridgeSupport416_003_mask, ridgeSupport416_004_mask, ridgeSupport416_005_mask, ridgeSupport416_006_mask, ridgeSupport416_007_mask, ridgeSupport416_008_mask, ridgeSupport416_009_mask, ridgeSupport416_010_mask, ridgeSupport416_011_mask, ridgeSupport416_012_mask, ridgeSupport416_013_mask, ridgeSupport416_014_mask, ridgeSupport416_015_mask, ridgeSupport416_016_mask, ridgeSupport416_017_mask, ridgeSupport416_018_mask, ridgeSupport416_019_mask, ridgeSupport416_020_mask, ridgeSupport416_021_mask, ridgeSupport416_022_mask, ridgeSupport416_023_mask, ridgeSupport416_024_mask, ridgeSupport416_025_mask, ridgeSupport416_026_mask, ridgeSupport416_027_mask, ridgeSupport416_028_mask, ridgeSupport416_029_mask, ridgeSupport416_030_mask, ridgeSupport416_031_mask, ridgeSupport416_032_mask, ridgeSupport416_033_mask, ridgeSupport416_034_mask, ridgeSupport416_035_mask]
    decide +kernel
  · rw [ridgeSupport416_eq]
    simp only [ridgeSupport416_suffix_000, ridgeSupport416_suffix_001, ridgeSupport416_suffix_002, ridgeSupport416_suffix_003, ridgeSupport416_suffix_004, ridgeSupport416_suffix_005, ridgeSupport416_suffix_006, ridgeSupport416_suffix_007, ridgeSupport416_suffix_008, ridgeSupport416_suffix_009, ridgeSupport416_suffix_010, ridgeSupport416_suffix_011, ridgeSupport416_suffix_012, ridgeSupport416_suffix_013, ridgeSupport416_suffix_014, ridgeSupport416_suffix_015, ridgeSupport416_suffix_016, ridgeSupport416_suffix_017, ridgeSupport416_suffix_018, ridgeSupport416_suffix_019, ridgeSupport416_suffix_020, ridgeSupport416_suffix_021, ridgeSupport416_suffix_022, ridgeSupport416_suffix_023, ridgeSupport416_suffix_024, ridgeSupport416_suffix_025, ridgeSupport416_suffix_026, ridgeSupport416_suffix_027, ridgeSupport416_suffix_028, ridgeSupport416_suffix_029, ridgeSupport416_suffix_030, ridgeSupport416_suffix_031, ridgeSupport416_suffix_032, ridgeSupport416_suffix_033, ridgeSupport416_suffix_034, ridgeSupport416_suffix_035, ridgeSupport416_suffix_036, List.all_append, List.all_nil, ridgeSupport416_000_checked, ridgeSupport416_001_checked, ridgeSupport416_002_checked, ridgeSupport416_003_checked, ridgeSupport416_004_checked, ridgeSupport416_005_checked, ridgeSupport416_006_checked, ridgeSupport416_007_checked, ridgeSupport416_008_checked, ridgeSupport416_009_checked, ridgeSupport416_010_checked, ridgeSupport416_011_checked, ridgeSupport416_012_checked, ridgeSupport416_013_checked, ridgeSupport416_014_checked, ridgeSupport416_015_checked, ridgeSupport416_016_checked, ridgeSupport416_017_checked, ridgeSupport416_018_checked, ridgeSupport416_019_checked, ridgeSupport416_020_checked, ridgeSupport416_021_checked, ridgeSupport416_022_checked, ridgeSupport416_023_checked, ridgeSupport416_024_checked, ridgeSupport416_025_checked, ridgeSupport416_026_checked, ridgeSupport416_027_checked, ridgeSupport416_028_checked, ridgeSupport416_029_checked, ridgeSupport416_030_checked, ridgeSupport416_031_checked, ridgeSupport416_032_checked, ridgeSupport416_033_checked, ridgeSupport416_034_checked, ridgeSupport416_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
