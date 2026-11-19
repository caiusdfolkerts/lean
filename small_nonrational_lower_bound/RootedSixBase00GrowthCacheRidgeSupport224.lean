module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport224Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 224 036 15
cert_ridgeSupport_suffix_decode_2 224 035 15 19 19 036 036 0
cert_ridgeSupport_suffix_decode_2 224 034 15 51 32 036 035 19
cert_ridgeSupport_suffix_decode_2 224 033 15 83 32 036 034 51
cert_ridgeSupport_suffix_decode_2 224 032 15 115 32 036 033 83
cert_ridgeSupport_suffix_decode_2 224 031 15 147 32 036 032 115
cert_ridgeSupport_suffix_decode_2 224 030 15 179 32 036 031 147
cert_ridgeSupport_suffix_decode_2 224 029 15 211 32 036 030 179
cert_ridgeSupport_suffix_decode_2 224 028 15 243 32 036 029 211
cert_ridgeSupport_suffix_decode_2 224 027 15 275 32 036 028 243
cert_ridgeSupport_suffix_decode_2 224 026 15 307 32 036 027 275
cert_ridgeSupport_suffix_decode_2 224 025 15 339 32 036 026 307
cert_ridgeSupport_suffix_decode_2 224 024 15 371 32 036 025 339
cert_ridgeSupport_suffix_decode_2 224 023 15 403 32 036 024 371
cert_ridgeSupport_suffix_decode_2 224 022 15 435 32 036 023 403
cert_ridgeSupport_suffix_decode_2 224 021 15 467 32 036 022 435
cert_ridgeSupport_suffix_decode_2 224 020 15 499 32 036 021 467
cert_ridgeSupport_suffix_decode_2 224 019 15 531 32 036 020 499
cert_ridgeSupport_suffix_decode_2 224 018 15 563 32 036 019 531
cert_ridgeSupport_suffix_decode_2 224 017 15 595 32 036 018 563
cert_ridgeSupport_suffix_decode_2 224 016 15 627 32 036 017 595
cert_ridgeSupport_suffix_decode_2 224 015 15 659 32 036 016 627
cert_ridgeSupport_suffix_decode_2 224 014 15 691 32 036 015 659
cert_ridgeSupport_suffix_decode_2 224 013 15 723 32 036 014 691
cert_ridgeSupport_suffix_decode_2 224 012 15 755 32 036 013 723
cert_ridgeSupport_suffix_decode_2 224 011 15 787 32 036 012 755
cert_ridgeSupport_suffix_decode_2 224 010 15 819 32 036 011 787
cert_ridgeSupport_suffix_decode_2 224 009 15 851 32 036 010 819
cert_ridgeSupport_suffix_decode_2 224 008 15 883 32 036 009 851
cert_ridgeSupport_suffix_decode_2 224 007 15 915 32 036 008 883
cert_ridgeSupport_suffix_decode_2 224 006 15 947 32 036 007 915
cert_ridgeSupport_suffix_decode_2 224 005 15 979 32 036 006 947
cert_ridgeSupport_suffix_decode_2 224 004 15 1011 32 036 005 979
cert_ridgeSupport_suffix_decode_2 224 003 15 1043 32 036 004 1011
cert_ridgeSupport_suffix_decode_2 224 002 15 1075 32 036 003 1043
cert_ridgeSupport_suffix_decode_2 224 001 15 1107 32 036 002 1075
cert_ridgeSupport_suffix_decode_2 224 000 15 1139 32 036 001 1107
cert_ridgeSupport_eq_3 224
theorem ridgeTest_large_224 : ridgeTest 224 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport224_eq]
    simp only [ridgeSupport224_suffix_000, ridgeSupport224_suffix_001, ridgeSupport224_suffix_002, ridgeSupport224_suffix_003, ridgeSupport224_suffix_004, ridgeSupport224_suffix_005, ridgeSupport224_suffix_006, ridgeSupport224_suffix_007, ridgeSupport224_suffix_008, ridgeSupport224_suffix_009, ridgeSupport224_suffix_010, ridgeSupport224_suffix_011, ridgeSupport224_suffix_012, ridgeSupport224_suffix_013, ridgeSupport224_suffix_014, ridgeSupport224_suffix_015, ridgeSupport224_suffix_016, ridgeSupport224_suffix_017, ridgeSupport224_suffix_018, ridgeSupport224_suffix_019, ridgeSupport224_suffix_020, ridgeSupport224_suffix_021, ridgeSupport224_suffix_022, ridgeSupport224_suffix_023, ridgeSupport224_suffix_024, ridgeSupport224_suffix_025, ridgeSupport224_suffix_026, ridgeSupport224_suffix_027, ridgeSupport224_suffix_028, ridgeSupport224_suffix_029, ridgeSupport224_suffix_030, ridgeSupport224_suffix_031, ridgeSupport224_suffix_032, ridgeSupport224_suffix_033, ridgeSupport224_suffix_034, ridgeSupport224_suffix_035, ridgeSupport224_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport224_000_mask, ridgeSupport224_001_mask, ridgeSupport224_002_mask, ridgeSupport224_003_mask, ridgeSupport224_004_mask, ridgeSupport224_005_mask, ridgeSupport224_006_mask, ridgeSupport224_007_mask, ridgeSupport224_008_mask, ridgeSupport224_009_mask, ridgeSupport224_010_mask, ridgeSupport224_011_mask, ridgeSupport224_012_mask, ridgeSupport224_013_mask, ridgeSupport224_014_mask, ridgeSupport224_015_mask, ridgeSupport224_016_mask, ridgeSupport224_017_mask, ridgeSupport224_018_mask, ridgeSupport224_019_mask, ridgeSupport224_020_mask, ridgeSupport224_021_mask, ridgeSupport224_022_mask, ridgeSupport224_023_mask, ridgeSupport224_024_mask, ridgeSupport224_025_mask, ridgeSupport224_026_mask, ridgeSupport224_027_mask, ridgeSupport224_028_mask, ridgeSupport224_029_mask, ridgeSupport224_030_mask, ridgeSupport224_031_mask, ridgeSupport224_032_mask, ridgeSupport224_033_mask, ridgeSupport224_034_mask, ridgeSupport224_035_mask]
    decide +kernel
  · rw [ridgeSupport224_eq]
    simp only [ridgeSupport224_suffix_000, ridgeSupport224_suffix_001, ridgeSupport224_suffix_002, ridgeSupport224_suffix_003, ridgeSupport224_suffix_004, ridgeSupport224_suffix_005, ridgeSupport224_suffix_006, ridgeSupport224_suffix_007, ridgeSupport224_suffix_008, ridgeSupport224_suffix_009, ridgeSupport224_suffix_010, ridgeSupport224_suffix_011, ridgeSupport224_suffix_012, ridgeSupport224_suffix_013, ridgeSupport224_suffix_014, ridgeSupport224_suffix_015, ridgeSupport224_suffix_016, ridgeSupport224_suffix_017, ridgeSupport224_suffix_018, ridgeSupport224_suffix_019, ridgeSupport224_suffix_020, ridgeSupport224_suffix_021, ridgeSupport224_suffix_022, ridgeSupport224_suffix_023, ridgeSupport224_suffix_024, ridgeSupport224_suffix_025, ridgeSupport224_suffix_026, ridgeSupport224_suffix_027, ridgeSupport224_suffix_028, ridgeSupport224_suffix_029, ridgeSupport224_suffix_030, ridgeSupport224_suffix_031, ridgeSupport224_suffix_032, ridgeSupport224_suffix_033, ridgeSupport224_suffix_034, ridgeSupport224_suffix_035, ridgeSupport224_suffix_036, List.all_append, List.all_nil, ridgeSupport224_000_checked, ridgeSupport224_001_checked, ridgeSupport224_002_checked, ridgeSupport224_003_checked, ridgeSupport224_004_checked, ridgeSupport224_005_checked, ridgeSupport224_006_checked, ridgeSupport224_007_checked, ridgeSupport224_008_checked, ridgeSupport224_009_checked, ridgeSupport224_010_checked, ridgeSupport224_011_checked, ridgeSupport224_012_checked, ridgeSupport224_013_checked, ridgeSupport224_014_checked, ridgeSupport224_015_checked, ridgeSupport224_016_checked, ridgeSupport224_017_checked, ridgeSupport224_018_checked, ridgeSupport224_019_checked, ridgeSupport224_020_checked, ridgeSupport224_021_checked, ridgeSupport224_022_checked, ridgeSupport224_023_checked, ridgeSupport224_024_checked, ridgeSupport224_025_checked, ridgeSupport224_026_checked, ridgeSupport224_027_checked, ridgeSupport224_028_checked, ridgeSupport224_029_checked, ridgeSupport224_030_checked, ridgeSupport224_031_checked, ridgeSupport224_032_checked, ridgeSupport224_033_checked, ridgeSupport224_034_checked, ridgeSupport224_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
