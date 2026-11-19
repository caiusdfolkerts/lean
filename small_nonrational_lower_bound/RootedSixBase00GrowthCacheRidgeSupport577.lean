module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase00GrowthCacheRidgeSupport577Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 577 036 15
cert_ridgeSupport_suffix_decode_2 577 035 15 19 19 036 036 0
cert_ridgeSupport_suffix_decode_2 577 034 15 51 32 036 035 19
cert_ridgeSupport_suffix_decode_2 577 033 15 83 32 036 034 51
cert_ridgeSupport_suffix_decode_2 577 032 15 115 32 036 033 83
cert_ridgeSupport_suffix_decode_2 577 031 15 147 32 036 032 115
cert_ridgeSupport_suffix_decode_2 577 030 15 179 32 036 031 147
cert_ridgeSupport_suffix_decode_2 577 029 15 211 32 036 030 179
cert_ridgeSupport_suffix_decode_2 577 028 15 243 32 036 029 211
cert_ridgeSupport_suffix_decode_2 577 027 15 275 32 036 028 243
cert_ridgeSupport_suffix_decode_2 577 026 15 307 32 036 027 275
cert_ridgeSupport_suffix_decode_2 577 025 15 339 32 036 026 307
cert_ridgeSupport_suffix_decode_2 577 024 15 371 32 036 025 339
cert_ridgeSupport_suffix_decode_2 577 023 15 403 32 036 024 371
cert_ridgeSupport_suffix_decode_2 577 022 15 435 32 036 023 403
cert_ridgeSupport_suffix_decode_2 577 021 15 467 32 036 022 435
cert_ridgeSupport_suffix_decode_2 577 020 15 499 32 036 021 467
cert_ridgeSupport_suffix_decode_2 577 019 15 531 32 036 020 499
cert_ridgeSupport_suffix_decode_2 577 018 15 563 32 036 019 531
cert_ridgeSupport_suffix_decode_2 577 017 15 595 32 036 018 563
cert_ridgeSupport_suffix_decode_2 577 016 15 627 32 036 017 595
cert_ridgeSupport_suffix_decode_2 577 015 15 659 32 036 016 627
cert_ridgeSupport_suffix_decode_2 577 014 15 691 32 036 015 659
cert_ridgeSupport_suffix_decode_2 577 013 15 723 32 036 014 691
cert_ridgeSupport_suffix_decode_2 577 012 15 755 32 036 013 723
cert_ridgeSupport_suffix_decode_2 577 011 15 787 32 036 012 755
cert_ridgeSupport_suffix_decode_2 577 010 15 819 32 036 011 787
cert_ridgeSupport_suffix_decode_2 577 009 15 851 32 036 010 819
cert_ridgeSupport_suffix_decode_2 577 008 15 883 32 036 009 851
cert_ridgeSupport_suffix_decode_2 577 007 15 915 32 036 008 883
cert_ridgeSupport_suffix_decode_2 577 006 15 947 32 036 007 915
cert_ridgeSupport_suffix_decode_2 577 005 15 979 32 036 006 947
cert_ridgeSupport_suffix_decode_2 577 004 15 1011 32 036 005 979
cert_ridgeSupport_suffix_decode_2 577 003 15 1043 32 036 004 1011
cert_ridgeSupport_suffix_decode_2 577 002 15 1075 32 036 003 1043
cert_ridgeSupport_suffix_decode_2 577 001 15 1107 32 036 002 1075
cert_ridgeSupport_suffix_decode_2 577 000 15 1139 32 036 001 1107
cert_ridgeSupport_eq_3 577
theorem ridgeTest_large_577 : ridgeTest 577 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport577_eq]
    simp only [ridgeSupport577_suffix_000, ridgeSupport577_suffix_001, ridgeSupport577_suffix_002, ridgeSupport577_suffix_003, ridgeSupport577_suffix_004, ridgeSupport577_suffix_005, ridgeSupport577_suffix_006, ridgeSupport577_suffix_007, ridgeSupport577_suffix_008, ridgeSupport577_suffix_009, ridgeSupport577_suffix_010, ridgeSupport577_suffix_011, ridgeSupport577_suffix_012, ridgeSupport577_suffix_013, ridgeSupport577_suffix_014, ridgeSupport577_suffix_015, ridgeSupport577_suffix_016, ridgeSupport577_suffix_017, ridgeSupport577_suffix_018, ridgeSupport577_suffix_019, ridgeSupport577_suffix_020, ridgeSupport577_suffix_021, ridgeSupport577_suffix_022, ridgeSupport577_suffix_023, ridgeSupport577_suffix_024, ridgeSupport577_suffix_025, ridgeSupport577_suffix_026, ridgeSupport577_suffix_027, ridgeSupport577_suffix_028, ridgeSupport577_suffix_029, ridgeSupport577_suffix_030, ridgeSupport577_suffix_031, ridgeSupport577_suffix_032, ridgeSupport577_suffix_033, ridgeSupport577_suffix_034, ridgeSupport577_suffix_035, ridgeSupport577_suffix_036, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport577_000_mask, ridgeSupport577_001_mask, ridgeSupport577_002_mask, ridgeSupport577_003_mask, ridgeSupport577_004_mask, ridgeSupport577_005_mask, ridgeSupport577_006_mask, ridgeSupport577_007_mask, ridgeSupport577_008_mask, ridgeSupport577_009_mask, ridgeSupport577_010_mask, ridgeSupport577_011_mask, ridgeSupport577_012_mask, ridgeSupport577_013_mask, ridgeSupport577_014_mask, ridgeSupport577_015_mask, ridgeSupport577_016_mask, ridgeSupport577_017_mask, ridgeSupport577_018_mask, ridgeSupport577_019_mask, ridgeSupport577_020_mask, ridgeSupport577_021_mask, ridgeSupport577_022_mask, ridgeSupport577_023_mask, ridgeSupport577_024_mask, ridgeSupport577_025_mask, ridgeSupport577_026_mask, ridgeSupport577_027_mask, ridgeSupport577_028_mask, ridgeSupport577_029_mask, ridgeSupport577_030_mask, ridgeSupport577_031_mask, ridgeSupport577_032_mask, ridgeSupport577_033_mask, ridgeSupport577_034_mask, ridgeSupport577_035_mask]
    decide +kernel
  · rw [ridgeSupport577_eq]
    simp only [ridgeSupport577_suffix_000, ridgeSupport577_suffix_001, ridgeSupport577_suffix_002, ridgeSupport577_suffix_003, ridgeSupport577_suffix_004, ridgeSupport577_suffix_005, ridgeSupport577_suffix_006, ridgeSupport577_suffix_007, ridgeSupport577_suffix_008, ridgeSupport577_suffix_009, ridgeSupport577_suffix_010, ridgeSupport577_suffix_011, ridgeSupport577_suffix_012, ridgeSupport577_suffix_013, ridgeSupport577_suffix_014, ridgeSupport577_suffix_015, ridgeSupport577_suffix_016, ridgeSupport577_suffix_017, ridgeSupport577_suffix_018, ridgeSupport577_suffix_019, ridgeSupport577_suffix_020, ridgeSupport577_suffix_021, ridgeSupport577_suffix_022, ridgeSupport577_suffix_023, ridgeSupport577_suffix_024, ridgeSupport577_suffix_025, ridgeSupport577_suffix_026, ridgeSupport577_suffix_027, ridgeSupport577_suffix_028, ridgeSupport577_suffix_029, ridgeSupport577_suffix_030, ridgeSupport577_suffix_031, ridgeSupport577_suffix_032, ridgeSupport577_suffix_033, ridgeSupport577_suffix_034, ridgeSupport577_suffix_035, ridgeSupport577_suffix_036, List.all_append, List.all_nil, ridgeSupport577_000_checked, ridgeSupport577_001_checked, ridgeSupport577_002_checked, ridgeSupport577_003_checked, ridgeSupport577_004_checked, ridgeSupport577_005_checked, ridgeSupport577_006_checked, ridgeSupport577_007_checked, ridgeSupport577_008_checked, ridgeSupport577_009_checked, ridgeSupport577_010_checked, ridgeSupport577_011_checked, ridgeSupport577_012_checked, ridgeSupport577_013_checked, ridgeSupport577_014_checked, ridgeSupport577_015_checked, ridgeSupport577_016_checked, ridgeSupport577_017_checked, ridgeSupport577_018_checked, ridgeSupport577_019_checked, ridgeSupport577_020_checked, ridgeSupport577_021_checked, ridgeSupport577_022_checked, ridgeSupport577_023_checked, ridgeSupport577_024_checked, ridgeSupport577_025_checked, ridgeSupport577_026_checked, ridgeSupport577_027_checked, ridgeSupport577_028_checked, ridgeSupport577_029_checked, ridgeSupport577_030_checked, ridgeSupport577_031_checked, ridgeSupport577_032_checked, ridgeSupport577_033_checked, ridgeSupport577_034_checked, ridgeSupport577_035_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
