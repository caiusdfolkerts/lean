module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport328Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 328 031 14
cert_ridgeSupport_suffix_decode_2 328 030 14 26 26 031 031 0
cert_ridgeSupport_suffix_decode_2 328 029 14 58 32 031 030 26
cert_ridgeSupport_suffix_decode_2 328 028 14 90 32 031 029 58
cert_ridgeSupport_suffix_decode_2 328 027 14 122 32 031 028 90
cert_ridgeSupport_suffix_decode_2 328 026 14 154 32 031 027 122
cert_ridgeSupport_suffix_decode_2 328 025 14 186 32 031 026 154
cert_ridgeSupport_suffix_decode_2 328 024 14 218 32 031 025 186
cert_ridgeSupport_suffix_decode_2 328 023 14 250 32 031 024 218
cert_ridgeSupport_suffix_decode_2 328 022 14 282 32 031 023 250
cert_ridgeSupport_suffix_decode_2 328 021 14 314 32 031 022 282
cert_ridgeSupport_suffix_decode_2 328 020 14 346 32 031 021 314
cert_ridgeSupport_suffix_decode_2 328 019 14 378 32 031 020 346
cert_ridgeSupport_suffix_decode_2 328 018 14 410 32 031 019 378
cert_ridgeSupport_suffix_decode_2 328 017 14 442 32 031 018 410
cert_ridgeSupport_suffix_decode_2 328 016 14 474 32 031 017 442
cert_ridgeSupport_suffix_decode_2 328 015 14 506 32 031 016 474
cert_ridgeSupport_suffix_decode_2 328 014 14 538 32 031 015 506
cert_ridgeSupport_suffix_decode_2 328 013 14 570 32 031 014 538
cert_ridgeSupport_suffix_decode_2 328 012 14 602 32 031 013 570
cert_ridgeSupport_suffix_decode_2 328 011 14 634 32 031 012 602
cert_ridgeSupport_suffix_decode_2 328 010 14 666 32 031 011 634
cert_ridgeSupport_suffix_decode_2 328 009 14 698 32 031 010 666
cert_ridgeSupport_suffix_decode_2 328 008 14 730 32 031 009 698
cert_ridgeSupport_suffix_decode_2 328 007 14 762 32 031 008 730
cert_ridgeSupport_suffix_decode_2 328 006 14 794 32 031 007 762
cert_ridgeSupport_suffix_decode_2 328 005 14 826 32 031 006 794
cert_ridgeSupport_suffix_decode_2 328 004 14 858 32 031 005 826
cert_ridgeSupport_suffix_decode_2 328 003 14 890 32 031 004 858
cert_ridgeSupport_suffix_decode_2 328 002 14 922 32 031 003 890
cert_ridgeSupport_suffix_decode_2 328 001 14 954 32 031 002 922
cert_ridgeSupport_suffix_decode_2 328 000 14 986 32 031 001 954
cert_ridgeSupport_eq_3 328
theorem ridgeTest_large_328 : ridgeTest 328 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport328_eq]
    simp only [ridgeSupport328_suffix_000, ridgeSupport328_suffix_001, ridgeSupport328_suffix_002, ridgeSupport328_suffix_003, ridgeSupport328_suffix_004, ridgeSupport328_suffix_005, ridgeSupport328_suffix_006, ridgeSupport328_suffix_007, ridgeSupport328_suffix_008, ridgeSupport328_suffix_009, ridgeSupport328_suffix_010, ridgeSupport328_suffix_011, ridgeSupport328_suffix_012, ridgeSupport328_suffix_013, ridgeSupport328_suffix_014, ridgeSupport328_suffix_015, ridgeSupport328_suffix_016, ridgeSupport328_suffix_017, ridgeSupport328_suffix_018, ridgeSupport328_suffix_019, ridgeSupport328_suffix_020, ridgeSupport328_suffix_021, ridgeSupport328_suffix_022, ridgeSupport328_suffix_023, ridgeSupport328_suffix_024, ridgeSupport328_suffix_025, ridgeSupport328_suffix_026, ridgeSupport328_suffix_027, ridgeSupport328_suffix_028, ridgeSupport328_suffix_029, ridgeSupport328_suffix_030, ridgeSupport328_suffix_031, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport328_000_mask, ridgeSupport328_001_mask, ridgeSupport328_002_mask, ridgeSupport328_003_mask, ridgeSupport328_004_mask, ridgeSupport328_005_mask, ridgeSupport328_006_mask, ridgeSupport328_007_mask, ridgeSupport328_008_mask, ridgeSupport328_009_mask, ridgeSupport328_010_mask, ridgeSupport328_011_mask, ridgeSupport328_012_mask, ridgeSupport328_013_mask, ridgeSupport328_014_mask, ridgeSupport328_015_mask, ridgeSupport328_016_mask, ridgeSupport328_017_mask, ridgeSupport328_018_mask, ridgeSupport328_019_mask, ridgeSupport328_020_mask, ridgeSupport328_021_mask, ridgeSupport328_022_mask, ridgeSupport328_023_mask, ridgeSupport328_024_mask, ridgeSupport328_025_mask, ridgeSupport328_026_mask, ridgeSupport328_027_mask, ridgeSupport328_028_mask, ridgeSupport328_029_mask, ridgeSupport328_030_mask]
    decide +kernel
  · rw [ridgeSupport328_eq]
    simp only [ridgeSupport328_suffix_000, ridgeSupport328_suffix_001, ridgeSupport328_suffix_002, ridgeSupport328_suffix_003, ridgeSupport328_suffix_004, ridgeSupport328_suffix_005, ridgeSupport328_suffix_006, ridgeSupport328_suffix_007, ridgeSupport328_suffix_008, ridgeSupport328_suffix_009, ridgeSupport328_suffix_010, ridgeSupport328_suffix_011, ridgeSupport328_suffix_012, ridgeSupport328_suffix_013, ridgeSupport328_suffix_014, ridgeSupport328_suffix_015, ridgeSupport328_suffix_016, ridgeSupport328_suffix_017, ridgeSupport328_suffix_018, ridgeSupport328_suffix_019, ridgeSupport328_suffix_020, ridgeSupport328_suffix_021, ridgeSupport328_suffix_022, ridgeSupport328_suffix_023, ridgeSupport328_suffix_024, ridgeSupport328_suffix_025, ridgeSupport328_suffix_026, ridgeSupport328_suffix_027, ridgeSupport328_suffix_028, ridgeSupport328_suffix_029, ridgeSupport328_suffix_030, ridgeSupport328_suffix_031, List.all_append, List.all_nil, ridgeSupport328_000_checked, ridgeSupport328_001_checked, ridgeSupport328_002_checked, ridgeSupport328_003_checked, ridgeSupport328_004_checked, ridgeSupport328_005_checked, ridgeSupport328_006_checked, ridgeSupport328_007_checked, ridgeSupport328_008_checked, ridgeSupport328_009_checked, ridgeSupport328_010_checked, ridgeSupport328_011_checked, ridgeSupport328_012_checked, ridgeSupport328_013_checked, ridgeSupport328_014_checked, ridgeSupport328_015_checked, ridgeSupport328_016_checked, ridgeSupport328_017_checked, ridgeSupport328_018_checked, ridgeSupport328_019_checked, ridgeSupport328_020_checked, ridgeSupport328_021_checked, ridgeSupport328_022_checked, ridgeSupport328_023_checked, ridgeSupport328_024_checked, ridgeSupport328_025_checked, ridgeSupport328_026_checked, ridgeSupport328_027_checked, ridgeSupport328_028_checked, ridgeSupport328_029_checked, ridgeSupport328_030_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
