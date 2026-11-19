module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport200Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 200 031 14
cert_ridgeSupport_suffix_decode_2 200 030 14 26 26 031 031 0
cert_ridgeSupport_suffix_decode_2 200 029 14 58 32 031 030 26
cert_ridgeSupport_suffix_decode_2 200 028 14 90 32 031 029 58
cert_ridgeSupport_suffix_decode_2 200 027 14 122 32 031 028 90
cert_ridgeSupport_suffix_decode_2 200 026 14 154 32 031 027 122
cert_ridgeSupport_suffix_decode_2 200 025 14 186 32 031 026 154
cert_ridgeSupport_suffix_decode_2 200 024 14 218 32 031 025 186
cert_ridgeSupport_suffix_decode_2 200 023 14 250 32 031 024 218
cert_ridgeSupport_suffix_decode_2 200 022 14 282 32 031 023 250
cert_ridgeSupport_suffix_decode_2 200 021 14 314 32 031 022 282
cert_ridgeSupport_suffix_decode_2 200 020 14 346 32 031 021 314
cert_ridgeSupport_suffix_decode_2 200 019 14 378 32 031 020 346
cert_ridgeSupport_suffix_decode_2 200 018 14 410 32 031 019 378
cert_ridgeSupport_suffix_decode_2 200 017 14 442 32 031 018 410
cert_ridgeSupport_suffix_decode_2 200 016 14 474 32 031 017 442
cert_ridgeSupport_suffix_decode_2 200 015 14 506 32 031 016 474
cert_ridgeSupport_suffix_decode_2 200 014 14 538 32 031 015 506
cert_ridgeSupport_suffix_decode_2 200 013 14 570 32 031 014 538
cert_ridgeSupport_suffix_decode_2 200 012 14 602 32 031 013 570
cert_ridgeSupport_suffix_decode_2 200 011 14 634 32 031 012 602
cert_ridgeSupport_suffix_decode_2 200 010 14 666 32 031 011 634
cert_ridgeSupport_suffix_decode_2 200 009 14 698 32 031 010 666
cert_ridgeSupport_suffix_decode_2 200 008 14 730 32 031 009 698
cert_ridgeSupport_suffix_decode_2 200 007 14 762 32 031 008 730
cert_ridgeSupport_suffix_decode_2 200 006 14 794 32 031 007 762
cert_ridgeSupport_suffix_decode_2 200 005 14 826 32 031 006 794
cert_ridgeSupport_suffix_decode_2 200 004 14 858 32 031 005 826
cert_ridgeSupport_suffix_decode_2 200 003 14 890 32 031 004 858
cert_ridgeSupport_suffix_decode_2 200 002 14 922 32 031 003 890
cert_ridgeSupport_suffix_decode_2 200 001 14 954 32 031 002 922
cert_ridgeSupport_suffix_decode_2 200 000 14 986 32 031 001 954
cert_ridgeSupport_eq_3 200
theorem ridgeTest_large_200 : ridgeTest 200 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport200_eq]
    simp only [ridgeSupport200_suffix_000, ridgeSupport200_suffix_001, ridgeSupport200_suffix_002, ridgeSupport200_suffix_003, ridgeSupport200_suffix_004, ridgeSupport200_suffix_005, ridgeSupport200_suffix_006, ridgeSupport200_suffix_007, ridgeSupport200_suffix_008, ridgeSupport200_suffix_009, ridgeSupport200_suffix_010, ridgeSupport200_suffix_011, ridgeSupport200_suffix_012, ridgeSupport200_suffix_013, ridgeSupport200_suffix_014, ridgeSupport200_suffix_015, ridgeSupport200_suffix_016, ridgeSupport200_suffix_017, ridgeSupport200_suffix_018, ridgeSupport200_suffix_019, ridgeSupport200_suffix_020, ridgeSupport200_suffix_021, ridgeSupport200_suffix_022, ridgeSupport200_suffix_023, ridgeSupport200_suffix_024, ridgeSupport200_suffix_025, ridgeSupport200_suffix_026, ridgeSupport200_suffix_027, ridgeSupport200_suffix_028, ridgeSupport200_suffix_029, ridgeSupport200_suffix_030, ridgeSupport200_suffix_031, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport200_000_mask, ridgeSupport200_001_mask, ridgeSupport200_002_mask, ridgeSupport200_003_mask, ridgeSupport200_004_mask, ridgeSupport200_005_mask, ridgeSupport200_006_mask, ridgeSupport200_007_mask, ridgeSupport200_008_mask, ridgeSupport200_009_mask, ridgeSupport200_010_mask, ridgeSupport200_011_mask, ridgeSupport200_012_mask, ridgeSupport200_013_mask, ridgeSupport200_014_mask, ridgeSupport200_015_mask, ridgeSupport200_016_mask, ridgeSupport200_017_mask, ridgeSupport200_018_mask, ridgeSupport200_019_mask, ridgeSupport200_020_mask, ridgeSupport200_021_mask, ridgeSupport200_022_mask, ridgeSupport200_023_mask, ridgeSupport200_024_mask, ridgeSupport200_025_mask, ridgeSupport200_026_mask, ridgeSupport200_027_mask, ridgeSupport200_028_mask, ridgeSupport200_029_mask, ridgeSupport200_030_mask]
    decide +kernel
  · rw [ridgeSupport200_eq]
    simp only [ridgeSupport200_suffix_000, ridgeSupport200_suffix_001, ridgeSupport200_suffix_002, ridgeSupport200_suffix_003, ridgeSupport200_suffix_004, ridgeSupport200_suffix_005, ridgeSupport200_suffix_006, ridgeSupport200_suffix_007, ridgeSupport200_suffix_008, ridgeSupport200_suffix_009, ridgeSupport200_suffix_010, ridgeSupport200_suffix_011, ridgeSupport200_suffix_012, ridgeSupport200_suffix_013, ridgeSupport200_suffix_014, ridgeSupport200_suffix_015, ridgeSupport200_suffix_016, ridgeSupport200_suffix_017, ridgeSupport200_suffix_018, ridgeSupport200_suffix_019, ridgeSupport200_suffix_020, ridgeSupport200_suffix_021, ridgeSupport200_suffix_022, ridgeSupport200_suffix_023, ridgeSupport200_suffix_024, ridgeSupport200_suffix_025, ridgeSupport200_suffix_026, ridgeSupport200_suffix_027, ridgeSupport200_suffix_028, ridgeSupport200_suffix_029, ridgeSupport200_suffix_030, ridgeSupport200_suffix_031, List.all_append, List.all_nil, ridgeSupport200_000_checked, ridgeSupport200_001_checked, ridgeSupport200_002_checked, ridgeSupport200_003_checked, ridgeSupport200_004_checked, ridgeSupport200_005_checked, ridgeSupport200_006_checked, ridgeSupport200_007_checked, ridgeSupport200_008_checked, ridgeSupport200_009_checked, ridgeSupport200_010_checked, ridgeSupport200_011_checked, ridgeSupport200_012_checked, ridgeSupport200_013_checked, ridgeSupport200_014_checked, ridgeSupport200_015_checked, ridgeSupport200_016_checked, ridgeSupport200_017_checked, ridgeSupport200_018_checked, ridgeSupport200_019_checked, ridgeSupport200_020_checked, ridgeSupport200_021_checked, ridgeSupport200_022_checked, ridgeSupport200_023_checked, ridgeSupport200_024_checked, ridgeSupport200_025_checked, ridgeSupport200_026_checked, ridgeSupport200_027_checked, ridgeSupport200_028_checked, ridgeSupport200_029_checked, ridgeSupport200_030_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
