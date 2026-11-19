module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport642Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 642 031 14
cert_ridgeSupport_suffix_decode_2 642 030 14 26 26 031 031 0
cert_ridgeSupport_suffix_decode_2 642 029 14 58 32 031 030 26
cert_ridgeSupport_suffix_decode_2 642 028 14 90 32 031 029 58
cert_ridgeSupport_suffix_decode_2 642 027 14 122 32 031 028 90
cert_ridgeSupport_suffix_decode_2 642 026 14 154 32 031 027 122
cert_ridgeSupport_suffix_decode_2 642 025 14 186 32 031 026 154
cert_ridgeSupport_suffix_decode_2 642 024 14 218 32 031 025 186
cert_ridgeSupport_suffix_decode_2 642 023 14 250 32 031 024 218
cert_ridgeSupport_suffix_decode_2 642 022 14 282 32 031 023 250
cert_ridgeSupport_suffix_decode_2 642 021 14 314 32 031 022 282
cert_ridgeSupport_suffix_decode_2 642 020 14 346 32 031 021 314
cert_ridgeSupport_suffix_decode_2 642 019 14 378 32 031 020 346
cert_ridgeSupport_suffix_decode_2 642 018 14 410 32 031 019 378
cert_ridgeSupport_suffix_decode_2 642 017 14 442 32 031 018 410
cert_ridgeSupport_suffix_decode_2 642 016 14 474 32 031 017 442
cert_ridgeSupport_suffix_decode_2 642 015 14 506 32 031 016 474
cert_ridgeSupport_suffix_decode_2 642 014 14 538 32 031 015 506
cert_ridgeSupport_suffix_decode_2 642 013 14 570 32 031 014 538
cert_ridgeSupport_suffix_decode_2 642 012 14 602 32 031 013 570
cert_ridgeSupport_suffix_decode_2 642 011 14 634 32 031 012 602
cert_ridgeSupport_suffix_decode_2 642 010 14 666 32 031 011 634
cert_ridgeSupport_suffix_decode_2 642 009 14 698 32 031 010 666
cert_ridgeSupport_suffix_decode_2 642 008 14 730 32 031 009 698
cert_ridgeSupport_suffix_decode_2 642 007 14 762 32 031 008 730
cert_ridgeSupport_suffix_decode_2 642 006 14 794 32 031 007 762
cert_ridgeSupport_suffix_decode_2 642 005 14 826 32 031 006 794
cert_ridgeSupport_suffix_decode_2 642 004 14 858 32 031 005 826
cert_ridgeSupport_suffix_decode_2 642 003 14 890 32 031 004 858
cert_ridgeSupport_suffix_decode_2 642 002 14 922 32 031 003 890
cert_ridgeSupport_suffix_decode_2 642 001 14 954 32 031 002 922
cert_ridgeSupport_suffix_decode_2 642 000 14 986 32 031 001 954
cert_ridgeSupport_eq_3 642
theorem ridgeTest_large_642 : ridgeTest 642 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport642_eq]
    simp only [ridgeSupport642_suffix_000, ridgeSupport642_suffix_001, ridgeSupport642_suffix_002, ridgeSupport642_suffix_003, ridgeSupport642_suffix_004, ridgeSupport642_suffix_005, ridgeSupport642_suffix_006, ridgeSupport642_suffix_007, ridgeSupport642_suffix_008, ridgeSupport642_suffix_009, ridgeSupport642_suffix_010, ridgeSupport642_suffix_011, ridgeSupport642_suffix_012, ridgeSupport642_suffix_013, ridgeSupport642_suffix_014, ridgeSupport642_suffix_015, ridgeSupport642_suffix_016, ridgeSupport642_suffix_017, ridgeSupport642_suffix_018, ridgeSupport642_suffix_019, ridgeSupport642_suffix_020, ridgeSupport642_suffix_021, ridgeSupport642_suffix_022, ridgeSupport642_suffix_023, ridgeSupport642_suffix_024, ridgeSupport642_suffix_025, ridgeSupport642_suffix_026, ridgeSupport642_suffix_027, ridgeSupport642_suffix_028, ridgeSupport642_suffix_029, ridgeSupport642_suffix_030, ridgeSupport642_suffix_031, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport642_000_mask, ridgeSupport642_001_mask, ridgeSupport642_002_mask, ridgeSupport642_003_mask, ridgeSupport642_004_mask, ridgeSupport642_005_mask, ridgeSupport642_006_mask, ridgeSupport642_007_mask, ridgeSupport642_008_mask, ridgeSupport642_009_mask, ridgeSupport642_010_mask, ridgeSupport642_011_mask, ridgeSupport642_012_mask, ridgeSupport642_013_mask, ridgeSupport642_014_mask, ridgeSupport642_015_mask, ridgeSupport642_016_mask, ridgeSupport642_017_mask, ridgeSupport642_018_mask, ridgeSupport642_019_mask, ridgeSupport642_020_mask, ridgeSupport642_021_mask, ridgeSupport642_022_mask, ridgeSupport642_023_mask, ridgeSupport642_024_mask, ridgeSupport642_025_mask, ridgeSupport642_026_mask, ridgeSupport642_027_mask, ridgeSupport642_028_mask, ridgeSupport642_029_mask, ridgeSupport642_030_mask]
    decide +kernel
  · rw [ridgeSupport642_eq]
    simp only [ridgeSupport642_suffix_000, ridgeSupport642_suffix_001, ridgeSupport642_suffix_002, ridgeSupport642_suffix_003, ridgeSupport642_suffix_004, ridgeSupport642_suffix_005, ridgeSupport642_suffix_006, ridgeSupport642_suffix_007, ridgeSupport642_suffix_008, ridgeSupport642_suffix_009, ridgeSupport642_suffix_010, ridgeSupport642_suffix_011, ridgeSupport642_suffix_012, ridgeSupport642_suffix_013, ridgeSupport642_suffix_014, ridgeSupport642_suffix_015, ridgeSupport642_suffix_016, ridgeSupport642_suffix_017, ridgeSupport642_suffix_018, ridgeSupport642_suffix_019, ridgeSupport642_suffix_020, ridgeSupport642_suffix_021, ridgeSupport642_suffix_022, ridgeSupport642_suffix_023, ridgeSupport642_suffix_024, ridgeSupport642_suffix_025, ridgeSupport642_suffix_026, ridgeSupport642_suffix_027, ridgeSupport642_suffix_028, ridgeSupport642_suffix_029, ridgeSupport642_suffix_030, ridgeSupport642_suffix_031, List.all_append, List.all_nil, ridgeSupport642_000_checked, ridgeSupport642_001_checked, ridgeSupport642_002_checked, ridgeSupport642_003_checked, ridgeSupport642_004_checked, ridgeSupport642_005_checked, ridgeSupport642_006_checked, ridgeSupport642_007_checked, ridgeSupport642_008_checked, ridgeSupport642_009_checked, ridgeSupport642_010_checked, ridgeSupport642_011_checked, ridgeSupport642_012_checked, ridgeSupport642_013_checked, ridgeSupport642_014_checked, ridgeSupport642_015_checked, ridgeSupport642_016_checked, ridgeSupport642_017_checked, ridgeSupport642_018_checked, ridgeSupport642_019_checked, ridgeSupport642_020_checked, ridgeSupport642_021_checked, ridgeSupport642_022_checked, ridgeSupport642_023_checked, ridgeSupport642_024_checked, ridgeSupport642_025_checked, ridgeSupport642_026_checked, ridgeSupport642_027_checked, ridgeSupport642_028_checked, ridgeSupport642_029_checked, ridgeSupport642_030_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
