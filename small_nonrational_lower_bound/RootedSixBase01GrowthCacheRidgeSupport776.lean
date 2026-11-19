module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport776Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 776 031 14
cert_ridgeSupport_suffix_decode_2 776 030 14 26 26 031 031 0
cert_ridgeSupport_suffix_decode_2 776 029 14 58 32 031 030 26
cert_ridgeSupport_suffix_decode_2 776 028 14 90 32 031 029 58
cert_ridgeSupport_suffix_decode_2 776 027 14 122 32 031 028 90
cert_ridgeSupport_suffix_decode_2 776 026 14 154 32 031 027 122
cert_ridgeSupport_suffix_decode_2 776 025 14 186 32 031 026 154
cert_ridgeSupport_suffix_decode_2 776 024 14 218 32 031 025 186
cert_ridgeSupport_suffix_decode_2 776 023 14 250 32 031 024 218
cert_ridgeSupport_suffix_decode_2 776 022 14 282 32 031 023 250
cert_ridgeSupport_suffix_decode_2 776 021 14 314 32 031 022 282
cert_ridgeSupport_suffix_decode_2 776 020 14 346 32 031 021 314
cert_ridgeSupport_suffix_decode_2 776 019 14 378 32 031 020 346
cert_ridgeSupport_suffix_decode_2 776 018 14 410 32 031 019 378
cert_ridgeSupport_suffix_decode_2 776 017 14 442 32 031 018 410
cert_ridgeSupport_suffix_decode_2 776 016 14 474 32 031 017 442
cert_ridgeSupport_suffix_decode_2 776 015 14 506 32 031 016 474
cert_ridgeSupport_suffix_decode_2 776 014 14 538 32 031 015 506
cert_ridgeSupport_suffix_decode_2 776 013 14 570 32 031 014 538
cert_ridgeSupport_suffix_decode_2 776 012 14 602 32 031 013 570
cert_ridgeSupport_suffix_decode_2 776 011 14 634 32 031 012 602
cert_ridgeSupport_suffix_decode_2 776 010 14 666 32 031 011 634
cert_ridgeSupport_suffix_decode_2 776 009 14 698 32 031 010 666
cert_ridgeSupport_suffix_decode_2 776 008 14 730 32 031 009 698
cert_ridgeSupport_suffix_decode_2 776 007 14 762 32 031 008 730
cert_ridgeSupport_suffix_decode_2 776 006 14 794 32 031 007 762
cert_ridgeSupport_suffix_decode_2 776 005 14 826 32 031 006 794
cert_ridgeSupport_suffix_decode_2 776 004 14 858 32 031 005 826
cert_ridgeSupport_suffix_decode_2 776 003 14 890 32 031 004 858
cert_ridgeSupport_suffix_decode_2 776 002 14 922 32 031 003 890
cert_ridgeSupport_suffix_decode_2 776 001 14 954 32 031 002 922
cert_ridgeSupport_suffix_decode_2 776 000 14 986 32 031 001 954
cert_ridgeSupport_eq_3 776
theorem ridgeTest_large_776 : ridgeTest 776 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport776_eq]
    simp only [ridgeSupport776_suffix_000, ridgeSupport776_suffix_001, ridgeSupport776_suffix_002, ridgeSupport776_suffix_003, ridgeSupport776_suffix_004, ridgeSupport776_suffix_005, ridgeSupport776_suffix_006, ridgeSupport776_suffix_007, ridgeSupport776_suffix_008, ridgeSupport776_suffix_009, ridgeSupport776_suffix_010, ridgeSupport776_suffix_011, ridgeSupport776_suffix_012, ridgeSupport776_suffix_013, ridgeSupport776_suffix_014, ridgeSupport776_suffix_015, ridgeSupport776_suffix_016, ridgeSupport776_suffix_017, ridgeSupport776_suffix_018, ridgeSupport776_suffix_019, ridgeSupport776_suffix_020, ridgeSupport776_suffix_021, ridgeSupport776_suffix_022, ridgeSupport776_suffix_023, ridgeSupport776_suffix_024, ridgeSupport776_suffix_025, ridgeSupport776_suffix_026, ridgeSupport776_suffix_027, ridgeSupport776_suffix_028, ridgeSupport776_suffix_029, ridgeSupport776_suffix_030, ridgeSupport776_suffix_031, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport776_000_mask, ridgeSupport776_001_mask, ridgeSupport776_002_mask, ridgeSupport776_003_mask, ridgeSupport776_004_mask, ridgeSupport776_005_mask, ridgeSupport776_006_mask, ridgeSupport776_007_mask, ridgeSupport776_008_mask, ridgeSupport776_009_mask, ridgeSupport776_010_mask, ridgeSupport776_011_mask, ridgeSupport776_012_mask, ridgeSupport776_013_mask, ridgeSupport776_014_mask, ridgeSupport776_015_mask, ridgeSupport776_016_mask, ridgeSupport776_017_mask, ridgeSupport776_018_mask, ridgeSupport776_019_mask, ridgeSupport776_020_mask, ridgeSupport776_021_mask, ridgeSupport776_022_mask, ridgeSupport776_023_mask, ridgeSupport776_024_mask, ridgeSupport776_025_mask, ridgeSupport776_026_mask, ridgeSupport776_027_mask, ridgeSupport776_028_mask, ridgeSupport776_029_mask, ridgeSupport776_030_mask]
    decide +kernel
  · rw [ridgeSupport776_eq]
    simp only [ridgeSupport776_suffix_000, ridgeSupport776_suffix_001, ridgeSupport776_suffix_002, ridgeSupport776_suffix_003, ridgeSupport776_suffix_004, ridgeSupport776_suffix_005, ridgeSupport776_suffix_006, ridgeSupport776_suffix_007, ridgeSupport776_suffix_008, ridgeSupport776_suffix_009, ridgeSupport776_suffix_010, ridgeSupport776_suffix_011, ridgeSupport776_suffix_012, ridgeSupport776_suffix_013, ridgeSupport776_suffix_014, ridgeSupport776_suffix_015, ridgeSupport776_suffix_016, ridgeSupport776_suffix_017, ridgeSupport776_suffix_018, ridgeSupport776_suffix_019, ridgeSupport776_suffix_020, ridgeSupport776_suffix_021, ridgeSupport776_suffix_022, ridgeSupport776_suffix_023, ridgeSupport776_suffix_024, ridgeSupport776_suffix_025, ridgeSupport776_suffix_026, ridgeSupport776_suffix_027, ridgeSupport776_suffix_028, ridgeSupport776_suffix_029, ridgeSupport776_suffix_030, ridgeSupport776_suffix_031, List.all_append, List.all_nil, ridgeSupport776_000_checked, ridgeSupport776_001_checked, ridgeSupport776_002_checked, ridgeSupport776_003_checked, ridgeSupport776_004_checked, ridgeSupport776_005_checked, ridgeSupport776_006_checked, ridgeSupport776_007_checked, ridgeSupport776_008_checked, ridgeSupport776_009_checked, ridgeSupport776_010_checked, ridgeSupport776_011_checked, ridgeSupport776_012_checked, ridgeSupport776_013_checked, ridgeSupport776_014_checked, ridgeSupport776_015_checked, ridgeSupport776_016_checked, ridgeSupport776_017_checked, ridgeSupport776_018_checked, ridgeSupport776_019_checked, ridgeSupport776_020_checked, ridgeSupport776_021_checked, ridgeSupport776_022_checked, ridgeSupport776_023_checked, ridgeSupport776_024_checked, ridgeSupport776_025_checked, ridgeSupport776_026_checked, ridgeSupport776_027_checked, ridgeSupport776_028_checked, ridgeSupport776_029_checked, ridgeSupport776_030_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
