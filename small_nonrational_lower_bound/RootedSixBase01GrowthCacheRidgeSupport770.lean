module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport770Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 770 031 14
cert_ridgeSupport_suffix_decode_2 770 030 14 26 26 031 031 0
cert_ridgeSupport_suffix_decode_2 770 029 14 58 32 031 030 26
cert_ridgeSupport_suffix_decode_2 770 028 14 90 32 031 029 58
cert_ridgeSupport_suffix_decode_2 770 027 14 122 32 031 028 90
cert_ridgeSupport_suffix_decode_2 770 026 14 154 32 031 027 122
cert_ridgeSupport_suffix_decode_2 770 025 14 186 32 031 026 154
cert_ridgeSupport_suffix_decode_2 770 024 14 218 32 031 025 186
cert_ridgeSupport_suffix_decode_2 770 023 14 250 32 031 024 218
cert_ridgeSupport_suffix_decode_2 770 022 14 282 32 031 023 250
cert_ridgeSupport_suffix_decode_2 770 021 14 314 32 031 022 282
cert_ridgeSupport_suffix_decode_2 770 020 14 346 32 031 021 314
cert_ridgeSupport_suffix_decode_2 770 019 14 378 32 031 020 346
cert_ridgeSupport_suffix_decode_2 770 018 14 410 32 031 019 378
cert_ridgeSupport_suffix_decode_2 770 017 14 442 32 031 018 410
cert_ridgeSupport_suffix_decode_2 770 016 14 474 32 031 017 442
cert_ridgeSupport_suffix_decode_2 770 015 14 506 32 031 016 474
cert_ridgeSupport_suffix_decode_2 770 014 14 538 32 031 015 506
cert_ridgeSupport_suffix_decode_2 770 013 14 570 32 031 014 538
cert_ridgeSupport_suffix_decode_2 770 012 14 602 32 031 013 570
cert_ridgeSupport_suffix_decode_2 770 011 14 634 32 031 012 602
cert_ridgeSupport_suffix_decode_2 770 010 14 666 32 031 011 634
cert_ridgeSupport_suffix_decode_2 770 009 14 698 32 031 010 666
cert_ridgeSupport_suffix_decode_2 770 008 14 730 32 031 009 698
cert_ridgeSupport_suffix_decode_2 770 007 14 762 32 031 008 730
cert_ridgeSupport_suffix_decode_2 770 006 14 794 32 031 007 762
cert_ridgeSupport_suffix_decode_2 770 005 14 826 32 031 006 794
cert_ridgeSupport_suffix_decode_2 770 004 14 858 32 031 005 826
cert_ridgeSupport_suffix_decode_2 770 003 14 890 32 031 004 858
cert_ridgeSupport_suffix_decode_2 770 002 14 922 32 031 003 890
cert_ridgeSupport_suffix_decode_2 770 001 14 954 32 031 002 922
cert_ridgeSupport_suffix_decode_2 770 000 14 986 32 031 001 954
cert_ridgeSupport_eq_3 770
theorem ridgeTest_large_770 : ridgeTest 770 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport770_eq]
    simp only [ridgeSupport770_suffix_000, ridgeSupport770_suffix_001, ridgeSupport770_suffix_002, ridgeSupport770_suffix_003, ridgeSupport770_suffix_004, ridgeSupport770_suffix_005, ridgeSupport770_suffix_006, ridgeSupport770_suffix_007, ridgeSupport770_suffix_008, ridgeSupport770_suffix_009, ridgeSupport770_suffix_010, ridgeSupport770_suffix_011, ridgeSupport770_suffix_012, ridgeSupport770_suffix_013, ridgeSupport770_suffix_014, ridgeSupport770_suffix_015, ridgeSupport770_suffix_016, ridgeSupport770_suffix_017, ridgeSupport770_suffix_018, ridgeSupport770_suffix_019, ridgeSupport770_suffix_020, ridgeSupport770_suffix_021, ridgeSupport770_suffix_022, ridgeSupport770_suffix_023, ridgeSupport770_suffix_024, ridgeSupport770_suffix_025, ridgeSupport770_suffix_026, ridgeSupport770_suffix_027, ridgeSupport770_suffix_028, ridgeSupport770_suffix_029, ridgeSupport770_suffix_030, ridgeSupport770_suffix_031, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport770_000_mask, ridgeSupport770_001_mask, ridgeSupport770_002_mask, ridgeSupport770_003_mask, ridgeSupport770_004_mask, ridgeSupport770_005_mask, ridgeSupport770_006_mask, ridgeSupport770_007_mask, ridgeSupport770_008_mask, ridgeSupport770_009_mask, ridgeSupport770_010_mask, ridgeSupport770_011_mask, ridgeSupport770_012_mask, ridgeSupport770_013_mask, ridgeSupport770_014_mask, ridgeSupport770_015_mask, ridgeSupport770_016_mask, ridgeSupport770_017_mask, ridgeSupport770_018_mask, ridgeSupport770_019_mask, ridgeSupport770_020_mask, ridgeSupport770_021_mask, ridgeSupport770_022_mask, ridgeSupport770_023_mask, ridgeSupport770_024_mask, ridgeSupport770_025_mask, ridgeSupport770_026_mask, ridgeSupport770_027_mask, ridgeSupport770_028_mask, ridgeSupport770_029_mask, ridgeSupport770_030_mask]
    decide +kernel
  · rw [ridgeSupport770_eq]
    simp only [ridgeSupport770_suffix_000, ridgeSupport770_suffix_001, ridgeSupport770_suffix_002, ridgeSupport770_suffix_003, ridgeSupport770_suffix_004, ridgeSupport770_suffix_005, ridgeSupport770_suffix_006, ridgeSupport770_suffix_007, ridgeSupport770_suffix_008, ridgeSupport770_suffix_009, ridgeSupport770_suffix_010, ridgeSupport770_suffix_011, ridgeSupport770_suffix_012, ridgeSupport770_suffix_013, ridgeSupport770_suffix_014, ridgeSupport770_suffix_015, ridgeSupport770_suffix_016, ridgeSupport770_suffix_017, ridgeSupport770_suffix_018, ridgeSupport770_suffix_019, ridgeSupport770_suffix_020, ridgeSupport770_suffix_021, ridgeSupport770_suffix_022, ridgeSupport770_suffix_023, ridgeSupport770_suffix_024, ridgeSupport770_suffix_025, ridgeSupport770_suffix_026, ridgeSupport770_suffix_027, ridgeSupport770_suffix_028, ridgeSupport770_suffix_029, ridgeSupport770_suffix_030, ridgeSupport770_suffix_031, List.all_append, List.all_nil, ridgeSupport770_000_checked, ridgeSupport770_001_checked, ridgeSupport770_002_checked, ridgeSupport770_003_checked, ridgeSupport770_004_checked, ridgeSupport770_005_checked, ridgeSupport770_006_checked, ridgeSupport770_007_checked, ridgeSupport770_008_checked, ridgeSupport770_009_checked, ridgeSupport770_010_checked, ridgeSupport770_011_checked, ridgeSupport770_012_checked, ridgeSupport770_013_checked, ridgeSupport770_014_checked, ridgeSupport770_015_checked, ridgeSupport770_016_checked, ridgeSupport770_017_checked, ridgeSupport770_018_checked, ridgeSupport770_019_checked, ridgeSupport770_020_checked, ridgeSupport770_021_checked, ridgeSupport770_022_checked, ridgeSupport770_023_checked, ridgeSupport770_024_checked, ridgeSupport770_025_checked, ridgeSupport770_026_checked, ridgeSupport770_027_checked, ridgeSupport770_028_checked, ridgeSupport770_029_checked, ridgeSupport770_030_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
