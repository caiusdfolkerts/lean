module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport648Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 648 031 14
cert_ridgeSupport_suffix_decode_2 648 030 14 26 26 031 031 0
cert_ridgeSupport_suffix_decode_2 648 029 14 58 32 031 030 26
cert_ridgeSupport_suffix_decode_2 648 028 14 90 32 031 029 58
cert_ridgeSupport_suffix_decode_2 648 027 14 122 32 031 028 90
cert_ridgeSupport_suffix_decode_2 648 026 14 154 32 031 027 122
cert_ridgeSupport_suffix_decode_2 648 025 14 186 32 031 026 154
cert_ridgeSupport_suffix_decode_2 648 024 14 218 32 031 025 186
cert_ridgeSupport_suffix_decode_2 648 023 14 250 32 031 024 218
cert_ridgeSupport_suffix_decode_2 648 022 14 282 32 031 023 250
cert_ridgeSupport_suffix_decode_2 648 021 14 314 32 031 022 282
cert_ridgeSupport_suffix_decode_2 648 020 14 346 32 031 021 314
cert_ridgeSupport_suffix_decode_2 648 019 14 378 32 031 020 346
cert_ridgeSupport_suffix_decode_2 648 018 14 410 32 031 019 378
cert_ridgeSupport_suffix_decode_2 648 017 14 442 32 031 018 410
cert_ridgeSupport_suffix_decode_2 648 016 14 474 32 031 017 442
cert_ridgeSupport_suffix_decode_2 648 015 14 506 32 031 016 474
cert_ridgeSupport_suffix_decode_2 648 014 14 538 32 031 015 506
cert_ridgeSupport_suffix_decode_2 648 013 14 570 32 031 014 538
cert_ridgeSupport_suffix_decode_2 648 012 14 602 32 031 013 570
cert_ridgeSupport_suffix_decode_2 648 011 14 634 32 031 012 602
cert_ridgeSupport_suffix_decode_2 648 010 14 666 32 031 011 634
cert_ridgeSupport_suffix_decode_2 648 009 14 698 32 031 010 666
cert_ridgeSupport_suffix_decode_2 648 008 14 730 32 031 009 698
cert_ridgeSupport_suffix_decode_2 648 007 14 762 32 031 008 730
cert_ridgeSupport_suffix_decode_2 648 006 14 794 32 031 007 762
cert_ridgeSupport_suffix_decode_2 648 005 14 826 32 031 006 794
cert_ridgeSupport_suffix_decode_2 648 004 14 858 32 031 005 826
cert_ridgeSupport_suffix_decode_2 648 003 14 890 32 031 004 858
cert_ridgeSupport_suffix_decode_2 648 002 14 922 32 031 003 890
cert_ridgeSupport_suffix_decode_2 648 001 14 954 32 031 002 922
cert_ridgeSupport_suffix_decode_2 648 000 14 986 32 031 001 954
cert_ridgeSupport_eq_3 648
theorem ridgeTest_large_648 : ridgeTest 648 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport648_eq]
    simp only [ridgeSupport648_suffix_000, ridgeSupport648_suffix_001, ridgeSupport648_suffix_002, ridgeSupport648_suffix_003, ridgeSupport648_suffix_004, ridgeSupport648_suffix_005, ridgeSupport648_suffix_006, ridgeSupport648_suffix_007, ridgeSupport648_suffix_008, ridgeSupport648_suffix_009, ridgeSupport648_suffix_010, ridgeSupport648_suffix_011, ridgeSupport648_suffix_012, ridgeSupport648_suffix_013, ridgeSupport648_suffix_014, ridgeSupport648_suffix_015, ridgeSupport648_suffix_016, ridgeSupport648_suffix_017, ridgeSupport648_suffix_018, ridgeSupport648_suffix_019, ridgeSupport648_suffix_020, ridgeSupport648_suffix_021, ridgeSupport648_suffix_022, ridgeSupport648_suffix_023, ridgeSupport648_suffix_024, ridgeSupport648_suffix_025, ridgeSupport648_suffix_026, ridgeSupport648_suffix_027, ridgeSupport648_suffix_028, ridgeSupport648_suffix_029, ridgeSupport648_suffix_030, ridgeSupport648_suffix_031, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport648_000_mask, ridgeSupport648_001_mask, ridgeSupport648_002_mask, ridgeSupport648_003_mask, ridgeSupport648_004_mask, ridgeSupport648_005_mask, ridgeSupport648_006_mask, ridgeSupport648_007_mask, ridgeSupport648_008_mask, ridgeSupport648_009_mask, ridgeSupport648_010_mask, ridgeSupport648_011_mask, ridgeSupport648_012_mask, ridgeSupport648_013_mask, ridgeSupport648_014_mask, ridgeSupport648_015_mask, ridgeSupport648_016_mask, ridgeSupport648_017_mask, ridgeSupport648_018_mask, ridgeSupport648_019_mask, ridgeSupport648_020_mask, ridgeSupport648_021_mask, ridgeSupport648_022_mask, ridgeSupport648_023_mask, ridgeSupport648_024_mask, ridgeSupport648_025_mask, ridgeSupport648_026_mask, ridgeSupport648_027_mask, ridgeSupport648_028_mask, ridgeSupport648_029_mask, ridgeSupport648_030_mask]
    decide +kernel
  · rw [ridgeSupport648_eq]
    simp only [ridgeSupport648_suffix_000, ridgeSupport648_suffix_001, ridgeSupport648_suffix_002, ridgeSupport648_suffix_003, ridgeSupport648_suffix_004, ridgeSupport648_suffix_005, ridgeSupport648_suffix_006, ridgeSupport648_suffix_007, ridgeSupport648_suffix_008, ridgeSupport648_suffix_009, ridgeSupport648_suffix_010, ridgeSupport648_suffix_011, ridgeSupport648_suffix_012, ridgeSupport648_suffix_013, ridgeSupport648_suffix_014, ridgeSupport648_suffix_015, ridgeSupport648_suffix_016, ridgeSupport648_suffix_017, ridgeSupport648_suffix_018, ridgeSupport648_suffix_019, ridgeSupport648_suffix_020, ridgeSupport648_suffix_021, ridgeSupport648_suffix_022, ridgeSupport648_suffix_023, ridgeSupport648_suffix_024, ridgeSupport648_suffix_025, ridgeSupport648_suffix_026, ridgeSupport648_suffix_027, ridgeSupport648_suffix_028, ridgeSupport648_suffix_029, ridgeSupport648_suffix_030, ridgeSupport648_suffix_031, List.all_append, List.all_nil, ridgeSupport648_000_checked, ridgeSupport648_001_checked, ridgeSupport648_002_checked, ridgeSupport648_003_checked, ridgeSupport648_004_checked, ridgeSupport648_005_checked, ridgeSupport648_006_checked, ridgeSupport648_007_checked, ridgeSupport648_008_checked, ridgeSupport648_009_checked, ridgeSupport648_010_checked, ridgeSupport648_011_checked, ridgeSupport648_012_checked, ridgeSupport648_013_checked, ridgeSupport648_014_checked, ridgeSupport648_015_checked, ridgeSupport648_016_checked, ridgeSupport648_017_checked, ridgeSupport648_018_checked, ridgeSupport648_019_checked, ridgeSupport648_020_checked, ridgeSupport648_021_checked, ridgeSupport648_022_checked, ridgeSupport648_023_checked, ridgeSupport648_024_checked, ridgeSupport648_025_checked, ridgeSupport648_026_checked, ridgeSupport648_027_checked, ridgeSupport648_028_checked, ridgeSupport648_029_checked, ridgeSupport648_030_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
