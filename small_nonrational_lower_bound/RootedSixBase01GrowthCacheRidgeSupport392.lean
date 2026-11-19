module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport392Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 392 031 14
cert_ridgeSupport_suffix_decode_2 392 030 14 26 26 031 031 0
cert_ridgeSupport_suffix_decode_2 392 029 14 58 32 031 030 26
cert_ridgeSupport_suffix_decode_2 392 028 14 90 32 031 029 58
cert_ridgeSupport_suffix_decode_2 392 027 14 122 32 031 028 90
cert_ridgeSupport_suffix_decode_2 392 026 14 154 32 031 027 122
cert_ridgeSupport_suffix_decode_2 392 025 14 186 32 031 026 154
cert_ridgeSupport_suffix_decode_2 392 024 14 218 32 031 025 186
cert_ridgeSupport_suffix_decode_2 392 023 14 250 32 031 024 218
cert_ridgeSupport_suffix_decode_2 392 022 14 282 32 031 023 250
cert_ridgeSupport_suffix_decode_2 392 021 14 314 32 031 022 282
cert_ridgeSupport_suffix_decode_2 392 020 14 346 32 031 021 314
cert_ridgeSupport_suffix_decode_2 392 019 14 378 32 031 020 346
cert_ridgeSupport_suffix_decode_2 392 018 14 410 32 031 019 378
cert_ridgeSupport_suffix_decode_2 392 017 14 442 32 031 018 410
cert_ridgeSupport_suffix_decode_2 392 016 14 474 32 031 017 442
cert_ridgeSupport_suffix_decode_2 392 015 14 506 32 031 016 474
cert_ridgeSupport_suffix_decode_2 392 014 14 538 32 031 015 506
cert_ridgeSupport_suffix_decode_2 392 013 14 570 32 031 014 538
cert_ridgeSupport_suffix_decode_2 392 012 14 602 32 031 013 570
cert_ridgeSupport_suffix_decode_2 392 011 14 634 32 031 012 602
cert_ridgeSupport_suffix_decode_2 392 010 14 666 32 031 011 634
cert_ridgeSupport_suffix_decode_2 392 009 14 698 32 031 010 666
cert_ridgeSupport_suffix_decode_2 392 008 14 730 32 031 009 698
cert_ridgeSupport_suffix_decode_2 392 007 14 762 32 031 008 730
cert_ridgeSupport_suffix_decode_2 392 006 14 794 32 031 007 762
cert_ridgeSupport_suffix_decode_2 392 005 14 826 32 031 006 794
cert_ridgeSupport_suffix_decode_2 392 004 14 858 32 031 005 826
cert_ridgeSupport_suffix_decode_2 392 003 14 890 32 031 004 858
cert_ridgeSupport_suffix_decode_2 392 002 14 922 32 031 003 890
cert_ridgeSupport_suffix_decode_2 392 001 14 954 32 031 002 922
cert_ridgeSupport_suffix_decode_2 392 000 14 986 32 031 001 954
cert_ridgeSupport_eq_3 392
theorem ridgeTest_large_392 : ridgeTest 392 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport392_eq]
    simp only [ridgeSupport392_suffix_000, ridgeSupport392_suffix_001, ridgeSupport392_suffix_002, ridgeSupport392_suffix_003, ridgeSupport392_suffix_004, ridgeSupport392_suffix_005, ridgeSupport392_suffix_006, ridgeSupport392_suffix_007, ridgeSupport392_suffix_008, ridgeSupport392_suffix_009, ridgeSupport392_suffix_010, ridgeSupport392_suffix_011, ridgeSupport392_suffix_012, ridgeSupport392_suffix_013, ridgeSupport392_suffix_014, ridgeSupport392_suffix_015, ridgeSupport392_suffix_016, ridgeSupport392_suffix_017, ridgeSupport392_suffix_018, ridgeSupport392_suffix_019, ridgeSupport392_suffix_020, ridgeSupport392_suffix_021, ridgeSupport392_suffix_022, ridgeSupport392_suffix_023, ridgeSupport392_suffix_024, ridgeSupport392_suffix_025, ridgeSupport392_suffix_026, ridgeSupport392_suffix_027, ridgeSupport392_suffix_028, ridgeSupport392_suffix_029, ridgeSupport392_suffix_030, ridgeSupport392_suffix_031, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport392_000_mask, ridgeSupport392_001_mask, ridgeSupport392_002_mask, ridgeSupport392_003_mask, ridgeSupport392_004_mask, ridgeSupport392_005_mask, ridgeSupport392_006_mask, ridgeSupport392_007_mask, ridgeSupport392_008_mask, ridgeSupport392_009_mask, ridgeSupport392_010_mask, ridgeSupport392_011_mask, ridgeSupport392_012_mask, ridgeSupport392_013_mask, ridgeSupport392_014_mask, ridgeSupport392_015_mask, ridgeSupport392_016_mask, ridgeSupport392_017_mask, ridgeSupport392_018_mask, ridgeSupport392_019_mask, ridgeSupport392_020_mask, ridgeSupport392_021_mask, ridgeSupport392_022_mask, ridgeSupport392_023_mask, ridgeSupport392_024_mask, ridgeSupport392_025_mask, ridgeSupport392_026_mask, ridgeSupport392_027_mask, ridgeSupport392_028_mask, ridgeSupport392_029_mask, ridgeSupport392_030_mask]
    decide +kernel
  · rw [ridgeSupport392_eq]
    simp only [ridgeSupport392_suffix_000, ridgeSupport392_suffix_001, ridgeSupport392_suffix_002, ridgeSupport392_suffix_003, ridgeSupport392_suffix_004, ridgeSupport392_suffix_005, ridgeSupport392_suffix_006, ridgeSupport392_suffix_007, ridgeSupport392_suffix_008, ridgeSupport392_suffix_009, ridgeSupport392_suffix_010, ridgeSupport392_suffix_011, ridgeSupport392_suffix_012, ridgeSupport392_suffix_013, ridgeSupport392_suffix_014, ridgeSupport392_suffix_015, ridgeSupport392_suffix_016, ridgeSupport392_suffix_017, ridgeSupport392_suffix_018, ridgeSupport392_suffix_019, ridgeSupport392_suffix_020, ridgeSupport392_suffix_021, ridgeSupport392_suffix_022, ridgeSupport392_suffix_023, ridgeSupport392_suffix_024, ridgeSupport392_suffix_025, ridgeSupport392_suffix_026, ridgeSupport392_suffix_027, ridgeSupport392_suffix_028, ridgeSupport392_suffix_029, ridgeSupport392_suffix_030, ridgeSupport392_suffix_031, List.all_append, List.all_nil, ridgeSupport392_000_checked, ridgeSupport392_001_checked, ridgeSupport392_002_checked, ridgeSupport392_003_checked, ridgeSupport392_004_checked, ridgeSupport392_005_checked, ridgeSupport392_006_checked, ridgeSupport392_007_checked, ridgeSupport392_008_checked, ridgeSupport392_009_checked, ridgeSupport392_010_checked, ridgeSupport392_011_checked, ridgeSupport392_012_checked, ridgeSupport392_013_checked, ridgeSupport392_014_checked, ridgeSupport392_015_checked, ridgeSupport392_016_checked, ridgeSupport392_017_checked, ridgeSupport392_018_checked, ridgeSupport392_019_checked, ridgeSupport392_020_checked, ridgeSupport392_021_checked, ridgeSupport392_022_checked, ridgeSupport392_023_checked, ridgeSupport392_024_checked, ridgeSupport392_025_checked, ridgeSupport392_026_checked, ridgeSupport392_027_checked, ridgeSupport392_028_checked, ridgeSupport392_029_checked, ridgeSupport392_030_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
