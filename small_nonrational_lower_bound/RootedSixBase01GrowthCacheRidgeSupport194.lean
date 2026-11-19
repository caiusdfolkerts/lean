module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import BundledChecks.RootedSixBase01GrowthCacheRidgeSupport194Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 194 031 14
cert_ridgeSupport_suffix_decode_2 194 030 14 26 26 031 031 0
cert_ridgeSupport_suffix_decode_2 194 029 14 58 32 031 030 26
cert_ridgeSupport_suffix_decode_2 194 028 14 90 32 031 029 58
cert_ridgeSupport_suffix_decode_2 194 027 14 122 32 031 028 90
cert_ridgeSupport_suffix_decode_2 194 026 14 154 32 031 027 122
cert_ridgeSupport_suffix_decode_2 194 025 14 186 32 031 026 154
cert_ridgeSupport_suffix_decode_2 194 024 14 218 32 031 025 186
cert_ridgeSupport_suffix_decode_2 194 023 14 250 32 031 024 218
cert_ridgeSupport_suffix_decode_2 194 022 14 282 32 031 023 250
cert_ridgeSupport_suffix_decode_2 194 021 14 314 32 031 022 282
cert_ridgeSupport_suffix_decode_2 194 020 14 346 32 031 021 314
cert_ridgeSupport_suffix_decode_2 194 019 14 378 32 031 020 346
cert_ridgeSupport_suffix_decode_2 194 018 14 410 32 031 019 378
cert_ridgeSupport_suffix_decode_2 194 017 14 442 32 031 018 410
cert_ridgeSupport_suffix_decode_2 194 016 14 474 32 031 017 442
cert_ridgeSupport_suffix_decode_2 194 015 14 506 32 031 016 474
cert_ridgeSupport_suffix_decode_2 194 014 14 538 32 031 015 506
cert_ridgeSupport_suffix_decode_2 194 013 14 570 32 031 014 538
cert_ridgeSupport_suffix_decode_2 194 012 14 602 32 031 013 570
cert_ridgeSupport_suffix_decode_2 194 011 14 634 32 031 012 602
cert_ridgeSupport_suffix_decode_2 194 010 14 666 32 031 011 634
cert_ridgeSupport_suffix_decode_2 194 009 14 698 32 031 010 666
cert_ridgeSupport_suffix_decode_2 194 008 14 730 32 031 009 698
cert_ridgeSupport_suffix_decode_2 194 007 14 762 32 031 008 730
cert_ridgeSupport_suffix_decode_2 194 006 14 794 32 031 007 762
cert_ridgeSupport_suffix_decode_2 194 005 14 826 32 031 006 794
cert_ridgeSupport_suffix_decode_2 194 004 14 858 32 031 005 826
cert_ridgeSupport_suffix_decode_2 194 003 14 890 32 031 004 858
cert_ridgeSupport_suffix_decode_2 194 002 14 922 32 031 003 890
cert_ridgeSupport_suffix_decode_2 194 001 14 954 32 031 002 922
cert_ridgeSupport_suffix_decode_2 194 000 14 986 32 031 001 954
cert_ridgeSupport_eq_3 194
theorem ridgeTest_large_194 : ridgeTest 194 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport194_eq]
    simp only [ridgeSupport194_suffix_000, ridgeSupport194_suffix_001, ridgeSupport194_suffix_002, ridgeSupport194_suffix_003, ridgeSupport194_suffix_004, ridgeSupport194_suffix_005, ridgeSupport194_suffix_006, ridgeSupport194_suffix_007, ridgeSupport194_suffix_008, ridgeSupport194_suffix_009, ridgeSupport194_suffix_010, ridgeSupport194_suffix_011, ridgeSupport194_suffix_012, ridgeSupport194_suffix_013, ridgeSupport194_suffix_014, ridgeSupport194_suffix_015, ridgeSupport194_suffix_016, ridgeSupport194_suffix_017, ridgeSupport194_suffix_018, ridgeSupport194_suffix_019, ridgeSupport194_suffix_020, ridgeSupport194_suffix_021, ridgeSupport194_suffix_022, ridgeSupport194_suffix_023, ridgeSupport194_suffix_024, ridgeSupport194_suffix_025, ridgeSupport194_suffix_026, ridgeSupport194_suffix_027, ridgeSupport194_suffix_028, ridgeSupport194_suffix_029, ridgeSupport194_suffix_030, ridgeSupport194_suffix_031, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport194_000_mask, ridgeSupport194_001_mask, ridgeSupport194_002_mask, ridgeSupport194_003_mask, ridgeSupport194_004_mask, ridgeSupport194_005_mask, ridgeSupport194_006_mask, ridgeSupport194_007_mask, ridgeSupport194_008_mask, ridgeSupport194_009_mask, ridgeSupport194_010_mask, ridgeSupport194_011_mask, ridgeSupport194_012_mask, ridgeSupport194_013_mask, ridgeSupport194_014_mask, ridgeSupport194_015_mask, ridgeSupport194_016_mask, ridgeSupport194_017_mask, ridgeSupport194_018_mask, ridgeSupport194_019_mask, ridgeSupport194_020_mask, ridgeSupport194_021_mask, ridgeSupport194_022_mask, ridgeSupport194_023_mask, ridgeSupport194_024_mask, ridgeSupport194_025_mask, ridgeSupport194_026_mask, ridgeSupport194_027_mask, ridgeSupport194_028_mask, ridgeSupport194_029_mask, ridgeSupport194_030_mask]
    decide +kernel
  · rw [ridgeSupport194_eq]
    simp only [ridgeSupport194_suffix_000, ridgeSupport194_suffix_001, ridgeSupport194_suffix_002, ridgeSupport194_suffix_003, ridgeSupport194_suffix_004, ridgeSupport194_suffix_005, ridgeSupport194_suffix_006, ridgeSupport194_suffix_007, ridgeSupport194_suffix_008, ridgeSupport194_suffix_009, ridgeSupport194_suffix_010, ridgeSupport194_suffix_011, ridgeSupport194_suffix_012, ridgeSupport194_suffix_013, ridgeSupport194_suffix_014, ridgeSupport194_suffix_015, ridgeSupport194_suffix_016, ridgeSupport194_suffix_017, ridgeSupport194_suffix_018, ridgeSupport194_suffix_019, ridgeSupport194_suffix_020, ridgeSupport194_suffix_021, ridgeSupport194_suffix_022, ridgeSupport194_suffix_023, ridgeSupport194_suffix_024, ridgeSupport194_suffix_025, ridgeSupport194_suffix_026, ridgeSupport194_suffix_027, ridgeSupport194_suffix_028, ridgeSupport194_suffix_029, ridgeSupport194_suffix_030, ridgeSupport194_suffix_031, List.all_append, List.all_nil, ridgeSupport194_000_checked, ridgeSupport194_001_checked, ridgeSupport194_002_checked, ridgeSupport194_003_checked, ridgeSupport194_004_checked, ridgeSupport194_005_checked, ridgeSupport194_006_checked, ridgeSupport194_007_checked, ridgeSupport194_008_checked, ridgeSupport194_009_checked, ridgeSupport194_010_checked, ridgeSupport194_011_checked, ridgeSupport194_012_checked, ridgeSupport194_013_checked, ridgeSupport194_014_checked, ridgeSupport194_015_checked, ridgeSupport194_016_checked, ridgeSupport194_017_checked, ridgeSupport194_018_checked, ridgeSupport194_019_checked, ridgeSupport194_020_checked, ridgeSupport194_021_checked, ridgeSupport194_022_checked, ridgeSupport194_023_checked, ridgeSupport194_024_checked, ridgeSupport194_025_checked, ridgeSupport194_026_checked, ridgeSupport194_027_checked, ridgeSupport194_028_checked, ridgeSupport194_029_checked, ridgeSupport194_030_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
