module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import BundledChecks.RootedSixExtra00GrowthCacheKindSupport3Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 3 030 14
cert_kindSupport_suffix_decode_6 3 029 14 26 26 030 030 0
cert_kindSupport_suffix_decode_6 3 028 14 58 32 030 029 26
cert_kindSupport_suffix_decode_6 3 027 14 90 32 030 028 58
cert_kindSupport_suffix_decode_6 3 026 14 122 32 030 027 90
cert_kindSupport_suffix_decode_6 3 025 14 154 32 030 026 122
cert_kindSupport_suffix_decode_6 3 024 14 186 32 030 025 154
cert_kindSupport_suffix_decode_6 3 023 14 218 32 030 024 186
cert_kindSupport_suffix_decode_6 3 022 14 250 32 030 023 218
cert_kindSupport_suffix_decode_6 3 021 14 282 32 030 022 250
cert_kindSupport_suffix_decode_6 3 020 14 314 32 030 021 282
cert_kindSupport_suffix_decode_6 3 019 14 346 32 030 020 314
cert_kindSupport_suffix_decode_6 3 018 14 378 32 030 019 346
cert_kindSupport_suffix_decode_6 3 017 14 410 32 030 018 378
cert_kindSupport_suffix_decode_6 3 016 14 442 32 030 017 410
cert_kindSupport_suffix_decode_6 3 015 14 474 32 030 016 442
cert_kindSupport_suffix_decode_6 3 014 14 506 32 030 015 474
cert_kindSupport_suffix_decode_6 3 013 14 538 32 030 014 506
cert_kindSupport_suffix_decode_6 3 012 14 570 32 030 013 538
cert_kindSupport_suffix_decode_6 3 011 14 602 32 030 012 570
cert_kindSupport_suffix_decode_6 3 010 14 634 32 030 011 602
cert_kindSupport_suffix_decode_6 3 009 14 666 32 030 010 634
cert_kindSupport_suffix_decode_6 3 008 14 698 32 030 009 666
cert_kindSupport_suffix_decode_6 3 007 14 730 32 030 008 698
cert_kindSupport_suffix_decode_6 3 006 14 762 32 030 007 730
cert_kindSupport_suffix_decode_6 3 005 14 794 32 030 006 762
cert_kindSupport_suffix_decode_6 3 004 14 826 32 030 005 794
cert_kindSupport_suffix_decode_6 3 003 14 858 32 030 004 826
cert_kindSupport_suffix_decode_6 3 002 14 890 32 030 003 858
cert_kindSupport_suffix_decode_6 3 001 14 922 32 030 002 890
cert_kindSupport_suffix_decode_6 3 000 14 954 32 030 001 922
cert_kindSupport_eq_3 3
theorem kindTest_large_3 : kindTest 3 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, kindSupport3_suffix_020, kindSupport3_suffix_021, kindSupport3_suffix_022, kindSupport3_suffix_023, kindSupport3_suffix_024, kindSupport3_suffix_025, kindSupport3_suffix_026, kindSupport3_suffix_027, kindSupport3_suffix_028, kindSupport3_suffix_029, kindSupport3_suffix_030, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport3_000_mask, kindSupport3_001_mask, kindSupport3_002_mask, kindSupport3_003_mask, kindSupport3_004_mask, kindSupport3_005_mask, kindSupport3_006_mask, kindSupport3_007_mask, kindSupport3_008_mask, kindSupport3_009_mask, kindSupport3_010_mask, kindSupport3_011_mask, kindSupport3_012_mask, kindSupport3_013_mask, kindSupport3_014_mask, kindSupport3_015_mask, kindSupport3_016_mask, kindSupport3_017_mask, kindSupport3_018_mask, kindSupport3_019_mask, kindSupport3_020_mask, kindSupport3_021_mask, kindSupport3_022_mask, kindSupport3_023_mask, kindSupport3_024_mask, kindSupport3_025_mask, kindSupport3_026_mask, kindSupport3_027_mask, kindSupport3_028_mask, kindSupport3_029_mask]
    decide +kernel
  · rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, kindSupport3_suffix_020, kindSupport3_suffix_021, kindSupport3_suffix_022, kindSupport3_suffix_023, kindSupport3_suffix_024, kindSupport3_suffix_025, kindSupport3_suffix_026, kindSupport3_suffix_027, kindSupport3_suffix_028, kindSupport3_suffix_029, kindSupport3_suffix_030, List.all_append, List.all_nil, kindSupport3_000_checked, kindSupport3_001_checked, kindSupport3_002_checked, kindSupport3_003_checked, kindSupport3_004_checked, kindSupport3_005_checked, kindSupport3_006_checked, kindSupport3_007_checked, kindSupport3_008_checked, kindSupport3_009_checked, kindSupport3_010_checked, kindSupport3_011_checked, kindSupport3_012_checked, kindSupport3_013_checked, kindSupport3_014_checked, kindSupport3_015_checked, kindSupport3_016_checked, kindSupport3_017_checked, kindSupport3_018_checked, kindSupport3_019_checked, kindSupport3_020_checked, kindSupport3_021_checked, kindSupport3_022_checked, kindSupport3_023_checked, kindSupport3_024_checked, kindSupport3_025_checked, kindSupport3_026_checked, kindSupport3_027_checked, kindSupport3_028_checked, kindSupport3_029_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra00
