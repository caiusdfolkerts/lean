module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra06GrowthCacheKindSupport10Part000
public import RootedSixExtra06GrowthCacheKindSupport10Part001
public import RootedSixExtra06GrowthCacheKindSupport10Part002
public import RootedSixExtra06GrowthCacheKindSupport10Part003
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 10 027 12
cert_kindSupport_suffix_decode_6 10 026 12 12 12 027 027 0
cert_kindSupport_suffix_decode_6 10 025 12 44 32 027 026 12
cert_kindSupport_suffix_decode_6 10 024 12 76 32 027 025 44
cert_kindSupport_suffix_decode_6 10 023 12 108 32 027 024 76
cert_kindSupport_suffix_decode_6 10 022 12 140 32 027 023 108
cert_kindSupport_suffix_decode_6 10 021 12 172 32 027 022 140
cert_kindSupport_suffix_decode_6 10 020 12 204 32 027 021 172
cert_kindSupport_suffix_decode_6 10 019 12 236 32 027 020 204
cert_kindSupport_suffix_decode_6 10 018 12 268 32 027 019 236
cert_kindSupport_suffix_decode_6 10 017 12 300 32 027 018 268
cert_kindSupport_suffix_decode_6 10 016 12 332 32 027 017 300
cert_kindSupport_suffix_decode_6 10 015 12 364 32 027 016 332
cert_kindSupport_suffix_decode_6 10 014 12 396 32 027 015 364
cert_kindSupport_suffix_decode_6 10 013 12 428 32 027 014 396
cert_kindSupport_suffix_decode_6 10 012 12 460 32 027 013 428
cert_kindSupport_suffix_decode_6 10 011 12 492 32 027 012 460
cert_kindSupport_suffix_decode_6 10 010 12 524 32 027 011 492
cert_kindSupport_suffix_decode_6 10 009 12 556 32 027 010 524
cert_kindSupport_suffix_decode_6 10 008 12 588 32 027 009 556
cert_kindSupport_suffix_decode_6 10 007 12 620 32 027 008 588
cert_kindSupport_suffix_decode_6 10 006 12 652 32 027 007 620
cert_kindSupport_suffix_decode_6 10 005 12 684 32 027 006 652
cert_kindSupport_suffix_decode_6 10 004 12 716 32 027 005 684
cert_kindSupport_suffix_decode_6 10 003 12 748 32 027 004 716
cert_kindSupport_suffix_decode_6 10 002 12 780 32 027 003 748
cert_kindSupport_suffix_decode_6 10 001 12 812 32 027 002 780
cert_kindSupport_suffix_decode_6 10 000 12 844 32 027 001 812
cert_kindSupport_eq_3 10
theorem kindTest_large_10 : kindTest 10 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport10_eq]
    simp only [kindSupport10_suffix_000, kindSupport10_suffix_001, kindSupport10_suffix_002, kindSupport10_suffix_003, kindSupport10_suffix_004, kindSupport10_suffix_005, kindSupport10_suffix_006, kindSupport10_suffix_007, kindSupport10_suffix_008, kindSupport10_suffix_009, kindSupport10_suffix_010, kindSupport10_suffix_011, kindSupport10_suffix_012, kindSupport10_suffix_013, kindSupport10_suffix_014, kindSupport10_suffix_015, kindSupport10_suffix_016, kindSupport10_suffix_017, kindSupport10_suffix_018, kindSupport10_suffix_019, kindSupport10_suffix_020, kindSupport10_suffix_021, kindSupport10_suffix_022, kindSupport10_suffix_023, kindSupport10_suffix_024, kindSupport10_suffix_025, kindSupport10_suffix_026, kindSupport10_suffix_027, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport10_000_mask, kindSupport10_001_mask, kindSupport10_002_mask, kindSupport10_003_mask, kindSupport10_004_mask, kindSupport10_005_mask, kindSupport10_006_mask, kindSupport10_007_mask, kindSupport10_008_mask, kindSupport10_009_mask, kindSupport10_010_mask, kindSupport10_011_mask, kindSupport10_012_mask, kindSupport10_013_mask, kindSupport10_014_mask, kindSupport10_015_mask, kindSupport10_016_mask, kindSupport10_017_mask, kindSupport10_018_mask, kindSupport10_019_mask, kindSupport10_020_mask, kindSupport10_021_mask, kindSupport10_022_mask, kindSupport10_023_mask, kindSupport10_024_mask, kindSupport10_025_mask, kindSupport10_026_mask]
    decide +kernel
  · rw [kindSupport10_eq]
    simp only [kindSupport10_suffix_000, kindSupport10_suffix_001, kindSupport10_suffix_002, kindSupport10_suffix_003, kindSupport10_suffix_004, kindSupport10_suffix_005, kindSupport10_suffix_006, kindSupport10_suffix_007, kindSupport10_suffix_008, kindSupport10_suffix_009, kindSupport10_suffix_010, kindSupport10_suffix_011, kindSupport10_suffix_012, kindSupport10_suffix_013, kindSupport10_suffix_014, kindSupport10_suffix_015, kindSupport10_suffix_016, kindSupport10_suffix_017, kindSupport10_suffix_018, kindSupport10_suffix_019, kindSupport10_suffix_020, kindSupport10_suffix_021, kindSupport10_suffix_022, kindSupport10_suffix_023, kindSupport10_suffix_024, kindSupport10_suffix_025, kindSupport10_suffix_026, kindSupport10_suffix_027, List.all_append, List.all_nil, kindSupport10_000_checked, kindSupport10_001_checked, kindSupport10_002_checked, kindSupport10_003_checked, kindSupport10_004_checked, kindSupport10_005_checked, kindSupport10_006_checked, kindSupport10_007_checked, kindSupport10_008_checked, kindSupport10_009_checked, kindSupport10_010_checked, kindSupport10_011_checked, kindSupport10_012_checked, kindSupport10_013_checked, kindSupport10_014_checked, kindSupport10_015_checked, kindSupport10_016_checked, kindSupport10_017_checked, kindSupport10_018_checked, kindSupport10_019_checked, kindSupport10_020_checked, kindSupport10_021_checked, kindSupport10_022_checked, kindSupport10_023_checked, kindSupport10_024_checked, kindSupport10_025_checked, kindSupport10_026_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
