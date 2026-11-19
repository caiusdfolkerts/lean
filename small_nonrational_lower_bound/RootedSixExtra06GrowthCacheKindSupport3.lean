module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra06GrowthCacheKindSupport3Part000
public import RootedSixExtra06GrowthCacheKindSupport3Part001
public import RootedSixExtra06GrowthCacheKindSupport3Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_7 3 024 12
cert_kindSupport_suffix_decode_6 3 023 12 14 14 024 024 0
cert_kindSupport_suffix_decode_6 3 022 12 46 32 024 023 14
cert_kindSupport_suffix_decode_6 3 021 12 78 32 024 022 46
cert_kindSupport_suffix_decode_6 3 020 12 110 32 024 021 78
cert_kindSupport_suffix_decode_6 3 019 12 142 32 024 020 110
cert_kindSupport_suffix_decode_6 3 018 12 174 32 024 019 142
cert_kindSupport_suffix_decode_6 3 017 12 206 32 024 018 174
cert_kindSupport_suffix_decode_6 3 016 12 238 32 024 017 206
cert_kindSupport_suffix_decode_6 3 015 12 270 32 024 016 238
cert_kindSupport_suffix_decode_6 3 014 12 302 32 024 015 270
cert_kindSupport_suffix_decode_6 3 013 12 334 32 024 014 302
cert_kindSupport_suffix_decode_6 3 012 12 366 32 024 013 334
cert_kindSupport_suffix_decode_6 3 011 12 398 32 024 012 366
cert_kindSupport_suffix_decode_6 3 010 12 430 32 024 011 398
cert_kindSupport_suffix_decode_6 3 009 12 462 32 024 010 430
cert_kindSupport_suffix_decode_6 3 008 12 494 32 024 009 462
cert_kindSupport_suffix_decode_6 3 007 12 526 32 024 008 494
cert_kindSupport_suffix_decode_6 3 006 12 558 32 024 007 526
cert_kindSupport_suffix_decode_6 3 005 12 590 32 024 006 558
cert_kindSupport_suffix_decode_6 3 004 12 622 32 024 005 590
cert_kindSupport_suffix_decode_6 3 003 12 654 32 024 004 622
cert_kindSupport_suffix_decode_6 3 002 12 686 32 024 003 654
cert_kindSupport_suffix_decode_6 3 001 12 718 32 024 002 686
cert_kindSupport_suffix_decode_6 3 000 12 750 32 024 001 718
cert_kindSupport_eq_3 3
theorem kindTest_large_3 : kindTest 3 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, kindSupport3_suffix_020, kindSupport3_suffix_021, kindSupport3_suffix_022, kindSupport3_suffix_023, kindSupport3_suffix_024, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport3_000_mask, kindSupport3_001_mask, kindSupport3_002_mask, kindSupport3_003_mask, kindSupport3_004_mask, kindSupport3_005_mask, kindSupport3_006_mask, kindSupport3_007_mask, kindSupport3_008_mask, kindSupport3_009_mask, kindSupport3_010_mask, kindSupport3_011_mask, kindSupport3_012_mask, kindSupport3_013_mask, kindSupport3_014_mask, kindSupport3_015_mask, kindSupport3_016_mask, kindSupport3_017_mask, kindSupport3_018_mask, kindSupport3_019_mask, kindSupport3_020_mask, kindSupport3_021_mask, kindSupport3_022_mask, kindSupport3_023_mask]
    decide +kernel
  · rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, kindSupport3_suffix_020, kindSupport3_suffix_021, kindSupport3_suffix_022, kindSupport3_suffix_023, kindSupport3_suffix_024, List.all_append, List.all_nil, kindSupport3_000_checked, kindSupport3_001_checked, kindSupport3_002_checked, kindSupport3_003_checked, kindSupport3_004_checked, kindSupport3_005_checked, kindSupport3_006_checked, kindSupport3_007_checked, kindSupport3_008_checked, kindSupport3_009_checked, kindSupport3_010_checked, kindSupport3_011_checked, kindSupport3_012_checked, kindSupport3_013_checked, kindSupport3_014_checked, kindSupport3_015_checked, kindSupport3_016_checked, kindSupport3_017_checked, kindSupport3_018_checked, kindSupport3_019_checked, kindSupport3_020_checked, kindSupport3_021_checked, kindSupport3_022_checked, kindSupport3_023_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
