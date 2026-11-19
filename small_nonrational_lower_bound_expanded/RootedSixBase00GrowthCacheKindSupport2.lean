module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import BundledChecks.RootedSixBase00GrowthCacheKindSupport2Batch000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase00
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_5 2 025 15
cert_kindSupport_suffix_decode_4 2 024 15 12 12 025 025 0
cert_kindSupport_suffix_decode_4 2 023 15 44 32 025 024 12
cert_kindSupport_suffix_decode_4 2 022 15 76 32 025 023 44
cert_kindSupport_suffix_decode_4 2 021 15 108 32 025 022 76
cert_kindSupport_suffix_decode_4 2 020 15 140 32 025 021 108
cert_kindSupport_suffix_decode_4 2 019 15 172 32 025 020 140
cert_kindSupport_suffix_decode_4 2 018 15 204 32 025 019 172
cert_kindSupport_suffix_decode_4 2 017 15 236 32 025 018 204
cert_kindSupport_suffix_decode_4 2 016 15 268 32 025 017 236
cert_kindSupport_suffix_decode_4 2 015 15 300 32 025 016 268
cert_kindSupport_suffix_decode_4 2 014 15 332 32 025 015 300
cert_kindSupport_suffix_decode_4 2 013 15 364 32 025 014 332
cert_kindSupport_suffix_decode_4 2 012 15 396 32 025 013 364
cert_kindSupport_suffix_decode_4 2 011 15 428 32 025 012 396
cert_kindSupport_suffix_decode_4 2 010 15 460 32 025 011 428
cert_kindSupport_suffix_decode_4 2 009 15 492 32 025 010 460
cert_kindSupport_suffix_decode_4 2 008 15 524 32 025 009 492
cert_kindSupport_suffix_decode_4 2 007 15 556 32 025 008 524
cert_kindSupport_suffix_decode_4 2 006 15 588 32 025 007 556
cert_kindSupport_suffix_decode_4 2 005 15 620 32 025 006 588
cert_kindSupport_suffix_decode_4 2 004 15 652 32 025 005 620
cert_kindSupport_suffix_decode_4 2 003 15 684 32 025 004 652
cert_kindSupport_suffix_decode_4 2 002 15 716 32 025 003 684
cert_kindSupport_suffix_decode_4 2 001 15 748 32 025 002 716
cert_kindSupport_suffix_decode_4 2 000 15 780 32 025 001 748
cert_kindSupport_eq_2 2
theorem kindTest_large_2 : kindTest 2 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, kindSupport2_suffix_016, kindSupport2_suffix_017, kindSupport2_suffix_018, kindSupport2_suffix_019, kindSupport2_suffix_020, kindSupport2_suffix_021, kindSupport2_suffix_022, kindSupport2_suffix_023, kindSupport2_suffix_024, kindSupport2_suffix_025, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport2_000_mask, kindSupport2_001_mask, kindSupport2_002_mask, kindSupport2_003_mask, kindSupport2_004_mask, kindSupport2_005_mask, kindSupport2_006_mask, kindSupport2_007_mask, kindSupport2_008_mask, kindSupport2_009_mask, kindSupport2_010_mask, kindSupport2_011_mask, kindSupport2_012_mask, kindSupport2_013_mask, kindSupport2_014_mask, kindSupport2_015_mask, kindSupport2_016_mask, kindSupport2_017_mask, kindSupport2_018_mask, kindSupport2_019_mask, kindSupport2_020_mask, kindSupport2_021_mask, kindSupport2_022_mask, kindSupport2_023_mask, kindSupport2_024_mask]
    decide +kernel
  · rw [kindSupport2_eq]
    simp only [kindSupport2_suffix_000, kindSupport2_suffix_001, kindSupport2_suffix_002, kindSupport2_suffix_003, kindSupport2_suffix_004, kindSupport2_suffix_005, kindSupport2_suffix_006, kindSupport2_suffix_007, kindSupport2_suffix_008, kindSupport2_suffix_009, kindSupport2_suffix_010, kindSupport2_suffix_011, kindSupport2_suffix_012, kindSupport2_suffix_013, kindSupport2_suffix_014, kindSupport2_suffix_015, kindSupport2_suffix_016, kindSupport2_suffix_017, kindSupport2_suffix_018, kindSupport2_suffix_019, kindSupport2_suffix_020, kindSupport2_suffix_021, kindSupport2_suffix_022, kindSupport2_suffix_023, kindSupport2_suffix_024, kindSupport2_suffix_025, List.all_append, List.all_nil, kindSupport2_000_checked, kindSupport2_001_checked, kindSupport2_002_checked, kindSupport2_003_checked, kindSupport2_004_checked, kindSupport2_005_checked, kindSupport2_006_checked, kindSupport2_007_checked, kindSupport2_008_checked, kindSupport2_009_checked, kindSupport2_010_checked, kindSupport2_011_checked, kindSupport2_012_checked, kindSupport2_013_checked, kindSupport2_014_checked, kindSupport2_015_checked, kindSupport2_016_checked, kindSupport2_017_checked, kindSupport2_018_checked, kindSupport2_019_checked, kindSupport2_020_checked, kindSupport2_021_checked, kindSupport2_022_checked, kindSupport2_023_checked, kindSupport2_024_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase00
