module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport672PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 672 023 14
cert_ridgeSupport_suffix_decode_2 672 022 14 15 15 023 023 0
cert_ridgeSupport_suffix_decode_2 672 021 14 47 32 023 022 15
cert_ridgeSupport_suffix_decode_2 672 020 14 79 32 023 021 47
cert_ridgeSupport_suffix_decode_2 672 019 14 111 32 023 020 79
cert_ridgeSupport_suffix_decode_2 672 018 14 143 32 023 019 111
cert_ridgeSupport_suffix_decode_2 672 017 14 175 32 023 018 143
cert_ridgeSupport_suffix_decode_2 672 016 14 207 32 023 017 175
cert_ridgeSupport_suffix_decode_2 672 015 14 239 32 023 016 207
cert_ridgeSupport_suffix_decode_2 672 014 14 271 32 023 015 239
cert_ridgeSupport_suffix_decode_2 672 013 14 303 32 023 014 271
cert_ridgeSupport_suffix_decode_2 672 012 14 335 32 023 013 303
cert_ridgeSupport_suffix_decode_2 672 011 14 367 32 023 012 335
cert_ridgeSupport_suffix_decode_2 672 010 14 399 32 023 011 367
cert_ridgeSupport_suffix_decode_2 672 009 14 431 32 023 010 399
cert_ridgeSupport_suffix_decode_2 672 008 14 463 32 023 009 431
cert_ridgeSupport_suffix_decode_2 672 007 14 495 32 023 008 463
cert_ridgeSupport_suffix_decode_2 672 006 14 527 32 023 007 495
cert_ridgeSupport_suffix_decode_2 672 005 14 559 32 023 006 527
cert_ridgeSupport_suffix_decode_2 672 004 14 591 32 023 005 559
cert_ridgeSupport_suffix_decode_2 672 003 14 623 32 023 004 591
cert_ridgeSupport_suffix_decode_2 672 002 14 655 32 023 003 623
cert_ridgeSupport_suffix_decode_2 672 001 14 687 32 023 002 655
cert_ridgeSupport_suffix_decode_2 672 000 14 719 32 023 001 687
cert_ridgeSupport_eq_3 672
theorem ridgeTest_large_672 : ridgeTest 672 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport672_eq]
    simp only [ridgeSupport672_suffix_000, ridgeSupport672_suffix_001, ridgeSupport672_suffix_002, ridgeSupport672_suffix_003, ridgeSupport672_suffix_004, ridgeSupport672_suffix_005, ridgeSupport672_suffix_006, ridgeSupport672_suffix_007, ridgeSupport672_suffix_008, ridgeSupport672_suffix_009, ridgeSupport672_suffix_010, ridgeSupport672_suffix_011, ridgeSupport672_suffix_012, ridgeSupport672_suffix_013, ridgeSupport672_suffix_014, ridgeSupport672_suffix_015, ridgeSupport672_suffix_016, ridgeSupport672_suffix_017, ridgeSupport672_suffix_018, ridgeSupport672_suffix_019, ridgeSupport672_suffix_020, ridgeSupport672_suffix_021, ridgeSupport672_suffix_022, ridgeSupport672_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport672_000_mask, ridgeSupport672_001_mask, ridgeSupport672_002_mask, ridgeSupport672_003_mask, ridgeSupport672_004_mask, ridgeSupport672_005_mask, ridgeSupport672_006_mask, ridgeSupport672_007_mask, ridgeSupport672_008_mask, ridgeSupport672_009_mask, ridgeSupport672_010_mask, ridgeSupport672_011_mask, ridgeSupport672_012_mask, ridgeSupport672_013_mask, ridgeSupport672_014_mask, ridgeSupport672_015_mask, ridgeSupport672_016_mask, ridgeSupport672_017_mask, ridgeSupport672_018_mask, ridgeSupport672_019_mask, ridgeSupport672_020_mask, ridgeSupport672_021_mask, ridgeSupport672_022_mask]
    decide +kernel
  · rw [ridgeSupport672_eq]
    simp only [ridgeSupport672_suffix_000, ridgeSupport672_suffix_001, ridgeSupport672_suffix_002, ridgeSupport672_suffix_003, ridgeSupport672_suffix_004, ridgeSupport672_suffix_005, ridgeSupport672_suffix_006, ridgeSupport672_suffix_007, ridgeSupport672_suffix_008, ridgeSupport672_suffix_009, ridgeSupport672_suffix_010, ridgeSupport672_suffix_011, ridgeSupport672_suffix_012, ridgeSupport672_suffix_013, ridgeSupport672_suffix_014, ridgeSupport672_suffix_015, ridgeSupport672_suffix_016, ridgeSupport672_suffix_017, ridgeSupport672_suffix_018, ridgeSupport672_suffix_019, ridgeSupport672_suffix_020, ridgeSupport672_suffix_021, ridgeSupport672_suffix_022, ridgeSupport672_suffix_023, List.all_append, List.all_nil, ridgeSupport672_000_checked, ridgeSupport672_001_checked, ridgeSupport672_002_checked, ridgeSupport672_003_checked, ridgeSupport672_004_checked, ridgeSupport672_005_checked, ridgeSupport672_006_checked, ridgeSupport672_007_checked, ridgeSupport672_008_checked, ridgeSupport672_009_checked, ridgeSupport672_010_checked, ridgeSupport672_011_checked, ridgeSupport672_012_checked, ridgeSupport672_013_checked, ridgeSupport672_014_checked, ridgeSupport672_015_checked, ridgeSupport672_016_checked, ridgeSupport672_017_checked, ridgeSupport672_018_checked, ridgeSupport672_019_checked, ridgeSupport672_020_checked, ridgeSupport672_021_checked, ridgeSupport672_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
