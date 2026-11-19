module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport608PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 608 023 14
cert_ridgeSupport_suffix_decode_2 608 022 14 15 15 023 023 0
cert_ridgeSupport_suffix_decode_2 608 021 14 47 32 023 022 15
cert_ridgeSupport_suffix_decode_2 608 020 14 79 32 023 021 47
cert_ridgeSupport_suffix_decode_2 608 019 14 111 32 023 020 79
cert_ridgeSupport_suffix_decode_2 608 018 14 143 32 023 019 111
cert_ridgeSupport_suffix_decode_2 608 017 14 175 32 023 018 143
cert_ridgeSupport_suffix_decode_2 608 016 14 207 32 023 017 175
cert_ridgeSupport_suffix_decode_2 608 015 14 239 32 023 016 207
cert_ridgeSupport_suffix_decode_2 608 014 14 271 32 023 015 239
cert_ridgeSupport_suffix_decode_2 608 013 14 303 32 023 014 271
cert_ridgeSupport_suffix_decode_2 608 012 14 335 32 023 013 303
cert_ridgeSupport_suffix_decode_2 608 011 14 367 32 023 012 335
cert_ridgeSupport_suffix_decode_2 608 010 14 399 32 023 011 367
cert_ridgeSupport_suffix_decode_2 608 009 14 431 32 023 010 399
cert_ridgeSupport_suffix_decode_2 608 008 14 463 32 023 009 431
cert_ridgeSupport_suffix_decode_2 608 007 14 495 32 023 008 463
cert_ridgeSupport_suffix_decode_2 608 006 14 527 32 023 007 495
cert_ridgeSupport_suffix_decode_2 608 005 14 559 32 023 006 527
cert_ridgeSupport_suffix_decode_2 608 004 14 591 32 023 005 559
cert_ridgeSupport_suffix_decode_2 608 003 14 623 32 023 004 591
cert_ridgeSupport_suffix_decode_2 608 002 14 655 32 023 003 623
cert_ridgeSupport_suffix_decode_2 608 001 14 687 32 023 002 655
cert_ridgeSupport_suffix_decode_2 608 000 14 719 32 023 001 687
cert_ridgeSupport_eq_3 608
theorem ridgeTest_large_608 : ridgeTest 608 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport608_eq]
    simp only [ridgeSupport608_suffix_000, ridgeSupport608_suffix_001, ridgeSupport608_suffix_002, ridgeSupport608_suffix_003, ridgeSupport608_suffix_004, ridgeSupport608_suffix_005, ridgeSupport608_suffix_006, ridgeSupport608_suffix_007, ridgeSupport608_suffix_008, ridgeSupport608_suffix_009, ridgeSupport608_suffix_010, ridgeSupport608_suffix_011, ridgeSupport608_suffix_012, ridgeSupport608_suffix_013, ridgeSupport608_suffix_014, ridgeSupport608_suffix_015, ridgeSupport608_suffix_016, ridgeSupport608_suffix_017, ridgeSupport608_suffix_018, ridgeSupport608_suffix_019, ridgeSupport608_suffix_020, ridgeSupport608_suffix_021, ridgeSupport608_suffix_022, ridgeSupport608_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport608_000_mask, ridgeSupport608_001_mask, ridgeSupport608_002_mask, ridgeSupport608_003_mask, ridgeSupport608_004_mask, ridgeSupport608_005_mask, ridgeSupport608_006_mask, ridgeSupport608_007_mask, ridgeSupport608_008_mask, ridgeSupport608_009_mask, ridgeSupport608_010_mask, ridgeSupport608_011_mask, ridgeSupport608_012_mask, ridgeSupport608_013_mask, ridgeSupport608_014_mask, ridgeSupport608_015_mask, ridgeSupport608_016_mask, ridgeSupport608_017_mask, ridgeSupport608_018_mask, ridgeSupport608_019_mask, ridgeSupport608_020_mask, ridgeSupport608_021_mask, ridgeSupport608_022_mask]
    decide +kernel
  · rw [ridgeSupport608_eq]
    simp only [ridgeSupport608_suffix_000, ridgeSupport608_suffix_001, ridgeSupport608_suffix_002, ridgeSupport608_suffix_003, ridgeSupport608_suffix_004, ridgeSupport608_suffix_005, ridgeSupport608_suffix_006, ridgeSupport608_suffix_007, ridgeSupport608_suffix_008, ridgeSupport608_suffix_009, ridgeSupport608_suffix_010, ridgeSupport608_suffix_011, ridgeSupport608_suffix_012, ridgeSupport608_suffix_013, ridgeSupport608_suffix_014, ridgeSupport608_suffix_015, ridgeSupport608_suffix_016, ridgeSupport608_suffix_017, ridgeSupport608_suffix_018, ridgeSupport608_suffix_019, ridgeSupport608_suffix_020, ridgeSupport608_suffix_021, ridgeSupport608_suffix_022, ridgeSupport608_suffix_023, List.all_append, List.all_nil, ridgeSupport608_000_checked, ridgeSupport608_001_checked, ridgeSupport608_002_checked, ridgeSupport608_003_checked, ridgeSupport608_004_checked, ridgeSupport608_005_checked, ridgeSupport608_006_checked, ridgeSupport608_007_checked, ridgeSupport608_008_checked, ridgeSupport608_009_checked, ridgeSupport608_010_checked, ridgeSupport608_011_checked, ridgeSupport608_012_checked, ridgeSupport608_013_checked, ridgeSupport608_014_checked, ridgeSupport608_015_checked, ridgeSupport608_016_checked, ridgeSupport608_017_checked, ridgeSupport608_018_checked, ridgeSupport608_019_checked, ridgeSupport608_020_checked, ridgeSupport608_021_checked, ridgeSupport608_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
