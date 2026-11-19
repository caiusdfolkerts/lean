module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport592PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 592 023 14
cert_ridgeSupport_suffix_decode_2 592 022 14 15 15 023 023 0
cert_ridgeSupport_suffix_decode_2 592 021 14 47 32 023 022 15
cert_ridgeSupport_suffix_decode_2 592 020 14 79 32 023 021 47
cert_ridgeSupport_suffix_decode_2 592 019 14 111 32 023 020 79
cert_ridgeSupport_suffix_decode_2 592 018 14 143 32 023 019 111
cert_ridgeSupport_suffix_decode_2 592 017 14 175 32 023 018 143
cert_ridgeSupport_suffix_decode_2 592 016 14 207 32 023 017 175
cert_ridgeSupport_suffix_decode_2 592 015 14 239 32 023 016 207
cert_ridgeSupport_suffix_decode_2 592 014 14 271 32 023 015 239
cert_ridgeSupport_suffix_decode_2 592 013 14 303 32 023 014 271
cert_ridgeSupport_suffix_decode_2 592 012 14 335 32 023 013 303
cert_ridgeSupport_suffix_decode_2 592 011 14 367 32 023 012 335
cert_ridgeSupport_suffix_decode_2 592 010 14 399 32 023 011 367
cert_ridgeSupport_suffix_decode_2 592 009 14 431 32 023 010 399
cert_ridgeSupport_suffix_decode_2 592 008 14 463 32 023 009 431
cert_ridgeSupport_suffix_decode_2 592 007 14 495 32 023 008 463
cert_ridgeSupport_suffix_decode_2 592 006 14 527 32 023 007 495
cert_ridgeSupport_suffix_decode_2 592 005 14 559 32 023 006 527
cert_ridgeSupport_suffix_decode_2 592 004 14 591 32 023 005 559
cert_ridgeSupport_suffix_decode_2 592 003 14 623 32 023 004 591
cert_ridgeSupport_suffix_decode_2 592 002 14 655 32 023 003 623
cert_ridgeSupport_suffix_decode_2 592 001 14 687 32 023 002 655
cert_ridgeSupport_suffix_decode_2 592 000 14 719 32 023 001 687
cert_ridgeSupport_eq_3 592
theorem ridgeTest_large_592 : ridgeTest 592 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport592_eq]
    simp only [ridgeSupport592_suffix_000, ridgeSupport592_suffix_001, ridgeSupport592_suffix_002, ridgeSupport592_suffix_003, ridgeSupport592_suffix_004, ridgeSupport592_suffix_005, ridgeSupport592_suffix_006, ridgeSupport592_suffix_007, ridgeSupport592_suffix_008, ridgeSupport592_suffix_009, ridgeSupport592_suffix_010, ridgeSupport592_suffix_011, ridgeSupport592_suffix_012, ridgeSupport592_suffix_013, ridgeSupport592_suffix_014, ridgeSupport592_suffix_015, ridgeSupport592_suffix_016, ridgeSupport592_suffix_017, ridgeSupport592_suffix_018, ridgeSupport592_suffix_019, ridgeSupport592_suffix_020, ridgeSupport592_suffix_021, ridgeSupport592_suffix_022, ridgeSupport592_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport592_000_mask, ridgeSupport592_001_mask, ridgeSupport592_002_mask, ridgeSupport592_003_mask, ridgeSupport592_004_mask, ridgeSupport592_005_mask, ridgeSupport592_006_mask, ridgeSupport592_007_mask, ridgeSupport592_008_mask, ridgeSupport592_009_mask, ridgeSupport592_010_mask, ridgeSupport592_011_mask, ridgeSupport592_012_mask, ridgeSupport592_013_mask, ridgeSupport592_014_mask, ridgeSupport592_015_mask, ridgeSupport592_016_mask, ridgeSupport592_017_mask, ridgeSupport592_018_mask, ridgeSupport592_019_mask, ridgeSupport592_020_mask, ridgeSupport592_021_mask, ridgeSupport592_022_mask]
    decide +kernel
  · rw [ridgeSupport592_eq]
    simp only [ridgeSupport592_suffix_000, ridgeSupport592_suffix_001, ridgeSupport592_suffix_002, ridgeSupport592_suffix_003, ridgeSupport592_suffix_004, ridgeSupport592_suffix_005, ridgeSupport592_suffix_006, ridgeSupport592_suffix_007, ridgeSupport592_suffix_008, ridgeSupport592_suffix_009, ridgeSupport592_suffix_010, ridgeSupport592_suffix_011, ridgeSupport592_suffix_012, ridgeSupport592_suffix_013, ridgeSupport592_suffix_014, ridgeSupport592_suffix_015, ridgeSupport592_suffix_016, ridgeSupport592_suffix_017, ridgeSupport592_suffix_018, ridgeSupport592_suffix_019, ridgeSupport592_suffix_020, ridgeSupport592_suffix_021, ridgeSupport592_suffix_022, ridgeSupport592_suffix_023, List.all_append, List.all_nil, ridgeSupport592_000_checked, ridgeSupport592_001_checked, ridgeSupport592_002_checked, ridgeSupport592_003_checked, ridgeSupport592_004_checked, ridgeSupport592_005_checked, ridgeSupport592_006_checked, ridgeSupport592_007_checked, ridgeSupport592_008_checked, ridgeSupport592_009_checked, ridgeSupport592_010_checked, ridgeSupport592_011_checked, ridgeSupport592_012_checked, ridgeSupport592_013_checked, ridgeSupport592_014_checked, ridgeSupport592_015_checked, ridgeSupport592_016_checked, ridgeSupport592_017_checked, ridgeSupport592_018_checked, ridgeSupport592_019_checked, ridgeSupport592_020_checked, ridgeSupport592_021_checked, ridgeSupport592_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
