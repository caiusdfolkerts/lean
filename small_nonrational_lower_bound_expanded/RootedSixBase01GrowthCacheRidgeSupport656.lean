module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase01GrowthCacheRidgeSupport656PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 656 023 14
cert_ridgeSupport_suffix_decode_2 656 022 14 15 15 023 023 0
cert_ridgeSupport_suffix_decode_2 656 021 14 47 32 023 022 15
cert_ridgeSupport_suffix_decode_2 656 020 14 79 32 023 021 47
cert_ridgeSupport_suffix_decode_2 656 019 14 111 32 023 020 79
cert_ridgeSupport_suffix_decode_2 656 018 14 143 32 023 019 111
cert_ridgeSupport_suffix_decode_2 656 017 14 175 32 023 018 143
cert_ridgeSupport_suffix_decode_2 656 016 14 207 32 023 017 175
cert_ridgeSupport_suffix_decode_2 656 015 14 239 32 023 016 207
cert_ridgeSupport_suffix_decode_2 656 014 14 271 32 023 015 239
cert_ridgeSupport_suffix_decode_2 656 013 14 303 32 023 014 271
cert_ridgeSupport_suffix_decode_2 656 012 14 335 32 023 013 303
cert_ridgeSupport_suffix_decode_2 656 011 14 367 32 023 012 335
cert_ridgeSupport_suffix_decode_2 656 010 14 399 32 023 011 367
cert_ridgeSupport_suffix_decode_2 656 009 14 431 32 023 010 399
cert_ridgeSupport_suffix_decode_2 656 008 14 463 32 023 009 431
cert_ridgeSupport_suffix_decode_2 656 007 14 495 32 023 008 463
cert_ridgeSupport_suffix_decode_2 656 006 14 527 32 023 007 495
cert_ridgeSupport_suffix_decode_2 656 005 14 559 32 023 006 527
cert_ridgeSupport_suffix_decode_2 656 004 14 591 32 023 005 559
cert_ridgeSupport_suffix_decode_2 656 003 14 623 32 023 004 591
cert_ridgeSupport_suffix_decode_2 656 002 14 655 32 023 003 623
cert_ridgeSupport_suffix_decode_2 656 001 14 687 32 023 002 655
cert_ridgeSupport_suffix_decode_2 656 000 14 719 32 023 001 687
cert_ridgeSupport_eq_3 656
theorem ridgeTest_large_656 : ridgeTest 656 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport656_eq]
    simp only [ridgeSupport656_suffix_000, ridgeSupport656_suffix_001, ridgeSupport656_suffix_002, ridgeSupport656_suffix_003, ridgeSupport656_suffix_004, ridgeSupport656_suffix_005, ridgeSupport656_suffix_006, ridgeSupport656_suffix_007, ridgeSupport656_suffix_008, ridgeSupport656_suffix_009, ridgeSupport656_suffix_010, ridgeSupport656_suffix_011, ridgeSupport656_suffix_012, ridgeSupport656_suffix_013, ridgeSupport656_suffix_014, ridgeSupport656_suffix_015, ridgeSupport656_suffix_016, ridgeSupport656_suffix_017, ridgeSupport656_suffix_018, ridgeSupport656_suffix_019, ridgeSupport656_suffix_020, ridgeSupport656_suffix_021, ridgeSupport656_suffix_022, ridgeSupport656_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport656_000_mask, ridgeSupport656_001_mask, ridgeSupport656_002_mask, ridgeSupport656_003_mask, ridgeSupport656_004_mask, ridgeSupport656_005_mask, ridgeSupport656_006_mask, ridgeSupport656_007_mask, ridgeSupport656_008_mask, ridgeSupport656_009_mask, ridgeSupport656_010_mask, ridgeSupport656_011_mask, ridgeSupport656_012_mask, ridgeSupport656_013_mask, ridgeSupport656_014_mask, ridgeSupport656_015_mask, ridgeSupport656_016_mask, ridgeSupport656_017_mask, ridgeSupport656_018_mask, ridgeSupport656_019_mask, ridgeSupport656_020_mask, ridgeSupport656_021_mask, ridgeSupport656_022_mask]
    decide +kernel
  · rw [ridgeSupport656_eq]
    simp only [ridgeSupport656_suffix_000, ridgeSupport656_suffix_001, ridgeSupport656_suffix_002, ridgeSupport656_suffix_003, ridgeSupport656_suffix_004, ridgeSupport656_suffix_005, ridgeSupport656_suffix_006, ridgeSupport656_suffix_007, ridgeSupport656_suffix_008, ridgeSupport656_suffix_009, ridgeSupport656_suffix_010, ridgeSupport656_suffix_011, ridgeSupport656_suffix_012, ridgeSupport656_suffix_013, ridgeSupport656_suffix_014, ridgeSupport656_suffix_015, ridgeSupport656_suffix_016, ridgeSupport656_suffix_017, ridgeSupport656_suffix_018, ridgeSupport656_suffix_019, ridgeSupport656_suffix_020, ridgeSupport656_suffix_021, ridgeSupport656_suffix_022, ridgeSupport656_suffix_023, List.all_append, List.all_nil, ridgeSupport656_000_checked, ridgeSupport656_001_checked, ridgeSupport656_002_checked, ridgeSupport656_003_checked, ridgeSupport656_004_checked, ridgeSupport656_005_checked, ridgeSupport656_006_checked, ridgeSupport656_007_checked, ridgeSupport656_008_checked, ridgeSupport656_009_checked, ridgeSupport656_010_checked, ridgeSupport656_011_checked, ridgeSupport656_012_checked, ridgeSupport656_013_checked, ridgeSupport656_014_checked, ridgeSupport656_015_checked, ridgeSupport656_016_checked, ridgeSupport656_017_checked, ridgeSupport656_018_checked, ridgeSupport656_019_checked, ridgeSupport656_020_checked, ridgeSupport656_021_checked, ridgeSupport656_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
