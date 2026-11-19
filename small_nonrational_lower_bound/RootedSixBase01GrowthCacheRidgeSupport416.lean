module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase01GrowthCacheRidgeSupport416Part000
public import RootedSixBase01GrowthCacheRidgeSupport416Part001
public import RootedSixBase01GrowthCacheRidgeSupport416Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 416 023 14
cert_ridgeSupport_suffix_decode_2 416 022 14 15 15 023 023 0
cert_ridgeSupport_suffix_decode_2 416 021 14 47 32 023 022 15
cert_ridgeSupport_suffix_decode_2 416 020 14 79 32 023 021 47
cert_ridgeSupport_suffix_decode_2 416 019 14 111 32 023 020 79
cert_ridgeSupport_suffix_decode_2 416 018 14 143 32 023 019 111
cert_ridgeSupport_suffix_decode_2 416 017 14 175 32 023 018 143
cert_ridgeSupport_suffix_decode_2 416 016 14 207 32 023 017 175
cert_ridgeSupport_suffix_decode_2 416 015 14 239 32 023 016 207
cert_ridgeSupport_suffix_decode_2 416 014 14 271 32 023 015 239
cert_ridgeSupport_suffix_decode_2 416 013 14 303 32 023 014 271
cert_ridgeSupport_suffix_decode_2 416 012 14 335 32 023 013 303
cert_ridgeSupport_suffix_decode_2 416 011 14 367 32 023 012 335
cert_ridgeSupport_suffix_decode_2 416 010 14 399 32 023 011 367
cert_ridgeSupport_suffix_decode_2 416 009 14 431 32 023 010 399
cert_ridgeSupport_suffix_decode_2 416 008 14 463 32 023 009 431
cert_ridgeSupport_suffix_decode_2 416 007 14 495 32 023 008 463
cert_ridgeSupport_suffix_decode_2 416 006 14 527 32 023 007 495
cert_ridgeSupport_suffix_decode_2 416 005 14 559 32 023 006 527
cert_ridgeSupport_suffix_decode_2 416 004 14 591 32 023 005 559
cert_ridgeSupport_suffix_decode_2 416 003 14 623 32 023 004 591
cert_ridgeSupport_suffix_decode_2 416 002 14 655 32 023 003 623
cert_ridgeSupport_suffix_decode_2 416 001 14 687 32 023 002 655
cert_ridgeSupport_suffix_decode_2 416 000 14 719 32 023 001 687
cert_ridgeSupport_eq_3 416
theorem ridgeTest_large_416 : ridgeTest 416 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport416_eq]
    simp only [ridgeSupport416_suffix_000, ridgeSupport416_suffix_001, ridgeSupport416_suffix_002, ridgeSupport416_suffix_003, ridgeSupport416_suffix_004, ridgeSupport416_suffix_005, ridgeSupport416_suffix_006, ridgeSupport416_suffix_007, ridgeSupport416_suffix_008, ridgeSupport416_suffix_009, ridgeSupport416_suffix_010, ridgeSupport416_suffix_011, ridgeSupport416_suffix_012, ridgeSupport416_suffix_013, ridgeSupport416_suffix_014, ridgeSupport416_suffix_015, ridgeSupport416_suffix_016, ridgeSupport416_suffix_017, ridgeSupport416_suffix_018, ridgeSupport416_suffix_019, ridgeSupport416_suffix_020, ridgeSupport416_suffix_021, ridgeSupport416_suffix_022, ridgeSupport416_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport416_000_mask, ridgeSupport416_001_mask, ridgeSupport416_002_mask, ridgeSupport416_003_mask, ridgeSupport416_004_mask, ridgeSupport416_005_mask, ridgeSupport416_006_mask, ridgeSupport416_007_mask, ridgeSupport416_008_mask, ridgeSupport416_009_mask, ridgeSupport416_010_mask, ridgeSupport416_011_mask, ridgeSupport416_012_mask, ridgeSupport416_013_mask, ridgeSupport416_014_mask, ridgeSupport416_015_mask, ridgeSupport416_016_mask, ridgeSupport416_017_mask, ridgeSupport416_018_mask, ridgeSupport416_019_mask, ridgeSupport416_020_mask, ridgeSupport416_021_mask, ridgeSupport416_022_mask]
    decide +kernel
  · rw [ridgeSupport416_eq]
    simp only [ridgeSupport416_suffix_000, ridgeSupport416_suffix_001, ridgeSupport416_suffix_002, ridgeSupport416_suffix_003, ridgeSupport416_suffix_004, ridgeSupport416_suffix_005, ridgeSupport416_suffix_006, ridgeSupport416_suffix_007, ridgeSupport416_suffix_008, ridgeSupport416_suffix_009, ridgeSupport416_suffix_010, ridgeSupport416_suffix_011, ridgeSupport416_suffix_012, ridgeSupport416_suffix_013, ridgeSupport416_suffix_014, ridgeSupport416_suffix_015, ridgeSupport416_suffix_016, ridgeSupport416_suffix_017, ridgeSupport416_suffix_018, ridgeSupport416_suffix_019, ridgeSupport416_suffix_020, ridgeSupport416_suffix_021, ridgeSupport416_suffix_022, ridgeSupport416_suffix_023, List.all_append, List.all_nil, ridgeSupport416_000_checked, ridgeSupport416_001_checked, ridgeSupport416_002_checked, ridgeSupport416_003_checked, ridgeSupport416_004_checked, ridgeSupport416_005_checked, ridgeSupport416_006_checked, ridgeSupport416_007_checked, ridgeSupport416_008_checked, ridgeSupport416_009_checked, ridgeSupport416_010_checked, ridgeSupport416_011_checked, ridgeSupport416_012_checked, ridgeSupport416_013_checked, ridgeSupport416_014_checked, ridgeSupport416_015_checked, ridgeSupport416_016_checked, ridgeSupport416_017_checked, ridgeSupport416_018_checked, ridgeSupport416_019_checked, ridgeSupport416_020_checked, ridgeSupport416_021_checked, ridgeSupport416_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
