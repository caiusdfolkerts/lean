module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase02GrowthCacheKindSupport3Part000
public import RootedSixBase02GrowthCacheKindSupport3Part001
public import RootedSixBase02GrowthCacheKindSupport3Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_5 3 023 13
cert_kindSupport_suffix_decode_4 3 022 13 18 18 023 023 0
cert_kindSupport_suffix_decode_4 3 021 13 50 32 023 022 18
cert_kindSupport_suffix_decode_4 3 020 13 82 32 023 021 50
cert_kindSupport_suffix_decode_4 3 019 13 114 32 023 020 82
cert_kindSupport_suffix_decode_4 3 018 13 146 32 023 019 114
cert_kindSupport_suffix_decode_4 3 017 13 178 32 023 018 146
cert_kindSupport_suffix_decode_4 3 016 13 210 32 023 017 178
cert_kindSupport_suffix_decode_4 3 015 13 242 32 023 016 210
cert_kindSupport_suffix_decode_4 3 014 13 274 32 023 015 242
cert_kindSupport_suffix_decode_4 3 013 13 306 32 023 014 274
cert_kindSupport_suffix_decode_4 3 012 13 338 32 023 013 306
cert_kindSupport_suffix_decode_4 3 011 13 370 32 023 012 338
cert_kindSupport_suffix_decode_4 3 010 13 402 32 023 011 370
cert_kindSupport_suffix_decode_4 3 009 13 434 32 023 010 402
cert_kindSupport_suffix_decode_4 3 008 13 466 32 023 009 434
cert_kindSupport_suffix_decode_4 3 007 13 498 32 023 008 466
cert_kindSupport_suffix_decode_4 3 006 13 530 32 023 007 498
cert_kindSupport_suffix_decode_4 3 005 13 562 32 023 006 530
cert_kindSupport_suffix_decode_4 3 004 13 594 32 023 005 562
cert_kindSupport_suffix_decode_4 3 003 13 626 32 023 004 594
cert_kindSupport_suffix_decode_4 3 002 13 658 32 023 003 626
cert_kindSupport_suffix_decode_4 3 001 13 690 32 023 002 658
cert_kindSupport_suffix_decode_4 3 000 13 722 32 023 001 690
theorem kindSupport3_eq : kindRows 3 = kindSupport3_suffix_000 := by
  change kindSupports 3 = kindSupport3_suffix_000
  rw [kindSupport3_source]
  exact congrArg Prod.fst kindSupport3_suffix_decode_000
theorem kindTest_large_3 : kindTest 3 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, kindSupport3_suffix_020, kindSupport3_suffix_021, kindSupport3_suffix_022, kindSupport3_suffix_023, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport3_000_mask, kindSupport3_001_mask, kindSupport3_002_mask, kindSupport3_003_mask, kindSupport3_004_mask, kindSupport3_005_mask, kindSupport3_006_mask, kindSupport3_007_mask, kindSupport3_008_mask, kindSupport3_009_mask, kindSupport3_010_mask, kindSupport3_011_mask, kindSupport3_012_mask, kindSupport3_013_mask, kindSupport3_014_mask, kindSupport3_015_mask, kindSupport3_016_mask, kindSupport3_017_mask, kindSupport3_018_mask, kindSupport3_019_mask, kindSupport3_020_mask, kindSupport3_021_mask, kindSupport3_022_mask]
    decide +kernel
  · rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, kindSupport3_suffix_020, kindSupport3_suffix_021, kindSupport3_suffix_022, kindSupport3_suffix_023, List.all_append, List.all_nil, kindSupport3_000_checked, kindSupport3_001_checked, kindSupport3_002_checked, kindSupport3_003_checked, kindSupport3_004_checked, kindSupport3_005_checked, kindSupport3_006_checked, kindSupport3_007_checked, kindSupport3_008_checked, kindSupport3_009_checked, kindSupport3_010_checked, kindSupport3_011_checked, kindSupport3_012_checked, kindSupport3_013_checked, kindSupport3_014_checked, kindSupport3_015_checked, kindSupport3_016_checked, kindSupport3_017_checked, kindSupport3_018_checked, kindSupport3_019_checked, kindSupport3_020_checked, kindSupport3_021_checked, kindSupport3_022_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
