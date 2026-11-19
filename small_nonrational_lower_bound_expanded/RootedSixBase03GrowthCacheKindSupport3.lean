module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase03GrowthCacheKindSupport3PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_kindSupport_suffix_decode_5 3 027 13
cert_kindSupport_suffix_decode_4 3 026 13 6 6 027 027 0
cert_kindSupport_suffix_decode_4 3 025 13 38 32 027 026 6
cert_kindSupport_suffix_decode_4 3 024 13 70 32 027 025 38
cert_kindSupport_suffix_decode_4 3 023 13 102 32 027 024 70
cert_kindSupport_suffix_decode_4 3 022 13 134 32 027 023 102
cert_kindSupport_suffix_decode_4 3 021 13 166 32 027 022 134
cert_kindSupport_suffix_decode_4 3 020 13 198 32 027 021 166
cert_kindSupport_suffix_decode_4 3 019 13 230 32 027 020 198
cert_kindSupport_suffix_decode_4 3 018 13 262 32 027 019 230
cert_kindSupport_suffix_decode_4 3 017 13 294 32 027 018 262
cert_kindSupport_suffix_decode_4 3 016 13 326 32 027 017 294
cert_kindSupport_suffix_decode_4 3 015 13 358 32 027 016 326
cert_kindSupport_suffix_decode_4 3 014 13 390 32 027 015 358
cert_kindSupport_suffix_decode_4 3 013 13 422 32 027 014 390
cert_kindSupport_suffix_decode_4 3 012 13 454 32 027 013 422
cert_kindSupport_suffix_decode_4 3 011 13 486 32 027 012 454
cert_kindSupport_suffix_decode_4 3 010 13 518 32 027 011 486
cert_kindSupport_suffix_decode_4 3 009 13 550 32 027 010 518
cert_kindSupport_suffix_decode_4 3 008 13 582 32 027 009 550
cert_kindSupport_suffix_decode_4 3 007 13 614 32 027 008 582
cert_kindSupport_suffix_decode_4 3 006 13 646 32 027 007 614
cert_kindSupport_suffix_decode_4 3 005 13 678 32 027 006 646
cert_kindSupport_suffix_decode_4 3 004 13 710 32 027 005 678
cert_kindSupport_suffix_decode_4 3 003 13 742 32 027 004 710
cert_kindSupport_suffix_decode_4 3 002 13 774 32 027 003 742
cert_kindSupport_suffix_decode_4 3 001 13 806 32 027 002 774
cert_kindSupport_suffix_decode_4 3 000 13 838 32 027 001 806
theorem kindSupport3_eq : kindSupports 3 = kindSupport3_suffix_000 := by
  rw [kindSupport3_source]
  exact congrArg Prod.fst kindSupport3_suffix_decode_000
theorem kindTest_large_3 : kindTest 3 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [show kindRows 3 = kindSupport3_suffix_000 from kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, kindSupport3_suffix_020, kindSupport3_suffix_021, kindSupport3_suffix_022, kindSupport3_suffix_023, kindSupport3_suffix_024, kindSupport3_suffix_025, kindSupport3_suffix_026, kindSupport3_suffix_027, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport3_000_mask, kindSupport3_001_mask, kindSupport3_002_mask, kindSupport3_003_mask, kindSupport3_004_mask, kindSupport3_005_mask, kindSupport3_006_mask, kindSupport3_007_mask, kindSupport3_008_mask, kindSupport3_009_mask, kindSupport3_010_mask, kindSupport3_011_mask, kindSupport3_012_mask, kindSupport3_013_mask, kindSupport3_014_mask, kindSupport3_015_mask, kindSupport3_016_mask, kindSupport3_017_mask, kindSupport3_018_mask, kindSupport3_019_mask, kindSupport3_020_mask, kindSupport3_021_mask, kindSupport3_022_mask, kindSupport3_023_mask, kindSupport3_024_mask, kindSupport3_025_mask, kindSupport3_026_mask]
    decide +kernel
  · rw [show kindRows 3 = kindSupport3_suffix_000 from kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, kindSupport3_suffix_010, kindSupport3_suffix_011, kindSupport3_suffix_012, kindSupport3_suffix_013, kindSupport3_suffix_014, kindSupport3_suffix_015, kindSupport3_suffix_016, kindSupport3_suffix_017, kindSupport3_suffix_018, kindSupport3_suffix_019, kindSupport3_suffix_020, kindSupport3_suffix_021, kindSupport3_suffix_022, kindSupport3_suffix_023, kindSupport3_suffix_024, kindSupport3_suffix_025, kindSupport3_suffix_026, kindSupport3_suffix_027, List.all_append, List.all_nil, kindSupport3_000_checked, kindSupport3_001_checked, kindSupport3_002_checked, kindSupport3_003_checked, kindSupport3_004_checked, kindSupport3_005_checked, kindSupport3_006_checked, kindSupport3_007_checked, kindSupport3_008_checked, kindSupport3_009_checked, kindSupport3_010_checked, kindSupport3_011_checked, kindSupport3_012_checked, kindSupport3_013_checked, kindSupport3_014_checked, kindSupport3_015_checked, kindSupport3_016_checked, kindSupport3_017_checked, kindSupport3_018_checked, kindSupport3_019_checked, kindSupport3_020_checked, kindSupport3_021_checked, kindSupport3_022_checked, kindSupport3_023_checked, kindSupport3_024_checked, kindSupport3_025_checked, kindSupport3_026_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase03
