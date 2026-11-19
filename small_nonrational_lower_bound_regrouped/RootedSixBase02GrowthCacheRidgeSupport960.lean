module
prelude
public meta import LowerSchemas.FiniteRootedSixBase.Part0
public import RootedSixBase02GrowthCacheRidgeSupport960PartGrouped000
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 960 024 13
cert_ridgeSupport_suffix_decode_2 960 023 13 2 2 024 024 0
cert_ridgeSupport_suffix_decode_2 960 022 13 34 32 024 023 2
cert_ridgeSupport_suffix_decode_2 960 021 13 66 32 024 022 34
cert_ridgeSupport_suffix_decode_2 960 020 13 98 32 024 021 66
cert_ridgeSupport_suffix_decode_2 960 019 13 130 32 024 020 98
cert_ridgeSupport_suffix_decode_2 960 018 13 162 32 024 019 130
cert_ridgeSupport_suffix_decode_2 960 017 13 194 32 024 018 162
cert_ridgeSupport_suffix_decode_2 960 016 13 226 32 024 017 194
cert_ridgeSupport_suffix_decode_2 960 015 13 258 32 024 016 226
cert_ridgeSupport_suffix_decode_2 960 014 13 290 32 024 015 258
cert_ridgeSupport_suffix_decode_2 960 013 13 322 32 024 014 290
cert_ridgeSupport_suffix_decode_2 960 012 13 354 32 024 013 322
cert_ridgeSupport_suffix_decode_2 960 011 13 386 32 024 012 354
cert_ridgeSupport_suffix_decode_2 960 010 13 418 32 024 011 386
cert_ridgeSupport_suffix_decode_2 960 009 13 450 32 024 010 418
cert_ridgeSupport_suffix_decode_2 960 008 13 482 32 024 009 450
cert_ridgeSupport_suffix_decode_2 960 007 13 514 32 024 008 482
cert_ridgeSupport_suffix_decode_2 960 006 13 546 32 024 007 514
cert_ridgeSupport_suffix_decode_2 960 005 13 578 32 024 006 546
cert_ridgeSupport_suffix_decode_2 960 004 13 610 32 024 005 578
cert_ridgeSupport_suffix_decode_2 960 003 13 642 32 024 004 610
cert_ridgeSupport_suffix_decode_2 960 002 13 674 32 024 003 642
cert_ridgeSupport_suffix_decode_2 960 001 13 706 32 024 002 674
cert_ridgeSupport_suffix_decode_2 960 000 13 738 32 024 001 706
cert_ridgeSupport_eq 960
theorem ridgeTest_large_960 : ridgeTest 960 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, ridgeSupport960_suffix_010, ridgeSupport960_suffix_011, ridgeSupport960_suffix_012, ridgeSupport960_suffix_013, ridgeSupport960_suffix_014, ridgeSupport960_suffix_015, ridgeSupport960_suffix_016, ridgeSupport960_suffix_017, ridgeSupport960_suffix_018, ridgeSupport960_suffix_019, ridgeSupport960_suffix_020, ridgeSupport960_suffix_021, ridgeSupport960_suffix_022, ridgeSupport960_suffix_023, ridgeSupport960_suffix_024, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport960_000_mask, ridgeSupport960_001_mask, ridgeSupport960_002_mask, ridgeSupport960_003_mask, ridgeSupport960_004_mask, ridgeSupport960_005_mask, ridgeSupport960_006_mask, ridgeSupport960_007_mask, ridgeSupport960_008_mask, ridgeSupport960_009_mask, ridgeSupport960_010_mask, ridgeSupport960_011_mask, ridgeSupport960_012_mask, ridgeSupport960_013_mask, ridgeSupport960_014_mask, ridgeSupport960_015_mask, ridgeSupport960_016_mask, ridgeSupport960_017_mask, ridgeSupport960_018_mask, ridgeSupport960_019_mask, ridgeSupport960_020_mask, ridgeSupport960_021_mask, ridgeSupport960_022_mask, ridgeSupport960_023_mask]
    decide +kernel
  · rw [ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, ridgeSupport960_suffix_010, ridgeSupport960_suffix_011, ridgeSupport960_suffix_012, ridgeSupport960_suffix_013, ridgeSupport960_suffix_014, ridgeSupport960_suffix_015, ridgeSupport960_suffix_016, ridgeSupport960_suffix_017, ridgeSupport960_suffix_018, ridgeSupport960_suffix_019, ridgeSupport960_suffix_020, ridgeSupport960_suffix_021, ridgeSupport960_suffix_022, ridgeSupport960_suffix_023, ridgeSupport960_suffix_024, List.all_append, List.all_nil, ridgeSupport960_000_checked, ridgeSupport960_001_checked, ridgeSupport960_002_checked, ridgeSupport960_003_checked, ridgeSupport960_004_checked, ridgeSupport960_005_checked, ridgeSupport960_006_checked, ridgeSupport960_007_checked, ridgeSupport960_008_checked, ridgeSupport960_009_checked, ridgeSupport960_010_checked, ridgeSupport960_011_checked, ridgeSupport960_012_checked, ridgeSupport960_013_checked, ridgeSupport960_014_checked, ridgeSupport960_015_checked, ridgeSupport960_016_checked, ridgeSupport960_017_checked, ridgeSupport960_018_checked, ridgeSupport960_019_checked, ridgeSupport960_020_checked, ridgeSupport960_021_checked, ridgeSupport960_022_checked, ridgeSupport960_023_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase02
