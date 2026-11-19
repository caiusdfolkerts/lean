module
prelude
public meta import LowerSchemas.FiniteRootedSixExtra
public import RootedSixExtra02GrowthCacheRidgeSupport960Part000
public import RootedSixExtra02GrowthCacheRidgeSupport960Part001
public import RootedSixExtra02GrowthCacheRidgeSupport960Part002
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode_3 960 020 13
cert_ridgeSupport_suffix_decode_4 960 019 13 10 10 020 020 0
cert_ridgeSupport_suffix_decode_4 960 018 13 42 32 020 019 10
cert_ridgeSupport_suffix_decode_4 960 017 13 74 32 020 018 42
cert_ridgeSupport_suffix_decode_4 960 016 13 106 32 020 017 74
cert_ridgeSupport_suffix_decode_4 960 015 13 138 32 020 016 106
cert_ridgeSupport_suffix_decode_4 960 014 13 170 32 020 015 138
cert_ridgeSupport_suffix_decode_4 960 013 13 202 32 020 014 170
cert_ridgeSupport_suffix_decode_4 960 012 13 234 32 020 013 202
cert_ridgeSupport_suffix_decode_4 960 011 13 266 32 020 012 234
cert_ridgeSupport_suffix_decode_4 960 010 13 298 32 020 011 266
cert_ridgeSupport_suffix_decode_4 960 009 13 330 32 020 010 298
cert_ridgeSupport_suffix_decode_4 960 008 13 362 32 020 009 330
cert_ridgeSupport_suffix_decode_4 960 007 13 394 32 020 008 362
cert_ridgeSupport_suffix_decode_4 960 006 13 426 32 020 007 394
cert_ridgeSupport_suffix_decode_4 960 005 13 458 32 020 006 426
cert_ridgeSupport_suffix_decode_4 960 004 13 490 32 020 005 458
cert_ridgeSupport_suffix_decode_4 960 003 13 522 32 020 004 490
cert_ridgeSupport_suffix_decode_4 960 002 13 554 32 020 003 522
cert_ridgeSupport_suffix_decode_4 960 001 13 586 32 020 002 554
cert_ridgeSupport_suffix_decode_4 960 000 13 618 32 020 001 586
cert_ridgeSupport_eq_4 960
theorem ridgeTest_large_960 : ridgeTest 960 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, ridgeSupport960_suffix_010, ridgeSupport960_suffix_011, ridgeSupport960_suffix_012, ridgeSupport960_suffix_013, ridgeSupport960_suffix_014, ridgeSupport960_suffix_015, ridgeSupport960_suffix_016, ridgeSupport960_suffix_017, ridgeSupport960_suffix_018, ridgeSupport960_suffix_019, ridgeSupport960_suffix_020, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport960_000_mask, ridgeSupport960_001_mask, ridgeSupport960_002_mask, ridgeSupport960_003_mask, ridgeSupport960_004_mask, ridgeSupport960_005_mask, ridgeSupport960_006_mask, ridgeSupport960_007_mask, ridgeSupport960_008_mask, ridgeSupport960_009_mask, ridgeSupport960_010_mask, ridgeSupport960_011_mask, ridgeSupport960_012_mask, ridgeSupport960_013_mask, ridgeSupport960_014_mask, ridgeSupport960_015_mask, ridgeSupport960_016_mask, ridgeSupport960_017_mask, ridgeSupport960_018_mask, ridgeSupport960_019_mask]
    decide +kernel
  · rw [ridgeSupport960_eq]
    simp only [ridgeSupport960_suffix_000, ridgeSupport960_suffix_001, ridgeSupport960_suffix_002, ridgeSupport960_suffix_003, ridgeSupport960_suffix_004, ridgeSupport960_suffix_005, ridgeSupport960_suffix_006, ridgeSupport960_suffix_007, ridgeSupport960_suffix_008, ridgeSupport960_suffix_009, ridgeSupport960_suffix_010, ridgeSupport960_suffix_011, ridgeSupport960_suffix_012, ridgeSupport960_suffix_013, ridgeSupport960_suffix_014, ridgeSupport960_suffix_015, ridgeSupport960_suffix_016, ridgeSupport960_suffix_017, ridgeSupport960_suffix_018, ridgeSupport960_suffix_019, ridgeSupport960_suffix_020, List.all_append, List.all_nil, ridgeSupport960_000_checked, ridgeSupport960_001_checked, ridgeSupport960_002_checked, ridgeSupport960_003_checked, ridgeSupport960_004_checked, ridgeSupport960_005_checked, ridgeSupport960_006_checked, ridgeSupport960_007_checked, ridgeSupport960_008_checked, ridgeSupport960_009_checked, ridgeSupport960_010_checked, ridgeSupport960_011_checked, ridgeSupport960_012_checked, ridgeSupport960_013_checked, ridgeSupport960_014_checked, ridgeSupport960_015_checked, ridgeSupport960_016_checked, ridgeSupport960_017_checked, ridgeSupport960_018_checked, ridgeSupport960_019_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
