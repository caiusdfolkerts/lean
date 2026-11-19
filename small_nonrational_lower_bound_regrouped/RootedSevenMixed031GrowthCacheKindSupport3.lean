module
prelude
public meta import LowerSchemas.FiniteRootedSevenMixed
public import RootedSevenMixed031GrowthCacheKindSupport3Part000
public import RootedSevenMixed031GrowthCacheKindSupport3Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenMixed031
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_suffix_decode_009 : PackedRawNatGrowth.readList 10 0 kindSupport3_rest_009 =
    (kindSupport3_suffix_009, kindSupport3_rest_009) := by rfl
cert_kindSupport_suffix_decode 008 26 26 009 0
cert_kindSupport_suffix_decode 007 58 32 008 26
cert_kindSupport_suffix_decode 006 90 32 007 58
cert_kindSupport_suffix_decode 005 122 32 006 90
cert_kindSupport_suffix_decode 004 154 32 005 122
cert_kindSupport_suffix_decode 003 186 32 004 154
cert_kindSupport_suffix_decode 002 218 32 003 186
cert_kindSupport_suffix_decode 001 250 32 002 218
cert_kindSupport_suffix_decode 000 282 32 001 250
theorem kindSupport3_eq : kindRows 3 = kindSupport3_suffix_000 := by
  rw [kindSupport3_source]
  exact congrArg Prod.fst kindSupport3_suffix_decode_000
theorem kindTest_large_3 : kindTest 3 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, kindSupport3_000_mask, kindSupport3_001_mask, kindSupport3_002_mask, kindSupport3_003_mask, kindSupport3_004_mask, kindSupport3_005_mask, kindSupport3_006_mask, kindSupport3_007_mask, kindSupport3_008_mask]
    decide +kernel
  · rw [kindSupport3_eq]
    simp only [kindSupport3_suffix_000, kindSupport3_suffix_001, kindSupport3_suffix_002, kindSupport3_suffix_003, kindSupport3_suffix_004, kindSupport3_suffix_005, kindSupport3_suffix_006, kindSupport3_suffix_007, kindSupport3_suffix_008, kindSupport3_suffix_009, List.all_append, List.all_nil, kindSupport3_000_checked, kindSupport3_001_checked, kindSupport3_002_checked, kindSupport3_003_checked, kindSupport3_004_checked, kindSupport3_005_checked, kindSupport3_006_checked, kindSupport3_007_checked, kindSupport3_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSevenMixed031
