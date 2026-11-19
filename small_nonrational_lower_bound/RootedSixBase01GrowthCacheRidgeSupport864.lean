module
prelude
public meta import LowerSchemas.FiniteRootedSixBase
public import RootedSixBase01GrowthCacheRidgeSupport864Part000
public import RootedSixBase01GrowthCacheRidgeSupport864Part001
public import RawMaskAppend

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
cert_ridgeSupport_suffix_decode 864 009 14
cert_ridgeSupport_suffix_decode_2 864 008 14 5 5 009 009 0
cert_ridgeSupport_suffix_decode_2 864 007 14 37 32 009 008 5
cert_ridgeSupport_suffix_decode_2 864 006 14 69 32 009 007 37
cert_ridgeSupport_suffix_decode_2 864 005 14 101 32 009 006 69
cert_ridgeSupport_suffix_decode_2 864 004 14 133 32 009 005 101
cert_ridgeSupport_suffix_decode_2 864 003 14 165 32 009 004 133
cert_ridgeSupport_suffix_decode_2 864 002 14 197 32 009 003 165
cert_ridgeSupport_suffix_decode_2 864 001 14 229 32 009 002 197
cert_ridgeSupport_suffix_decode_2 864 000 14 261 32 009 001 229
cert_ridgeSupport_eq_3 864
theorem ridgeTest_large_864 : ridgeTest 864 = true := by
  apply Bool.and_eq_true_iff.mpr
  constructor
  · apply decide_eq_true
    rw [ridgeSupport864_eq]
    simp only [ridgeSupport864_suffix_000, ridgeSupport864_suffix_001, ridgeSupport864_suffix_002, ridgeSupport864_suffix_003, ridgeSupport864_suffix_004, ridgeSupport864_suffix_005, ridgeSupport864_suffix_006, ridgeSupport864_suffix_007, ridgeSupport864_suffix_008, ridgeSupport864_suffix_009, RawMaskAppend.mask_append, RawMaskAppend.mask_nil, ridgeSupport864_000_mask, ridgeSupport864_001_mask, ridgeSupport864_002_mask, ridgeSupport864_003_mask, ridgeSupport864_004_mask, ridgeSupport864_005_mask, ridgeSupport864_006_mask, ridgeSupport864_007_mask, ridgeSupport864_008_mask]
    decide +kernel
  · rw [ridgeSupport864_eq]
    simp only [ridgeSupport864_suffix_000, ridgeSupport864_suffix_001, ridgeSupport864_suffix_002, ridgeSupport864_suffix_003, ridgeSupport864_suffix_004, ridgeSupport864_suffix_005, ridgeSupport864_suffix_006, ridgeSupport864_suffix_007, ridgeSupport864_suffix_008, ridgeSupport864_suffix_009, List.all_append, List.all_nil, ridgeSupport864_000_checked, ridgeSupport864_001_checked, ridgeSupport864_002_checked, ridgeSupport864_003_checked, ridgeSupport864_004_checked, ridgeSupport864_005_checked, ridgeSupport864_006_checked, ridgeSupport864_007_checked, ridgeSupport864_008_checked, Bool.and_self]

end Papers.RationalityTen.RootedCaches.RootedSixBase01
