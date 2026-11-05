module
prelude
public import RootedSevenPure039GrowthCacheKindSupport3Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure039
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_008_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport3_rest_008 =
      (kindSupport3_008, kindSupport3_rest_009) := by decide +kernel
theorem kindSupport3_008_mask : RawNatGrowthCheck.mask kindSupport3_008 = 0x3fe00fc0fc0fc0f8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_008_checked :
    (kindSupport3_008.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_009_decode :
    PackedRawNatGrowth.readList 10 27 kindSupport3_rest_009 =
      (kindSupport3_009, kindSupport3_rest_010) := by decide +kernel
theorem kindSupport3_009_mask : RawNatGrowthCheck.mask kindSupport3_009 = 0x7ff803ffc01c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_009_checked :
    (kindSupport3_009.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenPure039
