module
prelude
public import RootedSevenPure008GrowthCacheKindSupport2Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure008
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_008_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport2_rest_008 =
      (kindSupport2_008, kindSupport2_rest_009) := by decide +kernel
theorem kindSupport2_008_mask : RawNatGrowthCheck.mask kindSupport2_008 = 0x7fc0fc0fc0fc003e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_008_checked :
    (kindSupport2_008.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_009_decode :
    PackedRawNatGrowth.readList 10 27 kindSupport2_rest_009 =
      (kindSupport2_009, kindSupport2_rest_010) := by decide +kernel
theorem kindSupport2_009_mask : RawNatGrowthCheck.mask kindSupport2_009 = 0x3fe001ff000ff800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_009_checked :
    (kindSupport2_009.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenPure008
