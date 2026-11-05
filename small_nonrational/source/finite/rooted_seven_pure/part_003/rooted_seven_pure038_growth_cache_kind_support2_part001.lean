module
prelude
public import RootedSevenPure038GrowthCacheKindSupport2Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure038
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_008_decode :
    PackedRawNatGrowth.readList 10 14 kindSupport2_rest_008 =
      (kindSupport2_008, kindSupport2_rest_009) := by decide +kernel
theorem kindSupport2_008_mask : RawNatGrowthCheck.mask kindSupport2_008 = 0x3fe001f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_008_checked :
    (kindSupport2_008.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenPure038
