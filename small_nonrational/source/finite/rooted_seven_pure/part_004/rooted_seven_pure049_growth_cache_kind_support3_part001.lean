module
prelude
public import RootedSevenPure049GrowthCacheKindSupport3Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure049
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_008_decode :
    PackedRawNatGrowth.readList 9 14 kindSupport3_rest_008 =
      (kindSupport3_008, kindSupport3_rest_009) := by decide +kernel
theorem kindSupport3_008_mask : RawNatGrowthCheck.mask kindSupport3_008 = 0xfff0060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_008_checked :
    (kindSupport3_008.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenPure049
