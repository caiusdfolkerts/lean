module
prelude
public import RootedSixExtra02GrowthCacheKindSupport2Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra02
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_016_decode :
    PackedRawNatGrowth.readList 13 32 kindSupport2_rest_016 =
      (kindSupport2_016, kindSupport2_rest_017) := by decide +kernel
theorem kindSupport2_016_mask : RawNatGrowthCheck.mask kindSupport2_016 = 0x3fe001ff000ff8007c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_016_checked :
    (kindSupport2_016.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_017_decode :
    PackedRawNatGrowth.readList 13 20 kindSupport2_rest_017 =
      (kindSupport2_017, kindSupport2_rest_018) := by decide +kernel
theorem kindSupport2_017_mask : RawNatGrowthCheck.mask kindSupport2_017 = 0x1ff8000ffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_017_checked :
    (kindSupport2_017.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra02
