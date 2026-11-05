module
prelude
public import RootedSixExtra06GrowthCacheKindSupport2Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra06
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_016_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_016 =
      (kindSupport2_016, kindSupport2_rest_017) := by decide +kernel
theorem kindSupport2_016_mask : RawNatGrowthCheck.mask kindSupport2_016 = 0x7fe001ff000ff80078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_016_checked :
    (kindSupport2_016.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_017_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_017 =
      (kindSupport2_017, kindSupport2_rest_018) := by decide +kernel
theorem kindSupport2_017_mask : RawNatGrowthCheck.mask kindSupport2_017 = 0x3e001ff000ff8007fc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_017_checked :
    (kindSupport2_017.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_018_decode :
    PackedRawNatGrowth.readList 12 24 kindSupport2_rest_018 =
      (kindSupport2_018, kindSupport2_rest_019) := by decide +kernel
theorem kindSupport2_018_mask : RawNatGrowthCheck.mask kindSupport2_018 = 0x1ff8000ffc003c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_018_checked :
    (kindSupport2_018.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra06
