module
prelude
public import RootedSixExtra05GrowthCacheKindSupport3Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_016_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_016 =
      (kindSupport3_016, kindSupport3_rest_017) := by decide +kernel
theorem kindSupport3_016_mask : RawNatGrowthCheck.mask kindSupport3_016 = 0x3c01ffe00fffe0040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_016_checked :
    (kindSupport3_016.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_017_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_017 =
      (kindSupport3_017, kindSupport3_rest_018) := by decide +kernel
theorem kindSupport3_017_mask : RawNatGrowthCheck.mask kindSupport3_017 = 0xfff007ff803fc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_017_checked :
    (kindSupport3_017.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_018_decode :
    PackedRawNatGrowth.readList 12 30 kindSupport3_rest_018 =
      (kindSupport3_018, kindSupport3_rest_019) := by decide +kernel
theorem kindSupport3_018_mask : RawNatGrowthCheck.mask kindSupport3_018 = 0x3fff801fffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_018_checked :
    (kindSupport3_018.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
