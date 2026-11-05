module
prelude
public import RootedSevenPure056GrowthCacheKindSupport3Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure056
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_000_decode :
    PackedRawNatGrowth.readList 9 32 kindSupport3_rest_000 =
      (kindSupport3_000, kindSupport3_rest_001) := by decide +kernel
theorem kindSupport3_000_mask : RawNatGrowthCheck.mask kindSupport3_000 = 0xffe00ff81f81f80 := by decide +kernel
theorem kindSupport3_000_checked :
    (kindSupport3_000.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_001_decode :
    PackedRawNatGrowth.readList 9 32 kindSupport3_rest_001 =
      (kindSupport3_001, kindSupport3_rest_002) := by decide +kernel
theorem kindSupport3_001_mask : RawNatGrowthCheck.mask kindSupport3_001 = 0x803ffc01f81f81f81000000000000000 := by decide +kernel
theorem kindSupport3_001_checked :
    (kindSupport3_001.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_002_decode :
    PackedRawNatGrowth.readList 9 32 kindSupport3_rest_002 =
      (kindSupport3_002, kindSupport3_rest_003) := by decide +kernel
theorem kindSupport3_002_mask : RawNatGrowthCheck.mask kindSupport3_002 = 0x7e07ff803fff00000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_002_checked :
    (kindSupport3_002.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_003_decode :
    PackedRawNatGrowth.readList 9 32 kindSupport3_rest_003 =
      (kindSupport3_003, kindSupport3_rest_004) := by decide +kernel
theorem kindSupport3_003_mask : RawNatGrowthCheck.mask kindSupport3_003 = 0x1fe00fff007e07e000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_003_checked :
    (kindSupport3_003.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_004_decode :
    PackedRawNatGrowth.readList 9 32 kindSupport3_rest_004 =
      (kindSupport3_004, kindSupport3_rest_005) := by decide +kernel
theorem kindSupport3_004_mask : RawNatGrowthCheck.mask kindSupport3_004 = 0xffc01f81f81f81e00000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_004_checked :
    (kindSupport3_004.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_005_decode :
    PackedRawNatGrowth.readList 9 32 kindSupport3_rest_005 =
      (kindSupport3_005, kindSupport3_rest_006) := by decide +kernel
theorem kindSupport3_005_mask : RawNatGrowthCheck.mask kindSupport3_005 = 0x7e07e07e07ff80300000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_005_checked :
    (kindSupport3_005.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_006_decode :
    PackedRawNatGrowth.readList 9 32 kindSupport3_rest_006 =
      (kindSupport3_006, kindSupport3_rest_007) := by decide +kernel
theorem kindSupport3_006_mask : RawNatGrowthCheck.mask kindSupport3_006 = 0x181f81ffe00fff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_006_checked :
    (kindSupport3_006.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_007_decode :
    PackedRawNatGrowth.readList 9 32 kindSupport3_rest_007 =
      (kindSupport3_007, kindSupport3_rest_008) := by decide +kernel
theorem kindSupport3_007_mask : RawNatGrowthCheck.mask kindSupport3_007 = 0x1ff803ffc01f81e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_007_checked :
    (kindSupport3_007.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenPure056
