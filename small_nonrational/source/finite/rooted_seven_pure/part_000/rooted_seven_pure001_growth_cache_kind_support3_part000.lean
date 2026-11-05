module
prelude
public import RootedSevenPure001GrowthCacheKindSupport3Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure001
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_000_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport3_rest_000 =
      (kindSupport3_000, kindSupport3_rest_001) := by decide +kernel
theorem kindSupport3_000_mask : RawNatGrowthCheck.mask kindSupport3_000 = 0x607e07e07e07e07e0000000000000000000000 := by decide +kernel
theorem kindSupport3_000_checked :
    (kindSupport3_000.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_001_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport3_rest_001 =
      (kindSupport3_001, kindSupport3_rest_002) := by decide +kernel
theorem kindSupport3_001_mask : RawNatGrowthCheck.mask kindSupport3_001 = 0x3c0fc0fc0fff00780000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_001_checked :
    (kindSupport3_001.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_002_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport3_rest_002 =
      (kindSupport3_002, kindSupport3_rest_003) := by decide +kernel
theorem kindSupport3_002_mask : RawNatGrowthCheck.mask kindSupport3_002 = 0x3f03ffc01ffe00c0000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_002_checked :
    (kindSupport3_002.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_003_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport3_rest_003 =
      (kindSupport3_003, kindSupport3_rest_004) := by decide +kernel
theorem kindSupport3_003_mask : RawNatGrowthCheck.mask kindSupport3_003 = 0x607e07ff803f03f00000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_003_checked :
    (kindSupport3_003.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_004_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport3_rest_004 =
      (kindSupport3_004, kindSupport3_rest_005) := by decide +kernel
theorem kindSupport3_004_mask : RawNatGrowthCheck.mask kindSupport3_004 = 0x7fe00fff007e0780000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_004_checked :
    (kindSupport3_004.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_005_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport3_rest_005 =
      (kindSupport3_005, kindSupport3_rest_006) := by decide +kernel
theorem kindSupport3_005_mask : RawNatGrowthCheck.mask kindSupport3_005 = 0x3ffc01f81f81f818000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_005_checked :
    (kindSupport3_005.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_006_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport3_rest_006 =
      (kindSupport3_006, kindSupport3_rest_007) := by decide +kernel
theorem kindSupport3_006_mask : RawNatGrowthCheck.mask kindSupport3_006 = 0x607ff803f03f03f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_006_checked :
    (kindSupport3_006.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_007_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport3_rest_007 =
      (kindSupport3_007, kindSupport3_rest_008) := by decide +kernel
theorem kindSupport3_007_mask : RawNatGrowthCheck.mask kindSupport3_007 = 0x1e00fff007e07e0780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_007_checked :
    (kindSupport3_007.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenPure001
