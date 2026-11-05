module
prelude
public import RootedSevenPure006GrowthCacheKindSupport2Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure006
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_000_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport2_rest_000 =
      (kindSupport2_000, kindSupport2_rest_001) := by decide +kernel
theorem kindSupport2_000_mask : RawNatGrowthCheck.mask kindSupport2_000 = 0x3e001ff007e07e07e := by decide +kernel
theorem kindSupport2_000_checked :
    (kindSupport2_000.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_001_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport2_rest_001 =
      (kindSupport2_001, kindSupport2_rest_002) := by decide +kernel
theorem kindSupport2_001_mask : RawNatGrowthCheck.mask kindSupport2_001 = 0x8007fc003fe07e07e040000000000000000 := by decide +kernel
theorem kindSupport2_001_checked :
    (kindSupport2_001.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_002_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport2_rest_002 =
      (kindSupport2_002, kindSupport2_rest_003) := by decide +kernel
theorem kindSupport2_002_mask : RawNatGrowthCheck.mask kindSupport2_002 = 0x3f000ff81f81f81f00000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_002_checked :
    (kindSupport2_002.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_003_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport2_rest_003 =
      (kindSupport2_003, kindSupport2_rest_004) := by decide +kernel
theorem kindSupport2_003_mask : RawNatGrowthCheck.mask kindSupport2_003 = 0xc003fe07e07e07e001c00000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_003_checked :
    (kindSupport2_003.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_004_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport2_rest_004 =
      (kindSupport2_004, kindSupport2_rest_005) := by decide +kernel
theorem kindSupport2_004_mask : RawNatGrowthCheck.mask kindSupport2_004 = 0x3f8007fc0fc0fc0f000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_004_checked :
    (kindSupport2_004.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_005_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport2_rest_005 =
      (kindSupport2_005, kindSupport2_rest_006) := by decide +kernel
theorem kindSupport2_005_mask : RawNatGrowthCheck.mask kindSupport2_005 = 0xe001ff03f03f03f000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_005_checked :
    (kindSupport2_005.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_006_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport2_rest_006 =
      (kindSupport2_006, kindSupport2_rest_007) := by decide +kernel
theorem kindSupport2_006_mask : RawNatGrowthCheck.mask kindSupport2_006 = 0x3fc003fe07e07e070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_006_checked :
    (kindSupport2_006.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_007_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport2_rest_007 =
      (kindSupport2_007, kindSupport2_rest_008) := by decide +kernel
theorem kindSupport2_007_mask : RawNatGrowthCheck.mask kindSupport2_007 = 0xf000ff81f81f81f80040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_007_checked :
    (kindSupport2_007.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenPure006
