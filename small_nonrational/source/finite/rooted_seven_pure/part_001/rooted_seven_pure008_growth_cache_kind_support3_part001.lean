module
prelude
public import RootedSevenPure008GrowthCacheKindSupport3Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSevenPure008
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_008_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport3_rest_008 =
      (kindSupport3_008, kindSupport3_rest_009) := by decide +kernel
theorem kindSupport3_008_mask : RawNatGrowthCheck.mask kindSupport3_008 = 0xfc01ffe00fc0fc0c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_008_checked :
    (kindSupport3_008.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_009_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport3_rest_009 =
      (kindSupport3_009, kindSupport3_rest_010) := by decide +kernel
theorem kindSupport3_009_mask : RawNatGrowthCheck.mask kindSupport3_009 = 0x7f803f03f03f03f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_009_checked :
    (kindSupport3_009.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_010_decode :
    PackedRawNatGrowth.readList 10 32 kindSupport3_rest_010 =
      (kindSupport3_010, kindSupport3_rest_011) := by decide +kernel
theorem kindSupport3_010_mask : RawNatGrowthCheck.mask kindSupport3_010 = 0x3c01ffe00fff00780000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_010_checked :
    (kindSupport3_010.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_011_decode :
    PackedRawNatGrowth.readList 10 8 kindSupport3_rest_011 =
      (kindSupport3_011, kindSupport3_rest_012) := by decide +kernel
theorem kindSupport3_011_mask : RawNatGrowthCheck.mask kindSupport3_011 = 0x3fc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_011_checked :
    (kindSupport3_011.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSevenPure008
