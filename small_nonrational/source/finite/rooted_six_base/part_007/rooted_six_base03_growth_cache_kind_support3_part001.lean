module
prelude
public import RootedSixBase03GrowthCacheKindSupport3Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixBase03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_008_decode :
    PackedRawNatGrowth.readList 13 32 kindSupport3_rest_008 =
      (kindSupport3_008, kindSupport3_rest_009) := by decide +kernel
theorem kindSupport3_008_mask : RawNatGrowthCheck.mask kindSupport3_008 = 0xf803ffc01f81f81c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_008_checked :
    (kindSupport3_008.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_009_decode :
    PackedRawNatGrowth.readList 13 32 kindSupport3_rest_009 =
      (kindSupport3_009, kindSupport3_rest_010) := by decide +kernel
theorem kindSupport3_009_mask : RawNatGrowthCheck.mask kindSupport3_009 = 0x81ffe00fff007f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_009_checked :
    (kindSupport3_009.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_010_decode :
    PackedRawNatGrowth.readList 13 32 kindSupport3_rest_010 =
      (kindSupport3_010, kindSupport3_rest_011) := by decide +kernel
theorem kindSupport3_010_mask : RawNatGrowthCheck.mask kindSupport3_010 = 0x381f81f81f81f81f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_010_checked :
    (kindSupport3_010.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_011_decode :
    PackedRawNatGrowth.readList 13 32 kindSupport3_rest_011 =
      (kindSupport3_011, kindSupport3_rest_012) := by decide +kernel
theorem kindSupport3_011_mask : RawNatGrowthCheck.mask kindSupport3_011 = 0x1f007ff803ffc01c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_011_checked :
    (kindSupport3_011.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_012_decode :
    PackedRawNatGrowth.readList 13 32 kindSupport3_rest_012 =
      (kindSupport3_012, kindSupport3_rest_013) := by decide +kernel
theorem kindSupport3_012_mask : RawNatGrowthCheck.mask kindSupport3_012 = 0x803ffc01ffe00fe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_012_checked :
    (kindSupport3_012.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_013_decode :
    PackedRawNatGrowth.readList 13 32 kindSupport3_rest_013 =
      (kindSupport3_013, kindSupport3_rest_014) := by decide +kernel
theorem kindSupport3_013_mask : RawNatGrowthCheck.mask kindSupport3_013 = 0x3fe00fff007ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_013_checked :
    (kindSupport3_013.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_014_decode :
    PackedRawNatGrowth.readList 13 32 kindSupport3_rest_014 =
      (kindSupport3_014, kindSupport3_rest_015) := by decide +kernel
theorem kindSupport3_014_mask : RawNatGrowthCheck.mask kindSupport3_014 = 0x303f03f03fff801c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_014_checked :
    (kindSupport3_014.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_015_decode :
    PackedRawNatGrowth.readList 13 32 kindSupport3_rest_015 =
      (kindSupport3_015, kindSupport3_rest_016) := by decide +kernel
theorem kindSupport3_015_mask : RawNatGrowthCheck.mask kindSupport3_015 = 0x1ff803f03f03f03c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_015_checked :
    (kindSupport3_015.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixBase03
