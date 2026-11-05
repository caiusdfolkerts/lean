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
theorem kindSupport3_008_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_008 =
      (kindSupport3_008, kindSupport3_rest_009) := by decide +kernel
theorem kindSupport3_008_mask : RawNatGrowthCheck.mask kindSupport3_008 = 0x1ff007ff803ff8000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_008_checked :
    (kindSupport3_008.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_009_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_009 =
      (kindSupport3_009, kindSupport3_rest_010) := by decide +kernel
theorem kindSupport3_009_mask : RawNatGrowthCheck.mask kindSupport3_009 = 0x1803fff801ffe00e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_009_checked :
    (kindSupport3_009.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_010_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_010 =
      (kindSupport3_010, kindSupport3_rest_011) := by decide +kernel
theorem kindSupport3_010_mask : RawNatGrowthCheck.mask kindSupport3_010 = 0x7fe00fff007fe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_010_checked :
    (kindSupport3_010.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_011_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_011 =
      (kindSupport3_011, kindSupport3_rest_012) := by decide +kernel
theorem kindSupport3_011_mask : RawNatGrowthCheck.mask kindSupport3_011 = 0xe07fff003ffc0180000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_011_checked :
    (kindSupport3_011.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_012_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_012 =
      (kindSupport3_012, kindSupport3_rest_013) := by decide +kernel
theorem kindSupport3_012_mask : RawNatGrowthCheck.mask kindSupport3_012 = 0x3e07e07e07e07e070000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_012_checked :
    (kindSupport3_012.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_013_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_013 =
      (kindSupport3_013, kindSupport3_rest_014) := by decide +kernel
theorem kindSupport3_013_mask : RawNatGrowthCheck.mask kindSupport3_013 = 0x1fc01ffe00fff0040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_013_checked :
    (kindSupport3_013.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_014_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_014 =
      (kindSupport3_014, kindSupport3_rest_015) := by decide +kernel
theorem kindSupport3_014_mask : RawNatGrowthCheck.mask kindSupport3_014 = 0xe00fff007ff803e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_014_checked :
    (kindSupport3_014.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_015_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_015 =
      (kindSupport3_015, kindSupport3_rest_016) := by decide +kernel
theorem kindSupport3_015_mask : RawNatGrowthCheck.mask kindSupport3_015 = 0x3ff803ffc01ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_015_checked :
    (kindSupport3_015.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
