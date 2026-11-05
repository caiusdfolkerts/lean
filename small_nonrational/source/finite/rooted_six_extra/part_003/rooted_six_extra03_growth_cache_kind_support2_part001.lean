module
prelude
public import RootedSixExtra03GrowthCacheKindSupport2Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_008_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_008 =
      (kindSupport2_008, kindSupport2_rest_009) := by decide +kernel
theorem kindSupport2_008_mask : RawNatGrowthCheck.mask kindSupport2_008 = 0x607e07e07e07e001f80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_008_checked :
    (kindSupport2_008.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_009_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_009 =
      (kindSupport2_009, kindSupport2_rest_010) := by decide +kernel
theorem kindSupport2_009_mask : RawNatGrowthCheck.mask kindSupport2_009 = 0x78007fc003fe07e078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_009_checked :
    (kindSupport2_009.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_010_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_010 =
      (kindSupport2_010, kindSupport2_rest_011) := by decide +kernel
theorem kindSupport2_010_mask : RawNatGrowthCheck.mask kindSupport2_010 = 0x7fc003fe001ff000f800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_010_checked :
    (kindSupport2_010.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_011_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_011 =
      (kindSupport2_011, kindSupport2_rest_012) := by decide +kernel
theorem kindSupport2_011_mask : RawNatGrowthCheck.mask kindSupport2_011 = 0x3c0007fe001ff000ff80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_011_checked :
    (kindSupport2_011.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_012_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_012 =
      (kindSupport2_012, kindSupport2_rest_013) := by decide +kernel
theorem kindSupport2_012_mask : RawNatGrowthCheck.mask kindSupport2_012 = 0xfc0fc0fc0fc0fc0c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_012_checked :
    (kindSupport2_012.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_013_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_013 =
      (kindSupport2_013, kindSupport2_rest_014) := by decide +kernel
theorem kindSupport2_013_mask : RawNatGrowthCheck.mask kindSupport2_013 = 0x3e001ff000ff8007fc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_013_checked :
    (kindSupport2_013.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_014_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_014 =
      (kindSupport2_014, kindSupport2_rest_015) := by decide +kernel
theorem kindSupport2_014_mask : RawNatGrowthCheck.mask kindSupport2_014 = 0x2001ff000ff8007fc003c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_014_checked :
    (kindSupport2_014.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_015_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_015 =
      (kindSupport2_015, kindSupport2_rest_016) := by decide +kernel
theorem kindSupport2_015_mask : RawNatGrowthCheck.mask kindSupport2_015 = 0x181f81f8000ffc003fc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_015_checked :
    (kindSupport2_015.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra03
