module
prelude
public import RootedSixExtra04GrowthCacheKindSupport2Data

/- RootedSixExtra04GrowthCacheKindSupport2Part000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_000_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_000 =
      (kindSupport2_000, kindSupport2_rest_001) := by decide +kernel
theorem kindSupport2_000_mask : RawNatGrowthCheck.mask kindSupport2_000 = 0xc0fc0fc0fc0fc0fc00000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_000_checked :
    (kindSupport2_000.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_001_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_001 =
      (kindSupport2_001, kindSupport2_rest_002) := by decide +kernel
theorem kindSupport2_001_mask : RawNatGrowthCheck.mask kindSupport2_001 = 0x3c0fc0fc0fc0fc0f000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_001_checked :
    (kindSupport2_001.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_002_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_002 =
      (kindSupport2_002, kindSupport2_rest_003) := by decide +kernel
theorem kindSupport2_002_mask : RawNatGrowthCheck.mask kindSupport2_002 = 0x3f000ff8007fc0fc0c000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_002_checked :
    (kindSupport2_002.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_003_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_003 =
      (kindSupport2_003, kindSupport2_rest_004) := by decide +kernel
theorem kindSupport2_003_mask : RawNatGrowthCheck.mask kindSupport2_003 = 0xc0fc0fc0fc003fe001c00000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_003_checked :
    (kindSupport2_003.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_004_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_004 =
      (kindSupport2_004, kindSupport2_rest_005) := by decide +kernel
theorem kindSupport2_004_mask : RawNatGrowthCheck.mask kindSupport2_004 = 0x3f8007fc0fc0fc0f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_004_checked :
    (kindSupport2_004.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_005_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_005 =
      (kindSupport2_005, kindSupport2_rest_006) := by decide +kernel
theorem kindSupport2_005_mask : RawNatGrowthCheck.mask kindSupport2_005 = 0xfc0fc003fe001ff000c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_005_checked :
    (kindSupport2_005.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_006_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_006 =
      (kindSupport2_006, kindSupport2_rest_007) := by decide +kernel
theorem kindSupport2_006_mask : RawNatGrowthCheck.mask kindSupport2_006 = 0x3fc0fc0fc0fc0fc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_006_checked :
    (kindSupport2_006.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_007_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_007 =
      (kindSupport2_007, kindSupport2_rest_008) := by decide +kernel
theorem kindSupport2_007_mask : RawNatGrowthCheck.mask kindSupport2_007 = 0x3c003fe001ff000ff80040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_007_checked :
    (kindSupport2_007.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra04

end
end
/- RootedSixExtra04GrowthCacheKindSupport2Part001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_008_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_008 =
      (kindSupport2_008, kindSupport2_rest_009) := by decide +kernel
theorem kindSupport2_008_mask : RawNatGrowthCheck.mask kindSupport2_008 = 0x3fe001ff000ff8007c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_008_checked :
    (kindSupport2_008.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_009_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_009 =
      (kindSupport2_009, kindSupport2_rest_010) := by decide +kernel
theorem kindSupport2_009_mask : RawNatGrowthCheck.mask kindSupport2_009 = 0x781f81f81f8000ffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_009_checked :
    (kindSupport2_009.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_010_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_010 =
      (kindSupport2_010, kindSupport2_rest_011) := by decide +kernel
theorem kindSupport2_010_mask : RawNatGrowthCheck.mask kindSupport2_010 = 0x1ff000ff81f81f818000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_010_checked :
    (kindSupport2_010.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_011_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_011 =
      (kindSupport2_011, kindSupport2_rest_012) := by decide +kernel
theorem kindSupport2_011_mask : RawNatGrowthCheck.mask kindSupport2_011 = 0x181f81f8007fc003fe0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_011_checked :
    (kindSupport2_011.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_012_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_012 =
      (kindSupport2_012, kindSupport2_rest_013) := by decide +kernel
theorem kindSupport2_012_mask : RawNatGrowthCheck.mask kindSupport2_012 = 0x1000ff81f81f81f81e000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_012_checked :
    (kindSupport2_012.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_013_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_013 =
      (kindSupport2_013, kindSupport2_rest_014) := by decide +kernel
theorem kindSupport2_013_mask : RawNatGrowthCheck.mask kindSupport2_013 = 0x1f8007fc003fe001fe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_013_checked :
    (kindSupport2_013.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_014_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_014 =
      (kindSupport2_014, kindSupport2_rest_015) := by decide +kernel
theorem kindSupport2_014_mask : RawNatGrowthCheck.mask kindSupport2_014 = 0x18007fc003fe001ff000e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_014_checked :
    (kindSupport2_014.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_015_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_015 =
      (kindSupport2_015, kindSupport2_rest_016) := by decide +kernel
theorem kindSupport2_015_mask : RawNatGrowthCheck.mask kindSupport2_015 = 0x3f03f03f03f0001fe000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_015_checked :
    (kindSupport2_015.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra04

end
end
/- RootedSixExtra04GrowthCacheKindSupport2Part002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_016_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_016 =
      (kindSupport2_016, kindSupport2_rest_017) := by decide +kernel
theorem kindSupport2_016_mask : RawNatGrowthCheck.mask kindSupport2_016 = 0xc003fe001ff03f03f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_016_checked :
    (kindSupport2_016.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_017_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_017 =
      (kindSupport2_017, kindSupport2_rest_018) := by decide +kernel
theorem kindSupport2_017_mask : RawNatGrowthCheck.mask kindSupport2_017 = 0xfe001ff000ff8007f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_017_checked :
    (kindSupport2_017.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_018_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_018 =
      (kindSupport2_018, kindSupport2_rest_019) := by decide +kernel
theorem kindSupport2_018_mask : RawNatGrowthCheck.mask kindSupport2_018 = 0x60003ff000ff8007fc0030000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_018_checked :
    (kindSupport2_018.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_019_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_019 =
      (kindSupport2_019, kindSupport2_rest_020) := by decide +kernel
theorem kindSupport2_019_mask : RawNatGrowthCheck.mask kindSupport2_019 = 0x1e07e07e07e07e078000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_019_checked :
    (kindSupport2_019.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_020_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_020 =
      (kindSupport2_020, kindSupport2_rest_021) := by decide +kernel
theorem kindSupport2_020_mask : RawNatGrowthCheck.mask kindSupport2_020 = 0x7000ff8007fc003fe060000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_020_checked :
    (kindSupport2_020.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_021_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_021 =
      (kindSupport2_021, kindSupport2_rest_022) := by decide +kernel
theorem kindSupport2_021_mask : RawNatGrowthCheck.mask kindSupport2_021 = 0x7f8007fc003fe001f80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_021_checked :
    (kindSupport2_021.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_022_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_022 =
      (kindSupport2_022, kindSupport2_rest_023) := by decide +kernel
theorem kindSupport2_022_mask : RawNatGrowthCheck.mask kindSupport2_022 = 0x38007fc0007fe001ff0008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_022_checked :
    (kindSupport2_022.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel
theorem kindSupport2_023_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport2_rest_023 =
      (kindSupport2_023, kindSupport2_rest_024) := by decide +kernel
theorem kindSupport2_023_mask : RawNatGrowthCheck.mask kindSupport2_023 = 0x3fc003fe001ff000fc000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_023_checked :
    (kindSupport2_023.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra04

end
end
/- RootedSixExtra04GrowthCacheKindSupport2Part003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra04
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport2_024_decode :
    PackedRawNatGrowth.readList 12 12 kindSupport2_rest_024 =
      (kindSupport2_024, kindSupport2_rest_025) := by decide +kernel
theorem kindSupport2_024_mask : RawNatGrowthCheck.mask kindSupport2_024 = 0x1ff8000c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport2_024_checked :
    (kindSupport2_024.all (fun c => decide ((rawCells c).kind = 2))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra04

end
end
