module
prelude
public import RootedSixExtra01GrowthCacheKindSupport3Data

/- RootedSixExtra01GrowthCacheKindSupport3Part000 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_000_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_000 =
      (kindSupport3_000, kindSupport3_rest_001) := by decide +kernel
theorem kindSupport3_000_mask : RawNatGrowthCheck.mask kindSupport3_000 = 0xc0fc0fc0fc0fc0fc000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_000_checked :
    (kindSupport3_000.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_001_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_001 =
      (kindSupport3_001, kindSupport3_rest_002) := by decide +kernel
theorem kindSupport3_001_mask : RawNatGrowthCheck.mask kindSupport3_001 = 0x3c0fc0fc0fc0fc0f0000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_001_checked :
    (kindSupport3_001.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_002_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_002 =
      (kindSupport3_002, kindSupport3_rest_003) := by decide +kernel
theorem kindSupport3_002_mask : RawNatGrowthCheck.mask kindSupport3_002 = 0x3ffc01ffe00fc0c0000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_002_checked :
    (kindSupport3_002.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_003_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_003 =
      (kindSupport3_003, kindSupport3_rest_004) := by decide +kernel
theorem kindSupport3_003_mask : RawNatGrowthCheck.mask kindSupport3_003 = 0xc0fc0fff007ff800000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_003_checked :
    (kindSupport3_003.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_004_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_004 =
      (kindSupport3_004, kindSupport3_rest_005) := by decide +kernel
theorem kindSupport3_004_mask : RawNatGrowthCheck.mask kindSupport3_004 = 0x1e00fc0fc0fc0fc0f0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_004_checked :
    (kindSupport3_004.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_005_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_005 =
      (kindSupport3_005, kindSupport3_rest_006) := by decide +kernel
theorem kindSupport3_005_mask : RawNatGrowthCheck.mask kindSupport3_005 = 0x7ff803ffc01fe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_005_checked :
    (kindSupport3_005.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_006_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_006 =
      (kindSupport3_006, kindSupport3_rest_007) := by decide +kernel
theorem kindSupport3_006_mask : RawNatGrowthCheck.mask kindSupport3_006 = 0x3fc01ffe00fff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_006_checked :
    (kindSupport3_006.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_007_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_007 =
      (kindSupport3_007, kindSupport3_rest_008) := by decide +kernel
theorem kindSupport3_007_mask : RawNatGrowthCheck.mask kindSupport3_007 = 0x3c00fff007ff803c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_007_checked :
    (kindSupport3_007.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheKindSupport3Part001 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_008_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_008 =
      (kindSupport3_008, kindSupport3_rest_009) := by decide +kernel
theorem kindSupport3_008_mask : RawNatGrowthCheck.mask kindSupport3_008 = 0x381f81f81f81ffc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_008_checked :
    (kindSupport3_008.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_009_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_009 =
      (kindSupport3_009, kindSupport3_rest_010) := by decide +kernel
theorem kindSupport3_009_mask : RawNatGrowthCheck.mask kindSupport3_009 = 0xf803ffc01f81f81c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_009_checked :
    (kindSupport3_009.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_010_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_010 =
      (kindSupport3_010, kindSupport3_rest_011) := by decide +kernel
theorem kindSupport3_010_mask : RawNatGrowthCheck.mask kindSupport3_010 = 0x3ffe00fff007f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_010_checked :
    (kindSupport3_010.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_011_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_011 =
      (kindSupport3_011, kindSupport3_rest_012) := by decide +kernel
theorem kindSupport3_011_mask : RawNatGrowthCheck.mask kindSupport3_011 = 0x1f007ff803ffc01c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_011_checked :
    (kindSupport3_011.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_012_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_012 =
      (kindSupport3_012, kindSupport3_rest_013) := by decide +kernel
theorem kindSupport3_012_mask : RawNatGrowthCheck.mask kindSupport3_012 = 0x803ffc01ffe00fe00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_012_checked :
    (kindSupport3_012.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_013_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_013 =
      (kindSupport3_013, kindSupport3_rest_014) := by decide +kernel
theorem kindSupport3_013_mask : RawNatGrowthCheck.mask kindSupport3_013 = 0x3fe00fff007ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_013_checked :
    (kindSupport3_013.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_014_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_014 =
      (kindSupport3_014, kindSupport3_rest_015) := by decide +kernel
theorem kindSupport3_014_mask : RawNatGrowthCheck.mask kindSupport3_014 = 0x303f03f03fff801c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_014_checked :
    (kindSupport3_014.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_015_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_015 =
      (kindSupport3_015, kindSupport3_rest_016) := by decide +kernel
theorem kindSupport3_015_mask : RawNatGrowthCheck.mask kindSupport3_015 = 0x1ff803f03f03f03c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_015_checked :
    (kindSupport3_015.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheKindSupport3Part002 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_016_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_016 =
      (kindSupport3_016, kindSupport3_rest_017) := by decide +kernel
theorem kindSupport3_016_mask : RawNatGrowthCheck.mask kindSupport3_016 = 0xfc01ffe00fff00600000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_016_checked :
    (kindSupport3_016.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_017_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_017 =
      (kindSupport3_017, kindSupport3_rest_018) := by decide +kernel
theorem kindSupport3_017_mask : RawNatGrowthCheck.mask kindSupport3_017 = 0x303f03f03f03f03f00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_017_checked :
    (kindSupport3_017.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_018_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_018 =
      (kindSupport3_018, kindSupport3_rest_019) := by decide +kernel
theorem kindSupport3_018_mask : RawNatGrowthCheck.mask kindSupport3_018 = 0x3ff007ff803f03c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_018_checked :
    (kindSupport3_018.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_019_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_019 =
      (kindSupport3_019, kindSupport3_rest_020) := by decide +kernel
theorem kindSupport3_019_mask : RawNatGrowthCheck.mask kindSupport3_019 = 0x1f803ffc01ffe00c0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_019_checked :
    (kindSupport3_019.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_020_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_020 =
      (kindSupport3_020, kindSupport3_rest_021) := by decide +kernel
theorem kindSupport3_020_mask : RawNatGrowthCheck.mask kindSupport3_020 = 0xc01ffe00fff007e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_020_checked :
    (kindSupport3_020.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_021_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_021 =
      (kindSupport3_021, kindSupport3_rest_022) := by decide +kernel
theorem kindSupport3_021_mask : RawNatGrowthCheck.mask kindSupport3_021 = 0x7f007fff003ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_021_checked :
    (kindSupport3_021.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_022_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_022 =
      (kindSupport3_022, kindSupport3_rest_023) := by decide +kernel
theorem kindSupport3_022_mask : RawNatGrowthCheck.mask kindSupport3_022 = 0x3803ffc01ffe00f80000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_022_checked :
    (kindSupport3_022.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_023_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_023 =
      (kindSupport3_023, kindSupport3_rest_024) := by decide +kernel
theorem kindSupport3_023_mask : RawNatGrowthCheck.mask kindSupport3_023 = 0x1fe00fffe007fc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_023_checked :
    (kindSupport3_023.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
/- RootedSixExtra01GrowthCacheKindSupport3Part003 -/
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra01
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem kindSupport3_024_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_024 =
      (kindSupport3_024, kindSupport3_rest_025) := by decide +kernel
theorem kindSupport3_024_mask : RawNatGrowthCheck.mask kindSupport3_024 = 0xf007ff803ffc01e00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_024_checked :
    (kindSupport3_024.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_025_decode :
    PackedRawNatGrowth.readList 12 32 kindSupport3_rest_025 =
      (kindSupport3_025, kindSupport3_rest_026) := by decide +kernel
theorem kindSupport3_025_mask : RawNatGrowthCheck.mask kindSupport3_025 = 0xff801fffc00ff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_025_checked :
    (kindSupport3_025.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel
theorem kindSupport3_026_decode :
    PackedRawNatGrowth.readList 12 6 kindSupport3_rest_026 =
      (kindSupport3_026, kindSupport3_rest_027) := by decide +kernel
theorem kindSupport3_026_mask : RawNatGrowthCheck.mask kindSupport3_026 = 0x3f000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem kindSupport3_026_checked :
    (kindSupport3_026.all (fun c => decide ((rawCells c).kind = 3))) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra01

end
end
