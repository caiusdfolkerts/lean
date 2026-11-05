module
prelude
public import RootedSixExtra05GrowthCacheRidgeSupport704Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedCaches.RootedSixExtra05
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open RawGrowthCacheCertificate RawNatGrowthSoundness
theorem ridgeSupport704_000_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport704_rest_000 =
      (ridgeSupport704_000, ridgeSupport704_rest_001) := by decide +kernel
theorem ridgeSupport704_000_mask : RawNatGrowthCheck.mask ridgeSupport704_000 = 0x20000000000000003f007e00000000000000003f007e0000000000000000000000009100400004010001000000 := by decide +kernel
theorem ridgeSupport704_000_checked :
    (ridgeSupport704_000.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_001_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport704_rest_001 =
      (ridgeSupport704_001, ridgeSupport704_rest_002) := by decide +kernel
theorem ridgeSupport704_001_mask : RawNatGrowthCheck.mask ridgeSupport704_001 = 0xe00fc00000146c2ab00000000003f007c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_001_checked :
    (ridgeSupport704_001.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_002_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport704_rest_002 =
      (ridgeSupport704_002, ridgeSupport704_rest_003) := by decide +kernel
theorem ridgeSupport704_002_mask : RawNatGrowthCheck.mask ridgeSupport704_002 = 0xf8000028d855600000000007e00fc000000000000000700000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_002_checked :
    (ridgeSupport704_002.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_003_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport704_rest_003 =
      (ridgeSupport704_003, ridgeSupport704_rest_004) := by decide +kernel
theorem ridgeSupport704_003_mask : RawNatGrowthCheck.mask ridgeSupport704_003 = 0x10000000000000001f803f0000000000000000000000051b0aac0000000000fc0100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_003_checked :
    (ridgeSupport704_003.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_004_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport704_rest_004 =
      (ridgeSupport704_004, ridgeSupport704_rest_005) := by decide +kernel
theorem ridgeSupport704_004_mask : RawNatGrowthCheck.mask ridgeSupport704_004 = 0x7007e00000a3615580000000001f803e0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_004_checked :
    (ridgeSupport704_004.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_005_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport704_rest_005 =
      (ridgeSupport704_005, ridgeSupport704_rest_006) := by decide +kernel
theorem ridgeSupport704_005_mask : RawNatGrowthCheck.mask ridgeSupport704_005 = 0x7c0028d855746c2ab00000000003800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_005_checked :
    (ridgeSupport704_005.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_006_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport704_rest_006 =
      (ridgeSupport704_006, ridgeSupport704_rest_007) := by decide +kernel
theorem ridgeSupport704_006_mask : RawNatGrowthCheck.mask ridgeSupport704_006 = 0x40000000fc0000000fc000003f000000fc0000000fc00000008000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_006_checked :
    (ridgeSupport704_006.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel
theorem ridgeSupport704_007_decode :
    PackedRawNatGrowth.readList 12 32 ridgeSupport704_rest_007 =
      (ridgeSupport704_007, ridgeSupport704_rest_008) := by decide +kernel
theorem ridgeSupport704_007_mask : RawNatGrowthCheck.mask ridgeSupport704_007 = 0x38003f000000000000fc0000000000000fc0000000fc0000000000000f800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 := by decide +kernel
theorem ridgeSupport704_007_checked :
    (ridgeSupport704_007.all (fun c => hasNat (rawCells c).ridgeMasks 704)) = true := by decide +kernel

end Papers.RationalityTen.RootedCaches.RootedSixExtra05
