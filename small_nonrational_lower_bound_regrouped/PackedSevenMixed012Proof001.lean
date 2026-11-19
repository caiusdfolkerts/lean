module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed012Masks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed012
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
cert_test_4 640
cert_test_block 640 0 0 32 32
cert_test_block 640 1 32 64 32
cert_test_block 640 2 64 96 32
cert_test_block 640 3 96 128 32
cert_test_block 640 4 128 160 32
cert_test_block 640 5 160 192 32
cert_test_block 640 6 192 224 32
cert_test_block 640 7 224 228 4
theorem test640_complete : Interval test640 0 228 :=
  (interval_append test640 0 128 228
  (interval_append test640 0 64 128
  (interval_append test640 0 32 64
  test640_block_0
  test640_block_1)
  (interval_append test640 64 96 128
  test640_block_2
  test640_block_3))
  (interval_append test640 128 192 228
  (interval_append test640 128 160 192
  test640_block_4
  test640_block_5)
  (interval_append test640 192 224 228
  test640_block_6
  test640_block_7)))
cert_nodeInterval 640 868
cert_checkedInterval 640 868
end Papers.RationalityTen.PackedReplay.PackedSevenMixed012
