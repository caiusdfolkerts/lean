module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed002Masks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed002
open Papers.RationalityTen
open ConcreteGrowth GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth FiniteChecks
open RawNatGrowthSoundness RawNatGrowthCompleteness RawGrowthCacheCertificate
cert_test_4 0
cert_test_block 0 0 0 32 32
cert_test_block 0 1 32 64 32
cert_test_block 0 2 64 96 32
cert_test_block 0 3 96 128 32
cert_test_block 0 4 128 160 32
cert_test_block 0 5 160 192 32
cert_test_block 0 6 192 224 32
cert_test_block 0 7 224 256 32
cert_test_block 0 8 256 286 30
theorem test0_complete : Interval test0 0 286 :=
  (interval_append test0 0 128 286
  (interval_append test0 0 64 128
  (interval_append test0 0 32 64
  test0_block_0
  test0_block_1)
  (interval_append test0 64 96 128
  test0_block_2
  test0_block_3))
  (interval_append test0 128 192 286
  (interval_append test0 128 160 192
  test0_block_4
  test0_block_5)
  (interval_append test0 192 224 286
  test0_block_6
  (interval_append test0 224 256 286
  test0_block_7
  test0_block_8))))
cert_nodeInterval 0 286
cert_checkedInterval 0 286
end Papers.RationalityTen.PackedReplay.PackedSevenMixed002
