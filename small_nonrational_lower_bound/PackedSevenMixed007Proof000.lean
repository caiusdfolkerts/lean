module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed007Masks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed007
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
cert_test_block 0 8 256 288 32
cert_test_block 0 9 288 320 32
cert_test_block 0 10 320 322 2
theorem test0_complete : Interval test0 0 322 :=
  (interval_append test0 0 160 322
  (interval_append test0 0 64 160
  (interval_append test0 0 32 64
  test0_block_0
  test0_block_1)
  (interval_append test0 64 96 160
  test0_block_2
  (interval_append test0 96 128 160
  test0_block_3
  test0_block_4)))
  (interval_append test0 160 256 322
  (interval_append test0 160 192 256
  test0_block_5
  (interval_append test0 192 224 256
  test0_block_6
  test0_block_7))
  (interval_append test0 256 288 322
  test0_block_8
  (interval_append test0 288 320 322
  test0_block_9
  test0_block_10))))
cert_nodeInterval 0 322
cert_checkedInterval 0 322
end Papers.RationalityTen.PackedReplay.PackedSevenMixed007
