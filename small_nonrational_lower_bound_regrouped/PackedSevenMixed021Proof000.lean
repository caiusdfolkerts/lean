module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed021Masks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed021
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
cert_test_block 0 10 320 352 32
cert_test_block 0 11 352 384 32
cert_test_block 0 12 384 416 32
cert_test_block 0 13 416 445 29
theorem test0_complete : Interval test0 0 445 :=
  (interval_append test0 0 224 445
  (interval_append test0 0 96 224
  (interval_append test0 0 32 96
  test0_block_0
  (interval_append test0 32 64 96
  test0_block_1
  test0_block_2))
  (interval_append test0 96 160 224
  (interval_append test0 96 128 160
  test0_block_3
  test0_block_4)
  (interval_append test0 160 192 224
  test0_block_5
  test0_block_6)))
  (interval_append test0 224 320 445
  (interval_append test0 224 256 320
  test0_block_7
  (interval_append test0 256 288 320
  test0_block_8
  test0_block_9))
  (interval_append test0 320 384 445
  (interval_append test0 320 352 384
  test0_block_10
  test0_block_11)
  (interval_append test0 384 416 445
  test0_block_12
  test0_block_13))))
cert_nodeInterval 0 445
cert_checkedInterval 0 445
end Papers.RationalityTen.PackedReplay.PackedSevenMixed021
