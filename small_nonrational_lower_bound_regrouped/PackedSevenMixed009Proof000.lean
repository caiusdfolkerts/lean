module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed009Masks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed009
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
cert_test_block 0 13 416 448 32
cert_test_block 0 14 448 480 32
cert_test_block 0 15 480 508 28
theorem test0_complete : Interval test0 0 508 :=
  (interval_append test0 0 256 508
  (interval_append test0 0 128 256
  (interval_append test0 0 64 128
  (interval_append test0 0 32 64
  test0_block_0
  test0_block_1)
  (interval_append test0 64 96 128
  test0_block_2
  test0_block_3))
  (interval_append test0 128 192 256
  (interval_append test0 128 160 192
  test0_block_4
  test0_block_5)
  (interval_append test0 192 224 256
  test0_block_6
  test0_block_7)))
  (interval_append test0 256 384 508
  (interval_append test0 256 320 384
  (interval_append test0 256 288 320
  test0_block_8
  test0_block_9)
  (interval_append test0 320 352 384
  test0_block_10
  test0_block_11))
  (interval_append test0 384 448 508
  (interval_append test0 384 416 448
  test0_block_12
  test0_block_13)
  (interval_append test0 448 480 508
  test0_block_14
  test0_block_15))))
cert_nodeInterval 0 508
cert_checkedInterval 0 508
end Papers.RationalityTen.PackedReplay.PackedSevenMixed009
