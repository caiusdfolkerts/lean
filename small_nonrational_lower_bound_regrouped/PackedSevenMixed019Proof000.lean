module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed019Masks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed019
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
cert_test_block 0 15 480 512 32
cert_test_block 0 16 512 544 32
cert_test_block 0 17 544 553 9
theorem test0_complete : Interval test0 0 553 :=
  (interval_append test0 0 288 553
  (interval_append test0 0 128 288
  (interval_append test0 0 64 128
  (interval_append test0 0 32 64
  test0_block_0
  test0_block_1)
  (interval_append test0 64 96 128
  test0_block_2
  test0_block_3))
  (interval_append test0 128 192 288
  (interval_append test0 128 160 192
  test0_block_4
  test0_block_5)
  (interval_append test0 192 224 288
  test0_block_6
  (interval_append test0 224 256 288
  test0_block_7
  test0_block_8))))
  (interval_append test0 288 416 553
  (interval_append test0 288 352 416
  (interval_append test0 288 320 352
  test0_block_9
  test0_block_10)
  (interval_append test0 352 384 416
  test0_block_11
  test0_block_12))
  (interval_append test0 416 480 553
  (interval_append test0 416 448 480
  test0_block_13
  test0_block_14)
  (interval_append test0 480 512 553
  test0_block_15
  (interval_append test0 512 544 553
  test0_block_16
  test0_block_17)))))
cert_nodeInterval 0 553
cert_checkedInterval 0 553
end Papers.RationalityTen.PackedReplay.PackedSevenMixed019
