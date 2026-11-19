module
prelude
public meta import LowerSchemas.FinitePackedSevenMixed
public import PackedSevenMixed015Masks

@[expose] public section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.PackedReplay.PackedSevenMixed015
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
cert_test_block 640 7 224 256 32
cert_test_block 640 8 256 288 32
cert_test_block 640 9 288 320 32
cert_test_block 640 10 320 352 32
cert_test_block 640 11 352 384 32
cert_test_block 640 12 384 416 32
cert_test_block 640 13 416 448 32
cert_test_block 640 14 448 480 32
cert_test_block 640 15 480 512 32
cert_test_block 640 16 512 544 32
cert_test_block 640 17 544 576 32
cert_test_block 640 18 576 608 32
cert_test_block 640 19 608 640 32
theorem test640_complete : Interval test640 0 640 :=
  (interval_append test640 0 320 640
  (interval_append test640 0 160 320
  (interval_append test640 0 64 160
  (interval_append test640 0 32 64
  test640_block_0
  test640_block_1)
  (interval_append test640 64 96 160
  test640_block_2
  (interval_append test640 96 128 160
  test640_block_3
  test640_block_4)))
  (interval_append test640 160 224 320
  (interval_append test640 160 192 224
  test640_block_5
  test640_block_6)
  (interval_append test640 224 256 320
  test640_block_7
  (interval_append test640 256 288 320
  test640_block_8
  test640_block_9))))
  (interval_append test640 320 480 640
  (interval_append test640 320 384 480
  (interval_append test640 320 352 384
  test640_block_10
  test640_block_11)
  (interval_append test640 384 416 480
  test640_block_12
  (interval_append test640 416 448 480
  test640_block_13
  test640_block_14)))
  (interval_append test640 480 544 640
  (interval_append test640 480 512 544
  test640_block_15
  test640_block_16)
  (interval_append test640 544 576 640
  test640_block_17
  (interval_append test640 576 608 640
  test640_block_18
  test640_block_19)))))
cert_nodeInterval 640 1280
cert_checkedInterval 640 1280
end Papers.RationalityTen.PackedReplay.PackedSevenMixed015
