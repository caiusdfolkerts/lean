module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0278Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0278
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 4480
cert_test_block_3 4480 0 0 16 16
cert_test_block_3 4480 1 16 32 16
cert_test_block_3 4480 2 32 48 16
cert_test_block_3 4480 3 48 64 16
cert_test_block_3 4480 4 64 80 16
cert_test_block_3 4480 5 80 96 16
cert_test_block_3 4480 6 96 112 16
cert_test_block_3 4480 7 112 128 16
cert_test_block_3 4480 8 128 144 16
cert_test_block_3 4480 9 144 160 16
cert_test_block_3 4480 10 160 176 16
cert_test_block_3 4480 11 176 192 16
cert_test_block_3 4480 12 192 208 16
cert_test_block_3 4480 13 208 224 16
cert_test_block_3 4480 14 224 240 16
cert_test_block_3 4480 15 240 248 8
theorem test4480_complete : Interval test4480 0 248 :=
  (interval_append test4480 0 128 248
  (interval_append test4480 0 64 128
  (interval_append test4480 0 32 64
  (interval_append test4480 0 16 32
  test4480_block_0
  test4480_block_1)
  (interval_append test4480 32 48 64
  test4480_block_2
  test4480_block_3))
  (interval_append test4480 64 96 128
  (interval_append test4480 64 80 96
  test4480_block_4
  test4480_block_5)
  (interval_append test4480 96 112 128
  test4480_block_6
  test4480_block_7)))
  (interval_append test4480 128 192 248
  (interval_append test4480 128 160 192
  (interval_append test4480 128 144 160
  test4480_block_8
  test4480_block_9)
  (interval_append test4480 160 176 192
  test4480_block_10
  test4480_block_11))
  (interval_append test4480 192 224 248
  (interval_append test4480 192 208 224
  test4480_block_12
  test4480_block_13)
  (interval_append test4480 224 240 248
  test4480_block_14
  test4480_block_15))))
cert_nodeInterval_3 4480 4728
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0278
