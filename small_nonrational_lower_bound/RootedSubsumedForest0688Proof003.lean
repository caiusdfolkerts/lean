module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0688Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0688
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 1920
cert_test_block_3 1920 0 0 16 16
cert_test_block_3 1920 1 16 32 16
cert_test_block_3 1920 2 32 48 16
cert_test_block_3 1920 3 48 64 16
cert_test_block_3 1920 4 64 80 16
cert_test_block_3 1920 5 80 96 16
cert_test_block_3 1920 6 96 112 16
cert_test_block_3 1920 7 112 128 16
cert_test_block_3 1920 8 128 144 16
cert_test_block_3 1920 9 144 160 16
cert_test_block_3 1920 10 160 176 16
cert_test_block_3 1920 11 176 192 16
cert_test_block_3 1920 12 192 208 16
cert_test_block_3 1920 13 208 224 16
cert_test_block_3 1920 14 224 240 16
cert_test_block_3 1920 15 240 256 16
cert_test_block_3 1920 16 256 269 13
theorem test1920_complete : Interval test1920 0 269 :=
  (interval_append test1920 0 128 269
  (interval_append test1920 0 64 128
  (interval_append test1920 0 32 64
  (interval_append test1920 0 16 32
  test1920_block_0
  test1920_block_1)
  (interval_append test1920 32 48 64
  test1920_block_2
  test1920_block_3))
  (interval_append test1920 64 96 128
  (interval_append test1920 64 80 96
  test1920_block_4
  test1920_block_5)
  (interval_append test1920 96 112 128
  test1920_block_6
  test1920_block_7)))
  (interval_append test1920 128 192 269
  (interval_append test1920 128 160 192
  (interval_append test1920 128 144 160
  test1920_block_8
  test1920_block_9)
  (interval_append test1920 160 176 192
  test1920_block_10
  test1920_block_11))
  (interval_append test1920 192 224 269
  (interval_append test1920 192 208 224
  test1920_block_12
  test1920_block_13)
  (interval_append test1920 224 240 269
  test1920_block_14
  (interval_append test1920 240 256 269
  test1920_block_15
  test1920_block_16)))))
cert_nodeInterval_3 1920 2189
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0688
