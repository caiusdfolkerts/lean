module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 148480
cert_test_block_3 148480 0 0 16 16
cert_test_block_3 148480 1 16 32 16
cert_test_block_3 148480 2 32 48 16
cert_test_block_3 148480 3 48 64 16
cert_test_block_3 148480 4 64 80 16
cert_test_block_3 148480 5 80 96 16
cert_test_block_3 148480 6 96 112 16
cert_test_block_3 148480 7 112 128 16
cert_test_block_3 148480 8 128 144 16
cert_test_block_3 148480 9 144 160 16
cert_test_block_3 148480 10 160 176 16
cert_test_block_3 148480 11 176 192 16
cert_test_block_3 148480 12 192 208 16
cert_test_block_3 148480 13 208 224 16
cert_test_block_3 148480 14 224 240 16
cert_test_block_3 148480 15 240 256 16
cert_test_block_3 148480 16 256 266 10
theorem test148480_complete : Interval test148480 0 266 :=
  (interval_append test148480 0 128 266
  (interval_append test148480 0 64 128
  (interval_append test148480 0 32 64
  (interval_append test148480 0 16 32
  test148480_block_0
  test148480_block_1)
  (interval_append test148480 32 48 64
  test148480_block_2
  test148480_block_3))
  (interval_append test148480 64 96 128
  (interval_append test148480 64 80 96
  test148480_block_4
  test148480_block_5)
  (interval_append test148480 96 112 128
  test148480_block_6
  test148480_block_7)))
  (interval_append test148480 128 192 266
  (interval_append test148480 128 160 192
  (interval_append test148480 128 144 160
  test148480_block_8
  test148480_block_9)
  (interval_append test148480 160 176 192
  test148480_block_10
  test148480_block_11))
  (interval_append test148480 192 224 266
  (interval_append test148480 192 208 224
  test148480_block_12
  test148480_block_13)
  (interval_append test148480 224 240 266
  test148480_block_14
  (interval_append test148480 240 256 266
  test148480_block_15
  test148480_block_16)))))
cert_nodeInterval_3 148480 148746
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
