module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0702Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0702
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 2560
cert_test_block_3 2560 0 0 16 16
cert_test_block_3 2560 1 16 32 16
cert_test_block_3 2560 2 32 48 16
cert_test_block_3 2560 3 48 64 16
cert_test_block_3 2560 4 64 80 16
cert_test_block_3 2560 5 80 96 16
cert_test_block_3 2560 6 96 112 16
cert_test_block_3 2560 7 112 128 16
cert_test_block_3 2560 8 128 144 16
cert_test_block_3 2560 9 144 160 16
cert_test_block_3 2560 10 160 176 16
cert_test_block_3 2560 11 176 192 16
cert_test_block_3 2560 12 192 208 16
cert_test_block_3 2560 13 208 221 13
theorem test2560_complete : Interval test2560 0 221 :=
  (interval_append test2560 0 112 221
  (interval_append test2560 0 48 112
  (interval_append test2560 0 16 48
  test2560_block_0
  (interval_append test2560 16 32 48
  test2560_block_1
  test2560_block_2))
  (interval_append test2560 48 80 112
  (interval_append test2560 48 64 80
  test2560_block_3
  test2560_block_4)
  (interval_append test2560 80 96 112
  test2560_block_5
  test2560_block_6)))
  (interval_append test2560 112 160 221
  (interval_append test2560 112 128 160
  test2560_block_7
  (interval_append test2560 128 144 160
  test2560_block_8
  test2560_block_9))
  (interval_append test2560 160 192 221
  (interval_append test2560 160 176 192
  test2560_block_10
  test2560_block_11)
  (interval_append test2560 192 208 221
  test2560_block_12
  test2560_block_13))))
cert_nodeInterval_3 2560 2781
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0702
