module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0318Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0318
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 9600
cert_test_block_3 9600 0 0 16 16
cert_test_block_3 9600 1 16 32 16
cert_test_block_3 9600 2 32 48 16
cert_test_block_3 9600 3 48 64 16
cert_test_block_3 9600 4 64 80 16
cert_test_block_3 9600 5 80 96 16
cert_test_block_3 9600 6 96 112 16
cert_test_block_3 9600 7 112 128 16
cert_test_block_3 9600 8 128 144 16
cert_test_block_3 9600 9 144 160 16
cert_test_block_3 9600 10 160 176 16
cert_test_block_3 9600 11 176 192 16
cert_test_block_3 9600 12 192 208 16
cert_test_block_3 9600 13 208 217 9
theorem test9600_complete : Interval test9600 0 217 :=
  (interval_append test9600 0 112 217
  (interval_append test9600 0 48 112
  (interval_append test9600 0 16 48
  test9600_block_0
  (interval_append test9600 16 32 48
  test9600_block_1
  test9600_block_2))
  (interval_append test9600 48 80 112
  (interval_append test9600 48 64 80
  test9600_block_3
  test9600_block_4)
  (interval_append test9600 80 96 112
  test9600_block_5
  test9600_block_6)))
  (interval_append test9600 112 160 217
  (interval_append test9600 112 128 160
  test9600_block_7
  (interval_append test9600 128 144 160
  test9600_block_8
  test9600_block_9))
  (interval_append test9600 160 192 217
  (interval_append test9600 160 176 192
  test9600_block_10
  test9600_block_11)
  (interval_append test9600 192 208 217
  test9600_block_12
  test9600_block_13))))
cert_nodeInterval_3 9600 9817
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0318
