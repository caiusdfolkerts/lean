module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0296Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0296
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 10880
cert_test_block_3 10880 0 0 16 16
cert_test_block_3 10880 1 16 32 16
cert_test_block_3 10880 2 32 48 16
cert_test_block_3 10880 3 48 64 16
cert_test_block_3 10880 4 64 80 16
cert_test_block_3 10880 5 80 96 16
cert_test_block_3 10880 6 96 112 16
cert_test_block_3 10880 7 112 128 16
cert_test_block_3 10880 8 128 144 16
cert_test_block_3 10880 9 144 160 16
cert_test_block_3 10880 10 160 176 16
cert_test_block_3 10880 11 176 192 16
cert_test_block_3 10880 12 192 208 16
cert_test_block_3 10880 13 208 224 16
theorem test10880_complete : Interval test10880 0 224 :=
  (interval_append test10880 0 112 224
  (interval_append test10880 0 48 112
  (interval_append test10880 0 16 48
  test10880_block_0
  (interval_append test10880 16 32 48
  test10880_block_1
  test10880_block_2))
  (interval_append test10880 48 80 112
  (interval_append test10880 48 64 80
  test10880_block_3
  test10880_block_4)
  (interval_append test10880 80 96 112
  test10880_block_5
  test10880_block_6)))
  (interval_append test10880 112 160 224
  (interval_append test10880 112 128 160
  test10880_block_7
  (interval_append test10880 128 144 160
  test10880_block_8
  test10880_block_9))
  (interval_append test10880 160 192 224
  (interval_append test10880 160 176 192
  test10880_block_10
  test10880_block_11)
  (interval_append test10880 192 208 224
  test10880_block_12
  test10880_block_13))))
cert_nodeInterval_3 10880 11104
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0296
