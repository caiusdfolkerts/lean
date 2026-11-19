module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 60160
cert_test_block_3 60160 0 0 16 16
cert_test_block_3 60160 1 16 32 16
cert_test_block_3 60160 2 32 48 16
cert_test_block_3 60160 3 48 64 16
cert_test_block_3 60160 4 64 80 16
cert_test_block_3 60160 5 80 96 16
cert_test_block_3 60160 6 96 112 16
cert_test_block_3 60160 7 112 128 16
cert_test_block_3 60160 8 128 144 16
cert_test_block_3 60160 9 144 160 16
cert_test_block_3 60160 10 160 176 16
cert_test_block_3 60160 11 176 192 16
cert_test_block_3 60160 12 192 206 14
theorem test60160_complete : Interval test60160 0 206 :=
  (interval_append test60160 0 96 206
  (interval_append test60160 0 48 96
  (interval_append test60160 0 16 48
  test60160_block_0
  (interval_append test60160 16 32 48
  test60160_block_1
  test60160_block_2))
  (interval_append test60160 48 64 96
  test60160_block_3
  (interval_append test60160 64 80 96
  test60160_block_4
  test60160_block_5)))
  (interval_append test60160 96 144 206
  (interval_append test60160 96 112 144
  test60160_block_6
  (interval_append test60160 112 128 144
  test60160_block_7
  test60160_block_8))
  (interval_append test60160 144 176 206
  (interval_append test60160 144 160 176
  test60160_block_9
  test60160_block_10)
  (interval_append test60160 176 192 206
  test60160_block_11
  test60160_block_12))))
cert_nodeInterval_3 60160 60366
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
