module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest03Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest03
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_13 10240
cert_test_block_4 10240 0 0 16 16
cert_test_block_4 10240 1 16 32 16
cert_test_block_4 10240 2 32 48 16
cert_test_block_4 10240 3 48 64 16
cert_test_block_4 10240 4 64 80 16
cert_test_block_4 10240 5 80 96 16
cert_test_block_4 10240 6 96 112 16
cert_test_block_4 10240 7 112 128 16
cert_test_block_4 10240 8 128 144 16
cert_test_block_4 10240 9 144 160 16
cert_test_block_4 10240 10 160 162 2
theorem test10240_complete : Interval test10240 0 162 :=
  (interval_append test10240 0 80 162
  (interval_append test10240 0 32 80
  (interval_append test10240 0 16 32
  test10240_block_0
  test10240_block_1)
  (interval_append test10240 32 48 80
  test10240_block_2
  (interval_append test10240 48 64 80
  test10240_block_3
  test10240_block_4)))
  (interval_append test10240 80 128 162
  (interval_append test10240 80 96 128
  test10240_block_5
  (interval_append test10240 96 112 128
  test10240_block_6
  test10240_block_7))
  (interval_append test10240 128 144 162
  test10240_block_8
  (interval_append test10240 144 160 162
  test10240_block_9
  test10240_block_10))))
cert_nodeInterval_4 10240 10402
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest03
