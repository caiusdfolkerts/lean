module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0337Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 41600
cert_test_block_3 41600 0 0 16 16
cert_test_block_3 41600 1 16 32 16
cert_test_block_3 41600 2 32 48 16
cert_test_block_3 41600 3 48 64 16
cert_test_block_3 41600 4 64 80 16
cert_test_block_3 41600 5 80 96 16
cert_test_block_3 41600 6 96 112 16
cert_test_block_3 41600 7 112 128 16
cert_test_block_3 41600 8 128 144 16
cert_test_block_3 41600 9 144 160 16
cert_test_block_3 41600 10 160 176 16
cert_test_block_3 41600 11 176 192 16
cert_test_block_3 41600 12 192 208 16
cert_test_block_3 41600 13 208 224 16
cert_test_block_3 41600 14 224 240 16
cert_test_block_3 41600 15 240 256 16
cert_test_block_3 41600 16 256 272 16
cert_test_block_3 41600 17 272 288 16
cert_test_block_3 41600 18 288 295 7
theorem test41600_complete : Interval test41600 0 295 :=
  (interval_append test41600 0 144 295
  (interval_append test41600 0 64 144
  (interval_append test41600 0 32 64
  (interval_append test41600 0 16 32
  test41600_block_0
  test41600_block_1)
  (interval_append test41600 32 48 64
  test41600_block_2
  test41600_block_3))
  (interval_append test41600 64 96 144
  (interval_append test41600 64 80 96
  test41600_block_4
  test41600_block_5)
  (interval_append test41600 96 112 144
  test41600_block_6
  (interval_append test41600 112 128 144
  test41600_block_7
  test41600_block_8))))
  (interval_append test41600 144 224 295
  (interval_append test41600 144 176 224
  (interval_append test41600 144 160 176
  test41600_block_9
  test41600_block_10)
  (interval_append test41600 176 192 224
  test41600_block_11
  (interval_append test41600 192 208 224
  test41600_block_12
  test41600_block_13)))
  (interval_append test41600 224 256 295
  (interval_append test41600 224 240 256
  test41600_block_14
  test41600_block_15)
  (interval_append test41600 256 272 295
  test41600_block_16
  (interval_append test41600 272 288 295
  test41600_block_17
  test41600_block_18)))))
cert_nodeInterval_3 41600 41895
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
