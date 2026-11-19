module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0352Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 15360
cert_test_block_3 15360 0 0 16 16
cert_test_block_3 15360 1 16 32 16
cert_test_block_3 15360 2 32 48 16
cert_test_block_3 15360 3 48 64 16
cert_test_block_3 15360 4 64 80 16
cert_test_block_3 15360 5 80 96 16
cert_test_block_3 15360 6 96 112 16
cert_test_block_3 15360 7 112 128 16
cert_test_block_3 15360 8 128 144 16
cert_test_block_3 15360 9 144 160 16
cert_test_block_3 15360 10 160 176 16
cert_test_block_3 15360 11 176 192 16
cert_test_block_3 15360 12 192 208 16
cert_test_block_3 15360 13 208 224 16
cert_test_block_3 15360 14 224 240 16
cert_test_block_3 15360 15 240 256 16
cert_test_block_3 15360 16 256 272 16
cert_test_block_3 15360 17 272 288 16
cert_test_block_3 15360 18 288 304 16
cert_test_block_3 15360 19 304 320 16
cert_test_block_3 15360 20 320 336 16
cert_test_block_3 15360 21 336 337 1
theorem test15360_complete : Interval test15360 0 337 :=
  (interval_append test15360 0 176 337
  (interval_append test15360 0 80 176
  (interval_append test15360 0 32 80
  (interval_append test15360 0 16 32
  test15360_block_0
  test15360_block_1)
  (interval_append test15360 32 48 80
  test15360_block_2
  (interval_append test15360 48 64 80
  test15360_block_3
  test15360_block_4)))
  (interval_append test15360 80 128 176
  (interval_append test15360 80 96 128
  test15360_block_5
  (interval_append test15360 96 112 128
  test15360_block_6
  test15360_block_7))
  (interval_append test15360 128 144 176
  test15360_block_8
  (interval_append test15360 144 160 176
  test15360_block_9
  test15360_block_10))))
  (interval_append test15360 176 256 337
  (interval_append test15360 176 208 256
  (interval_append test15360 176 192 208
  test15360_block_11
  test15360_block_12)
  (interval_append test15360 208 224 256
  test15360_block_13
  (interval_append test15360 224 240 256
  test15360_block_14
  test15360_block_15)))
  (interval_append test15360 256 304 337
  (interval_append test15360 256 272 304
  test15360_block_16
  (interval_append test15360 272 288 304
  test15360_block_17
  test15360_block_18))
  (interval_append test15360 304 320 337
  test15360_block_19
  (interval_append test15360 320 336 337
  test15360_block_20
  test15360_block_21)))))
cert_nodeInterval_3 15360 15697
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
