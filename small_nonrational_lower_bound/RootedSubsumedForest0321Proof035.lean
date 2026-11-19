module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0321Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0321
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_test_11 22400
cert_test_block_3 22400 0 0 16 16
cert_test_block_3 22400 1 16 32 16
cert_test_block_3 22400 2 32 48 16
cert_test_block_3 22400 3 48 64 16
cert_test_block_3 22400 4 64 80 16
cert_test_block_3 22400 5 80 96 16
cert_test_block_3 22400 6 96 112 16
cert_test_block_3 22400 7 112 128 16
cert_test_block_3 22400 8 128 144 16
cert_test_block_3 22400 9 144 160 16
cert_test_block_3 22400 10 160 176 16
cert_test_block_3 22400 11 176 192 16
cert_test_block_3 22400 12 192 208 16
cert_test_block_3 22400 13 208 224 16
cert_test_block_3 22400 14 224 240 16
cert_test_block_3 22400 15 240 256 16
cert_test_block_3 22400 16 256 272 16
cert_test_block_3 22400 17 272 288 16
cert_test_block_3 22400 18 288 304 16
cert_test_block_3 22400 19 304 320 16
cert_test_block_3 22400 20 320 336 16
cert_test_block_3 22400 21 336 337 1
theorem test22400_complete : Interval test22400 0 337 :=
  (interval_append test22400 0 176 337
  (interval_append test22400 0 80 176
  (interval_append test22400 0 32 80
  (interval_append test22400 0 16 32
  test22400_block_0
  test22400_block_1)
  (interval_append test22400 32 48 80
  test22400_block_2
  (interval_append test22400 48 64 80
  test22400_block_3
  test22400_block_4)))
  (interval_append test22400 80 128 176
  (interval_append test22400 80 96 128
  test22400_block_5
  (interval_append test22400 96 112 128
  test22400_block_6
  test22400_block_7))
  (interval_append test22400 128 144 176
  test22400_block_8
  (interval_append test22400 144 160 176
  test22400_block_9
  test22400_block_10))))
  (interval_append test22400 176 256 337
  (interval_append test22400 176 208 256
  (interval_append test22400 176 192 208
  test22400_block_11
  test22400_block_12)
  (interval_append test22400 208 224 256
  test22400_block_13
  (interval_append test22400 224 240 256
  test22400_block_14
  test22400_block_15)))
  (interval_append test22400 256 304 337
  (interval_append test22400 256 272 304
  test22400_block_16
  (interval_append test22400 272 288 304
  test22400_block_17
  test22400_block_18))
  (interval_append test22400 304 320 337
  test22400_block_19
  (interval_append test22400 320 336 337
  test22400_block_20
  test22400_block_21)))))
cert_nodeInterval_3 22400 22737
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0321
