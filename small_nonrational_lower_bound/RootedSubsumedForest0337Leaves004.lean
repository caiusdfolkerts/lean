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
cert_leafTestAt 128
cert_leafTestAt_block_2 128 0 1
cert_leafTestAt_block_2 128 1 2
cert_leafTestAt_block_2 128 2 3
cert_leafTestAt_block_2 128 3 4
cert_leafTestAt_block_2 128 4 5
cert_leafTestAt_block_2 128 5 6
cert_leafTestAt_block_2 128 6 7
cert_leafTestAt_block_2 128 7 8
cert_leafTestAt_block_2 128 8 9
cert_leafTestAt_block_2 128 9 10
cert_leafTestAt_block_2 128 10 11
cert_leafTestAt_block_2 128 11 12
cert_leafTestAt_block_2 128 12 13
cert_leafTestAt_block_2 128 13 14
cert_leafTestAt_block_2 128 14 15
cert_leafTestAt_block_2 128 15 16
cert_leafTestAt_block_2 128 16 17
theorem leafTestAt128_complete : Interval leafTestAt128 0 17 :=
  (interval_append leafTestAt128 0 8 17
  (interval_append leafTestAt128 0 4 8
  (interval_append leafTestAt128 0 2 4
  (interval_append leafTestAt128 0 1 2
  leafTestAt128_block_0
  leafTestAt128_block_1)
  (interval_append leafTestAt128 2 3 4
  leafTestAt128_block_2
  leafTestAt128_block_3))
  (interval_append leafTestAt128 4 6 8
  (interval_append leafTestAt128 4 5 6
  leafTestAt128_block_4
  leafTestAt128_block_5)
  (interval_append leafTestAt128 6 7 8
  leafTestAt128_block_6
  leafTestAt128_block_7)))
  (interval_append leafTestAt128 8 12 17
  (interval_append leafTestAt128 8 10 12
  (interval_append leafTestAt128 8 9 10
  leafTestAt128_block_8
  leafTestAt128_block_9)
  (interval_append leafTestAt128 10 11 12
  leafTestAt128_block_10
  leafTestAt128_block_11))
  (interval_append leafTestAt128 12 14 17
  (interval_append leafTestAt128 12 13 14
  leafTestAt128_block_12
  leafTestAt128_block_13)
  (interval_append leafTestAt128 14 15 17
  leafTestAt128_block_14
  (interval_append leafTestAt128 15 16 17
  leafTestAt128_block_15
  leafTestAt128_block_16)))))
cert_leafInterval 128 145
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0337
