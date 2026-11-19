module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest07Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest07
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt_2 64
cert_leafTestAt_block_3 64 0 1
cert_leafTestAt_block_3 64 1 2
cert_leafTestAt_block_3 64 2 3
cert_leafTestAt_block_3 64 3 4
cert_leafTestAt_block_3 64 4 5
cert_leafTestAt_block_3 64 5 6
cert_leafTestAt_block_3 64 6 7
cert_leafTestAt_block_3 64 7 8
cert_leafTestAt_block_3 64 8 9
cert_leafTestAt_block_3 64 9 10
cert_leafTestAt_block_3 64 10 11
cert_leafTestAt_block_3 64 11 12
cert_leafTestAt_block_3 64 12 13
cert_leafTestAt_block_3 64 13 14
cert_leafTestAt_block_3 64 14 15
cert_leafTestAt_block_3 64 15 16
cert_leafTestAt_block_3 64 16 17
cert_leafTestAt_block_3 64 17 18
cert_leafTestAt_block_3 64 18 19
cert_leafTestAt_block_3 64 19 20
theorem leafTestAt64_complete : Interval leafTestAt64 0 20 :=
  (interval_append leafTestAt64 0 10 20
  (interval_append leafTestAt64 0 5 10
  (interval_append leafTestAt64 0 2 5
  (interval_append leafTestAt64 0 1 2
  leafTestAt64_block_0
  leafTestAt64_block_1)
  (interval_append leafTestAt64 2 3 5
  leafTestAt64_block_2
  (interval_append leafTestAt64 3 4 5
  leafTestAt64_block_3
  leafTestAt64_block_4)))
  (interval_append leafTestAt64 5 7 10
  (interval_append leafTestAt64 5 6 7
  leafTestAt64_block_5
  leafTestAt64_block_6)
  (interval_append leafTestAt64 7 8 10
  leafTestAt64_block_7
  (interval_append leafTestAt64 8 9 10
  leafTestAt64_block_8
  leafTestAt64_block_9))))
  (interval_append leafTestAt64 10 15 20
  (interval_append leafTestAt64 10 12 15
  (interval_append leafTestAt64 10 11 12
  leafTestAt64_block_10
  leafTestAt64_block_11)
  (interval_append leafTestAt64 12 13 15
  leafTestAt64_block_12
  (interval_append leafTestAt64 13 14 15
  leafTestAt64_block_13
  leafTestAt64_block_14)))
  (interval_append leafTestAt64 15 17 20
  (interval_append leafTestAt64 15 16 17
  leafTestAt64_block_15
  leafTestAt64_block_16)
  (interval_append leafTestAt64 17 18 20
  leafTestAt64_block_17
  (interval_append leafTestAt64 18 19 20
  leafTestAt64_block_18
  leafTestAt64_block_19)))))
cert_leafInterval_2 64 84
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest07
