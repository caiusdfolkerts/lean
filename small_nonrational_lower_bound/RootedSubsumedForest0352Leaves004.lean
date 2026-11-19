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
cert_leafTestAt_block_2 128 17 18
cert_leafTestAt_block_2 128 18 19
cert_leafTestAt_block_2 128 19 20
cert_leafTestAt_block_2 128 20 21
cert_leafTestAt_block_2 128 21 22
cert_leafTestAt_block_2 128 22 23
cert_leafTestAt_block_2 128 23 24
theorem leafTestAt128_complete : Interval leafTestAt128 0 24 :=
  (interval_append leafTestAt128 0 12 24
  (interval_append leafTestAt128 0 6 12
  (interval_append leafTestAt128 0 3 6
  (interval_append leafTestAt128 0 1 3
  leafTestAt128_block_0
  (interval_append leafTestAt128 1 2 3
  leafTestAt128_block_1
  leafTestAt128_block_2))
  (interval_append leafTestAt128 3 4 6
  leafTestAt128_block_3
  (interval_append leafTestAt128 4 5 6
  leafTestAt128_block_4
  leafTestAt128_block_5)))
  (interval_append leafTestAt128 6 9 12
  (interval_append leafTestAt128 6 7 9
  leafTestAt128_block_6
  (interval_append leafTestAt128 7 8 9
  leafTestAt128_block_7
  leafTestAt128_block_8))
  (interval_append leafTestAt128 9 10 12
  leafTestAt128_block_9
  (interval_append leafTestAt128 10 11 12
  leafTestAt128_block_10
  leafTestAt128_block_11))))
  (interval_append leafTestAt128 12 18 24
  (interval_append leafTestAt128 12 15 18
  (interval_append leafTestAt128 12 13 15
  leafTestAt128_block_12
  (interval_append leafTestAt128 13 14 15
  leafTestAt128_block_13
  leafTestAt128_block_14))
  (interval_append leafTestAt128 15 16 18
  leafTestAt128_block_15
  (interval_append leafTestAt128 16 17 18
  leafTestAt128_block_16
  leafTestAt128_block_17)))
  (interval_append leafTestAt128 18 21 24
  (interval_append leafTestAt128 18 19 21
  leafTestAt128_block_18
  (interval_append leafTestAt128 19 20 21
  leafTestAt128_block_19
  leafTestAt128_block_20))
  (interval_append leafTestAt128 21 22 24
  leafTestAt128_block_21
  (interval_append leafTestAt128 22 23 24
  leafTestAt128_block_22
  leafTestAt128_block_23)))))
cert_leafInterval 128 152
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0352
