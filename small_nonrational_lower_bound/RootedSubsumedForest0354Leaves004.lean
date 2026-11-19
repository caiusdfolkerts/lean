module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0354Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
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
cert_leafTestAt_block_2 128 24 25
cert_leafTestAt_block_2 128 25 26
cert_leafTestAt_block_2 128 26 27
cert_leafTestAt_block_2 128 27 28
theorem leafTestAt128_complete : Interval leafTestAt128 0 28 :=
  (interval_append leafTestAt128 0 14 28
  (interval_append leafTestAt128 0 7 14
  (interval_append leafTestAt128 0 3 7
  (interval_append leafTestAt128 0 1 3
  leafTestAt128_block_0
  (interval_append leafTestAt128 1 2 3
  leafTestAt128_block_1
  leafTestAt128_block_2))
  (interval_append leafTestAt128 3 5 7
  (interval_append leafTestAt128 3 4 5
  leafTestAt128_block_3
  leafTestAt128_block_4)
  (interval_append leafTestAt128 5 6 7
  leafTestAt128_block_5
  leafTestAt128_block_6)))
  (interval_append leafTestAt128 7 10 14
  (interval_append leafTestAt128 7 8 10
  leafTestAt128_block_7
  (interval_append leafTestAt128 8 9 10
  leafTestAt128_block_8
  leafTestAt128_block_9))
  (interval_append leafTestAt128 10 12 14
  (interval_append leafTestAt128 10 11 12
  leafTestAt128_block_10
  leafTestAt128_block_11)
  (interval_append leafTestAt128 12 13 14
  leafTestAt128_block_12
  leafTestAt128_block_13))))
  (interval_append leafTestAt128 14 21 28
  (interval_append leafTestAt128 14 17 21
  (interval_append leafTestAt128 14 15 17
  leafTestAt128_block_14
  (interval_append leafTestAt128 15 16 17
  leafTestAt128_block_15
  leafTestAt128_block_16))
  (interval_append leafTestAt128 17 19 21
  (interval_append leafTestAt128 17 18 19
  leafTestAt128_block_17
  leafTestAt128_block_18)
  (interval_append leafTestAt128 19 20 21
  leafTestAt128_block_19
  leafTestAt128_block_20)))
  (interval_append leafTestAt128 21 24 28
  (interval_append leafTestAt128 21 22 24
  leafTestAt128_block_21
  (interval_append leafTestAt128 22 23 24
  leafTestAt128_block_22
  leafTestAt128_block_23))
  (interval_append leafTestAt128 24 26 28
  (interval_append leafTestAt128 24 25 26
  leafTestAt128_block_24
  leafTestAt128_block_25)
  (interval_append leafTestAt128 26 27 28
  leafTestAt128_block_26
  leafTestAt128_block_27)))))
cert_leafInterval 128 156
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0354
