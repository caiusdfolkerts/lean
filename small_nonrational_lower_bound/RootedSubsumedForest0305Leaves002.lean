module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0305Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0305
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 64
cert_leafTestAt_block_2 64 0 1
cert_leafTestAt_block_2 64 1 2
cert_leafTestAt_block_2 64 2 3
cert_leafTestAt_block_2 64 3 4
cert_leafTestAt_block_2 64 4 5
cert_leafTestAt_block_2 64 5 6
cert_leafTestAt_block_2 64 6 7
cert_leafTestAt_block_2 64 7 8
cert_leafTestAt_block_2 64 8 9
cert_leafTestAt_block_2 64 9 10
cert_leafTestAt_block_2 64 10 11
cert_leafTestAt_block_2 64 11 12
cert_leafTestAt_block_2 64 12 13
cert_leafTestAt_block_2 64 13 14
cert_leafTestAt_block_2 64 14 15
cert_leafTestAt_block_2 64 15 16
cert_leafTestAt_block_2 64 16 17
cert_leafTestAt_block_2 64 17 18
cert_leafTestAt_block_2 64 18 19
cert_leafTestAt_block_2 64 19 20
cert_leafTestAt_block_2 64 20 21
cert_leafTestAt_block_2 64 21 22
cert_leafTestAt_block_2 64 22 23
cert_leafTestAt_block_2 64 23 24
cert_leafTestAt_block_2 64 24 25
cert_leafTestAt_block_2 64 25 26
cert_leafTestAt_block_2 64 26 27
cert_leafTestAt_block_2 64 27 28
cert_leafTestAt_block_2 64 28 29
theorem leafTestAt64_complete : Interval leafTestAt64 0 29 :=
  (interval_append leafTestAt64 0 14 29
  (interval_append leafTestAt64 0 7 14
  (interval_append leafTestAt64 0 3 7
  (interval_append leafTestAt64 0 1 3
  leafTestAt64_block_0
  (interval_append leafTestAt64 1 2 3
  leafTestAt64_block_1
  leafTestAt64_block_2))
  (interval_append leafTestAt64 3 5 7
  (interval_append leafTestAt64 3 4 5
  leafTestAt64_block_3
  leafTestAt64_block_4)
  (interval_append leafTestAt64 5 6 7
  leafTestAt64_block_5
  leafTestAt64_block_6)))
  (interval_append leafTestAt64 7 10 14
  (interval_append leafTestAt64 7 8 10
  leafTestAt64_block_7
  (interval_append leafTestAt64 8 9 10
  leafTestAt64_block_8
  leafTestAt64_block_9))
  (interval_append leafTestAt64 10 12 14
  (interval_append leafTestAt64 10 11 12
  leafTestAt64_block_10
  leafTestAt64_block_11)
  (interval_append leafTestAt64 12 13 14
  leafTestAt64_block_12
  leafTestAt64_block_13))))
  (interval_append leafTestAt64 14 21 29
  (interval_append leafTestAt64 14 17 21
  (interval_append leafTestAt64 14 15 17
  leafTestAt64_block_14
  (interval_append leafTestAt64 15 16 17
  leafTestAt64_block_15
  leafTestAt64_block_16))
  (interval_append leafTestAt64 17 19 21
  (interval_append leafTestAt64 17 18 19
  leafTestAt64_block_17
  leafTestAt64_block_18)
  (interval_append leafTestAt64 19 20 21
  leafTestAt64_block_19
  leafTestAt64_block_20)))
  (interval_append leafTestAt64 21 25 29
  (interval_append leafTestAt64 21 23 25
  (interval_append leafTestAt64 21 22 23
  leafTestAt64_block_21
  leafTestAt64_block_22)
  (interval_append leafTestAt64 23 24 25
  leafTestAt64_block_23
  leafTestAt64_block_24))
  (interval_append leafTestAt64 25 27 29
  (interval_append leafTestAt64 25 26 27
  leafTestAt64_block_25
  leafTestAt64_block_26)
  (interval_append leafTestAt64 27 28 29
  leafTestAt64_block_27
  leafTestAt64_block_28)))))
cert_leafInterval 64 93
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0305
