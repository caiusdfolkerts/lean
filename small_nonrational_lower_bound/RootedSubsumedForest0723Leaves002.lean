module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0723Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0723
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
cert_leafTestAt_block_2 64 29 30
cert_leafTestAt_block_2 64 30 31
cert_leafTestAt_block_2 64 31 32
theorem leafTestAt64_complete : Interval leafTestAt64 0 32 :=
  (interval_append leafTestAt64 0 16 32
  (interval_append leafTestAt64 0 8 16
  (interval_append leafTestAt64 0 4 8
  (interval_append leafTestAt64 0 2 4
  (interval_append leafTestAt64 0 1 2
  leafTestAt64_block_0
  leafTestAt64_block_1)
  (interval_append leafTestAt64 2 3 4
  leafTestAt64_block_2
  leafTestAt64_block_3))
  (interval_append leafTestAt64 4 6 8
  (interval_append leafTestAt64 4 5 6
  leafTestAt64_block_4
  leafTestAt64_block_5)
  (interval_append leafTestAt64 6 7 8
  leafTestAt64_block_6
  leafTestAt64_block_7)))
  (interval_append leafTestAt64 8 12 16
  (interval_append leafTestAt64 8 10 12
  (interval_append leafTestAt64 8 9 10
  leafTestAt64_block_8
  leafTestAt64_block_9)
  (interval_append leafTestAt64 10 11 12
  leafTestAt64_block_10
  leafTestAt64_block_11))
  (interval_append leafTestAt64 12 14 16
  (interval_append leafTestAt64 12 13 14
  leafTestAt64_block_12
  leafTestAt64_block_13)
  (interval_append leafTestAt64 14 15 16
  leafTestAt64_block_14
  leafTestAt64_block_15))))
  (interval_append leafTestAt64 16 24 32
  (interval_append leafTestAt64 16 20 24
  (interval_append leafTestAt64 16 18 20
  (interval_append leafTestAt64 16 17 18
  leafTestAt64_block_16
  leafTestAt64_block_17)
  (interval_append leafTestAt64 18 19 20
  leafTestAt64_block_18
  leafTestAt64_block_19))
  (interval_append leafTestAt64 20 22 24
  (interval_append leafTestAt64 20 21 22
  leafTestAt64_block_20
  leafTestAt64_block_21)
  (interval_append leafTestAt64 22 23 24
  leafTestAt64_block_22
  leafTestAt64_block_23)))
  (interval_append leafTestAt64 24 28 32
  (interval_append leafTestAt64 24 26 28
  (interval_append leafTestAt64 24 25 26
  leafTestAt64_block_24
  leafTestAt64_block_25)
  (interval_append leafTestAt64 26 27 28
  leafTestAt64_block_26
  leafTestAt64_block_27))
  (interval_append leafTestAt64 28 30 32
  (interval_append leafTestAt64 28 29 30
  leafTestAt64_block_28
  leafTestAt64_block_29)
  (interval_append leafTestAt64 30 31 32
  leafTestAt64_block_30
  leafTestAt64_block_31)))))
cert_leafInterval 64 96
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0723
