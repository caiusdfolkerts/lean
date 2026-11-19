module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0306Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0306
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 96
cert_leafTestAt_block_2 96 0 1
cert_leafTestAt_block_2 96 1 2
cert_leafTestAt_block_2 96 2 3
cert_leafTestAt_block_2 96 3 4
cert_leafTestAt_block_2 96 4 5
cert_leafTestAt_block_2 96 5 6
cert_leafTestAt_block_2 96 6 7
cert_leafTestAt_block_2 96 7 8
cert_leafTestAt_block_2 96 8 9
cert_leafTestAt_block_2 96 9 10
cert_leafTestAt_block_2 96 10 11
cert_leafTestAt_block_2 96 11 12
cert_leafTestAt_block_2 96 12 13
cert_leafTestAt_block_2 96 13 14
cert_leafTestAt_block_2 96 14 15
cert_leafTestAt_block_2 96 15 16
cert_leafTestAt_block_2 96 16 17
cert_leafTestAt_block_2 96 17 18
cert_leafTestAt_block_2 96 18 19
cert_leafTestAt_block_2 96 19 20
cert_leafTestAt_block_2 96 20 21
cert_leafTestAt_block_2 96 21 22
cert_leafTestAt_block_2 96 22 23
theorem leafTestAt96_complete : Interval leafTestAt96 0 23 :=
  (interval_append leafTestAt96 0 11 23
  (interval_append leafTestAt96 0 5 11
  (interval_append leafTestAt96 0 2 5
  (interval_append leafTestAt96 0 1 2
  leafTestAt96_block_0
  leafTestAt96_block_1)
  (interval_append leafTestAt96 2 3 5
  leafTestAt96_block_2
  (interval_append leafTestAt96 3 4 5
  leafTestAt96_block_3
  leafTestAt96_block_4)))
  (interval_append leafTestAt96 5 8 11
  (interval_append leafTestAt96 5 6 8
  leafTestAt96_block_5
  (interval_append leafTestAt96 6 7 8
  leafTestAt96_block_6
  leafTestAt96_block_7))
  (interval_append leafTestAt96 8 9 11
  leafTestAt96_block_8
  (interval_append leafTestAt96 9 10 11
  leafTestAt96_block_9
  leafTestAt96_block_10))))
  (interval_append leafTestAt96 11 17 23
  (interval_append leafTestAt96 11 14 17
  (interval_append leafTestAt96 11 12 14
  leafTestAt96_block_11
  (interval_append leafTestAt96 12 13 14
  leafTestAt96_block_12
  leafTestAt96_block_13))
  (interval_append leafTestAt96 14 15 17
  leafTestAt96_block_14
  (interval_append leafTestAt96 15 16 17
  leafTestAt96_block_15
  leafTestAt96_block_16)))
  (interval_append leafTestAt96 17 20 23
  (interval_append leafTestAt96 17 18 20
  leafTestAt96_block_17
  (interval_append leafTestAt96 18 19 20
  leafTestAt96_block_18
  leafTestAt96_block_19))
  (interval_append leafTestAt96 20 21 23
  leafTestAt96_block_20
  (interval_append leafTestAt96 21 22 23
  leafTestAt96_block_21
  leafTestAt96_block_22)))))
cert_leafInterval 96 119
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0306
