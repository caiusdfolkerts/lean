module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0301Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
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
cert_leafTestAt_block_2 96 23 24
theorem leafTestAt96_complete : Interval leafTestAt96 0 24 :=
  (interval_append leafTestAt96 0 12 24
  (interval_append leafTestAt96 0 6 12
  (interval_append leafTestAt96 0 3 6
  (interval_append leafTestAt96 0 1 3
  leafTestAt96_block_0
  (interval_append leafTestAt96 1 2 3
  leafTestAt96_block_1
  leafTestAt96_block_2))
  (interval_append leafTestAt96 3 4 6
  leafTestAt96_block_3
  (interval_append leafTestAt96 4 5 6
  leafTestAt96_block_4
  leafTestAt96_block_5)))
  (interval_append leafTestAt96 6 9 12
  (interval_append leafTestAt96 6 7 9
  leafTestAt96_block_6
  (interval_append leafTestAt96 7 8 9
  leafTestAt96_block_7
  leafTestAt96_block_8))
  (interval_append leafTestAt96 9 10 12
  leafTestAt96_block_9
  (interval_append leafTestAt96 10 11 12
  leafTestAt96_block_10
  leafTestAt96_block_11))))
  (interval_append leafTestAt96 12 18 24
  (interval_append leafTestAt96 12 15 18
  (interval_append leafTestAt96 12 13 15
  leafTestAt96_block_12
  (interval_append leafTestAt96 13 14 15
  leafTestAt96_block_13
  leafTestAt96_block_14))
  (interval_append leafTestAt96 15 16 18
  leafTestAt96_block_15
  (interval_append leafTestAt96 16 17 18
  leafTestAt96_block_16
  leafTestAt96_block_17)))
  (interval_append leafTestAt96 18 21 24
  (interval_append leafTestAt96 18 19 21
  leafTestAt96_block_18
  (interval_append leafTestAt96 19 20 21
  leafTestAt96_block_19
  leafTestAt96_block_20))
  (interval_append leafTestAt96 21 22 24
  leafTestAt96_block_21
  (interval_append leafTestAt96 22 23 24
  leafTestAt96_block_22
  leafTestAt96_block_23)))))
cert_leafInterval 96 120
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0301
