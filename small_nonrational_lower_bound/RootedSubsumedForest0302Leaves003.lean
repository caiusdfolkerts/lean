module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0302Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
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
cert_leafTestAt_block_2 96 24 25
cert_leafTestAt_block_2 96 25 26
cert_leafTestAt_block_2 96 26 27
cert_leafTestAt_block_2 96 27 28
cert_leafTestAt_block_2 96 28 29
cert_leafTestAt_block_2 96 29 30
cert_leafTestAt_block_2 96 30 31
cert_leafTestAt_block_2 96 31 32
theorem leafTestAt96_complete : Interval leafTestAt96 0 32 :=
  (interval_append leafTestAt96 0 16 32
  (interval_append leafTestAt96 0 8 16
  (interval_append leafTestAt96 0 4 8
  (interval_append leafTestAt96 0 2 4
  (interval_append leafTestAt96 0 1 2
  leafTestAt96_block_0
  leafTestAt96_block_1)
  (interval_append leafTestAt96 2 3 4
  leafTestAt96_block_2
  leafTestAt96_block_3))
  (interval_append leafTestAt96 4 6 8
  (interval_append leafTestAt96 4 5 6
  leafTestAt96_block_4
  leafTestAt96_block_5)
  (interval_append leafTestAt96 6 7 8
  leafTestAt96_block_6
  leafTestAt96_block_7)))
  (interval_append leafTestAt96 8 12 16
  (interval_append leafTestAt96 8 10 12
  (interval_append leafTestAt96 8 9 10
  leafTestAt96_block_8
  leafTestAt96_block_9)
  (interval_append leafTestAt96 10 11 12
  leafTestAt96_block_10
  leafTestAt96_block_11))
  (interval_append leafTestAt96 12 14 16
  (interval_append leafTestAt96 12 13 14
  leafTestAt96_block_12
  leafTestAt96_block_13)
  (interval_append leafTestAt96 14 15 16
  leafTestAt96_block_14
  leafTestAt96_block_15))))
  (interval_append leafTestAt96 16 24 32
  (interval_append leafTestAt96 16 20 24
  (interval_append leafTestAt96 16 18 20
  (interval_append leafTestAt96 16 17 18
  leafTestAt96_block_16
  leafTestAt96_block_17)
  (interval_append leafTestAt96 18 19 20
  leafTestAt96_block_18
  leafTestAt96_block_19))
  (interval_append leafTestAt96 20 22 24
  (interval_append leafTestAt96 20 21 22
  leafTestAt96_block_20
  leafTestAt96_block_21)
  (interval_append leafTestAt96 22 23 24
  leafTestAt96_block_22
  leafTestAt96_block_23)))
  (interval_append leafTestAt96 24 28 32
  (interval_append leafTestAt96 24 26 28
  (interval_append leafTestAt96 24 25 26
  leafTestAt96_block_24
  leafTestAt96_block_25)
  (interval_append leafTestAt96 26 27 28
  leafTestAt96_block_26
  leafTestAt96_block_27))
  (interval_append leafTestAt96 28 30 32
  (interval_append leafTestAt96 28 29 30
  leafTestAt96_block_28
  leafTestAt96_block_29)
  (interval_append leafTestAt96 30 31 32
  leafTestAt96_block_30
  leafTestAt96_block_31)))))
cert_leafInterval 96 128
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0302
