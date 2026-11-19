module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0355Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 992
cert_leafTestAt_block_2 992 0 1
cert_leafTestAt_block_2 992 1 2
cert_leafTestAt_block_2 992 2 3
cert_leafTestAt_block_2 992 3 4
cert_leafTestAt_block_2 992 4 5
cert_leafTestAt_block_2 992 5 6
cert_leafTestAt_block_2 992 6 7
cert_leafTestAt_block_2 992 7 8
cert_leafTestAt_block_2 992 8 9
cert_leafTestAt_block_2 992 9 10
cert_leafTestAt_block_2 992 10 11
cert_leafTestAt_block_2 992 11 12
cert_leafTestAt_block_2 992 12 13
cert_leafTestAt_block_2 992 13 14
cert_leafTestAt_block_2 992 14 15
cert_leafTestAt_block_2 992 15 16
cert_leafTestAt_block_2 992 16 17
cert_leafTestAt_block_2 992 17 18
cert_leafTestAt_block_2 992 18 19
cert_leafTestAt_block_2 992 19 20
cert_leafTestAt_block_2 992 20 21
cert_leafTestAt_block_2 992 21 22
cert_leafTestAt_block_2 992 22 23
cert_leafTestAt_block_2 992 23 24
cert_leafTestAt_block_2 992 24 25
cert_leafTestAt_block_2 992 25 26
cert_leafTestAt_block_2 992 26 27
cert_leafTestAt_block_2 992 27 28
cert_leafTestAt_block_2 992 28 29
cert_leafTestAt_block_2 992 29 30
cert_leafTestAt_block_2 992 30 31
cert_leafTestAt_block_2 992 31 32
theorem leafTestAt992_complete : Interval leafTestAt992 0 32 :=
  (interval_append leafTestAt992 0 16 32
  (interval_append leafTestAt992 0 8 16
  (interval_append leafTestAt992 0 4 8
  (interval_append leafTestAt992 0 2 4
  (interval_append leafTestAt992 0 1 2
  leafTestAt992_block_0
  leafTestAt992_block_1)
  (interval_append leafTestAt992 2 3 4
  leafTestAt992_block_2
  leafTestAt992_block_3))
  (interval_append leafTestAt992 4 6 8
  (interval_append leafTestAt992 4 5 6
  leafTestAt992_block_4
  leafTestAt992_block_5)
  (interval_append leafTestAt992 6 7 8
  leafTestAt992_block_6
  leafTestAt992_block_7)))
  (interval_append leafTestAt992 8 12 16
  (interval_append leafTestAt992 8 10 12
  (interval_append leafTestAt992 8 9 10
  leafTestAt992_block_8
  leafTestAt992_block_9)
  (interval_append leafTestAt992 10 11 12
  leafTestAt992_block_10
  leafTestAt992_block_11))
  (interval_append leafTestAt992 12 14 16
  (interval_append leafTestAt992 12 13 14
  leafTestAt992_block_12
  leafTestAt992_block_13)
  (interval_append leafTestAt992 14 15 16
  leafTestAt992_block_14
  leafTestAt992_block_15))))
  (interval_append leafTestAt992 16 24 32
  (interval_append leafTestAt992 16 20 24
  (interval_append leafTestAt992 16 18 20
  (interval_append leafTestAt992 16 17 18
  leafTestAt992_block_16
  leafTestAt992_block_17)
  (interval_append leafTestAt992 18 19 20
  leafTestAt992_block_18
  leafTestAt992_block_19))
  (interval_append leafTestAt992 20 22 24
  (interval_append leafTestAt992 20 21 22
  leafTestAt992_block_20
  leafTestAt992_block_21)
  (interval_append leafTestAt992 22 23 24
  leafTestAt992_block_22
  leafTestAt992_block_23)))
  (interval_append leafTestAt992 24 28 32
  (interval_append leafTestAt992 24 26 28
  (interval_append leafTestAt992 24 25 26
  leafTestAt992_block_24
  leafTestAt992_block_25)
  (interval_append leafTestAt992 26 27 28
  leafTestAt992_block_26
  leafTestAt992_block_27))
  (interval_append leafTestAt992 28 30 32
  (interval_append leafTestAt992 28 29 30
  leafTestAt992_block_28
  leafTestAt992_block_29)
  (interval_append leafTestAt992 30 31 32
  leafTestAt992_block_30
  leafTestAt992_block_31)))))
cert_leafInterval 992 1024
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
