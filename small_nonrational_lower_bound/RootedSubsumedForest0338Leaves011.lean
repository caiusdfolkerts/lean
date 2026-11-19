module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest
public import RootedSubsumedForest0338Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 352
cert_leafTestAt_block_2 352 0 1
cert_leafTestAt_block_2 352 1 2
cert_leafTestAt_block_2 352 2 3
cert_leafTestAt_block_2 352 3 4
cert_leafTestAt_block_2 352 4 5
cert_leafTestAt_block_2 352 5 6
cert_leafTestAt_block_2 352 6 7
cert_leafTestAt_block_2 352 7 8
cert_leafTestAt_block_2 352 8 9
cert_leafTestAt_block_2 352 9 10
cert_leafTestAt_block_2 352 10 11
cert_leafTestAt_block_2 352 11 12
cert_leafTestAt_block_2 352 12 13
cert_leafTestAt_block_2 352 13 14
cert_leafTestAt_block_2 352 14 15
cert_leafTestAt_block_2 352 15 16
cert_leafTestAt_block_2 352 16 17
cert_leafTestAt_block_2 352 17 18
cert_leafTestAt_block_2 352 18 19
cert_leafTestAt_block_2 352 19 20
cert_leafTestAt_block_2 352 20 21
cert_leafTestAt_block_2 352 21 22
cert_leafTestAt_block_2 352 22 23
cert_leafTestAt_block_2 352 23 24
cert_leafTestAt_block_2 352 24 25
cert_leafTestAt_block_2 352 25 26
cert_leafTestAt_block_2 352 26 27
cert_leafTestAt_block_2 352 27 28
cert_leafTestAt_block_2 352 28 29
cert_leafTestAt_block_2 352 29 30
cert_leafTestAt_block_2 352 30 31
theorem leafTestAt352_complete : Interval leafTestAt352 0 31 :=
  (interval_append leafTestAt352 0 15 31
  (interval_append leafTestAt352 0 7 15
  (interval_append leafTestAt352 0 3 7
  (interval_append leafTestAt352 0 1 3
  leafTestAt352_block_0
  (interval_append leafTestAt352 1 2 3
  leafTestAt352_block_1
  leafTestAt352_block_2))
  (interval_append leafTestAt352 3 5 7
  (interval_append leafTestAt352 3 4 5
  leafTestAt352_block_3
  leafTestAt352_block_4)
  (interval_append leafTestAt352 5 6 7
  leafTestAt352_block_5
  leafTestAt352_block_6)))
  (interval_append leafTestAt352 7 11 15
  (interval_append leafTestAt352 7 9 11
  (interval_append leafTestAt352 7 8 9
  leafTestAt352_block_7
  leafTestAt352_block_8)
  (interval_append leafTestAt352 9 10 11
  leafTestAt352_block_9
  leafTestAt352_block_10))
  (interval_append leafTestAt352 11 13 15
  (interval_append leafTestAt352 11 12 13
  leafTestAt352_block_11
  leafTestAt352_block_12)
  (interval_append leafTestAt352 13 14 15
  leafTestAt352_block_13
  leafTestAt352_block_14))))
  (interval_append leafTestAt352 15 23 31
  (interval_append leafTestAt352 15 19 23
  (interval_append leafTestAt352 15 17 19
  (interval_append leafTestAt352 15 16 17
  leafTestAt352_block_15
  leafTestAt352_block_16)
  (interval_append leafTestAt352 17 18 19
  leafTestAt352_block_17
  leafTestAt352_block_18))
  (interval_append leafTestAt352 19 21 23
  (interval_append leafTestAt352 19 20 21
  leafTestAt352_block_19
  leafTestAt352_block_20)
  (interval_append leafTestAt352 21 22 23
  leafTestAt352_block_21
  leafTestAt352_block_22)))
  (interval_append leafTestAt352 23 27 31
  (interval_append leafTestAt352 23 25 27
  (interval_append leafTestAt352 23 24 25
  leafTestAt352_block_23
  leafTestAt352_block_24)
  (interval_append leafTestAt352 25 26 27
  leafTestAt352_block_25
  leafTestAt352_block_26))
  (interval_append leafTestAt352 27 29 31
  (interval_append leafTestAt352 27 28 29
  leafTestAt352_block_27
  leafTestAt352_block_28)
  (interval_append leafTestAt352 29 30 31
  leafTestAt352_block_29
  leafTestAt352_block_30)))))
cert_leafInterval 352 383
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
