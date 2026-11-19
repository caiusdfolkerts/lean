module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest18Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt_2 384
cert_leafTestAt_block_3 384 0 1
cert_leafTestAt_block_3 384 1 2
cert_leafTestAt_block_3 384 2 3
cert_leafTestAt_block_3 384 3 4
cert_leafTestAt_block_3 384 4 5
cert_leafTestAt_block_3 384 5 6
cert_leafTestAt_block_3 384 6 7
cert_leafTestAt_block_3 384 7 8
cert_leafTestAt_block_3 384 8 9
cert_leafTestAt_block_3 384 9 10
cert_leafTestAt_block_3 384 10 11
cert_leafTestAt_block_3 384 11 12
cert_leafTestAt_block_3 384 12 13
cert_leafTestAt_block_3 384 13 14
cert_leafTestAt_block_3 384 14 15
cert_leafTestAt_block_3 384 15 16
cert_leafTestAt_block_3 384 16 17
cert_leafTestAt_block_3 384 17 18
cert_leafTestAt_block_3 384 18 19
cert_leafTestAt_block_3 384 19 20
cert_leafTestAt_block_3 384 20 21
cert_leafTestAt_block_3 384 21 22
cert_leafTestAt_block_3 384 22 23
cert_leafTestAt_block_3 384 23 24
cert_leafTestAt_block_3 384 24 25
cert_leafTestAt_block_3 384 25 26
cert_leafTestAt_block_3 384 26 27
cert_leafTestAt_block_3 384 27 28
cert_leafTestAt_block_3 384 28 29
cert_leafTestAt_block_3 384 29 30
cert_leafTestAt_block_3 384 30 31
cert_leafTestAt_block_3 384 31 32
theorem leafTestAt384_complete : Interval leafTestAt384 0 32 :=
  (interval_append leafTestAt384 0 16 32
  (interval_append leafTestAt384 0 8 16
  (interval_append leafTestAt384 0 4 8
  (interval_append leafTestAt384 0 2 4
  (interval_append leafTestAt384 0 1 2
  leafTestAt384_block_0
  leafTestAt384_block_1)
  (interval_append leafTestAt384 2 3 4
  leafTestAt384_block_2
  leafTestAt384_block_3))
  (interval_append leafTestAt384 4 6 8
  (interval_append leafTestAt384 4 5 6
  leafTestAt384_block_4
  leafTestAt384_block_5)
  (interval_append leafTestAt384 6 7 8
  leafTestAt384_block_6
  leafTestAt384_block_7)))
  (interval_append leafTestAt384 8 12 16
  (interval_append leafTestAt384 8 10 12
  (interval_append leafTestAt384 8 9 10
  leafTestAt384_block_8
  leafTestAt384_block_9)
  (interval_append leafTestAt384 10 11 12
  leafTestAt384_block_10
  leafTestAt384_block_11))
  (interval_append leafTestAt384 12 14 16
  (interval_append leafTestAt384 12 13 14
  leafTestAt384_block_12
  leafTestAt384_block_13)
  (interval_append leafTestAt384 14 15 16
  leafTestAt384_block_14
  leafTestAt384_block_15))))
  (interval_append leafTestAt384 16 24 32
  (interval_append leafTestAt384 16 20 24
  (interval_append leafTestAt384 16 18 20
  (interval_append leafTestAt384 16 17 18
  leafTestAt384_block_16
  leafTestAt384_block_17)
  (interval_append leafTestAt384 18 19 20
  leafTestAt384_block_18
  leafTestAt384_block_19))
  (interval_append leafTestAt384 20 22 24
  (interval_append leafTestAt384 20 21 22
  leafTestAt384_block_20
  leafTestAt384_block_21)
  (interval_append leafTestAt384 22 23 24
  leafTestAt384_block_22
  leafTestAt384_block_23)))
  (interval_append leafTestAt384 24 28 32
  (interval_append leafTestAt384 24 26 28
  (interval_append leafTestAt384 24 25 26
  leafTestAt384_block_24
  leafTestAt384_block_25)
  (interval_append leafTestAt384 26 27 28
  leafTestAt384_block_26
  leafTestAt384_block_27))
  (interval_append leafTestAt384 28 30 32
  (interval_append leafTestAt384 28 29 30
  leafTestAt384_block_28
  leafTestAt384_block_29)
  (interval_append leafTestAt384 30 31 32
  leafTestAt384_block_30
  leafTestAt384_block_31)))))
cert_leafInterval_2 384 416
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
