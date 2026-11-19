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
cert_leafTestAt_2 128
cert_leafTestAt_block_3 128 0 1
cert_leafTestAt_block_3 128 1 2
cert_leafTestAt_block_3 128 2 3
cert_leafTestAt_block_3 128 3 4
cert_leafTestAt_block_3 128 4 5
cert_leafTestAt_block_3 128 5 6
cert_leafTestAt_block_3 128 6 7
cert_leafTestAt_block_3 128 7 8
cert_leafTestAt_block_3 128 8 9
cert_leafTestAt_block_3 128 9 10
cert_leafTestAt_block_3 128 10 11
cert_leafTestAt_block_3 128 11 12
cert_leafTestAt_block_3 128 12 13
cert_leafTestAt_block_3 128 13 14
cert_leafTestAt_block_3 128 14 15
cert_leafTestAt_block_3 128 15 16
cert_leafTestAt_block_3 128 16 17
cert_leafTestAt_block_3 128 17 18
cert_leafTestAt_block_3 128 18 19
cert_leafTestAt_block_3 128 19 20
cert_leafTestAt_block_3 128 20 21
cert_leafTestAt_block_3 128 21 22
cert_leafTestAt_block_3 128 22 23
cert_leafTestAt_block_3 128 23 24
cert_leafTestAt_block_3 128 24 25
cert_leafTestAt_block_3 128 25 26
cert_leafTestAt_block_3 128 26 27
cert_leafTestAt_block_3 128 27 28
cert_leafTestAt_block_3 128 28 29
cert_leafTestAt_block_3 128 29 30
cert_leafTestAt_block_3 128 30 31
cert_leafTestAt_block_3 128 31 32
theorem leafTestAt128_complete : Interval leafTestAt128 0 32 :=
  (interval_append leafTestAt128 0 16 32
  (interval_append leafTestAt128 0 8 16
  (interval_append leafTestAt128 0 4 8
  (interval_append leafTestAt128 0 2 4
  (interval_append leafTestAt128 0 1 2
  leafTestAt128_block_0
  leafTestAt128_block_1)
  (interval_append leafTestAt128 2 3 4
  leafTestAt128_block_2
  leafTestAt128_block_3))
  (interval_append leafTestAt128 4 6 8
  (interval_append leafTestAt128 4 5 6
  leafTestAt128_block_4
  leafTestAt128_block_5)
  (interval_append leafTestAt128 6 7 8
  leafTestAt128_block_6
  leafTestAt128_block_7)))
  (interval_append leafTestAt128 8 12 16
  (interval_append leafTestAt128 8 10 12
  (interval_append leafTestAt128 8 9 10
  leafTestAt128_block_8
  leafTestAt128_block_9)
  (interval_append leafTestAt128 10 11 12
  leafTestAt128_block_10
  leafTestAt128_block_11))
  (interval_append leafTestAt128 12 14 16
  (interval_append leafTestAt128 12 13 14
  leafTestAt128_block_12
  leafTestAt128_block_13)
  (interval_append leafTestAt128 14 15 16
  leafTestAt128_block_14
  leafTestAt128_block_15))))
  (interval_append leafTestAt128 16 24 32
  (interval_append leafTestAt128 16 20 24
  (interval_append leafTestAt128 16 18 20
  (interval_append leafTestAt128 16 17 18
  leafTestAt128_block_16
  leafTestAt128_block_17)
  (interval_append leafTestAt128 18 19 20
  leafTestAt128_block_18
  leafTestAt128_block_19))
  (interval_append leafTestAt128 20 22 24
  (interval_append leafTestAt128 20 21 22
  leafTestAt128_block_20
  leafTestAt128_block_21)
  (interval_append leafTestAt128 22 23 24
  leafTestAt128_block_22
  leafTestAt128_block_23)))
  (interval_append leafTestAt128 24 28 32
  (interval_append leafTestAt128 24 26 28
  (interval_append leafTestAt128 24 25 26
  leafTestAt128_block_24
  leafTestAt128_block_25)
  (interval_append leafTestAt128 26 27 28
  leafTestAt128_block_26
  leafTestAt128_block_27))
  (interval_append leafTestAt128 28 30 32
  (interval_append leafTestAt128 28 29 30
  leafTestAt128_block_28
  leafTestAt128_block_29)
  (interval_append leafTestAt128 30 31 32
  leafTestAt128_block_30
  leafTestAt128_block_31)))))
cert_leafInterval_2 128 160
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
