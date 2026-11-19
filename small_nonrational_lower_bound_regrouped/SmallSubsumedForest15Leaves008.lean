module
prelude
public meta import LowerSchemas.FiniteSmallSubsumedForest
public import SmallSubsumedForest15Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt_2 256
cert_leafTestAt_block_3 256 0 1
cert_leafTestAt_block_3 256 1 2
cert_leafTestAt_block_3 256 2 3
cert_leafTestAt_block_3 256 3 4
cert_leafTestAt_block_3 256 4 5
cert_leafTestAt_block_3 256 5 6
cert_leafTestAt_block_3 256 6 7
cert_leafTestAt_block_3 256 7 8
cert_leafTestAt_block_3 256 8 9
cert_leafTestAt_block_3 256 9 10
cert_leafTestAt_block_3 256 10 11
cert_leafTestAt_block_3 256 11 12
cert_leafTestAt_block_3 256 12 13
cert_leafTestAt_block_3 256 13 14
cert_leafTestAt_block_3 256 14 15
cert_leafTestAt_block_3 256 15 16
cert_leafTestAt_block_3 256 16 17
cert_leafTestAt_block_3 256 17 18
cert_leafTestAt_block_3 256 18 19
cert_leafTestAt_block_3 256 19 20
cert_leafTestAt_block_3 256 20 21
cert_leafTestAt_block_3 256 21 22
cert_leafTestAt_block_3 256 22 23
cert_leafTestAt_block_3 256 23 24
cert_leafTestAt_block_3 256 24 25
cert_leafTestAt_block_3 256 25 26
cert_leafTestAt_block_3 256 26 27
cert_leafTestAt_block_3 256 27 28
cert_leafTestAt_block_3 256 28 29
cert_leafTestAt_block_3 256 29 30
cert_leafTestAt_block_3 256 30 31
cert_leafTestAt_block_3 256 31 32
theorem leafTestAt256_complete : Interval leafTestAt256 0 32 :=
  (interval_append leafTestAt256 0 16 32
  (interval_append leafTestAt256 0 8 16
  (interval_append leafTestAt256 0 4 8
  (interval_append leafTestAt256 0 2 4
  (interval_append leafTestAt256 0 1 2
  leafTestAt256_block_0
  leafTestAt256_block_1)
  (interval_append leafTestAt256 2 3 4
  leafTestAt256_block_2
  leafTestAt256_block_3))
  (interval_append leafTestAt256 4 6 8
  (interval_append leafTestAt256 4 5 6
  leafTestAt256_block_4
  leafTestAt256_block_5)
  (interval_append leafTestAt256 6 7 8
  leafTestAt256_block_6
  leafTestAt256_block_7)))
  (interval_append leafTestAt256 8 12 16
  (interval_append leafTestAt256 8 10 12
  (interval_append leafTestAt256 8 9 10
  leafTestAt256_block_8
  leafTestAt256_block_9)
  (interval_append leafTestAt256 10 11 12
  leafTestAt256_block_10
  leafTestAt256_block_11))
  (interval_append leafTestAt256 12 14 16
  (interval_append leafTestAt256 12 13 14
  leafTestAt256_block_12
  leafTestAt256_block_13)
  (interval_append leafTestAt256 14 15 16
  leafTestAt256_block_14
  leafTestAt256_block_15))))
  (interval_append leafTestAt256 16 24 32
  (interval_append leafTestAt256 16 20 24
  (interval_append leafTestAt256 16 18 20
  (interval_append leafTestAt256 16 17 18
  leafTestAt256_block_16
  leafTestAt256_block_17)
  (interval_append leafTestAt256 18 19 20
  leafTestAt256_block_18
  leafTestAt256_block_19))
  (interval_append leafTestAt256 20 22 24
  (interval_append leafTestAt256 20 21 22
  leafTestAt256_block_20
  leafTestAt256_block_21)
  (interval_append leafTestAt256 22 23 24
  leafTestAt256_block_22
  leafTestAt256_block_23)))
  (interval_append leafTestAt256 24 28 32
  (interval_append leafTestAt256 24 26 28
  (interval_append leafTestAt256 24 25 26
  leafTestAt256_block_24
  leafTestAt256_block_25)
  (interval_append leafTestAt256 26 27 28
  leafTestAt256_block_26
  leafTestAt256_block_27))
  (interval_append leafTestAt256 28 30 32
  (interval_append leafTestAt256 28 29 30
  leafTestAt256_block_28
  leafTestAt256_block_29)
  (interval_append leafTestAt256 30 31 32
  leafTestAt256_block_30
  leafTestAt256_block_31)))))
cert_leafInterval_2 256 288
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest15
