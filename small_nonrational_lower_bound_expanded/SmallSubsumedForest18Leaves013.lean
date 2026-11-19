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
cert_leafTestAt_2 416
cert_leafTestAt_block_3 416 0 1
cert_leafTestAt_block_3 416 1 2
cert_leafTestAt_block_3 416 2 3
cert_leafTestAt_block_3 416 3 4
cert_leafTestAt_block_3 416 4 5
cert_leafTestAt_block_3 416 5 6
cert_leafTestAt_block_3 416 6 7
cert_leafTestAt_block_3 416 7 8
cert_leafTestAt_block_3 416 8 9
cert_leafTestAt_block_3 416 9 10
cert_leafTestAt_block_3 416 10 11
cert_leafTestAt_block_3 416 11 12
cert_leafTestAt_block_3 416 12 13
cert_leafTestAt_block_3 416 13 14
cert_leafTestAt_block_3 416 14 15
cert_leafTestAt_block_3 416 15 16
theorem leafTestAt416_complete : Interval leafTestAt416 0 16 :=
  (interval_append leafTestAt416 0 8 16
  (interval_append leafTestAt416 0 4 8
  (interval_append leafTestAt416 0 2 4
  (interval_append leafTestAt416 0 1 2
  leafTestAt416_block_0
  leafTestAt416_block_1)
  (interval_append leafTestAt416 2 3 4
  leafTestAt416_block_2
  leafTestAt416_block_3))
  (interval_append leafTestAt416 4 6 8
  (interval_append leafTestAt416 4 5 6
  leafTestAt416_block_4
  leafTestAt416_block_5)
  (interval_append leafTestAt416 6 7 8
  leafTestAt416_block_6
  leafTestAt416_block_7)))
  (interval_append leafTestAt416 8 12 16
  (interval_append leafTestAt416 8 10 12
  (interval_append leafTestAt416 8 9 10
  leafTestAt416_block_8
  leafTestAt416_block_9)
  (interval_append leafTestAt416 10 11 12
  leafTestAt416_block_10
  leafTestAt416_block_11))
  (interval_append leafTestAt416 12 14 16
  (interval_append leafTestAt416 12 13 14
  leafTestAt416_block_12
  leafTestAt416_block_13)
  (interval_append leafTestAt416 14 15 16
  leafTestAt416_block_14
  leafTestAt416_block_15))))
cert_leafInterval_2 416 432
end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest18
