module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0708Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1536
cert_leafTestAt_block_2 1536 0 1
cert_leafTestAt_block_2 1536 1 2
cert_leafTestAt_block_2 1536 2 3
cert_leafTestAt_block_2 1536 3 4
cert_leafTestAt_block_2 1536 4 5
cert_leafTestAt_block_2 1536 5 6
cert_leafTestAt_block_2 1536 6 7
cert_leafTestAt_block_2 1536 7 8
cert_leafTestAt_block_2 1536 8 9
cert_leafTestAt_block_2 1536 9 10
cert_leafTestAt_block_2 1536 10 11
cert_leafTestAt_block_2 1536 11 12
cert_leafTestAt_block_2 1536 12 13
cert_leafTestAt_block_2 1536 13 14
cert_leafTestAt_block_2 1536 14 15
cert_leafTestAt_block_2 1536 15 16
cert_leafTestAt_block_2 1536 16 17
cert_leafTestAt_block_2 1536 17 18
cert_leafTestAt_block_2 1536 18 19
cert_leafTestAt_block_2 1536 19 20
cert_leafTestAt_block_2 1536 20 21
cert_leafTestAt_block_2 1536 21 22
cert_leafTestAt_block_2 1536 22 23
cert_leafTestAt_block_2 1536 23 24
cert_leafTestAt_block_2 1536 24 25
cert_leafTestAt_block_2 1536 25 26
cert_leafTestAt_block_2 1536 26 27
cert_leafTestAt_block_2 1536 27 28
cert_leafTestAt_block_2 1536 28 29
cert_leafTestAt_block_2 1536 29 30
cert_leafTestAt_block_2 1536 30 31
cert_leafTestAt_block_2 1536 31 32
theorem leafTestAt1536_complete : Interval leafTestAt1536 0 32 :=
  (interval_append leafTestAt1536 0 16 32
  (interval_append leafTestAt1536 0 8 16
  (interval_append leafTestAt1536 0 4 8
  (interval_append leafTestAt1536 0 2 4
  (interval_append leafTestAt1536 0 1 2
  leafTestAt1536_block_0
  leafTestAt1536_block_1)
  (interval_append leafTestAt1536 2 3 4
  leafTestAt1536_block_2
  leafTestAt1536_block_3))
  (interval_append leafTestAt1536 4 6 8
  (interval_append leafTestAt1536 4 5 6
  leafTestAt1536_block_4
  leafTestAt1536_block_5)
  (interval_append leafTestAt1536 6 7 8
  leafTestAt1536_block_6
  leafTestAt1536_block_7)))
  (interval_append leafTestAt1536 8 12 16
  (interval_append leafTestAt1536 8 10 12
  (interval_append leafTestAt1536 8 9 10
  leafTestAt1536_block_8
  leafTestAt1536_block_9)
  (interval_append leafTestAt1536 10 11 12
  leafTestAt1536_block_10
  leafTestAt1536_block_11))
  (interval_append leafTestAt1536 12 14 16
  (interval_append leafTestAt1536 12 13 14
  leafTestAt1536_block_12
  leafTestAt1536_block_13)
  (interval_append leafTestAt1536 14 15 16
  leafTestAt1536_block_14
  leafTestAt1536_block_15))))
  (interval_append leafTestAt1536 16 24 32
  (interval_append leafTestAt1536 16 20 24
  (interval_append leafTestAt1536 16 18 20
  (interval_append leafTestAt1536 16 17 18
  leafTestAt1536_block_16
  leafTestAt1536_block_17)
  (interval_append leafTestAt1536 18 19 20
  leafTestAt1536_block_18
  leafTestAt1536_block_19))
  (interval_append leafTestAt1536 20 22 24
  (interval_append leafTestAt1536 20 21 22
  leafTestAt1536_block_20
  leafTestAt1536_block_21)
  (interval_append leafTestAt1536 22 23 24
  leafTestAt1536_block_22
  leafTestAt1536_block_23)))
  (interval_append leafTestAt1536 24 28 32
  (interval_append leafTestAt1536 24 26 28
  (interval_append leafTestAt1536 24 25 26
  leafTestAt1536_block_24
  leafTestAt1536_block_25)
  (interval_append leafTestAt1536 26 27 28
  leafTestAt1536_block_26
  leafTestAt1536_block_27))
  (interval_append leafTestAt1536 28 30 32
  (interval_append leafTestAt1536 28 29 30
  leafTestAt1536_block_28
  leafTestAt1536_block_29)
  (interval_append leafTestAt1536 30 31 32
  leafTestAt1536_block_30
  leafTestAt1536_block_31)))))
cert_leafInterval 1536 1568
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1568
cert_leafTestAt_block_2 1568 0 1
cert_leafTestAt_block_2 1568 1 2
cert_leafTestAt_block_2 1568 2 3
cert_leafTestAt_block_2 1568 3 4
cert_leafTestAt_block_2 1568 4 5
cert_leafTestAt_block_2 1568 5 6
cert_leafTestAt_block_2 1568 6 7
cert_leafTestAt_block_2 1568 7 8
cert_leafTestAt_block_2 1568 8 9
cert_leafTestAt_block_2 1568 9 10
cert_leafTestAt_block_2 1568 10 11
cert_leafTestAt_block_2 1568 11 12
cert_leafTestAt_block_2 1568 12 13
cert_leafTestAt_block_2 1568 13 14
cert_leafTestAt_block_2 1568 14 15
cert_leafTestAt_block_2 1568 15 16
cert_leafTestAt_block_2 1568 16 17
cert_leafTestAt_block_2 1568 17 18
cert_leafTestAt_block_2 1568 18 19
cert_leafTestAt_block_2 1568 19 20
cert_leafTestAt_block_2 1568 20 21
cert_leafTestAt_block_2 1568 21 22
cert_leafTestAt_block_2 1568 22 23
cert_leafTestAt_block_2 1568 23 24
cert_leafTestAt_block_2 1568 24 25
cert_leafTestAt_block_2 1568 25 26
cert_leafTestAt_block_2 1568 26 27
cert_leafTestAt_block_2 1568 27 28
cert_leafTestAt_block_2 1568 28 29
cert_leafTestAt_block_2 1568 29 30
cert_leafTestAt_block_2 1568 30 31
cert_leafTestAt_block_2 1568 31 32
theorem leafTestAt1568_complete : Interval leafTestAt1568 0 32 :=
  (interval_append leafTestAt1568 0 16 32
  (interval_append leafTestAt1568 0 8 16
  (interval_append leafTestAt1568 0 4 8
  (interval_append leafTestAt1568 0 2 4
  (interval_append leafTestAt1568 0 1 2
  leafTestAt1568_block_0
  leafTestAt1568_block_1)
  (interval_append leafTestAt1568 2 3 4
  leafTestAt1568_block_2
  leafTestAt1568_block_3))
  (interval_append leafTestAt1568 4 6 8
  (interval_append leafTestAt1568 4 5 6
  leafTestAt1568_block_4
  leafTestAt1568_block_5)
  (interval_append leafTestAt1568 6 7 8
  leafTestAt1568_block_6
  leafTestAt1568_block_7)))
  (interval_append leafTestAt1568 8 12 16
  (interval_append leafTestAt1568 8 10 12
  (interval_append leafTestAt1568 8 9 10
  leafTestAt1568_block_8
  leafTestAt1568_block_9)
  (interval_append leafTestAt1568 10 11 12
  leafTestAt1568_block_10
  leafTestAt1568_block_11))
  (interval_append leafTestAt1568 12 14 16
  (interval_append leafTestAt1568 12 13 14
  leafTestAt1568_block_12
  leafTestAt1568_block_13)
  (interval_append leafTestAt1568 14 15 16
  leafTestAt1568_block_14
  leafTestAt1568_block_15))))
  (interval_append leafTestAt1568 16 24 32
  (interval_append leafTestAt1568 16 20 24
  (interval_append leafTestAt1568 16 18 20
  (interval_append leafTestAt1568 16 17 18
  leafTestAt1568_block_16
  leafTestAt1568_block_17)
  (interval_append leafTestAt1568 18 19 20
  leafTestAt1568_block_18
  leafTestAt1568_block_19))
  (interval_append leafTestAt1568 20 22 24
  (interval_append leafTestAt1568 20 21 22
  leafTestAt1568_block_20
  leafTestAt1568_block_21)
  (interval_append leafTestAt1568 22 23 24
  leafTestAt1568_block_22
  leafTestAt1568_block_23)))
  (interval_append leafTestAt1568 24 28 32
  (interval_append leafTestAt1568 24 26 28
  (interval_append leafTestAt1568 24 25 26
  leafTestAt1568_block_24
  leafTestAt1568_block_25)
  (interval_append leafTestAt1568 26 27 28
  leafTestAt1568_block_26
  leafTestAt1568_block_27))
  (interval_append leafTestAt1568 28 30 32
  (interval_append leafTestAt1568 28 29 30
  leafTestAt1568_block_28
  leafTestAt1568_block_29)
  (interval_append leafTestAt1568 30 31 32
  leafTestAt1568_block_30
  leafTestAt1568_block_31)))))
cert_leafInterval 1568 1600
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1600
cert_leafTestAt_block_2 1600 0 1
cert_leafTestAt_block_2 1600 1 2
cert_leafTestAt_block_2 1600 2 3
cert_leafTestAt_block_2 1600 3 4
cert_leafTestAt_block_2 1600 4 5
cert_leafTestAt_block_2 1600 5 6
cert_leafTestAt_block_2 1600 6 7
cert_leafTestAt_block_2 1600 7 8
cert_leafTestAt_block_2 1600 8 9
cert_leafTestAt_block_2 1600 9 10
cert_leafTestAt_block_2 1600 10 11
cert_leafTestAt_block_2 1600 11 12
cert_leafTestAt_block_2 1600 12 13
cert_leafTestAt_block_2 1600 13 14
cert_leafTestAt_block_2 1600 14 15
cert_leafTestAt_block_2 1600 15 16
cert_leafTestAt_block_2 1600 16 17
cert_leafTestAt_block_2 1600 17 18
cert_leafTestAt_block_2 1600 18 19
cert_leafTestAt_block_2 1600 19 20
cert_leafTestAt_block_2 1600 20 21
cert_leafTestAt_block_2 1600 21 22
cert_leafTestAt_block_2 1600 22 23
cert_leafTestAt_block_2 1600 23 24
cert_leafTestAt_block_2 1600 24 25
cert_leafTestAt_block_2 1600 25 26
cert_leafTestAt_block_2 1600 26 27
cert_leafTestAt_block_2 1600 27 28
cert_leafTestAt_block_2 1600 28 29
cert_leafTestAt_block_2 1600 29 30
cert_leafTestAt_block_2 1600 30 31
theorem leafTestAt1600_complete : Interval leafTestAt1600 0 31 :=
  (interval_append leafTestAt1600 0 15 31
  (interval_append leafTestAt1600 0 7 15
  (interval_append leafTestAt1600 0 3 7
  (interval_append leafTestAt1600 0 1 3
  leafTestAt1600_block_0
  (interval_append leafTestAt1600 1 2 3
  leafTestAt1600_block_1
  leafTestAt1600_block_2))
  (interval_append leafTestAt1600 3 5 7
  (interval_append leafTestAt1600 3 4 5
  leafTestAt1600_block_3
  leafTestAt1600_block_4)
  (interval_append leafTestAt1600 5 6 7
  leafTestAt1600_block_5
  leafTestAt1600_block_6)))
  (interval_append leafTestAt1600 7 11 15
  (interval_append leafTestAt1600 7 9 11
  (interval_append leafTestAt1600 7 8 9
  leafTestAt1600_block_7
  leafTestAt1600_block_8)
  (interval_append leafTestAt1600 9 10 11
  leafTestAt1600_block_9
  leafTestAt1600_block_10))
  (interval_append leafTestAt1600 11 13 15
  (interval_append leafTestAt1600 11 12 13
  leafTestAt1600_block_11
  leafTestAt1600_block_12)
  (interval_append leafTestAt1600 13 14 15
  leafTestAt1600_block_13
  leafTestAt1600_block_14))))
  (interval_append leafTestAt1600 15 23 31
  (interval_append leafTestAt1600 15 19 23
  (interval_append leafTestAt1600 15 17 19
  (interval_append leafTestAt1600 15 16 17
  leafTestAt1600_block_15
  leafTestAt1600_block_16)
  (interval_append leafTestAt1600 17 18 19
  leafTestAt1600_block_17
  leafTestAt1600_block_18))
  (interval_append leafTestAt1600 19 21 23
  (interval_append leafTestAt1600 19 20 21
  leafTestAt1600_block_19
  leafTestAt1600_block_20)
  (interval_append leafTestAt1600 21 22 23
  leafTestAt1600_block_21
  leafTestAt1600_block_22)))
  (interval_append leafTestAt1600 23 27 31
  (interval_append leafTestAt1600 23 25 27
  (interval_append leafTestAt1600 23 24 25
  leafTestAt1600_block_23
  leafTestAt1600_block_24)
  (interval_append leafTestAt1600 25 26 27
  leafTestAt1600_block_25
  leafTestAt1600_block_26))
  (interval_append leafTestAt1600 27 29 31
  (interval_append leafTestAt1600 27 28 29
  leafTestAt1600_block_27
  leafTestAt1600_block_28)
  (interval_append leafTestAt1600 29 30 31
  leafTestAt1600_block_29
  leafTestAt1600_block_30)))))
cert_leafInterval 1600 1631
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0708
end
end
