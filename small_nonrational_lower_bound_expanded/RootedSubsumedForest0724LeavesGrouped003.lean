module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0724Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
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
cert_leafTestAt_block_2 1600 31 32
theorem leafTestAt1600_complete : Interval leafTestAt1600 0 32 :=
  (interval_append leafTestAt1600 0 16 32
  (interval_append leafTestAt1600 0 8 16
  (interval_append leafTestAt1600 0 4 8
  (interval_append leafTestAt1600 0 2 4
  (interval_append leafTestAt1600 0 1 2
  leafTestAt1600_block_0
  leafTestAt1600_block_1)
  (interval_append leafTestAt1600 2 3 4
  leafTestAt1600_block_2
  leafTestAt1600_block_3))
  (interval_append leafTestAt1600 4 6 8
  (interval_append leafTestAt1600 4 5 6
  leafTestAt1600_block_4
  leafTestAt1600_block_5)
  (interval_append leafTestAt1600 6 7 8
  leafTestAt1600_block_6
  leafTestAt1600_block_7)))
  (interval_append leafTestAt1600 8 12 16
  (interval_append leafTestAt1600 8 10 12
  (interval_append leafTestAt1600 8 9 10
  leafTestAt1600_block_8
  leafTestAt1600_block_9)
  (interval_append leafTestAt1600 10 11 12
  leafTestAt1600_block_10
  leafTestAt1600_block_11))
  (interval_append leafTestAt1600 12 14 16
  (interval_append leafTestAt1600 12 13 14
  leafTestAt1600_block_12
  leafTestAt1600_block_13)
  (interval_append leafTestAt1600 14 15 16
  leafTestAt1600_block_14
  leafTestAt1600_block_15))))
  (interval_append leafTestAt1600 16 24 32
  (interval_append leafTestAt1600 16 20 24
  (interval_append leafTestAt1600 16 18 20
  (interval_append leafTestAt1600 16 17 18
  leafTestAt1600_block_16
  leafTestAt1600_block_17)
  (interval_append leafTestAt1600 18 19 20
  leafTestAt1600_block_18
  leafTestAt1600_block_19))
  (interval_append leafTestAt1600 20 22 24
  (interval_append leafTestAt1600 20 21 22
  leafTestAt1600_block_20
  leafTestAt1600_block_21)
  (interval_append leafTestAt1600 22 23 24
  leafTestAt1600_block_22
  leafTestAt1600_block_23)))
  (interval_append leafTestAt1600 24 28 32
  (interval_append leafTestAt1600 24 26 28
  (interval_append leafTestAt1600 24 25 26
  leafTestAt1600_block_24
  leafTestAt1600_block_25)
  (interval_append leafTestAt1600 26 27 28
  leafTestAt1600_block_26
  leafTestAt1600_block_27))
  (interval_append leafTestAt1600 28 30 32
  (interval_append leafTestAt1600 28 29 30
  leafTestAt1600_block_28
  leafTestAt1600_block_29)
  (interval_append leafTestAt1600 30 31 32
  leafTestAt1600_block_30
  leafTestAt1600_block_31)))))
cert_leafInterval 1600 1632
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1632
cert_leafTestAt_block_2 1632 0 1
cert_leafTestAt_block_2 1632 1 2
cert_leafTestAt_block_2 1632 2 3
cert_leafTestAt_block_2 1632 3 4
cert_leafTestAt_block_2 1632 4 5
cert_leafTestAt_block_2 1632 5 6
cert_leafTestAt_block_2 1632 6 7
cert_leafTestAt_block_2 1632 7 8
cert_leafTestAt_block_2 1632 8 9
cert_leafTestAt_block_2 1632 9 10
cert_leafTestAt_block_2 1632 10 11
cert_leafTestAt_block_2 1632 11 12
cert_leafTestAt_block_2 1632 12 13
cert_leafTestAt_block_2 1632 13 14
cert_leafTestAt_block_2 1632 14 15
cert_leafTestAt_block_2 1632 15 16
cert_leafTestAt_block_2 1632 16 17
cert_leafTestAt_block_2 1632 17 18
cert_leafTestAt_block_2 1632 18 19
cert_leafTestAt_block_2 1632 19 20
cert_leafTestAt_block_2 1632 20 21
cert_leafTestAt_block_2 1632 21 22
cert_leafTestAt_block_2 1632 22 23
cert_leafTestAt_block_2 1632 23 24
cert_leafTestAt_block_2 1632 24 25
cert_leafTestAt_block_2 1632 25 26
cert_leafTestAt_block_2 1632 26 27
cert_leafTestAt_block_2 1632 27 28
cert_leafTestAt_block_2 1632 28 29
cert_leafTestAt_block_2 1632 29 30
cert_leafTestAt_block_2 1632 30 31
cert_leafTestAt_block_2 1632 31 32
theorem leafTestAt1632_complete : Interval leafTestAt1632 0 32 :=
  (interval_append leafTestAt1632 0 16 32
  (interval_append leafTestAt1632 0 8 16
  (interval_append leafTestAt1632 0 4 8
  (interval_append leafTestAt1632 0 2 4
  (interval_append leafTestAt1632 0 1 2
  leafTestAt1632_block_0
  leafTestAt1632_block_1)
  (interval_append leafTestAt1632 2 3 4
  leafTestAt1632_block_2
  leafTestAt1632_block_3))
  (interval_append leafTestAt1632 4 6 8
  (interval_append leafTestAt1632 4 5 6
  leafTestAt1632_block_4
  leafTestAt1632_block_5)
  (interval_append leafTestAt1632 6 7 8
  leafTestAt1632_block_6
  leafTestAt1632_block_7)))
  (interval_append leafTestAt1632 8 12 16
  (interval_append leafTestAt1632 8 10 12
  (interval_append leafTestAt1632 8 9 10
  leafTestAt1632_block_8
  leafTestAt1632_block_9)
  (interval_append leafTestAt1632 10 11 12
  leafTestAt1632_block_10
  leafTestAt1632_block_11))
  (interval_append leafTestAt1632 12 14 16
  (interval_append leafTestAt1632 12 13 14
  leafTestAt1632_block_12
  leafTestAt1632_block_13)
  (interval_append leafTestAt1632 14 15 16
  leafTestAt1632_block_14
  leafTestAt1632_block_15))))
  (interval_append leafTestAt1632 16 24 32
  (interval_append leafTestAt1632 16 20 24
  (interval_append leafTestAt1632 16 18 20
  (interval_append leafTestAt1632 16 17 18
  leafTestAt1632_block_16
  leafTestAt1632_block_17)
  (interval_append leafTestAt1632 18 19 20
  leafTestAt1632_block_18
  leafTestAt1632_block_19))
  (interval_append leafTestAt1632 20 22 24
  (interval_append leafTestAt1632 20 21 22
  leafTestAt1632_block_20
  leafTestAt1632_block_21)
  (interval_append leafTestAt1632 22 23 24
  leafTestAt1632_block_22
  leafTestAt1632_block_23)))
  (interval_append leafTestAt1632 24 28 32
  (interval_append leafTestAt1632 24 26 28
  (interval_append leafTestAt1632 24 25 26
  leafTestAt1632_block_24
  leafTestAt1632_block_25)
  (interval_append leafTestAt1632 26 27 28
  leafTestAt1632_block_26
  leafTestAt1632_block_27))
  (interval_append leafTestAt1632 28 30 32
  (interval_append leafTestAt1632 28 29 30
  leafTestAt1632_block_28
  leafTestAt1632_block_29)
  (interval_append leafTestAt1632 30 31 32
  leafTestAt1632_block_30
  leafTestAt1632_block_31)))))
cert_leafInterval 1632 1664
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1664
cert_leafTestAt_block_2 1664 0 1
cert_leafTestAt_block_2 1664 1 2
cert_leafTestAt_block_2 1664 2 3
cert_leafTestAt_block_2 1664 3 4
cert_leafTestAt_block_2 1664 4 5
cert_leafTestAt_block_2 1664 5 6
cert_leafTestAt_block_2 1664 6 7
cert_leafTestAt_block_2 1664 7 8
cert_leafTestAt_block_2 1664 8 9
cert_leafTestAt_block_2 1664 9 10
cert_leafTestAt_block_2 1664 10 11
cert_leafTestAt_block_2 1664 11 12
cert_leafTestAt_block_2 1664 12 13
cert_leafTestAt_block_2 1664 13 14
cert_leafTestAt_block_2 1664 14 15
cert_leafTestAt_block_2 1664 15 16
cert_leafTestAt_block_2 1664 16 17
cert_leafTestAt_block_2 1664 17 18
cert_leafTestAt_block_2 1664 18 19
cert_leafTestAt_block_2 1664 19 20
cert_leafTestAt_block_2 1664 20 21
cert_leafTestAt_block_2 1664 21 22
cert_leafTestAt_block_2 1664 22 23
cert_leafTestAt_block_2 1664 23 24
cert_leafTestAt_block_2 1664 24 25
cert_leafTestAt_block_2 1664 25 26
cert_leafTestAt_block_2 1664 26 27
cert_leafTestAt_block_2 1664 27 28
cert_leafTestAt_block_2 1664 28 29
cert_leafTestAt_block_2 1664 29 30
cert_leafTestAt_block_2 1664 30 31
cert_leafTestAt_block_2 1664 31 32
theorem leafTestAt1664_complete : Interval leafTestAt1664 0 32 :=
  (interval_append leafTestAt1664 0 16 32
  (interval_append leafTestAt1664 0 8 16
  (interval_append leafTestAt1664 0 4 8
  (interval_append leafTestAt1664 0 2 4
  (interval_append leafTestAt1664 0 1 2
  leafTestAt1664_block_0
  leafTestAt1664_block_1)
  (interval_append leafTestAt1664 2 3 4
  leafTestAt1664_block_2
  leafTestAt1664_block_3))
  (interval_append leafTestAt1664 4 6 8
  (interval_append leafTestAt1664 4 5 6
  leafTestAt1664_block_4
  leafTestAt1664_block_5)
  (interval_append leafTestAt1664 6 7 8
  leafTestAt1664_block_6
  leafTestAt1664_block_7)))
  (interval_append leafTestAt1664 8 12 16
  (interval_append leafTestAt1664 8 10 12
  (interval_append leafTestAt1664 8 9 10
  leafTestAt1664_block_8
  leafTestAt1664_block_9)
  (interval_append leafTestAt1664 10 11 12
  leafTestAt1664_block_10
  leafTestAt1664_block_11))
  (interval_append leafTestAt1664 12 14 16
  (interval_append leafTestAt1664 12 13 14
  leafTestAt1664_block_12
  leafTestAt1664_block_13)
  (interval_append leafTestAt1664 14 15 16
  leafTestAt1664_block_14
  leafTestAt1664_block_15))))
  (interval_append leafTestAt1664 16 24 32
  (interval_append leafTestAt1664 16 20 24
  (interval_append leafTestAt1664 16 18 20
  (interval_append leafTestAt1664 16 17 18
  leafTestAt1664_block_16
  leafTestAt1664_block_17)
  (interval_append leafTestAt1664 18 19 20
  leafTestAt1664_block_18
  leafTestAt1664_block_19))
  (interval_append leafTestAt1664 20 22 24
  (interval_append leafTestAt1664 20 21 22
  leafTestAt1664_block_20
  leafTestAt1664_block_21)
  (interval_append leafTestAt1664 22 23 24
  leafTestAt1664_block_22
  leafTestAt1664_block_23)))
  (interval_append leafTestAt1664 24 28 32
  (interval_append leafTestAt1664 24 26 28
  (interval_append leafTestAt1664 24 25 26
  leafTestAt1664_block_24
  leafTestAt1664_block_25)
  (interval_append leafTestAt1664 26 27 28
  leafTestAt1664_block_26
  leafTestAt1664_block_27))
  (interval_append leafTestAt1664 28 30 32
  (interval_append leafTestAt1664 28 29 30
  leafTestAt1664_block_28
  leafTestAt1664_block_29)
  (interval_append leafTestAt1664 30 31 32
  leafTestAt1664_block_30
  leafTestAt1664_block_31)))))
cert_leafInterval 1664 1696
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1696
cert_leafTestAt_block_2 1696 0 1
cert_leafTestAt_block_2 1696 1 2
cert_leafTestAt_block_2 1696 2 3
cert_leafTestAt_block_2 1696 3 4
cert_leafTestAt_block_2 1696 4 5
cert_leafTestAt_block_2 1696 5 6
cert_leafTestAt_block_2 1696 6 7
cert_leafTestAt_block_2 1696 7 8
cert_leafTestAt_block_2 1696 8 9
cert_leafTestAt_block_2 1696 9 10
cert_leafTestAt_block_2 1696 10 11
cert_leafTestAt_block_2 1696 11 12
cert_leafTestAt_block_2 1696 12 13
cert_leafTestAt_block_2 1696 13 14
cert_leafTestAt_block_2 1696 14 15
cert_leafTestAt_block_2 1696 15 16
cert_leafTestAt_block_2 1696 16 17
cert_leafTestAt_block_2 1696 17 18
cert_leafTestAt_block_2 1696 18 19
cert_leafTestAt_block_2 1696 19 20
cert_leafTestAt_block_2 1696 20 21
cert_leafTestAt_block_2 1696 21 22
cert_leafTestAt_block_2 1696 22 23
cert_leafTestAt_block_2 1696 23 24
cert_leafTestAt_block_2 1696 24 25
cert_leafTestAt_block_2 1696 25 26
cert_leafTestAt_block_2 1696 26 27
cert_leafTestAt_block_2 1696 27 28
cert_leafTestAt_block_2 1696 28 29
cert_leafTestAt_block_2 1696 29 30
cert_leafTestAt_block_2 1696 30 31
cert_leafTestAt_block_2 1696 31 32
theorem leafTestAt1696_complete : Interval leafTestAt1696 0 32 :=
  (interval_append leafTestAt1696 0 16 32
  (interval_append leafTestAt1696 0 8 16
  (interval_append leafTestAt1696 0 4 8
  (interval_append leafTestAt1696 0 2 4
  (interval_append leafTestAt1696 0 1 2
  leafTestAt1696_block_0
  leafTestAt1696_block_1)
  (interval_append leafTestAt1696 2 3 4
  leafTestAt1696_block_2
  leafTestAt1696_block_3))
  (interval_append leafTestAt1696 4 6 8
  (interval_append leafTestAt1696 4 5 6
  leafTestAt1696_block_4
  leafTestAt1696_block_5)
  (interval_append leafTestAt1696 6 7 8
  leafTestAt1696_block_6
  leafTestAt1696_block_7)))
  (interval_append leafTestAt1696 8 12 16
  (interval_append leafTestAt1696 8 10 12
  (interval_append leafTestAt1696 8 9 10
  leafTestAt1696_block_8
  leafTestAt1696_block_9)
  (interval_append leafTestAt1696 10 11 12
  leafTestAt1696_block_10
  leafTestAt1696_block_11))
  (interval_append leafTestAt1696 12 14 16
  (interval_append leafTestAt1696 12 13 14
  leafTestAt1696_block_12
  leafTestAt1696_block_13)
  (interval_append leafTestAt1696 14 15 16
  leafTestAt1696_block_14
  leafTestAt1696_block_15))))
  (interval_append leafTestAt1696 16 24 32
  (interval_append leafTestAt1696 16 20 24
  (interval_append leafTestAt1696 16 18 20
  (interval_append leafTestAt1696 16 17 18
  leafTestAt1696_block_16
  leafTestAt1696_block_17)
  (interval_append leafTestAt1696 18 19 20
  leafTestAt1696_block_18
  leafTestAt1696_block_19))
  (interval_append leafTestAt1696 20 22 24
  (interval_append leafTestAt1696 20 21 22
  leafTestAt1696_block_20
  leafTestAt1696_block_21)
  (interval_append leafTestAt1696 22 23 24
  leafTestAt1696_block_22
  leafTestAt1696_block_23)))
  (interval_append leafTestAt1696 24 28 32
  (interval_append leafTestAt1696 24 26 28
  (interval_append leafTestAt1696 24 25 26
  leafTestAt1696_block_24
  leafTestAt1696_block_25)
  (interval_append leafTestAt1696 26 27 28
  leafTestAt1696_block_26
  leafTestAt1696_block_27))
  (interval_append leafTestAt1696 28 30 32
  (interval_append leafTestAt1696 28 29 30
  leafTestAt1696_block_28
  leafTestAt1696_block_29)
  (interval_append leafTestAt1696 30 31 32
  leafTestAt1696_block_30
  leafTestAt1696_block_31)))))
cert_leafInterval 1696 1728
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1728
cert_leafTestAt_block_2 1728 0 1
cert_leafTestAt_block_2 1728 1 2
cert_leafTestAt_block_2 1728 2 3
cert_leafTestAt_block_2 1728 3 4
cert_leafTestAt_block_2 1728 4 5
cert_leafTestAt_block_2 1728 5 6
cert_leafTestAt_block_2 1728 6 7
cert_leafTestAt_block_2 1728 7 8
cert_leafTestAt_block_2 1728 8 9
cert_leafTestAt_block_2 1728 9 10
cert_leafTestAt_block_2 1728 10 11
cert_leafTestAt_block_2 1728 11 12
cert_leafTestAt_block_2 1728 12 13
cert_leafTestAt_block_2 1728 13 14
cert_leafTestAt_block_2 1728 14 15
cert_leafTestAt_block_2 1728 15 16
cert_leafTestAt_block_2 1728 16 17
cert_leafTestAt_block_2 1728 17 18
cert_leafTestAt_block_2 1728 18 19
cert_leafTestAt_block_2 1728 19 20
cert_leafTestAt_block_2 1728 20 21
cert_leafTestAt_block_2 1728 21 22
cert_leafTestAt_block_2 1728 22 23
cert_leafTestAt_block_2 1728 23 24
cert_leafTestAt_block_2 1728 24 25
cert_leafTestAt_block_2 1728 25 26
cert_leafTestAt_block_2 1728 26 27
cert_leafTestAt_block_2 1728 27 28
cert_leafTestAt_block_2 1728 28 29
cert_leafTestAt_block_2 1728 29 30
cert_leafTestAt_block_2 1728 30 31
cert_leafTestAt_block_2 1728 31 32
theorem leafTestAt1728_complete : Interval leafTestAt1728 0 32 :=
  (interval_append leafTestAt1728 0 16 32
  (interval_append leafTestAt1728 0 8 16
  (interval_append leafTestAt1728 0 4 8
  (interval_append leafTestAt1728 0 2 4
  (interval_append leafTestAt1728 0 1 2
  leafTestAt1728_block_0
  leafTestAt1728_block_1)
  (interval_append leafTestAt1728 2 3 4
  leafTestAt1728_block_2
  leafTestAt1728_block_3))
  (interval_append leafTestAt1728 4 6 8
  (interval_append leafTestAt1728 4 5 6
  leafTestAt1728_block_4
  leafTestAt1728_block_5)
  (interval_append leafTestAt1728 6 7 8
  leafTestAt1728_block_6
  leafTestAt1728_block_7)))
  (interval_append leafTestAt1728 8 12 16
  (interval_append leafTestAt1728 8 10 12
  (interval_append leafTestAt1728 8 9 10
  leafTestAt1728_block_8
  leafTestAt1728_block_9)
  (interval_append leafTestAt1728 10 11 12
  leafTestAt1728_block_10
  leafTestAt1728_block_11))
  (interval_append leafTestAt1728 12 14 16
  (interval_append leafTestAt1728 12 13 14
  leafTestAt1728_block_12
  leafTestAt1728_block_13)
  (interval_append leafTestAt1728 14 15 16
  leafTestAt1728_block_14
  leafTestAt1728_block_15))))
  (interval_append leafTestAt1728 16 24 32
  (interval_append leafTestAt1728 16 20 24
  (interval_append leafTestAt1728 16 18 20
  (interval_append leafTestAt1728 16 17 18
  leafTestAt1728_block_16
  leafTestAt1728_block_17)
  (interval_append leafTestAt1728 18 19 20
  leafTestAt1728_block_18
  leafTestAt1728_block_19))
  (interval_append leafTestAt1728 20 22 24
  (interval_append leafTestAt1728 20 21 22
  leafTestAt1728_block_20
  leafTestAt1728_block_21)
  (interval_append leafTestAt1728 22 23 24
  leafTestAt1728_block_22
  leafTestAt1728_block_23)))
  (interval_append leafTestAt1728 24 28 32
  (interval_append leafTestAt1728 24 26 28
  (interval_append leafTestAt1728 24 25 26
  leafTestAt1728_block_24
  leafTestAt1728_block_25)
  (interval_append leafTestAt1728 26 27 28
  leafTestAt1728_block_26
  leafTestAt1728_block_27))
  (interval_append leafTestAt1728 28 30 32
  (interval_append leafTestAt1728 28 29 30
  leafTestAt1728_block_28
  leafTestAt1728_block_29)
  (interval_append leafTestAt1728 30 31 32
  leafTestAt1728_block_30
  leafTestAt1728_block_31)))))
cert_leafInterval 1728 1760
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1760
cert_leafTestAt_block_2 1760 0 1
cert_leafTestAt_block_2 1760 1 2
cert_leafTestAt_block_2 1760 2 3
cert_leafTestAt_block_2 1760 3 4
cert_leafTestAt_block_2 1760 4 5
cert_leafTestAt_block_2 1760 5 6
cert_leafTestAt_block_2 1760 6 7
cert_leafTestAt_block_2 1760 7 8
cert_leafTestAt_block_2 1760 8 9
cert_leafTestAt_block_2 1760 9 10
cert_leafTestAt_block_2 1760 10 11
cert_leafTestAt_block_2 1760 11 12
cert_leafTestAt_block_2 1760 12 13
cert_leafTestAt_block_2 1760 13 14
cert_leafTestAt_block_2 1760 14 15
cert_leafTestAt_block_2 1760 15 16
cert_leafTestAt_block_2 1760 16 17
cert_leafTestAt_block_2 1760 17 18
cert_leafTestAt_block_2 1760 18 19
cert_leafTestAt_block_2 1760 19 20
cert_leafTestAt_block_2 1760 20 21
cert_leafTestAt_block_2 1760 21 22
cert_leafTestAt_block_2 1760 22 23
cert_leafTestAt_block_2 1760 23 24
cert_leafTestAt_block_2 1760 24 25
cert_leafTestAt_block_2 1760 25 26
cert_leafTestAt_block_2 1760 26 27
cert_leafTestAt_block_2 1760 27 28
cert_leafTestAt_block_2 1760 28 29
cert_leafTestAt_block_2 1760 29 30
cert_leafTestAt_block_2 1760 30 31
cert_leafTestAt_block_2 1760 31 32
theorem leafTestAt1760_complete : Interval leafTestAt1760 0 32 :=
  (interval_append leafTestAt1760 0 16 32
  (interval_append leafTestAt1760 0 8 16
  (interval_append leafTestAt1760 0 4 8
  (interval_append leafTestAt1760 0 2 4
  (interval_append leafTestAt1760 0 1 2
  leafTestAt1760_block_0
  leafTestAt1760_block_1)
  (interval_append leafTestAt1760 2 3 4
  leafTestAt1760_block_2
  leafTestAt1760_block_3))
  (interval_append leafTestAt1760 4 6 8
  (interval_append leafTestAt1760 4 5 6
  leafTestAt1760_block_4
  leafTestAt1760_block_5)
  (interval_append leafTestAt1760 6 7 8
  leafTestAt1760_block_6
  leafTestAt1760_block_7)))
  (interval_append leafTestAt1760 8 12 16
  (interval_append leafTestAt1760 8 10 12
  (interval_append leafTestAt1760 8 9 10
  leafTestAt1760_block_8
  leafTestAt1760_block_9)
  (interval_append leafTestAt1760 10 11 12
  leafTestAt1760_block_10
  leafTestAt1760_block_11))
  (interval_append leafTestAt1760 12 14 16
  (interval_append leafTestAt1760 12 13 14
  leafTestAt1760_block_12
  leafTestAt1760_block_13)
  (interval_append leafTestAt1760 14 15 16
  leafTestAt1760_block_14
  leafTestAt1760_block_15))))
  (interval_append leafTestAt1760 16 24 32
  (interval_append leafTestAt1760 16 20 24
  (interval_append leafTestAt1760 16 18 20
  (interval_append leafTestAt1760 16 17 18
  leafTestAt1760_block_16
  leafTestAt1760_block_17)
  (interval_append leafTestAt1760 18 19 20
  leafTestAt1760_block_18
  leafTestAt1760_block_19))
  (interval_append leafTestAt1760 20 22 24
  (interval_append leafTestAt1760 20 21 22
  leafTestAt1760_block_20
  leafTestAt1760_block_21)
  (interval_append leafTestAt1760 22 23 24
  leafTestAt1760_block_22
  leafTestAt1760_block_23)))
  (interval_append leafTestAt1760 24 28 32
  (interval_append leafTestAt1760 24 26 28
  (interval_append leafTestAt1760 24 25 26
  leafTestAt1760_block_24
  leafTestAt1760_block_25)
  (interval_append leafTestAt1760 26 27 28
  leafTestAt1760_block_26
  leafTestAt1760_block_27))
  (interval_append leafTestAt1760 28 30 32
  (interval_append leafTestAt1760 28 29 30
  leafTestAt1760_block_28
  leafTestAt1760_block_29)
  (interval_append leafTestAt1760 30 31 32
  leafTestAt1760_block_30
  leafTestAt1760_block_31)))))
cert_leafInterval 1760 1792
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1792
cert_leafTestAt_block_2 1792 0 1
cert_leafTestAt_block_2 1792 1 2
cert_leafTestAt_block_2 1792 2 3
cert_leafTestAt_block_2 1792 3 4
cert_leafTestAt_block_2 1792 4 5
cert_leafTestAt_block_2 1792 5 6
cert_leafTestAt_block_2 1792 6 7
cert_leafTestAt_block_2 1792 7 8
cert_leafTestAt_block_2 1792 8 9
cert_leafTestAt_block_2 1792 9 10
cert_leafTestAt_block_2 1792 10 11
cert_leafTestAt_block_2 1792 11 12
cert_leafTestAt_block_2 1792 12 13
cert_leafTestAt_block_2 1792 13 14
cert_leafTestAt_block_2 1792 14 15
cert_leafTestAt_block_2 1792 15 16
cert_leafTestAt_block_2 1792 16 17
cert_leafTestAt_block_2 1792 17 18
cert_leafTestAt_block_2 1792 18 19
cert_leafTestAt_block_2 1792 19 20
cert_leafTestAt_block_2 1792 20 21
cert_leafTestAt_block_2 1792 21 22
cert_leafTestAt_block_2 1792 22 23
cert_leafTestAt_block_2 1792 23 24
cert_leafTestAt_block_2 1792 24 25
cert_leafTestAt_block_2 1792 25 26
cert_leafTestAt_block_2 1792 26 27
cert_leafTestAt_block_2 1792 27 28
cert_leafTestAt_block_2 1792 28 29
cert_leafTestAt_block_2 1792 29 30
cert_leafTestAt_block_2 1792 30 31
cert_leafTestAt_block_2 1792 31 32
theorem leafTestAt1792_complete : Interval leafTestAt1792 0 32 :=
  (interval_append leafTestAt1792 0 16 32
  (interval_append leafTestAt1792 0 8 16
  (interval_append leafTestAt1792 0 4 8
  (interval_append leafTestAt1792 0 2 4
  (interval_append leafTestAt1792 0 1 2
  leafTestAt1792_block_0
  leafTestAt1792_block_1)
  (interval_append leafTestAt1792 2 3 4
  leafTestAt1792_block_2
  leafTestAt1792_block_3))
  (interval_append leafTestAt1792 4 6 8
  (interval_append leafTestAt1792 4 5 6
  leafTestAt1792_block_4
  leafTestAt1792_block_5)
  (interval_append leafTestAt1792 6 7 8
  leafTestAt1792_block_6
  leafTestAt1792_block_7)))
  (interval_append leafTestAt1792 8 12 16
  (interval_append leafTestAt1792 8 10 12
  (interval_append leafTestAt1792 8 9 10
  leafTestAt1792_block_8
  leafTestAt1792_block_9)
  (interval_append leafTestAt1792 10 11 12
  leafTestAt1792_block_10
  leafTestAt1792_block_11))
  (interval_append leafTestAt1792 12 14 16
  (interval_append leafTestAt1792 12 13 14
  leafTestAt1792_block_12
  leafTestAt1792_block_13)
  (interval_append leafTestAt1792 14 15 16
  leafTestAt1792_block_14
  leafTestAt1792_block_15))))
  (interval_append leafTestAt1792 16 24 32
  (interval_append leafTestAt1792 16 20 24
  (interval_append leafTestAt1792 16 18 20
  (interval_append leafTestAt1792 16 17 18
  leafTestAt1792_block_16
  leafTestAt1792_block_17)
  (interval_append leafTestAt1792 18 19 20
  leafTestAt1792_block_18
  leafTestAt1792_block_19))
  (interval_append leafTestAt1792 20 22 24
  (interval_append leafTestAt1792 20 21 22
  leafTestAt1792_block_20
  leafTestAt1792_block_21)
  (interval_append leafTestAt1792 22 23 24
  leafTestAt1792_block_22
  leafTestAt1792_block_23)))
  (interval_append leafTestAt1792 24 28 32
  (interval_append leafTestAt1792 24 26 28
  (interval_append leafTestAt1792 24 25 26
  leafTestAt1792_block_24
  leafTestAt1792_block_25)
  (interval_append leafTestAt1792 26 27 28
  leafTestAt1792_block_26
  leafTestAt1792_block_27))
  (interval_append leafTestAt1792 28 30 32
  (interval_append leafTestAt1792 28 29 30
  leafTestAt1792_block_28
  leafTestAt1792_block_29)
  (interval_append leafTestAt1792 30 31 32
  leafTestAt1792_block_30
  leafTestAt1792_block_31)))))
cert_leafInterval 1792 1824
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1824
cert_leafTestAt_block_2 1824 0 1
cert_leafTestAt_block_2 1824 1 2
cert_leafTestAt_block_2 1824 2 3
cert_leafTestAt_block_2 1824 3 4
cert_leafTestAt_block_2 1824 4 5
cert_leafTestAt_block_2 1824 5 6
cert_leafTestAt_block_2 1824 6 7
cert_leafTestAt_block_2 1824 7 8
cert_leafTestAt_block_2 1824 8 9
cert_leafTestAt_block_2 1824 9 10
cert_leafTestAt_block_2 1824 10 11
cert_leafTestAt_block_2 1824 11 12
cert_leafTestAt_block_2 1824 12 13
cert_leafTestAt_block_2 1824 13 14
cert_leafTestAt_block_2 1824 14 15
cert_leafTestAt_block_2 1824 15 16
cert_leafTestAt_block_2 1824 16 17
cert_leafTestAt_block_2 1824 17 18
cert_leafTestAt_block_2 1824 18 19
cert_leafTestAt_block_2 1824 19 20
cert_leafTestAt_block_2 1824 20 21
cert_leafTestAt_block_2 1824 21 22
cert_leafTestAt_block_2 1824 22 23
cert_leafTestAt_block_2 1824 23 24
cert_leafTestAt_block_2 1824 24 25
cert_leafTestAt_block_2 1824 25 26
cert_leafTestAt_block_2 1824 26 27
cert_leafTestAt_block_2 1824 27 28
cert_leafTestAt_block_2 1824 28 29
cert_leafTestAt_block_2 1824 29 30
cert_leafTestAt_block_2 1824 30 31
cert_leafTestAt_block_2 1824 31 32
theorem leafTestAt1824_complete : Interval leafTestAt1824 0 32 :=
  (interval_append leafTestAt1824 0 16 32
  (interval_append leafTestAt1824 0 8 16
  (interval_append leafTestAt1824 0 4 8
  (interval_append leafTestAt1824 0 2 4
  (interval_append leafTestAt1824 0 1 2
  leafTestAt1824_block_0
  leafTestAt1824_block_1)
  (interval_append leafTestAt1824 2 3 4
  leafTestAt1824_block_2
  leafTestAt1824_block_3))
  (interval_append leafTestAt1824 4 6 8
  (interval_append leafTestAt1824 4 5 6
  leafTestAt1824_block_4
  leafTestAt1824_block_5)
  (interval_append leafTestAt1824 6 7 8
  leafTestAt1824_block_6
  leafTestAt1824_block_7)))
  (interval_append leafTestAt1824 8 12 16
  (interval_append leafTestAt1824 8 10 12
  (interval_append leafTestAt1824 8 9 10
  leafTestAt1824_block_8
  leafTestAt1824_block_9)
  (interval_append leafTestAt1824 10 11 12
  leafTestAt1824_block_10
  leafTestAt1824_block_11))
  (interval_append leafTestAt1824 12 14 16
  (interval_append leafTestAt1824 12 13 14
  leafTestAt1824_block_12
  leafTestAt1824_block_13)
  (interval_append leafTestAt1824 14 15 16
  leafTestAt1824_block_14
  leafTestAt1824_block_15))))
  (interval_append leafTestAt1824 16 24 32
  (interval_append leafTestAt1824 16 20 24
  (interval_append leafTestAt1824 16 18 20
  (interval_append leafTestAt1824 16 17 18
  leafTestAt1824_block_16
  leafTestAt1824_block_17)
  (interval_append leafTestAt1824 18 19 20
  leafTestAt1824_block_18
  leafTestAt1824_block_19))
  (interval_append leafTestAt1824 20 22 24
  (interval_append leafTestAt1824 20 21 22
  leafTestAt1824_block_20
  leafTestAt1824_block_21)
  (interval_append leafTestAt1824 22 23 24
  leafTestAt1824_block_22
  leafTestAt1824_block_23)))
  (interval_append leafTestAt1824 24 28 32
  (interval_append leafTestAt1824 24 26 28
  (interval_append leafTestAt1824 24 25 26
  leafTestAt1824_block_24
  leafTestAt1824_block_25)
  (interval_append leafTestAt1824 26 27 28
  leafTestAt1824_block_26
  leafTestAt1824_block_27))
  (interval_append leafTestAt1824 28 30 32
  (interval_append leafTestAt1824 28 29 30
  leafTestAt1824_block_28
  leafTestAt1824_block_29)
  (interval_append leafTestAt1824 30 31 32
  leafTestAt1824_block_30
  leafTestAt1824_block_31)))))
cert_leafInterval 1824 1856
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1856
cert_leafTestAt_block_2 1856 0 1
cert_leafTestAt_block_2 1856 1 2
cert_leafTestAt_block_2 1856 2 3
cert_leafTestAt_block_2 1856 3 4
cert_leafTestAt_block_2 1856 4 5
cert_leafTestAt_block_2 1856 5 6
cert_leafTestAt_block_2 1856 6 7
cert_leafTestAt_block_2 1856 7 8
cert_leafTestAt_block_2 1856 8 9
cert_leafTestAt_block_2 1856 9 10
cert_leafTestAt_block_2 1856 10 11
cert_leafTestAt_block_2 1856 11 12
cert_leafTestAt_block_2 1856 12 13
cert_leafTestAt_block_2 1856 13 14
cert_leafTestAt_block_2 1856 14 15
cert_leafTestAt_block_2 1856 15 16
cert_leafTestAt_block_2 1856 16 17
cert_leafTestAt_block_2 1856 17 18
cert_leafTestAt_block_2 1856 18 19
cert_leafTestAt_block_2 1856 19 20
cert_leafTestAt_block_2 1856 20 21
cert_leafTestAt_block_2 1856 21 22
cert_leafTestAt_block_2 1856 22 23
cert_leafTestAt_block_2 1856 23 24
cert_leafTestAt_block_2 1856 24 25
cert_leafTestAt_block_2 1856 25 26
cert_leafTestAt_block_2 1856 26 27
cert_leafTestAt_block_2 1856 27 28
cert_leafTestAt_block_2 1856 28 29
cert_leafTestAt_block_2 1856 29 30
cert_leafTestAt_block_2 1856 30 31
cert_leafTestAt_block_2 1856 31 32
theorem leafTestAt1856_complete : Interval leafTestAt1856 0 32 :=
  (interval_append leafTestAt1856 0 16 32
  (interval_append leafTestAt1856 0 8 16
  (interval_append leafTestAt1856 0 4 8
  (interval_append leafTestAt1856 0 2 4
  (interval_append leafTestAt1856 0 1 2
  leafTestAt1856_block_0
  leafTestAt1856_block_1)
  (interval_append leafTestAt1856 2 3 4
  leafTestAt1856_block_2
  leafTestAt1856_block_3))
  (interval_append leafTestAt1856 4 6 8
  (interval_append leafTestAt1856 4 5 6
  leafTestAt1856_block_4
  leafTestAt1856_block_5)
  (interval_append leafTestAt1856 6 7 8
  leafTestAt1856_block_6
  leafTestAt1856_block_7)))
  (interval_append leafTestAt1856 8 12 16
  (interval_append leafTestAt1856 8 10 12
  (interval_append leafTestAt1856 8 9 10
  leafTestAt1856_block_8
  leafTestAt1856_block_9)
  (interval_append leafTestAt1856 10 11 12
  leafTestAt1856_block_10
  leafTestAt1856_block_11))
  (interval_append leafTestAt1856 12 14 16
  (interval_append leafTestAt1856 12 13 14
  leafTestAt1856_block_12
  leafTestAt1856_block_13)
  (interval_append leafTestAt1856 14 15 16
  leafTestAt1856_block_14
  leafTestAt1856_block_15))))
  (interval_append leafTestAt1856 16 24 32
  (interval_append leafTestAt1856 16 20 24
  (interval_append leafTestAt1856 16 18 20
  (interval_append leafTestAt1856 16 17 18
  leafTestAt1856_block_16
  leafTestAt1856_block_17)
  (interval_append leafTestAt1856 18 19 20
  leafTestAt1856_block_18
  leafTestAt1856_block_19))
  (interval_append leafTestAt1856 20 22 24
  (interval_append leafTestAt1856 20 21 22
  leafTestAt1856_block_20
  leafTestAt1856_block_21)
  (interval_append leafTestAt1856 22 23 24
  leafTestAt1856_block_22
  leafTestAt1856_block_23)))
  (interval_append leafTestAt1856 24 28 32
  (interval_append leafTestAt1856 24 26 28
  (interval_append leafTestAt1856 24 25 26
  leafTestAt1856_block_24
  leafTestAt1856_block_25)
  (interval_append leafTestAt1856 26 27 28
  leafTestAt1856_block_26
  leafTestAt1856_block_27))
  (interval_append leafTestAt1856 28 30 32
  (interval_append leafTestAt1856 28 29 30
  leafTestAt1856_block_28
  leafTestAt1856_block_29)
  (interval_append leafTestAt1856 30 31 32
  leafTestAt1856_block_30
  leafTestAt1856_block_31)))))
cert_leafInterval 1856 1888
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1888
cert_leafTestAt_block_2 1888 0 1
cert_leafTestAt_block_2 1888 1 2
cert_leafTestAt_block_2 1888 2 3
cert_leafTestAt_block_2 1888 3 4
cert_leafTestAt_block_2 1888 4 5
cert_leafTestAt_block_2 1888 5 6
cert_leafTestAt_block_2 1888 6 7
cert_leafTestAt_block_2 1888 7 8
cert_leafTestAt_block_2 1888 8 9
cert_leafTestAt_block_2 1888 9 10
cert_leafTestAt_block_2 1888 10 11
cert_leafTestAt_block_2 1888 11 12
cert_leafTestAt_block_2 1888 12 13
cert_leafTestAt_block_2 1888 13 14
cert_leafTestAt_block_2 1888 14 15
cert_leafTestAt_block_2 1888 15 16
cert_leafTestAt_block_2 1888 16 17
cert_leafTestAt_block_2 1888 17 18
cert_leafTestAt_block_2 1888 18 19
cert_leafTestAt_block_2 1888 19 20
cert_leafTestAt_block_2 1888 20 21
cert_leafTestAt_block_2 1888 21 22
cert_leafTestAt_block_2 1888 22 23
cert_leafTestAt_block_2 1888 23 24
cert_leafTestAt_block_2 1888 24 25
cert_leafTestAt_block_2 1888 25 26
cert_leafTestAt_block_2 1888 26 27
cert_leafTestAt_block_2 1888 27 28
cert_leafTestAt_block_2 1888 28 29
cert_leafTestAt_block_2 1888 29 30
cert_leafTestAt_block_2 1888 30 31
cert_leafTestAt_block_2 1888 31 32
theorem leafTestAt1888_complete : Interval leafTestAt1888 0 32 :=
  (interval_append leafTestAt1888 0 16 32
  (interval_append leafTestAt1888 0 8 16
  (interval_append leafTestAt1888 0 4 8
  (interval_append leafTestAt1888 0 2 4
  (interval_append leafTestAt1888 0 1 2
  leafTestAt1888_block_0
  leafTestAt1888_block_1)
  (interval_append leafTestAt1888 2 3 4
  leafTestAt1888_block_2
  leafTestAt1888_block_3))
  (interval_append leafTestAt1888 4 6 8
  (interval_append leafTestAt1888 4 5 6
  leafTestAt1888_block_4
  leafTestAt1888_block_5)
  (interval_append leafTestAt1888 6 7 8
  leafTestAt1888_block_6
  leafTestAt1888_block_7)))
  (interval_append leafTestAt1888 8 12 16
  (interval_append leafTestAt1888 8 10 12
  (interval_append leafTestAt1888 8 9 10
  leafTestAt1888_block_8
  leafTestAt1888_block_9)
  (interval_append leafTestAt1888 10 11 12
  leafTestAt1888_block_10
  leafTestAt1888_block_11))
  (interval_append leafTestAt1888 12 14 16
  (interval_append leafTestAt1888 12 13 14
  leafTestAt1888_block_12
  leafTestAt1888_block_13)
  (interval_append leafTestAt1888 14 15 16
  leafTestAt1888_block_14
  leafTestAt1888_block_15))))
  (interval_append leafTestAt1888 16 24 32
  (interval_append leafTestAt1888 16 20 24
  (interval_append leafTestAt1888 16 18 20
  (interval_append leafTestAt1888 16 17 18
  leafTestAt1888_block_16
  leafTestAt1888_block_17)
  (interval_append leafTestAt1888 18 19 20
  leafTestAt1888_block_18
  leafTestAt1888_block_19))
  (interval_append leafTestAt1888 20 22 24
  (interval_append leafTestAt1888 20 21 22
  leafTestAt1888_block_20
  leafTestAt1888_block_21)
  (interval_append leafTestAt1888 22 23 24
  leafTestAt1888_block_22
  leafTestAt1888_block_23)))
  (interval_append leafTestAt1888 24 28 32
  (interval_append leafTestAt1888 24 26 28
  (interval_append leafTestAt1888 24 25 26
  leafTestAt1888_block_24
  leafTestAt1888_block_25)
  (interval_append leafTestAt1888 26 27 28
  leafTestAt1888_block_26
  leafTestAt1888_block_27))
  (interval_append leafTestAt1888 28 30 32
  (interval_append leafTestAt1888 28 29 30
  leafTestAt1888_block_28
  leafTestAt1888_block_29)
  (interval_append leafTestAt1888 30 31 32
  leafTestAt1888_block_30
  leafTestAt1888_block_31)))))
cert_leafInterval 1888 1920
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1920
cert_leafTestAt_block_2 1920 0 1
cert_leafTestAt_block_2 1920 1 2
cert_leafTestAt_block_2 1920 2 3
cert_leafTestAt_block_2 1920 3 4
cert_leafTestAt_block_2 1920 4 5
cert_leafTestAt_block_2 1920 5 6
cert_leafTestAt_block_2 1920 6 7
cert_leafTestAt_block_2 1920 7 8
cert_leafTestAt_block_2 1920 8 9
cert_leafTestAt_block_2 1920 9 10
cert_leafTestAt_block_2 1920 10 11
cert_leafTestAt_block_2 1920 11 12
cert_leafTestAt_block_2 1920 12 13
cert_leafTestAt_block_2 1920 13 14
cert_leafTestAt_block_2 1920 14 15
cert_leafTestAt_block_2 1920 15 16
cert_leafTestAt_block_2 1920 16 17
cert_leafTestAt_block_2 1920 17 18
cert_leafTestAt_block_2 1920 18 19
cert_leafTestAt_block_2 1920 19 20
cert_leafTestAt_block_2 1920 20 21
cert_leafTestAt_block_2 1920 21 22
cert_leafTestAt_block_2 1920 22 23
cert_leafTestAt_block_2 1920 23 24
cert_leafTestAt_block_2 1920 24 25
cert_leafTestAt_block_2 1920 25 26
cert_leafTestAt_block_2 1920 26 27
cert_leafTestAt_block_2 1920 27 28
cert_leafTestAt_block_2 1920 28 29
cert_leafTestAt_block_2 1920 29 30
cert_leafTestAt_block_2 1920 30 31
cert_leafTestAt_block_2 1920 31 32
theorem leafTestAt1920_complete : Interval leafTestAt1920 0 32 :=
  (interval_append leafTestAt1920 0 16 32
  (interval_append leafTestAt1920 0 8 16
  (interval_append leafTestAt1920 0 4 8
  (interval_append leafTestAt1920 0 2 4
  (interval_append leafTestAt1920 0 1 2
  leafTestAt1920_block_0
  leafTestAt1920_block_1)
  (interval_append leafTestAt1920 2 3 4
  leafTestAt1920_block_2
  leafTestAt1920_block_3))
  (interval_append leafTestAt1920 4 6 8
  (interval_append leafTestAt1920 4 5 6
  leafTestAt1920_block_4
  leafTestAt1920_block_5)
  (interval_append leafTestAt1920 6 7 8
  leafTestAt1920_block_6
  leafTestAt1920_block_7)))
  (interval_append leafTestAt1920 8 12 16
  (interval_append leafTestAt1920 8 10 12
  (interval_append leafTestAt1920 8 9 10
  leafTestAt1920_block_8
  leafTestAt1920_block_9)
  (interval_append leafTestAt1920 10 11 12
  leafTestAt1920_block_10
  leafTestAt1920_block_11))
  (interval_append leafTestAt1920 12 14 16
  (interval_append leafTestAt1920 12 13 14
  leafTestAt1920_block_12
  leafTestAt1920_block_13)
  (interval_append leafTestAt1920 14 15 16
  leafTestAt1920_block_14
  leafTestAt1920_block_15))))
  (interval_append leafTestAt1920 16 24 32
  (interval_append leafTestAt1920 16 20 24
  (interval_append leafTestAt1920 16 18 20
  (interval_append leafTestAt1920 16 17 18
  leafTestAt1920_block_16
  leafTestAt1920_block_17)
  (interval_append leafTestAt1920 18 19 20
  leafTestAt1920_block_18
  leafTestAt1920_block_19))
  (interval_append leafTestAt1920 20 22 24
  (interval_append leafTestAt1920 20 21 22
  leafTestAt1920_block_20
  leafTestAt1920_block_21)
  (interval_append leafTestAt1920 22 23 24
  leafTestAt1920_block_22
  leafTestAt1920_block_23)))
  (interval_append leafTestAt1920 24 28 32
  (interval_append leafTestAt1920 24 26 28
  (interval_append leafTestAt1920 24 25 26
  leafTestAt1920_block_24
  leafTestAt1920_block_25)
  (interval_append leafTestAt1920 26 27 28
  leafTestAt1920_block_26
  leafTestAt1920_block_27))
  (interval_append leafTestAt1920 28 30 32
  (interval_append leafTestAt1920 28 29 30
  leafTestAt1920_block_28
  leafTestAt1920_block_29)
  (interval_append leafTestAt1920 30 31 32
  leafTestAt1920_block_30
  leafTestAt1920_block_31)))))
cert_leafInterval 1920 1952
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1952
cert_leafTestAt_block_2 1952 0 1
cert_leafTestAt_block_2 1952 1 2
cert_leafTestAt_block_2 1952 2 3
cert_leafTestAt_block_2 1952 3 4
cert_leafTestAt_block_2 1952 4 5
cert_leafTestAt_block_2 1952 5 6
cert_leafTestAt_block_2 1952 6 7
cert_leafTestAt_block_2 1952 7 8
cert_leafTestAt_block_2 1952 8 9
cert_leafTestAt_block_2 1952 9 10
cert_leafTestAt_block_2 1952 10 11
cert_leafTestAt_block_2 1952 11 12
cert_leafTestAt_block_2 1952 12 13
cert_leafTestAt_block_2 1952 13 14
cert_leafTestAt_block_2 1952 14 15
cert_leafTestAt_block_2 1952 15 16
cert_leafTestAt_block_2 1952 16 17
cert_leafTestAt_block_2 1952 17 18
cert_leafTestAt_block_2 1952 18 19
cert_leafTestAt_block_2 1952 19 20
cert_leafTestAt_block_2 1952 20 21
cert_leafTestAt_block_2 1952 21 22
cert_leafTestAt_block_2 1952 22 23
cert_leafTestAt_block_2 1952 23 24
cert_leafTestAt_block_2 1952 24 25
cert_leafTestAt_block_2 1952 25 26
cert_leafTestAt_block_2 1952 26 27
cert_leafTestAt_block_2 1952 27 28
cert_leafTestAt_block_2 1952 28 29
cert_leafTestAt_block_2 1952 29 30
cert_leafTestAt_block_2 1952 30 31
cert_leafTestAt_block_2 1952 31 32
theorem leafTestAt1952_complete : Interval leafTestAt1952 0 32 :=
  (interval_append leafTestAt1952 0 16 32
  (interval_append leafTestAt1952 0 8 16
  (interval_append leafTestAt1952 0 4 8
  (interval_append leafTestAt1952 0 2 4
  (interval_append leafTestAt1952 0 1 2
  leafTestAt1952_block_0
  leafTestAt1952_block_1)
  (interval_append leafTestAt1952 2 3 4
  leafTestAt1952_block_2
  leafTestAt1952_block_3))
  (interval_append leafTestAt1952 4 6 8
  (interval_append leafTestAt1952 4 5 6
  leafTestAt1952_block_4
  leafTestAt1952_block_5)
  (interval_append leafTestAt1952 6 7 8
  leafTestAt1952_block_6
  leafTestAt1952_block_7)))
  (interval_append leafTestAt1952 8 12 16
  (interval_append leafTestAt1952 8 10 12
  (interval_append leafTestAt1952 8 9 10
  leafTestAt1952_block_8
  leafTestAt1952_block_9)
  (interval_append leafTestAt1952 10 11 12
  leafTestAt1952_block_10
  leafTestAt1952_block_11))
  (interval_append leafTestAt1952 12 14 16
  (interval_append leafTestAt1952 12 13 14
  leafTestAt1952_block_12
  leafTestAt1952_block_13)
  (interval_append leafTestAt1952 14 15 16
  leafTestAt1952_block_14
  leafTestAt1952_block_15))))
  (interval_append leafTestAt1952 16 24 32
  (interval_append leafTestAt1952 16 20 24
  (interval_append leafTestAt1952 16 18 20
  (interval_append leafTestAt1952 16 17 18
  leafTestAt1952_block_16
  leafTestAt1952_block_17)
  (interval_append leafTestAt1952 18 19 20
  leafTestAt1952_block_18
  leafTestAt1952_block_19))
  (interval_append leafTestAt1952 20 22 24
  (interval_append leafTestAt1952 20 21 22
  leafTestAt1952_block_20
  leafTestAt1952_block_21)
  (interval_append leafTestAt1952 22 23 24
  leafTestAt1952_block_22
  leafTestAt1952_block_23)))
  (interval_append leafTestAt1952 24 28 32
  (interval_append leafTestAt1952 24 26 28
  (interval_append leafTestAt1952 24 25 26
  leafTestAt1952_block_24
  leafTestAt1952_block_25)
  (interval_append leafTestAt1952 26 27 28
  leafTestAt1952_block_26
  leafTestAt1952_block_27))
  (interval_append leafTestAt1952 28 30 32
  (interval_append leafTestAt1952 28 29 30
  leafTestAt1952_block_28
  leafTestAt1952_block_29)
  (interval_append leafTestAt1952 30 31 32
  leafTestAt1952_block_30
  leafTestAt1952_block_31)))))
cert_leafInterval 1952 1984
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 1984
cert_leafTestAt_block_2 1984 0 1
cert_leafTestAt_block_2 1984 1 2
cert_leafTestAt_block_2 1984 2 3
cert_leafTestAt_block_2 1984 3 4
cert_leafTestAt_block_2 1984 4 5
cert_leafTestAt_block_2 1984 5 6
cert_leafTestAt_block_2 1984 6 7
cert_leafTestAt_block_2 1984 7 8
cert_leafTestAt_block_2 1984 8 9
cert_leafTestAt_block_2 1984 9 10
cert_leafTestAt_block_2 1984 10 11
cert_leafTestAt_block_2 1984 11 12
cert_leafTestAt_block_2 1984 12 13
cert_leafTestAt_block_2 1984 13 14
cert_leafTestAt_block_2 1984 14 15
cert_leafTestAt_block_2 1984 15 16
cert_leafTestAt_block_2 1984 16 17
cert_leafTestAt_block_2 1984 17 18
cert_leafTestAt_block_2 1984 18 19
cert_leafTestAt_block_2 1984 19 20
cert_leafTestAt_block_2 1984 20 21
cert_leafTestAt_block_2 1984 21 22
cert_leafTestAt_block_2 1984 22 23
cert_leafTestAt_block_2 1984 23 24
cert_leafTestAt_block_2 1984 24 25
cert_leafTestAt_block_2 1984 25 26
cert_leafTestAt_block_2 1984 26 27
cert_leafTestAt_block_2 1984 27 28
cert_leafTestAt_block_2 1984 28 29
cert_leafTestAt_block_2 1984 29 30
cert_leafTestAt_block_2 1984 30 31
cert_leafTestAt_block_2 1984 31 32
theorem leafTestAt1984_complete : Interval leafTestAt1984 0 32 :=
  (interval_append leafTestAt1984 0 16 32
  (interval_append leafTestAt1984 0 8 16
  (interval_append leafTestAt1984 0 4 8
  (interval_append leafTestAt1984 0 2 4
  (interval_append leafTestAt1984 0 1 2
  leafTestAt1984_block_0
  leafTestAt1984_block_1)
  (interval_append leafTestAt1984 2 3 4
  leafTestAt1984_block_2
  leafTestAt1984_block_3))
  (interval_append leafTestAt1984 4 6 8
  (interval_append leafTestAt1984 4 5 6
  leafTestAt1984_block_4
  leafTestAt1984_block_5)
  (interval_append leafTestAt1984 6 7 8
  leafTestAt1984_block_6
  leafTestAt1984_block_7)))
  (interval_append leafTestAt1984 8 12 16
  (interval_append leafTestAt1984 8 10 12
  (interval_append leafTestAt1984 8 9 10
  leafTestAt1984_block_8
  leafTestAt1984_block_9)
  (interval_append leafTestAt1984 10 11 12
  leafTestAt1984_block_10
  leafTestAt1984_block_11))
  (interval_append leafTestAt1984 12 14 16
  (interval_append leafTestAt1984 12 13 14
  leafTestAt1984_block_12
  leafTestAt1984_block_13)
  (interval_append leafTestAt1984 14 15 16
  leafTestAt1984_block_14
  leafTestAt1984_block_15))))
  (interval_append leafTestAt1984 16 24 32
  (interval_append leafTestAt1984 16 20 24
  (interval_append leafTestAt1984 16 18 20
  (interval_append leafTestAt1984 16 17 18
  leafTestAt1984_block_16
  leafTestAt1984_block_17)
  (interval_append leafTestAt1984 18 19 20
  leafTestAt1984_block_18
  leafTestAt1984_block_19))
  (interval_append leafTestAt1984 20 22 24
  (interval_append leafTestAt1984 20 21 22
  leafTestAt1984_block_20
  leafTestAt1984_block_21)
  (interval_append leafTestAt1984 22 23 24
  leafTestAt1984_block_22
  leafTestAt1984_block_23)))
  (interval_append leafTestAt1984 24 28 32
  (interval_append leafTestAt1984 24 26 28
  (interval_append leafTestAt1984 24 25 26
  leafTestAt1984_block_24
  leafTestAt1984_block_25)
  (interval_append leafTestAt1984 26 27 28
  leafTestAt1984_block_26
  leafTestAt1984_block_27))
  (interval_append leafTestAt1984 28 30 32
  (interval_append leafTestAt1984 28 29 30
  leafTestAt1984_block_28
  leafTestAt1984_block_29)
  (interval_append leafTestAt1984 30 31 32
  leafTestAt1984_block_30
  leafTestAt1984_block_31)))))
cert_leafInterval 1984 2016
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2016
cert_leafTestAt_block_2 2016 0 1
cert_leafTestAt_block_2 2016 1 2
cert_leafTestAt_block_2 2016 2 3
cert_leafTestAt_block_2 2016 3 4
cert_leafTestAt_block_2 2016 4 5
cert_leafTestAt_block_2 2016 5 6
cert_leafTestAt_block_2 2016 6 7
cert_leafTestAt_block_2 2016 7 8
cert_leafTestAt_block_2 2016 8 9
cert_leafTestAt_block_2 2016 9 10
cert_leafTestAt_block_2 2016 10 11
cert_leafTestAt_block_2 2016 11 12
cert_leafTestAt_block_2 2016 12 13
cert_leafTestAt_block_2 2016 13 14
cert_leafTestAt_block_2 2016 14 15
cert_leafTestAt_block_2 2016 15 16
cert_leafTestAt_block_2 2016 16 17
cert_leafTestAt_block_2 2016 17 18
cert_leafTestAt_block_2 2016 18 19
cert_leafTestAt_block_2 2016 19 20
cert_leafTestAt_block_2 2016 20 21
cert_leafTestAt_block_2 2016 21 22
cert_leafTestAt_block_2 2016 22 23
cert_leafTestAt_block_2 2016 23 24
cert_leafTestAt_block_2 2016 24 25
cert_leafTestAt_block_2 2016 25 26
cert_leafTestAt_block_2 2016 26 27
cert_leafTestAt_block_2 2016 27 28
cert_leafTestAt_block_2 2016 28 29
cert_leafTestAt_block_2 2016 29 30
cert_leafTestAt_block_2 2016 30 31
cert_leafTestAt_block_2 2016 31 32
theorem leafTestAt2016_complete : Interval leafTestAt2016 0 32 :=
  (interval_append leafTestAt2016 0 16 32
  (interval_append leafTestAt2016 0 8 16
  (interval_append leafTestAt2016 0 4 8
  (interval_append leafTestAt2016 0 2 4
  (interval_append leafTestAt2016 0 1 2
  leafTestAt2016_block_0
  leafTestAt2016_block_1)
  (interval_append leafTestAt2016 2 3 4
  leafTestAt2016_block_2
  leafTestAt2016_block_3))
  (interval_append leafTestAt2016 4 6 8
  (interval_append leafTestAt2016 4 5 6
  leafTestAt2016_block_4
  leafTestAt2016_block_5)
  (interval_append leafTestAt2016 6 7 8
  leafTestAt2016_block_6
  leafTestAt2016_block_7)))
  (interval_append leafTestAt2016 8 12 16
  (interval_append leafTestAt2016 8 10 12
  (interval_append leafTestAt2016 8 9 10
  leafTestAt2016_block_8
  leafTestAt2016_block_9)
  (interval_append leafTestAt2016 10 11 12
  leafTestAt2016_block_10
  leafTestAt2016_block_11))
  (interval_append leafTestAt2016 12 14 16
  (interval_append leafTestAt2016 12 13 14
  leafTestAt2016_block_12
  leafTestAt2016_block_13)
  (interval_append leafTestAt2016 14 15 16
  leafTestAt2016_block_14
  leafTestAt2016_block_15))))
  (interval_append leafTestAt2016 16 24 32
  (interval_append leafTestAt2016 16 20 24
  (interval_append leafTestAt2016 16 18 20
  (interval_append leafTestAt2016 16 17 18
  leafTestAt2016_block_16
  leafTestAt2016_block_17)
  (interval_append leafTestAt2016 18 19 20
  leafTestAt2016_block_18
  leafTestAt2016_block_19))
  (interval_append leafTestAt2016 20 22 24
  (interval_append leafTestAt2016 20 21 22
  leafTestAt2016_block_20
  leafTestAt2016_block_21)
  (interval_append leafTestAt2016 22 23 24
  leafTestAt2016_block_22
  leafTestAt2016_block_23)))
  (interval_append leafTestAt2016 24 28 32
  (interval_append leafTestAt2016 24 26 28
  (interval_append leafTestAt2016 24 25 26
  leafTestAt2016_block_24
  leafTestAt2016_block_25)
  (interval_append leafTestAt2016 26 27 28
  leafTestAt2016_block_26
  leafTestAt2016_block_27))
  (interval_append leafTestAt2016 28 30 32
  (interval_append leafTestAt2016 28 29 30
  leafTestAt2016_block_28
  leafTestAt2016_block_29)
  (interval_append leafTestAt2016 30 31 32
  leafTestAt2016_block_30
  leafTestAt2016_block_31)))))
cert_leafInterval 2016 2048
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end
