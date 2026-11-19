module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
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
cert_leafTestAt 2560
cert_leafTestAt_block_2 2560 0 1
cert_leafTestAt_block_2 2560 1 2
cert_leafTestAt_block_2 2560 2 3
cert_leafTestAt_block_2 2560 3 4
cert_leafTestAt_block_2 2560 4 5
cert_leafTestAt_block_2 2560 5 6
cert_leafTestAt_block_2 2560 6 7
cert_leafTestAt_block_2 2560 7 8
cert_leafTestAt_block_2 2560 8 9
cert_leafTestAt_block_2 2560 9 10
cert_leafTestAt_block_2 2560 10 11
cert_leafTestAt_block_2 2560 11 12
cert_leafTestAt_block_2 2560 12 13
cert_leafTestAt_block_2 2560 13 14
cert_leafTestAt_block_2 2560 14 15
cert_leafTestAt_block_2 2560 15 16
cert_leafTestAt_block_2 2560 16 17
cert_leafTestAt_block_2 2560 17 18
cert_leafTestAt_block_2 2560 18 19
cert_leafTestAt_block_2 2560 19 20
cert_leafTestAt_block_2 2560 20 21
cert_leafTestAt_block_2 2560 21 22
cert_leafTestAt_block_2 2560 22 23
cert_leafTestAt_block_2 2560 23 24
cert_leafTestAt_block_2 2560 24 25
cert_leafTestAt_block_2 2560 25 26
cert_leafTestAt_block_2 2560 26 27
cert_leafTestAt_block_2 2560 27 28
cert_leafTestAt_block_2 2560 28 29
cert_leafTestAt_block_2 2560 29 30
cert_leafTestAt_block_2 2560 30 31
cert_leafTestAt_block_2 2560 31 32
theorem leafTestAt2560_complete : Interval leafTestAt2560 0 32 :=
  (interval_append leafTestAt2560 0 16 32
  (interval_append leafTestAt2560 0 8 16
  (interval_append leafTestAt2560 0 4 8
  (interval_append leafTestAt2560 0 2 4
  (interval_append leafTestAt2560 0 1 2
  leafTestAt2560_block_0
  leafTestAt2560_block_1)
  (interval_append leafTestAt2560 2 3 4
  leafTestAt2560_block_2
  leafTestAt2560_block_3))
  (interval_append leafTestAt2560 4 6 8
  (interval_append leafTestAt2560 4 5 6
  leafTestAt2560_block_4
  leafTestAt2560_block_5)
  (interval_append leafTestAt2560 6 7 8
  leafTestAt2560_block_6
  leafTestAt2560_block_7)))
  (interval_append leafTestAt2560 8 12 16
  (interval_append leafTestAt2560 8 10 12
  (interval_append leafTestAt2560 8 9 10
  leafTestAt2560_block_8
  leafTestAt2560_block_9)
  (interval_append leafTestAt2560 10 11 12
  leafTestAt2560_block_10
  leafTestAt2560_block_11))
  (interval_append leafTestAt2560 12 14 16
  (interval_append leafTestAt2560 12 13 14
  leafTestAt2560_block_12
  leafTestAt2560_block_13)
  (interval_append leafTestAt2560 14 15 16
  leafTestAt2560_block_14
  leafTestAt2560_block_15))))
  (interval_append leafTestAt2560 16 24 32
  (interval_append leafTestAt2560 16 20 24
  (interval_append leafTestAt2560 16 18 20
  (interval_append leafTestAt2560 16 17 18
  leafTestAt2560_block_16
  leafTestAt2560_block_17)
  (interval_append leafTestAt2560 18 19 20
  leafTestAt2560_block_18
  leafTestAt2560_block_19))
  (interval_append leafTestAt2560 20 22 24
  (interval_append leafTestAt2560 20 21 22
  leafTestAt2560_block_20
  leafTestAt2560_block_21)
  (interval_append leafTestAt2560 22 23 24
  leafTestAt2560_block_22
  leafTestAt2560_block_23)))
  (interval_append leafTestAt2560 24 28 32
  (interval_append leafTestAt2560 24 26 28
  (interval_append leafTestAt2560 24 25 26
  leafTestAt2560_block_24
  leafTestAt2560_block_25)
  (interval_append leafTestAt2560 26 27 28
  leafTestAt2560_block_26
  leafTestAt2560_block_27))
  (interval_append leafTestAt2560 28 30 32
  (interval_append leafTestAt2560 28 29 30
  leafTestAt2560_block_28
  leafTestAt2560_block_29)
  (interval_append leafTestAt2560 30 31 32
  leafTestAt2560_block_30
  leafTestAt2560_block_31)))))
cert_leafInterval 2560 2592
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2592
cert_leafTestAt_block_2 2592 0 1
cert_leafTestAt_block_2 2592 1 2
cert_leafTestAt_block_2 2592 2 3
cert_leafTestAt_block_2 2592 3 4
cert_leafTestAt_block_2 2592 4 5
cert_leafTestAt_block_2 2592 5 6
cert_leafTestAt_block_2 2592 6 7
cert_leafTestAt_block_2 2592 7 8
cert_leafTestAt_block_2 2592 8 9
cert_leafTestAt_block_2 2592 9 10
cert_leafTestAt_block_2 2592 10 11
cert_leafTestAt_block_2 2592 11 12
cert_leafTestAt_block_2 2592 12 13
cert_leafTestAt_block_2 2592 13 14
cert_leafTestAt_block_2 2592 14 15
cert_leafTestAt_block_2 2592 15 16
cert_leafTestAt_block_2 2592 16 17
cert_leafTestAt_block_2 2592 17 18
cert_leafTestAt_block_2 2592 18 19
cert_leafTestAt_block_2 2592 19 20
cert_leafTestAt_block_2 2592 20 21
cert_leafTestAt_block_2 2592 21 22
cert_leafTestAt_block_2 2592 22 23
cert_leafTestAt_block_2 2592 23 24
cert_leafTestAt_block_2 2592 24 25
cert_leafTestAt_block_2 2592 25 26
cert_leafTestAt_block_2 2592 26 27
cert_leafTestAt_block_2 2592 27 28
cert_leafTestAt_block_2 2592 28 29
cert_leafTestAt_block_2 2592 29 30
cert_leafTestAt_block_2 2592 30 31
cert_leafTestAt_block_2 2592 31 32
theorem leafTestAt2592_complete : Interval leafTestAt2592 0 32 :=
  (interval_append leafTestAt2592 0 16 32
  (interval_append leafTestAt2592 0 8 16
  (interval_append leafTestAt2592 0 4 8
  (interval_append leafTestAt2592 0 2 4
  (interval_append leafTestAt2592 0 1 2
  leafTestAt2592_block_0
  leafTestAt2592_block_1)
  (interval_append leafTestAt2592 2 3 4
  leafTestAt2592_block_2
  leafTestAt2592_block_3))
  (interval_append leafTestAt2592 4 6 8
  (interval_append leafTestAt2592 4 5 6
  leafTestAt2592_block_4
  leafTestAt2592_block_5)
  (interval_append leafTestAt2592 6 7 8
  leafTestAt2592_block_6
  leafTestAt2592_block_7)))
  (interval_append leafTestAt2592 8 12 16
  (interval_append leafTestAt2592 8 10 12
  (interval_append leafTestAt2592 8 9 10
  leafTestAt2592_block_8
  leafTestAt2592_block_9)
  (interval_append leafTestAt2592 10 11 12
  leafTestAt2592_block_10
  leafTestAt2592_block_11))
  (interval_append leafTestAt2592 12 14 16
  (interval_append leafTestAt2592 12 13 14
  leafTestAt2592_block_12
  leafTestAt2592_block_13)
  (interval_append leafTestAt2592 14 15 16
  leafTestAt2592_block_14
  leafTestAt2592_block_15))))
  (interval_append leafTestAt2592 16 24 32
  (interval_append leafTestAt2592 16 20 24
  (interval_append leafTestAt2592 16 18 20
  (interval_append leafTestAt2592 16 17 18
  leafTestAt2592_block_16
  leafTestAt2592_block_17)
  (interval_append leafTestAt2592 18 19 20
  leafTestAt2592_block_18
  leafTestAt2592_block_19))
  (interval_append leafTestAt2592 20 22 24
  (interval_append leafTestAt2592 20 21 22
  leafTestAt2592_block_20
  leafTestAt2592_block_21)
  (interval_append leafTestAt2592 22 23 24
  leafTestAt2592_block_22
  leafTestAt2592_block_23)))
  (interval_append leafTestAt2592 24 28 32
  (interval_append leafTestAt2592 24 26 28
  (interval_append leafTestAt2592 24 25 26
  leafTestAt2592_block_24
  leafTestAt2592_block_25)
  (interval_append leafTestAt2592 26 27 28
  leafTestAt2592_block_26
  leafTestAt2592_block_27))
  (interval_append leafTestAt2592 28 30 32
  (interval_append leafTestAt2592 28 29 30
  leafTestAt2592_block_28
  leafTestAt2592_block_29)
  (interval_append leafTestAt2592 30 31 32
  leafTestAt2592_block_30
  leafTestAt2592_block_31)))))
cert_leafInterval 2592 2624
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2624
cert_leafTestAt_block_2 2624 0 1
cert_leafTestAt_block_2 2624 1 2
cert_leafTestAt_block_2 2624 2 3
cert_leafTestAt_block_2 2624 3 4
cert_leafTestAt_block_2 2624 4 5
cert_leafTestAt_block_2 2624 5 6
cert_leafTestAt_block_2 2624 6 7
cert_leafTestAt_block_2 2624 7 8
cert_leafTestAt_block_2 2624 8 9
cert_leafTestAt_block_2 2624 9 10
cert_leafTestAt_block_2 2624 10 11
cert_leafTestAt_block_2 2624 11 12
cert_leafTestAt_block_2 2624 12 13
cert_leafTestAt_block_2 2624 13 14
cert_leafTestAt_block_2 2624 14 15
cert_leafTestAt_block_2 2624 15 16
cert_leafTestAt_block_2 2624 16 17
cert_leafTestAt_block_2 2624 17 18
cert_leafTestAt_block_2 2624 18 19
cert_leafTestAt_block_2 2624 19 20
cert_leafTestAt_block_2 2624 20 21
cert_leafTestAt_block_2 2624 21 22
cert_leafTestAt_block_2 2624 22 23
cert_leafTestAt_block_2 2624 23 24
cert_leafTestAt_block_2 2624 24 25
cert_leafTestAt_block_2 2624 25 26
cert_leafTestAt_block_2 2624 26 27
cert_leafTestAt_block_2 2624 27 28
cert_leafTestAt_block_2 2624 28 29
cert_leafTestAt_block_2 2624 29 30
cert_leafTestAt_block_2 2624 30 31
cert_leafTestAt_block_2 2624 31 32
theorem leafTestAt2624_complete : Interval leafTestAt2624 0 32 :=
  (interval_append leafTestAt2624 0 16 32
  (interval_append leafTestAt2624 0 8 16
  (interval_append leafTestAt2624 0 4 8
  (interval_append leafTestAt2624 0 2 4
  (interval_append leafTestAt2624 0 1 2
  leafTestAt2624_block_0
  leafTestAt2624_block_1)
  (interval_append leafTestAt2624 2 3 4
  leafTestAt2624_block_2
  leafTestAt2624_block_3))
  (interval_append leafTestAt2624 4 6 8
  (interval_append leafTestAt2624 4 5 6
  leafTestAt2624_block_4
  leafTestAt2624_block_5)
  (interval_append leafTestAt2624 6 7 8
  leafTestAt2624_block_6
  leafTestAt2624_block_7)))
  (interval_append leafTestAt2624 8 12 16
  (interval_append leafTestAt2624 8 10 12
  (interval_append leafTestAt2624 8 9 10
  leafTestAt2624_block_8
  leafTestAt2624_block_9)
  (interval_append leafTestAt2624 10 11 12
  leafTestAt2624_block_10
  leafTestAt2624_block_11))
  (interval_append leafTestAt2624 12 14 16
  (interval_append leafTestAt2624 12 13 14
  leafTestAt2624_block_12
  leafTestAt2624_block_13)
  (interval_append leafTestAt2624 14 15 16
  leafTestAt2624_block_14
  leafTestAt2624_block_15))))
  (interval_append leafTestAt2624 16 24 32
  (interval_append leafTestAt2624 16 20 24
  (interval_append leafTestAt2624 16 18 20
  (interval_append leafTestAt2624 16 17 18
  leafTestAt2624_block_16
  leafTestAt2624_block_17)
  (interval_append leafTestAt2624 18 19 20
  leafTestAt2624_block_18
  leafTestAt2624_block_19))
  (interval_append leafTestAt2624 20 22 24
  (interval_append leafTestAt2624 20 21 22
  leafTestAt2624_block_20
  leafTestAt2624_block_21)
  (interval_append leafTestAt2624 22 23 24
  leafTestAt2624_block_22
  leafTestAt2624_block_23)))
  (interval_append leafTestAt2624 24 28 32
  (interval_append leafTestAt2624 24 26 28
  (interval_append leafTestAt2624 24 25 26
  leafTestAt2624_block_24
  leafTestAt2624_block_25)
  (interval_append leafTestAt2624 26 27 28
  leafTestAt2624_block_26
  leafTestAt2624_block_27))
  (interval_append leafTestAt2624 28 30 32
  (interval_append leafTestAt2624 28 29 30
  leafTestAt2624_block_28
  leafTestAt2624_block_29)
  (interval_append leafTestAt2624 30 31 32
  leafTestAt2624_block_30
  leafTestAt2624_block_31)))))
cert_leafInterval 2624 2656
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2656
cert_leafTestAt_block_2 2656 0 1
cert_leafTestAt_block_2 2656 1 2
cert_leafTestAt_block_2 2656 2 3
cert_leafTestAt_block_2 2656 3 4
cert_leafTestAt_block_2 2656 4 5
cert_leafTestAt_block_2 2656 5 6
cert_leafTestAt_block_2 2656 6 7
cert_leafTestAt_block_2 2656 7 8
cert_leafTestAt_block_2 2656 8 9
cert_leafTestAt_block_2 2656 9 10
cert_leafTestAt_block_2 2656 10 11
cert_leafTestAt_block_2 2656 11 12
cert_leafTestAt_block_2 2656 12 13
cert_leafTestAt_block_2 2656 13 14
cert_leafTestAt_block_2 2656 14 15
cert_leafTestAt_block_2 2656 15 16
cert_leafTestAt_block_2 2656 16 17
cert_leafTestAt_block_2 2656 17 18
cert_leafTestAt_block_2 2656 18 19
cert_leafTestAt_block_2 2656 19 20
cert_leafTestAt_block_2 2656 20 21
cert_leafTestAt_block_2 2656 21 22
cert_leafTestAt_block_2 2656 22 23
cert_leafTestAt_block_2 2656 23 24
cert_leafTestAt_block_2 2656 24 25
cert_leafTestAt_block_2 2656 25 26
cert_leafTestAt_block_2 2656 26 27
cert_leafTestAt_block_2 2656 27 28
cert_leafTestAt_block_2 2656 28 29
cert_leafTestAt_block_2 2656 29 30
cert_leafTestAt_block_2 2656 30 31
cert_leafTestAt_block_2 2656 31 32
theorem leafTestAt2656_complete : Interval leafTestAt2656 0 32 :=
  (interval_append leafTestAt2656 0 16 32
  (interval_append leafTestAt2656 0 8 16
  (interval_append leafTestAt2656 0 4 8
  (interval_append leafTestAt2656 0 2 4
  (interval_append leafTestAt2656 0 1 2
  leafTestAt2656_block_0
  leafTestAt2656_block_1)
  (interval_append leafTestAt2656 2 3 4
  leafTestAt2656_block_2
  leafTestAt2656_block_3))
  (interval_append leafTestAt2656 4 6 8
  (interval_append leafTestAt2656 4 5 6
  leafTestAt2656_block_4
  leafTestAt2656_block_5)
  (interval_append leafTestAt2656 6 7 8
  leafTestAt2656_block_6
  leafTestAt2656_block_7)))
  (interval_append leafTestAt2656 8 12 16
  (interval_append leafTestAt2656 8 10 12
  (interval_append leafTestAt2656 8 9 10
  leafTestAt2656_block_8
  leafTestAt2656_block_9)
  (interval_append leafTestAt2656 10 11 12
  leafTestAt2656_block_10
  leafTestAt2656_block_11))
  (interval_append leafTestAt2656 12 14 16
  (interval_append leafTestAt2656 12 13 14
  leafTestAt2656_block_12
  leafTestAt2656_block_13)
  (interval_append leafTestAt2656 14 15 16
  leafTestAt2656_block_14
  leafTestAt2656_block_15))))
  (interval_append leafTestAt2656 16 24 32
  (interval_append leafTestAt2656 16 20 24
  (interval_append leafTestAt2656 16 18 20
  (interval_append leafTestAt2656 16 17 18
  leafTestAt2656_block_16
  leafTestAt2656_block_17)
  (interval_append leafTestAt2656 18 19 20
  leafTestAt2656_block_18
  leafTestAt2656_block_19))
  (interval_append leafTestAt2656 20 22 24
  (interval_append leafTestAt2656 20 21 22
  leafTestAt2656_block_20
  leafTestAt2656_block_21)
  (interval_append leafTestAt2656 22 23 24
  leafTestAt2656_block_22
  leafTestAt2656_block_23)))
  (interval_append leafTestAt2656 24 28 32
  (interval_append leafTestAt2656 24 26 28
  (interval_append leafTestAt2656 24 25 26
  leafTestAt2656_block_24
  leafTestAt2656_block_25)
  (interval_append leafTestAt2656 26 27 28
  leafTestAt2656_block_26
  leafTestAt2656_block_27))
  (interval_append leafTestAt2656 28 30 32
  (interval_append leafTestAt2656 28 29 30
  leafTestAt2656_block_28
  leafTestAt2656_block_29)
  (interval_append leafTestAt2656 30 31 32
  leafTestAt2656_block_30
  leafTestAt2656_block_31)))))
cert_leafInterval 2656 2688
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2688
cert_leafTestAt_block_2 2688 0 1
cert_leafTestAt_block_2 2688 1 2
cert_leafTestAt_block_2 2688 2 3
cert_leafTestAt_block_2 2688 3 4
cert_leafTestAt_block_2 2688 4 5
cert_leafTestAt_block_2 2688 5 6
cert_leafTestAt_block_2 2688 6 7
cert_leafTestAt_block_2 2688 7 8
cert_leafTestAt_block_2 2688 8 9
cert_leafTestAt_block_2 2688 9 10
cert_leafTestAt_block_2 2688 10 11
cert_leafTestAt_block_2 2688 11 12
cert_leafTestAt_block_2 2688 12 13
cert_leafTestAt_block_2 2688 13 14
cert_leafTestAt_block_2 2688 14 15
cert_leafTestAt_block_2 2688 15 16
cert_leafTestAt_block_2 2688 16 17
cert_leafTestAt_block_2 2688 17 18
cert_leafTestAt_block_2 2688 18 19
cert_leafTestAt_block_2 2688 19 20
cert_leafTestAt_block_2 2688 20 21
cert_leafTestAt_block_2 2688 21 22
cert_leafTestAt_block_2 2688 22 23
cert_leafTestAt_block_2 2688 23 24
cert_leafTestAt_block_2 2688 24 25
cert_leafTestAt_block_2 2688 25 26
cert_leafTestAt_block_2 2688 26 27
cert_leafTestAt_block_2 2688 27 28
cert_leafTestAt_block_2 2688 28 29
cert_leafTestAt_block_2 2688 29 30
cert_leafTestAt_block_2 2688 30 31
cert_leafTestAt_block_2 2688 31 32
theorem leafTestAt2688_complete : Interval leafTestAt2688 0 32 :=
  (interval_append leafTestAt2688 0 16 32
  (interval_append leafTestAt2688 0 8 16
  (interval_append leafTestAt2688 0 4 8
  (interval_append leafTestAt2688 0 2 4
  (interval_append leafTestAt2688 0 1 2
  leafTestAt2688_block_0
  leafTestAt2688_block_1)
  (interval_append leafTestAt2688 2 3 4
  leafTestAt2688_block_2
  leafTestAt2688_block_3))
  (interval_append leafTestAt2688 4 6 8
  (interval_append leafTestAt2688 4 5 6
  leafTestAt2688_block_4
  leafTestAt2688_block_5)
  (interval_append leafTestAt2688 6 7 8
  leafTestAt2688_block_6
  leafTestAt2688_block_7)))
  (interval_append leafTestAt2688 8 12 16
  (interval_append leafTestAt2688 8 10 12
  (interval_append leafTestAt2688 8 9 10
  leafTestAt2688_block_8
  leafTestAt2688_block_9)
  (interval_append leafTestAt2688 10 11 12
  leafTestAt2688_block_10
  leafTestAt2688_block_11))
  (interval_append leafTestAt2688 12 14 16
  (interval_append leafTestAt2688 12 13 14
  leafTestAt2688_block_12
  leafTestAt2688_block_13)
  (interval_append leafTestAt2688 14 15 16
  leafTestAt2688_block_14
  leafTestAt2688_block_15))))
  (interval_append leafTestAt2688 16 24 32
  (interval_append leafTestAt2688 16 20 24
  (interval_append leafTestAt2688 16 18 20
  (interval_append leafTestAt2688 16 17 18
  leafTestAt2688_block_16
  leafTestAt2688_block_17)
  (interval_append leafTestAt2688 18 19 20
  leafTestAt2688_block_18
  leafTestAt2688_block_19))
  (interval_append leafTestAt2688 20 22 24
  (interval_append leafTestAt2688 20 21 22
  leafTestAt2688_block_20
  leafTestAt2688_block_21)
  (interval_append leafTestAt2688 22 23 24
  leafTestAt2688_block_22
  leafTestAt2688_block_23)))
  (interval_append leafTestAt2688 24 28 32
  (interval_append leafTestAt2688 24 26 28
  (interval_append leafTestAt2688 24 25 26
  leafTestAt2688_block_24
  leafTestAt2688_block_25)
  (interval_append leafTestAt2688 26 27 28
  leafTestAt2688_block_26
  leafTestAt2688_block_27))
  (interval_append leafTestAt2688 28 30 32
  (interval_append leafTestAt2688 28 29 30
  leafTestAt2688_block_28
  leafTestAt2688_block_29)
  (interval_append leafTestAt2688 30 31 32
  leafTestAt2688_block_30
  leafTestAt2688_block_31)))))
cert_leafInterval 2688 2720
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2720
cert_leafTestAt_block_2 2720 0 1
cert_leafTestAt_block_2 2720 1 2
cert_leafTestAt_block_2 2720 2 3
cert_leafTestAt_block_2 2720 3 4
cert_leafTestAt_block_2 2720 4 5
cert_leafTestAt_block_2 2720 5 6
cert_leafTestAt_block_2 2720 6 7
cert_leafTestAt_block_2 2720 7 8
cert_leafTestAt_block_2 2720 8 9
cert_leafTestAt_block_2 2720 9 10
cert_leafTestAt_block_2 2720 10 11
cert_leafTestAt_block_2 2720 11 12
cert_leafTestAt_block_2 2720 12 13
cert_leafTestAt_block_2 2720 13 14
cert_leafTestAt_block_2 2720 14 15
cert_leafTestAt_block_2 2720 15 16
cert_leafTestAt_block_2 2720 16 17
cert_leafTestAt_block_2 2720 17 18
cert_leafTestAt_block_2 2720 18 19
cert_leafTestAt_block_2 2720 19 20
cert_leafTestAt_block_2 2720 20 21
cert_leafTestAt_block_2 2720 21 22
cert_leafTestAt_block_2 2720 22 23
cert_leafTestAt_block_2 2720 23 24
cert_leafTestAt_block_2 2720 24 25
cert_leafTestAt_block_2 2720 25 26
cert_leafTestAt_block_2 2720 26 27
cert_leafTestAt_block_2 2720 27 28
cert_leafTestAt_block_2 2720 28 29
cert_leafTestAt_block_2 2720 29 30
cert_leafTestAt_block_2 2720 30 31
cert_leafTestAt_block_2 2720 31 32
theorem leafTestAt2720_complete : Interval leafTestAt2720 0 32 :=
  (interval_append leafTestAt2720 0 16 32
  (interval_append leafTestAt2720 0 8 16
  (interval_append leafTestAt2720 0 4 8
  (interval_append leafTestAt2720 0 2 4
  (interval_append leafTestAt2720 0 1 2
  leafTestAt2720_block_0
  leafTestAt2720_block_1)
  (interval_append leafTestAt2720 2 3 4
  leafTestAt2720_block_2
  leafTestAt2720_block_3))
  (interval_append leafTestAt2720 4 6 8
  (interval_append leafTestAt2720 4 5 6
  leafTestAt2720_block_4
  leafTestAt2720_block_5)
  (interval_append leafTestAt2720 6 7 8
  leafTestAt2720_block_6
  leafTestAt2720_block_7)))
  (interval_append leafTestAt2720 8 12 16
  (interval_append leafTestAt2720 8 10 12
  (interval_append leafTestAt2720 8 9 10
  leafTestAt2720_block_8
  leafTestAt2720_block_9)
  (interval_append leafTestAt2720 10 11 12
  leafTestAt2720_block_10
  leafTestAt2720_block_11))
  (interval_append leafTestAt2720 12 14 16
  (interval_append leafTestAt2720 12 13 14
  leafTestAt2720_block_12
  leafTestAt2720_block_13)
  (interval_append leafTestAt2720 14 15 16
  leafTestAt2720_block_14
  leafTestAt2720_block_15))))
  (interval_append leafTestAt2720 16 24 32
  (interval_append leafTestAt2720 16 20 24
  (interval_append leafTestAt2720 16 18 20
  (interval_append leafTestAt2720 16 17 18
  leafTestAt2720_block_16
  leafTestAt2720_block_17)
  (interval_append leafTestAt2720 18 19 20
  leafTestAt2720_block_18
  leafTestAt2720_block_19))
  (interval_append leafTestAt2720 20 22 24
  (interval_append leafTestAt2720 20 21 22
  leafTestAt2720_block_20
  leafTestAt2720_block_21)
  (interval_append leafTestAt2720 22 23 24
  leafTestAt2720_block_22
  leafTestAt2720_block_23)))
  (interval_append leafTestAt2720 24 28 32
  (interval_append leafTestAt2720 24 26 28
  (interval_append leafTestAt2720 24 25 26
  leafTestAt2720_block_24
  leafTestAt2720_block_25)
  (interval_append leafTestAt2720 26 27 28
  leafTestAt2720_block_26
  leafTestAt2720_block_27))
  (interval_append leafTestAt2720 28 30 32
  (interval_append leafTestAt2720 28 29 30
  leafTestAt2720_block_28
  leafTestAt2720_block_29)
  (interval_append leafTestAt2720 30 31 32
  leafTestAt2720_block_30
  leafTestAt2720_block_31)))))
cert_leafInterval 2720 2752
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2752
cert_leafTestAt_block_2 2752 0 1
cert_leafTestAt_block_2 2752 1 2
cert_leafTestAt_block_2 2752 2 3
cert_leafTestAt_block_2 2752 3 4
cert_leafTestAt_block_2 2752 4 5
cert_leafTestAt_block_2 2752 5 6
cert_leafTestAt_block_2 2752 6 7
cert_leafTestAt_block_2 2752 7 8
cert_leafTestAt_block_2 2752 8 9
cert_leafTestAt_block_2 2752 9 10
cert_leafTestAt_block_2 2752 10 11
cert_leafTestAt_block_2 2752 11 12
cert_leafTestAt_block_2 2752 12 13
cert_leafTestAt_block_2 2752 13 14
cert_leafTestAt_block_2 2752 14 15
cert_leafTestAt_block_2 2752 15 16
cert_leafTestAt_block_2 2752 16 17
cert_leafTestAt_block_2 2752 17 18
cert_leafTestAt_block_2 2752 18 19
cert_leafTestAt_block_2 2752 19 20
cert_leafTestAt_block_2 2752 20 21
cert_leafTestAt_block_2 2752 21 22
cert_leafTestAt_block_2 2752 22 23
cert_leafTestAt_block_2 2752 23 24
cert_leafTestAt_block_2 2752 24 25
cert_leafTestAt_block_2 2752 25 26
cert_leafTestAt_block_2 2752 26 27
cert_leafTestAt_block_2 2752 27 28
cert_leafTestAt_block_2 2752 28 29
cert_leafTestAt_block_2 2752 29 30
cert_leafTestAt_block_2 2752 30 31
cert_leafTestAt_block_2 2752 31 32
theorem leafTestAt2752_complete : Interval leafTestAt2752 0 32 :=
  (interval_append leafTestAt2752 0 16 32
  (interval_append leafTestAt2752 0 8 16
  (interval_append leafTestAt2752 0 4 8
  (interval_append leafTestAt2752 0 2 4
  (interval_append leafTestAt2752 0 1 2
  leafTestAt2752_block_0
  leafTestAt2752_block_1)
  (interval_append leafTestAt2752 2 3 4
  leafTestAt2752_block_2
  leafTestAt2752_block_3))
  (interval_append leafTestAt2752 4 6 8
  (interval_append leafTestAt2752 4 5 6
  leafTestAt2752_block_4
  leafTestAt2752_block_5)
  (interval_append leafTestAt2752 6 7 8
  leafTestAt2752_block_6
  leafTestAt2752_block_7)))
  (interval_append leafTestAt2752 8 12 16
  (interval_append leafTestAt2752 8 10 12
  (interval_append leafTestAt2752 8 9 10
  leafTestAt2752_block_8
  leafTestAt2752_block_9)
  (interval_append leafTestAt2752 10 11 12
  leafTestAt2752_block_10
  leafTestAt2752_block_11))
  (interval_append leafTestAt2752 12 14 16
  (interval_append leafTestAt2752 12 13 14
  leafTestAt2752_block_12
  leafTestAt2752_block_13)
  (interval_append leafTestAt2752 14 15 16
  leafTestAt2752_block_14
  leafTestAt2752_block_15))))
  (interval_append leafTestAt2752 16 24 32
  (interval_append leafTestAt2752 16 20 24
  (interval_append leafTestAt2752 16 18 20
  (interval_append leafTestAt2752 16 17 18
  leafTestAt2752_block_16
  leafTestAt2752_block_17)
  (interval_append leafTestAt2752 18 19 20
  leafTestAt2752_block_18
  leafTestAt2752_block_19))
  (interval_append leafTestAt2752 20 22 24
  (interval_append leafTestAt2752 20 21 22
  leafTestAt2752_block_20
  leafTestAt2752_block_21)
  (interval_append leafTestAt2752 22 23 24
  leafTestAt2752_block_22
  leafTestAt2752_block_23)))
  (interval_append leafTestAt2752 24 28 32
  (interval_append leafTestAt2752 24 26 28
  (interval_append leafTestAt2752 24 25 26
  leafTestAt2752_block_24
  leafTestAt2752_block_25)
  (interval_append leafTestAt2752 26 27 28
  leafTestAt2752_block_26
  leafTestAt2752_block_27))
  (interval_append leafTestAt2752 28 30 32
  (interval_append leafTestAt2752 28 29 30
  leafTestAt2752_block_28
  leafTestAt2752_block_29)
  (interval_append leafTestAt2752 30 31 32
  leafTestAt2752_block_30
  leafTestAt2752_block_31)))))
cert_leafInterval 2752 2784
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2784
cert_leafTestAt_block_2 2784 0 1
cert_leafTestAt_block_2 2784 1 2
cert_leafTestAt_block_2 2784 2 3
cert_leafTestAt_block_2 2784 3 4
cert_leafTestAt_block_2 2784 4 5
cert_leafTestAt_block_2 2784 5 6
cert_leafTestAt_block_2 2784 6 7
cert_leafTestAt_block_2 2784 7 8
cert_leafTestAt_block_2 2784 8 9
cert_leafTestAt_block_2 2784 9 10
cert_leafTestAt_block_2 2784 10 11
cert_leafTestAt_block_2 2784 11 12
cert_leafTestAt_block_2 2784 12 13
cert_leafTestAt_block_2 2784 13 14
cert_leafTestAt_block_2 2784 14 15
cert_leafTestAt_block_2 2784 15 16
cert_leafTestAt_block_2 2784 16 17
cert_leafTestAt_block_2 2784 17 18
cert_leafTestAt_block_2 2784 18 19
cert_leafTestAt_block_2 2784 19 20
cert_leafTestAt_block_2 2784 20 21
cert_leafTestAt_block_2 2784 21 22
cert_leafTestAt_block_2 2784 22 23
cert_leafTestAt_block_2 2784 23 24
cert_leafTestAt_block_2 2784 24 25
cert_leafTestAt_block_2 2784 25 26
cert_leafTestAt_block_2 2784 26 27
cert_leafTestAt_block_2 2784 27 28
cert_leafTestAt_block_2 2784 28 29
cert_leafTestAt_block_2 2784 29 30
cert_leafTestAt_block_2 2784 30 31
cert_leafTestAt_block_2 2784 31 32
theorem leafTestAt2784_complete : Interval leafTestAt2784 0 32 :=
  (interval_append leafTestAt2784 0 16 32
  (interval_append leafTestAt2784 0 8 16
  (interval_append leafTestAt2784 0 4 8
  (interval_append leafTestAt2784 0 2 4
  (interval_append leafTestAt2784 0 1 2
  leafTestAt2784_block_0
  leafTestAt2784_block_1)
  (interval_append leafTestAt2784 2 3 4
  leafTestAt2784_block_2
  leafTestAt2784_block_3))
  (interval_append leafTestAt2784 4 6 8
  (interval_append leafTestAt2784 4 5 6
  leafTestAt2784_block_4
  leafTestAt2784_block_5)
  (interval_append leafTestAt2784 6 7 8
  leafTestAt2784_block_6
  leafTestAt2784_block_7)))
  (interval_append leafTestAt2784 8 12 16
  (interval_append leafTestAt2784 8 10 12
  (interval_append leafTestAt2784 8 9 10
  leafTestAt2784_block_8
  leafTestAt2784_block_9)
  (interval_append leafTestAt2784 10 11 12
  leafTestAt2784_block_10
  leafTestAt2784_block_11))
  (interval_append leafTestAt2784 12 14 16
  (interval_append leafTestAt2784 12 13 14
  leafTestAt2784_block_12
  leafTestAt2784_block_13)
  (interval_append leafTestAt2784 14 15 16
  leafTestAt2784_block_14
  leafTestAt2784_block_15))))
  (interval_append leafTestAt2784 16 24 32
  (interval_append leafTestAt2784 16 20 24
  (interval_append leafTestAt2784 16 18 20
  (interval_append leafTestAt2784 16 17 18
  leafTestAt2784_block_16
  leafTestAt2784_block_17)
  (interval_append leafTestAt2784 18 19 20
  leafTestAt2784_block_18
  leafTestAt2784_block_19))
  (interval_append leafTestAt2784 20 22 24
  (interval_append leafTestAt2784 20 21 22
  leafTestAt2784_block_20
  leafTestAt2784_block_21)
  (interval_append leafTestAt2784 22 23 24
  leafTestAt2784_block_22
  leafTestAt2784_block_23)))
  (interval_append leafTestAt2784 24 28 32
  (interval_append leafTestAt2784 24 26 28
  (interval_append leafTestAt2784 24 25 26
  leafTestAt2784_block_24
  leafTestAt2784_block_25)
  (interval_append leafTestAt2784 26 27 28
  leafTestAt2784_block_26
  leafTestAt2784_block_27))
  (interval_append leafTestAt2784 28 30 32
  (interval_append leafTestAt2784 28 29 30
  leafTestAt2784_block_28
  leafTestAt2784_block_29)
  (interval_append leafTestAt2784 30 31 32
  leafTestAt2784_block_30
  leafTestAt2784_block_31)))))
cert_leafInterval 2784 2816
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2816
cert_leafTestAt_block_2 2816 0 1
cert_leafTestAt_block_2 2816 1 2
cert_leafTestAt_block_2 2816 2 3
cert_leafTestAt_block_2 2816 3 4
cert_leafTestAt_block_2 2816 4 5
cert_leafTestAt_block_2 2816 5 6
cert_leafTestAt_block_2 2816 6 7
cert_leafTestAt_block_2 2816 7 8
cert_leafTestAt_block_2 2816 8 9
cert_leafTestAt_block_2 2816 9 10
cert_leafTestAt_block_2 2816 10 11
cert_leafTestAt_block_2 2816 11 12
cert_leafTestAt_block_2 2816 12 13
cert_leafTestAt_block_2 2816 13 14
cert_leafTestAt_block_2 2816 14 15
cert_leafTestAt_block_2 2816 15 16
cert_leafTestAt_block_2 2816 16 17
cert_leafTestAt_block_2 2816 17 18
cert_leafTestAt_block_2 2816 18 19
cert_leafTestAt_block_2 2816 19 20
cert_leafTestAt_block_2 2816 20 21
cert_leafTestAt_block_2 2816 21 22
cert_leafTestAt_block_2 2816 22 23
cert_leafTestAt_block_2 2816 23 24
cert_leafTestAt_block_2 2816 24 25
cert_leafTestAt_block_2 2816 25 26
cert_leafTestAt_block_2 2816 26 27
cert_leafTestAt_block_2 2816 27 28
cert_leafTestAt_block_2 2816 28 29
cert_leafTestAt_block_2 2816 29 30
cert_leafTestAt_block_2 2816 30 31
cert_leafTestAt_block_2 2816 31 32
theorem leafTestAt2816_complete : Interval leafTestAt2816 0 32 :=
  (interval_append leafTestAt2816 0 16 32
  (interval_append leafTestAt2816 0 8 16
  (interval_append leafTestAt2816 0 4 8
  (interval_append leafTestAt2816 0 2 4
  (interval_append leafTestAt2816 0 1 2
  leafTestAt2816_block_0
  leafTestAt2816_block_1)
  (interval_append leafTestAt2816 2 3 4
  leafTestAt2816_block_2
  leafTestAt2816_block_3))
  (interval_append leafTestAt2816 4 6 8
  (interval_append leafTestAt2816 4 5 6
  leafTestAt2816_block_4
  leafTestAt2816_block_5)
  (interval_append leafTestAt2816 6 7 8
  leafTestAt2816_block_6
  leafTestAt2816_block_7)))
  (interval_append leafTestAt2816 8 12 16
  (interval_append leafTestAt2816 8 10 12
  (interval_append leafTestAt2816 8 9 10
  leafTestAt2816_block_8
  leafTestAt2816_block_9)
  (interval_append leafTestAt2816 10 11 12
  leafTestAt2816_block_10
  leafTestAt2816_block_11))
  (interval_append leafTestAt2816 12 14 16
  (interval_append leafTestAt2816 12 13 14
  leafTestAt2816_block_12
  leafTestAt2816_block_13)
  (interval_append leafTestAt2816 14 15 16
  leafTestAt2816_block_14
  leafTestAt2816_block_15))))
  (interval_append leafTestAt2816 16 24 32
  (interval_append leafTestAt2816 16 20 24
  (interval_append leafTestAt2816 16 18 20
  (interval_append leafTestAt2816 16 17 18
  leafTestAt2816_block_16
  leafTestAt2816_block_17)
  (interval_append leafTestAt2816 18 19 20
  leafTestAt2816_block_18
  leafTestAt2816_block_19))
  (interval_append leafTestAt2816 20 22 24
  (interval_append leafTestAt2816 20 21 22
  leafTestAt2816_block_20
  leafTestAt2816_block_21)
  (interval_append leafTestAt2816 22 23 24
  leafTestAt2816_block_22
  leafTestAt2816_block_23)))
  (interval_append leafTestAt2816 24 28 32
  (interval_append leafTestAt2816 24 26 28
  (interval_append leafTestAt2816 24 25 26
  leafTestAt2816_block_24
  leafTestAt2816_block_25)
  (interval_append leafTestAt2816 26 27 28
  leafTestAt2816_block_26
  leafTestAt2816_block_27))
  (interval_append leafTestAt2816 28 30 32
  (interval_append leafTestAt2816 28 29 30
  leafTestAt2816_block_28
  leafTestAt2816_block_29)
  (interval_append leafTestAt2816 30 31 32
  leafTestAt2816_block_30
  leafTestAt2816_block_31)))))
cert_leafInterval 2816 2848
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2848
cert_leafTestAt_block_2 2848 0 1
cert_leafTestAt_block_2 2848 1 2
cert_leafTestAt_block_2 2848 2 3
cert_leafTestAt_block_2 2848 3 4
cert_leafTestAt_block_2 2848 4 5
cert_leafTestAt_block_2 2848 5 6
cert_leafTestAt_block_2 2848 6 7
cert_leafTestAt_block_2 2848 7 8
cert_leafTestAt_block_2 2848 8 9
cert_leafTestAt_block_2 2848 9 10
cert_leafTestAt_block_2 2848 10 11
cert_leafTestAt_block_2 2848 11 12
cert_leafTestAt_block_2 2848 12 13
cert_leafTestAt_block_2 2848 13 14
cert_leafTestAt_block_2 2848 14 15
cert_leafTestAt_block_2 2848 15 16
cert_leafTestAt_block_2 2848 16 17
cert_leafTestAt_block_2 2848 17 18
cert_leafTestAt_block_2 2848 18 19
cert_leafTestAt_block_2 2848 19 20
cert_leafTestAt_block_2 2848 20 21
cert_leafTestAt_block_2 2848 21 22
cert_leafTestAt_block_2 2848 22 23
cert_leafTestAt_block_2 2848 23 24
cert_leafTestAt_block_2 2848 24 25
cert_leafTestAt_block_2 2848 25 26
cert_leafTestAt_block_2 2848 26 27
cert_leafTestAt_block_2 2848 27 28
cert_leafTestAt_block_2 2848 28 29
cert_leafTestAt_block_2 2848 29 30
cert_leafTestAt_block_2 2848 30 31
cert_leafTestAt_block_2 2848 31 32
theorem leafTestAt2848_complete : Interval leafTestAt2848 0 32 :=
  (interval_append leafTestAt2848 0 16 32
  (interval_append leafTestAt2848 0 8 16
  (interval_append leafTestAt2848 0 4 8
  (interval_append leafTestAt2848 0 2 4
  (interval_append leafTestAt2848 0 1 2
  leafTestAt2848_block_0
  leafTestAt2848_block_1)
  (interval_append leafTestAt2848 2 3 4
  leafTestAt2848_block_2
  leafTestAt2848_block_3))
  (interval_append leafTestAt2848 4 6 8
  (interval_append leafTestAt2848 4 5 6
  leafTestAt2848_block_4
  leafTestAt2848_block_5)
  (interval_append leafTestAt2848 6 7 8
  leafTestAt2848_block_6
  leafTestAt2848_block_7)))
  (interval_append leafTestAt2848 8 12 16
  (interval_append leafTestAt2848 8 10 12
  (interval_append leafTestAt2848 8 9 10
  leafTestAt2848_block_8
  leafTestAt2848_block_9)
  (interval_append leafTestAt2848 10 11 12
  leafTestAt2848_block_10
  leafTestAt2848_block_11))
  (interval_append leafTestAt2848 12 14 16
  (interval_append leafTestAt2848 12 13 14
  leafTestAt2848_block_12
  leafTestAt2848_block_13)
  (interval_append leafTestAt2848 14 15 16
  leafTestAt2848_block_14
  leafTestAt2848_block_15))))
  (interval_append leafTestAt2848 16 24 32
  (interval_append leafTestAt2848 16 20 24
  (interval_append leafTestAt2848 16 18 20
  (interval_append leafTestAt2848 16 17 18
  leafTestAt2848_block_16
  leafTestAt2848_block_17)
  (interval_append leafTestAt2848 18 19 20
  leafTestAt2848_block_18
  leafTestAt2848_block_19))
  (interval_append leafTestAt2848 20 22 24
  (interval_append leafTestAt2848 20 21 22
  leafTestAt2848_block_20
  leafTestAt2848_block_21)
  (interval_append leafTestAt2848 22 23 24
  leafTestAt2848_block_22
  leafTestAt2848_block_23)))
  (interval_append leafTestAt2848 24 28 32
  (interval_append leafTestAt2848 24 26 28
  (interval_append leafTestAt2848 24 25 26
  leafTestAt2848_block_24
  leafTestAt2848_block_25)
  (interval_append leafTestAt2848 26 27 28
  leafTestAt2848_block_26
  leafTestAt2848_block_27))
  (interval_append leafTestAt2848 28 30 32
  (interval_append leafTestAt2848 28 29 30
  leafTestAt2848_block_28
  leafTestAt2848_block_29)
  (interval_append leafTestAt2848 30 31 32
  leafTestAt2848_block_30
  leafTestAt2848_block_31)))))
cert_leafInterval 2848 2880
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2880
cert_leafTestAt_block_2 2880 0 1
cert_leafTestAt_block_2 2880 1 2
cert_leafTestAt_block_2 2880 2 3
cert_leafTestAt_block_2 2880 3 4
cert_leafTestAt_block_2 2880 4 5
cert_leafTestAt_block_2 2880 5 6
cert_leafTestAt_block_2 2880 6 7
cert_leafTestAt_block_2 2880 7 8
cert_leafTestAt_block_2 2880 8 9
cert_leafTestAt_block_2 2880 9 10
cert_leafTestAt_block_2 2880 10 11
cert_leafTestAt_block_2 2880 11 12
cert_leafTestAt_block_2 2880 12 13
cert_leafTestAt_block_2 2880 13 14
cert_leafTestAt_block_2 2880 14 15
cert_leafTestAt_block_2 2880 15 16
cert_leafTestAt_block_2 2880 16 17
cert_leafTestAt_block_2 2880 17 18
cert_leafTestAt_block_2 2880 18 19
cert_leafTestAt_block_2 2880 19 20
cert_leafTestAt_block_2 2880 20 21
cert_leafTestAt_block_2 2880 21 22
cert_leafTestAt_block_2 2880 22 23
cert_leafTestAt_block_2 2880 23 24
cert_leafTestAt_block_2 2880 24 25
cert_leafTestAt_block_2 2880 25 26
cert_leafTestAt_block_2 2880 26 27
cert_leafTestAt_block_2 2880 27 28
cert_leafTestAt_block_2 2880 28 29
cert_leafTestAt_block_2 2880 29 30
cert_leafTestAt_block_2 2880 30 31
cert_leafTestAt_block_2 2880 31 32
theorem leafTestAt2880_complete : Interval leafTestAt2880 0 32 :=
  (interval_append leafTestAt2880 0 16 32
  (interval_append leafTestAt2880 0 8 16
  (interval_append leafTestAt2880 0 4 8
  (interval_append leafTestAt2880 0 2 4
  (interval_append leafTestAt2880 0 1 2
  leafTestAt2880_block_0
  leafTestAt2880_block_1)
  (interval_append leafTestAt2880 2 3 4
  leafTestAt2880_block_2
  leafTestAt2880_block_3))
  (interval_append leafTestAt2880 4 6 8
  (interval_append leafTestAt2880 4 5 6
  leafTestAt2880_block_4
  leafTestAt2880_block_5)
  (interval_append leafTestAt2880 6 7 8
  leafTestAt2880_block_6
  leafTestAt2880_block_7)))
  (interval_append leafTestAt2880 8 12 16
  (interval_append leafTestAt2880 8 10 12
  (interval_append leafTestAt2880 8 9 10
  leafTestAt2880_block_8
  leafTestAt2880_block_9)
  (interval_append leafTestAt2880 10 11 12
  leafTestAt2880_block_10
  leafTestAt2880_block_11))
  (interval_append leafTestAt2880 12 14 16
  (interval_append leafTestAt2880 12 13 14
  leafTestAt2880_block_12
  leafTestAt2880_block_13)
  (interval_append leafTestAt2880 14 15 16
  leafTestAt2880_block_14
  leafTestAt2880_block_15))))
  (interval_append leafTestAt2880 16 24 32
  (interval_append leafTestAt2880 16 20 24
  (interval_append leafTestAt2880 16 18 20
  (interval_append leafTestAt2880 16 17 18
  leafTestAt2880_block_16
  leafTestAt2880_block_17)
  (interval_append leafTestAt2880 18 19 20
  leafTestAt2880_block_18
  leafTestAt2880_block_19))
  (interval_append leafTestAt2880 20 22 24
  (interval_append leafTestAt2880 20 21 22
  leafTestAt2880_block_20
  leafTestAt2880_block_21)
  (interval_append leafTestAt2880 22 23 24
  leafTestAt2880_block_22
  leafTestAt2880_block_23)))
  (interval_append leafTestAt2880 24 28 32
  (interval_append leafTestAt2880 24 26 28
  (interval_append leafTestAt2880 24 25 26
  leafTestAt2880_block_24
  leafTestAt2880_block_25)
  (interval_append leafTestAt2880 26 27 28
  leafTestAt2880_block_26
  leafTestAt2880_block_27))
  (interval_append leafTestAt2880 28 30 32
  (interval_append leafTestAt2880 28 29 30
  leafTestAt2880_block_28
  leafTestAt2880_block_29)
  (interval_append leafTestAt2880 30 31 32
  leafTestAt2880_block_30
  leafTestAt2880_block_31)))))
cert_leafInterval 2880 2912
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2912
cert_leafTestAt_block_2 2912 0 1
cert_leafTestAt_block_2 2912 1 2
cert_leafTestAt_block_2 2912 2 3
cert_leafTestAt_block_2 2912 3 4
cert_leafTestAt_block_2 2912 4 5
cert_leafTestAt_block_2 2912 5 6
cert_leafTestAt_block_2 2912 6 7
cert_leafTestAt_block_2 2912 7 8
cert_leafTestAt_block_2 2912 8 9
cert_leafTestAt_block_2 2912 9 10
cert_leafTestAt_block_2 2912 10 11
cert_leafTestAt_block_2 2912 11 12
cert_leafTestAt_block_2 2912 12 13
cert_leafTestAt_block_2 2912 13 14
cert_leafTestAt_block_2 2912 14 15
cert_leafTestAt_block_2 2912 15 16
cert_leafTestAt_block_2 2912 16 17
cert_leafTestAt_block_2 2912 17 18
cert_leafTestAt_block_2 2912 18 19
cert_leafTestAt_block_2 2912 19 20
cert_leafTestAt_block_2 2912 20 21
cert_leafTestAt_block_2 2912 21 22
cert_leafTestAt_block_2 2912 22 23
cert_leafTestAt_block_2 2912 23 24
cert_leafTestAt_block_2 2912 24 25
cert_leafTestAt_block_2 2912 25 26
cert_leafTestAt_block_2 2912 26 27
cert_leafTestAt_block_2 2912 27 28
cert_leafTestAt_block_2 2912 28 29
cert_leafTestAt_block_2 2912 29 30
cert_leafTestAt_block_2 2912 30 31
cert_leafTestAt_block_2 2912 31 32
theorem leafTestAt2912_complete : Interval leafTestAt2912 0 32 :=
  (interval_append leafTestAt2912 0 16 32
  (interval_append leafTestAt2912 0 8 16
  (interval_append leafTestAt2912 0 4 8
  (interval_append leafTestAt2912 0 2 4
  (interval_append leafTestAt2912 0 1 2
  leafTestAt2912_block_0
  leafTestAt2912_block_1)
  (interval_append leafTestAt2912 2 3 4
  leafTestAt2912_block_2
  leafTestAt2912_block_3))
  (interval_append leafTestAt2912 4 6 8
  (interval_append leafTestAt2912 4 5 6
  leafTestAt2912_block_4
  leafTestAt2912_block_5)
  (interval_append leafTestAt2912 6 7 8
  leafTestAt2912_block_6
  leafTestAt2912_block_7)))
  (interval_append leafTestAt2912 8 12 16
  (interval_append leafTestAt2912 8 10 12
  (interval_append leafTestAt2912 8 9 10
  leafTestAt2912_block_8
  leafTestAt2912_block_9)
  (interval_append leafTestAt2912 10 11 12
  leafTestAt2912_block_10
  leafTestAt2912_block_11))
  (interval_append leafTestAt2912 12 14 16
  (interval_append leafTestAt2912 12 13 14
  leafTestAt2912_block_12
  leafTestAt2912_block_13)
  (interval_append leafTestAt2912 14 15 16
  leafTestAt2912_block_14
  leafTestAt2912_block_15))))
  (interval_append leafTestAt2912 16 24 32
  (interval_append leafTestAt2912 16 20 24
  (interval_append leafTestAt2912 16 18 20
  (interval_append leafTestAt2912 16 17 18
  leafTestAt2912_block_16
  leafTestAt2912_block_17)
  (interval_append leafTestAt2912 18 19 20
  leafTestAt2912_block_18
  leafTestAt2912_block_19))
  (interval_append leafTestAt2912 20 22 24
  (interval_append leafTestAt2912 20 21 22
  leafTestAt2912_block_20
  leafTestAt2912_block_21)
  (interval_append leafTestAt2912 22 23 24
  leafTestAt2912_block_22
  leafTestAt2912_block_23)))
  (interval_append leafTestAt2912 24 28 32
  (interval_append leafTestAt2912 24 26 28
  (interval_append leafTestAt2912 24 25 26
  leafTestAt2912_block_24
  leafTestAt2912_block_25)
  (interval_append leafTestAt2912 26 27 28
  leafTestAt2912_block_26
  leafTestAt2912_block_27))
  (interval_append leafTestAt2912 28 30 32
  (interval_append leafTestAt2912 28 29 30
  leafTestAt2912_block_28
  leafTestAt2912_block_29)
  (interval_append leafTestAt2912 30 31 32
  leafTestAt2912_block_30
  leafTestAt2912_block_31)))))
cert_leafInterval 2912 2944
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2944
cert_leafTestAt_block_2 2944 0 1
cert_leafTestAt_block_2 2944 1 2
cert_leafTestAt_block_2 2944 2 3
cert_leafTestAt_block_2 2944 3 4
cert_leafTestAt_block_2 2944 4 5
cert_leafTestAt_block_2 2944 5 6
cert_leafTestAt_block_2 2944 6 7
cert_leafTestAt_block_2 2944 7 8
cert_leafTestAt_block_2 2944 8 9
cert_leafTestAt_block_2 2944 9 10
cert_leafTestAt_block_2 2944 10 11
cert_leafTestAt_block_2 2944 11 12
cert_leafTestAt_block_2 2944 12 13
cert_leafTestAt_block_2 2944 13 14
cert_leafTestAt_block_2 2944 14 15
cert_leafTestAt_block_2 2944 15 16
cert_leafTestAt_block_2 2944 16 17
cert_leafTestAt_block_2 2944 17 18
cert_leafTestAt_block_2 2944 18 19
cert_leafTestAt_block_2 2944 19 20
cert_leafTestAt_block_2 2944 20 21
cert_leafTestAt_block_2 2944 21 22
cert_leafTestAt_block_2 2944 22 23
cert_leafTestAt_block_2 2944 23 24
cert_leafTestAt_block_2 2944 24 25
cert_leafTestAt_block_2 2944 25 26
cert_leafTestAt_block_2 2944 26 27
cert_leafTestAt_block_2 2944 27 28
cert_leafTestAt_block_2 2944 28 29
cert_leafTestAt_block_2 2944 29 30
cert_leafTestAt_block_2 2944 30 31
cert_leafTestAt_block_2 2944 31 32
theorem leafTestAt2944_complete : Interval leafTestAt2944 0 32 :=
  (interval_append leafTestAt2944 0 16 32
  (interval_append leafTestAt2944 0 8 16
  (interval_append leafTestAt2944 0 4 8
  (interval_append leafTestAt2944 0 2 4
  (interval_append leafTestAt2944 0 1 2
  leafTestAt2944_block_0
  leafTestAt2944_block_1)
  (interval_append leafTestAt2944 2 3 4
  leafTestAt2944_block_2
  leafTestAt2944_block_3))
  (interval_append leafTestAt2944 4 6 8
  (interval_append leafTestAt2944 4 5 6
  leafTestAt2944_block_4
  leafTestAt2944_block_5)
  (interval_append leafTestAt2944 6 7 8
  leafTestAt2944_block_6
  leafTestAt2944_block_7)))
  (interval_append leafTestAt2944 8 12 16
  (interval_append leafTestAt2944 8 10 12
  (interval_append leafTestAt2944 8 9 10
  leafTestAt2944_block_8
  leafTestAt2944_block_9)
  (interval_append leafTestAt2944 10 11 12
  leafTestAt2944_block_10
  leafTestAt2944_block_11))
  (interval_append leafTestAt2944 12 14 16
  (interval_append leafTestAt2944 12 13 14
  leafTestAt2944_block_12
  leafTestAt2944_block_13)
  (interval_append leafTestAt2944 14 15 16
  leafTestAt2944_block_14
  leafTestAt2944_block_15))))
  (interval_append leafTestAt2944 16 24 32
  (interval_append leafTestAt2944 16 20 24
  (interval_append leafTestAt2944 16 18 20
  (interval_append leafTestAt2944 16 17 18
  leafTestAt2944_block_16
  leafTestAt2944_block_17)
  (interval_append leafTestAt2944 18 19 20
  leafTestAt2944_block_18
  leafTestAt2944_block_19))
  (interval_append leafTestAt2944 20 22 24
  (interval_append leafTestAt2944 20 21 22
  leafTestAt2944_block_20
  leafTestAt2944_block_21)
  (interval_append leafTestAt2944 22 23 24
  leafTestAt2944_block_22
  leafTestAt2944_block_23)))
  (interval_append leafTestAt2944 24 28 32
  (interval_append leafTestAt2944 24 26 28
  (interval_append leafTestAt2944 24 25 26
  leafTestAt2944_block_24
  leafTestAt2944_block_25)
  (interval_append leafTestAt2944 26 27 28
  leafTestAt2944_block_26
  leafTestAt2944_block_27))
  (interval_append leafTestAt2944 28 30 32
  (interval_append leafTestAt2944 28 29 30
  leafTestAt2944_block_28
  leafTestAt2944_block_29)
  (interval_append leafTestAt2944 30 31 32
  leafTestAt2944_block_30
  leafTestAt2944_block_31)))))
cert_leafInterval 2944 2976
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 2976
cert_leafTestAt_block_2 2976 0 1
cert_leafTestAt_block_2 2976 1 2
cert_leafTestAt_block_2 2976 2 3
cert_leafTestAt_block_2 2976 3 4
cert_leafTestAt_block_2 2976 4 5
cert_leafTestAt_block_2 2976 5 6
cert_leafTestAt_block_2 2976 6 7
cert_leafTestAt_block_2 2976 7 8
cert_leafTestAt_block_2 2976 8 9
cert_leafTestAt_block_2 2976 9 10
cert_leafTestAt_block_2 2976 10 11
cert_leafTestAt_block_2 2976 11 12
cert_leafTestAt_block_2 2976 12 13
cert_leafTestAt_block_2 2976 13 14
cert_leafTestAt_block_2 2976 14 15
cert_leafTestAt_block_2 2976 15 16
cert_leafTestAt_block_2 2976 16 17
cert_leafTestAt_block_2 2976 17 18
cert_leafTestAt_block_2 2976 18 19
cert_leafTestAt_block_2 2976 19 20
cert_leafTestAt_block_2 2976 20 21
cert_leafTestAt_block_2 2976 21 22
cert_leafTestAt_block_2 2976 22 23
cert_leafTestAt_block_2 2976 23 24
cert_leafTestAt_block_2 2976 24 25
cert_leafTestAt_block_2 2976 25 26
cert_leafTestAt_block_2 2976 26 27
cert_leafTestAt_block_2 2976 27 28
cert_leafTestAt_block_2 2976 28 29
cert_leafTestAt_block_2 2976 29 30
cert_leafTestAt_block_2 2976 30 31
cert_leafTestAt_block_2 2976 31 32
theorem leafTestAt2976_complete : Interval leafTestAt2976 0 32 :=
  (interval_append leafTestAt2976 0 16 32
  (interval_append leafTestAt2976 0 8 16
  (interval_append leafTestAt2976 0 4 8
  (interval_append leafTestAt2976 0 2 4
  (interval_append leafTestAt2976 0 1 2
  leafTestAt2976_block_0
  leafTestAt2976_block_1)
  (interval_append leafTestAt2976 2 3 4
  leafTestAt2976_block_2
  leafTestAt2976_block_3))
  (interval_append leafTestAt2976 4 6 8
  (interval_append leafTestAt2976 4 5 6
  leafTestAt2976_block_4
  leafTestAt2976_block_5)
  (interval_append leafTestAt2976 6 7 8
  leafTestAt2976_block_6
  leafTestAt2976_block_7)))
  (interval_append leafTestAt2976 8 12 16
  (interval_append leafTestAt2976 8 10 12
  (interval_append leafTestAt2976 8 9 10
  leafTestAt2976_block_8
  leafTestAt2976_block_9)
  (interval_append leafTestAt2976 10 11 12
  leafTestAt2976_block_10
  leafTestAt2976_block_11))
  (interval_append leafTestAt2976 12 14 16
  (interval_append leafTestAt2976 12 13 14
  leafTestAt2976_block_12
  leafTestAt2976_block_13)
  (interval_append leafTestAt2976 14 15 16
  leafTestAt2976_block_14
  leafTestAt2976_block_15))))
  (interval_append leafTestAt2976 16 24 32
  (interval_append leafTestAt2976 16 20 24
  (interval_append leafTestAt2976 16 18 20
  (interval_append leafTestAt2976 16 17 18
  leafTestAt2976_block_16
  leafTestAt2976_block_17)
  (interval_append leafTestAt2976 18 19 20
  leafTestAt2976_block_18
  leafTestAt2976_block_19))
  (interval_append leafTestAt2976 20 22 24
  (interval_append leafTestAt2976 20 21 22
  leafTestAt2976_block_20
  leafTestAt2976_block_21)
  (interval_append leafTestAt2976 22 23 24
  leafTestAt2976_block_22
  leafTestAt2976_block_23)))
  (interval_append leafTestAt2976 24 28 32
  (interval_append leafTestAt2976 24 26 28
  (interval_append leafTestAt2976 24 25 26
  leafTestAt2976_block_24
  leafTestAt2976_block_25)
  (interval_append leafTestAt2976 26 27 28
  leafTestAt2976_block_26
  leafTestAt2976_block_27))
  (interval_append leafTestAt2976 28 30 32
  (interval_append leafTestAt2976 28 29 30
  leafTestAt2976_block_28
  leafTestAt2976_block_29)
  (interval_append leafTestAt2976 30 31 32
  leafTestAt2976_block_30
  leafTestAt2976_block_31)))))
cert_leafInterval 2976 3008
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 3008
cert_leafTestAt_block_2 3008 0 1
cert_leafTestAt_block_2 3008 1 2
cert_leafTestAt_block_2 3008 2 3
cert_leafTestAt_block_2 3008 3 4
cert_leafTestAt_block_2 3008 4 5
cert_leafTestAt_block_2 3008 5 6
cert_leafTestAt_block_2 3008 6 7
cert_leafTestAt_block_2 3008 7 8
cert_leafTestAt_block_2 3008 8 9
cert_leafTestAt_block_2 3008 9 10
cert_leafTestAt_block_2 3008 10 11
cert_leafTestAt_block_2 3008 11 12
cert_leafTestAt_block_2 3008 12 13
cert_leafTestAt_block_2 3008 13 14
cert_leafTestAt_block_2 3008 14 15
cert_leafTestAt_block_2 3008 15 16
cert_leafTestAt_block_2 3008 16 17
cert_leafTestAt_block_2 3008 17 18
cert_leafTestAt_block_2 3008 18 19
cert_leafTestAt_block_2 3008 19 20
cert_leafTestAt_block_2 3008 20 21
cert_leafTestAt_block_2 3008 21 22
cert_leafTestAt_block_2 3008 22 23
cert_leafTestAt_block_2 3008 23 24
cert_leafTestAt_block_2 3008 24 25
cert_leafTestAt_block_2 3008 25 26
cert_leafTestAt_block_2 3008 26 27
cert_leafTestAt_block_2 3008 27 28
cert_leafTestAt_block_2 3008 28 29
cert_leafTestAt_block_2 3008 29 30
cert_leafTestAt_block_2 3008 30 31
cert_leafTestAt_block_2 3008 31 32
theorem leafTestAt3008_complete : Interval leafTestAt3008 0 32 :=
  (interval_append leafTestAt3008 0 16 32
  (interval_append leafTestAt3008 0 8 16
  (interval_append leafTestAt3008 0 4 8
  (interval_append leafTestAt3008 0 2 4
  (interval_append leafTestAt3008 0 1 2
  leafTestAt3008_block_0
  leafTestAt3008_block_1)
  (interval_append leafTestAt3008 2 3 4
  leafTestAt3008_block_2
  leafTestAt3008_block_3))
  (interval_append leafTestAt3008 4 6 8
  (interval_append leafTestAt3008 4 5 6
  leafTestAt3008_block_4
  leafTestAt3008_block_5)
  (interval_append leafTestAt3008 6 7 8
  leafTestAt3008_block_6
  leafTestAt3008_block_7)))
  (interval_append leafTestAt3008 8 12 16
  (interval_append leafTestAt3008 8 10 12
  (interval_append leafTestAt3008 8 9 10
  leafTestAt3008_block_8
  leafTestAt3008_block_9)
  (interval_append leafTestAt3008 10 11 12
  leafTestAt3008_block_10
  leafTestAt3008_block_11))
  (interval_append leafTestAt3008 12 14 16
  (interval_append leafTestAt3008 12 13 14
  leafTestAt3008_block_12
  leafTestAt3008_block_13)
  (interval_append leafTestAt3008 14 15 16
  leafTestAt3008_block_14
  leafTestAt3008_block_15))))
  (interval_append leafTestAt3008 16 24 32
  (interval_append leafTestAt3008 16 20 24
  (interval_append leafTestAt3008 16 18 20
  (interval_append leafTestAt3008 16 17 18
  leafTestAt3008_block_16
  leafTestAt3008_block_17)
  (interval_append leafTestAt3008 18 19 20
  leafTestAt3008_block_18
  leafTestAt3008_block_19))
  (interval_append leafTestAt3008 20 22 24
  (interval_append leafTestAt3008 20 21 22
  leafTestAt3008_block_20
  leafTestAt3008_block_21)
  (interval_append leafTestAt3008 22 23 24
  leafTestAt3008_block_22
  leafTestAt3008_block_23)))
  (interval_append leafTestAt3008 24 28 32
  (interval_append leafTestAt3008 24 26 28
  (interval_append leafTestAt3008 24 25 26
  leafTestAt3008_block_24
  leafTestAt3008_block_25)
  (interval_append leafTestAt3008 26 27 28
  leafTestAt3008_block_26
  leafTestAt3008_block_27))
  (interval_append leafTestAt3008 28 30 32
  (interval_append leafTestAt3008 28 29 30
  leafTestAt3008_block_28
  leafTestAt3008_block_29)
  (interval_append leafTestAt3008 30 31 32
  leafTestAt3008_block_30
  leafTestAt3008_block_31)))))
cert_leafInterval 3008 3040
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 3040
cert_leafTestAt_block_2 3040 0 1
cert_leafTestAt_block_2 3040 1 2
cert_leafTestAt_block_2 3040 2 3
cert_leafTestAt_block_2 3040 3 4
cert_leafTestAt_block_2 3040 4 5
cert_leafTestAt_block_2 3040 5 6
cert_leafTestAt_block_2 3040 6 7
cert_leafTestAt_block_2 3040 7 8
cert_leafTestAt_block_2 3040 8 9
cert_leafTestAt_block_2 3040 9 10
cert_leafTestAt_block_2 3040 10 11
cert_leafTestAt_block_2 3040 11 12
cert_leafTestAt_block_2 3040 12 13
cert_leafTestAt_block_2 3040 13 14
cert_leafTestAt_block_2 3040 14 15
cert_leafTestAt_block_2 3040 15 16
cert_leafTestAt_block_2 3040 16 17
cert_leafTestAt_block_2 3040 17 18
cert_leafTestAt_block_2 3040 18 19
cert_leafTestAt_block_2 3040 19 20
cert_leafTestAt_block_2 3040 20 21
cert_leafTestAt_block_2 3040 21 22
cert_leafTestAt_block_2 3040 22 23
cert_leafTestAt_block_2 3040 23 24
cert_leafTestAt_block_2 3040 24 25
cert_leafTestAt_block_2 3040 25 26
cert_leafTestAt_block_2 3040 26 27
cert_leafTestAt_block_2 3040 27 28
cert_leafTestAt_block_2 3040 28 29
cert_leafTestAt_block_2 3040 29 30
cert_leafTestAt_block_2 3040 30 31
cert_leafTestAt_block_2 3040 31 32
theorem leafTestAt3040_complete : Interval leafTestAt3040 0 32 :=
  (interval_append leafTestAt3040 0 16 32
  (interval_append leafTestAt3040 0 8 16
  (interval_append leafTestAt3040 0 4 8
  (interval_append leafTestAt3040 0 2 4
  (interval_append leafTestAt3040 0 1 2
  leafTestAt3040_block_0
  leafTestAt3040_block_1)
  (interval_append leafTestAt3040 2 3 4
  leafTestAt3040_block_2
  leafTestAt3040_block_3))
  (interval_append leafTestAt3040 4 6 8
  (interval_append leafTestAt3040 4 5 6
  leafTestAt3040_block_4
  leafTestAt3040_block_5)
  (interval_append leafTestAt3040 6 7 8
  leafTestAt3040_block_6
  leafTestAt3040_block_7)))
  (interval_append leafTestAt3040 8 12 16
  (interval_append leafTestAt3040 8 10 12
  (interval_append leafTestAt3040 8 9 10
  leafTestAt3040_block_8
  leafTestAt3040_block_9)
  (interval_append leafTestAt3040 10 11 12
  leafTestAt3040_block_10
  leafTestAt3040_block_11))
  (interval_append leafTestAt3040 12 14 16
  (interval_append leafTestAt3040 12 13 14
  leafTestAt3040_block_12
  leafTestAt3040_block_13)
  (interval_append leafTestAt3040 14 15 16
  leafTestAt3040_block_14
  leafTestAt3040_block_15))))
  (interval_append leafTestAt3040 16 24 32
  (interval_append leafTestAt3040 16 20 24
  (interval_append leafTestAt3040 16 18 20
  (interval_append leafTestAt3040 16 17 18
  leafTestAt3040_block_16
  leafTestAt3040_block_17)
  (interval_append leafTestAt3040 18 19 20
  leafTestAt3040_block_18
  leafTestAt3040_block_19))
  (interval_append leafTestAt3040 20 22 24
  (interval_append leafTestAt3040 20 21 22
  leafTestAt3040_block_20
  leafTestAt3040_block_21)
  (interval_append leafTestAt3040 22 23 24
  leafTestAt3040_block_22
  leafTestAt3040_block_23)))
  (interval_append leafTestAt3040 24 28 32
  (interval_append leafTestAt3040 24 26 28
  (interval_append leafTestAt3040 24 25 26
  leafTestAt3040_block_24
  leafTestAt3040_block_25)
  (interval_append leafTestAt3040 26 27 28
  leafTestAt3040_block_26
  leafTestAt3040_block_27))
  (interval_append leafTestAt3040 28 30 32
  (interval_append leafTestAt3040 28 29 30
  leafTestAt3040_block_28
  leafTestAt3040_block_29)
  (interval_append leafTestAt3040 30 31 32
  leafTestAt3040_block_30
  leafTestAt3040_block_31)))))
cert_leafInterval 3040 3072
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
