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
cert_leafTestAt 3584
cert_leafTestAt_block_2 3584 0 1
cert_leafTestAt_block_2 3584 1 2
cert_leafTestAt_block_2 3584 2 3
cert_leafTestAt_block_2 3584 3 4
cert_leafTestAt_block_2 3584 4 5
cert_leafTestAt_block_2 3584 5 6
cert_leafTestAt_block_2 3584 6 7
cert_leafTestAt_block_2 3584 7 8
cert_leafTestAt_block_2 3584 8 9
cert_leafTestAt_block_2 3584 9 10
cert_leafTestAt_block_2 3584 10 11
cert_leafTestAt_block_2 3584 11 12
cert_leafTestAt_block_2 3584 12 13
cert_leafTestAt_block_2 3584 13 14
cert_leafTestAt_block_2 3584 14 15
cert_leafTestAt_block_2 3584 15 16
cert_leafTestAt_block_2 3584 16 17
cert_leafTestAt_block_2 3584 17 18
cert_leafTestAt_block_2 3584 18 19
cert_leafTestAt_block_2 3584 19 20
cert_leafTestAt_block_2 3584 20 21
cert_leafTestAt_block_2 3584 21 22
cert_leafTestAt_block_2 3584 22 23
cert_leafTestAt_block_2 3584 23 24
cert_leafTestAt_block_2 3584 24 25
cert_leafTestAt_block_2 3584 25 26
cert_leafTestAt_block_2 3584 26 27
cert_leafTestAt_block_2 3584 27 28
cert_leafTestAt_block_2 3584 28 29
cert_leafTestAt_block_2 3584 29 30
cert_leafTestAt_block_2 3584 30 31
cert_leafTestAt_block_2 3584 31 32
theorem leafTestAt3584_complete : Interval leafTestAt3584 0 32 :=
  (interval_append leafTestAt3584 0 16 32
  (interval_append leafTestAt3584 0 8 16
  (interval_append leafTestAt3584 0 4 8
  (interval_append leafTestAt3584 0 2 4
  (interval_append leafTestAt3584 0 1 2
  leafTestAt3584_block_0
  leafTestAt3584_block_1)
  (interval_append leafTestAt3584 2 3 4
  leafTestAt3584_block_2
  leafTestAt3584_block_3))
  (interval_append leafTestAt3584 4 6 8
  (interval_append leafTestAt3584 4 5 6
  leafTestAt3584_block_4
  leafTestAt3584_block_5)
  (interval_append leafTestAt3584 6 7 8
  leafTestAt3584_block_6
  leafTestAt3584_block_7)))
  (interval_append leafTestAt3584 8 12 16
  (interval_append leafTestAt3584 8 10 12
  (interval_append leafTestAt3584 8 9 10
  leafTestAt3584_block_8
  leafTestAt3584_block_9)
  (interval_append leafTestAt3584 10 11 12
  leafTestAt3584_block_10
  leafTestAt3584_block_11))
  (interval_append leafTestAt3584 12 14 16
  (interval_append leafTestAt3584 12 13 14
  leafTestAt3584_block_12
  leafTestAt3584_block_13)
  (interval_append leafTestAt3584 14 15 16
  leafTestAt3584_block_14
  leafTestAt3584_block_15))))
  (interval_append leafTestAt3584 16 24 32
  (interval_append leafTestAt3584 16 20 24
  (interval_append leafTestAt3584 16 18 20
  (interval_append leafTestAt3584 16 17 18
  leafTestAt3584_block_16
  leafTestAt3584_block_17)
  (interval_append leafTestAt3584 18 19 20
  leafTestAt3584_block_18
  leafTestAt3584_block_19))
  (interval_append leafTestAt3584 20 22 24
  (interval_append leafTestAt3584 20 21 22
  leafTestAt3584_block_20
  leafTestAt3584_block_21)
  (interval_append leafTestAt3584 22 23 24
  leafTestAt3584_block_22
  leafTestAt3584_block_23)))
  (interval_append leafTestAt3584 24 28 32
  (interval_append leafTestAt3584 24 26 28
  (interval_append leafTestAt3584 24 25 26
  leafTestAt3584_block_24
  leafTestAt3584_block_25)
  (interval_append leafTestAt3584 26 27 28
  leafTestAt3584_block_26
  leafTestAt3584_block_27))
  (interval_append leafTestAt3584 28 30 32
  (interval_append leafTestAt3584 28 29 30
  leafTestAt3584_block_28
  leafTestAt3584_block_29)
  (interval_append leafTestAt3584 30 31 32
  leafTestAt3584_block_30
  leafTestAt3584_block_31)))))
cert_leafInterval 3584 3616
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
cert_leafTestAt 3616
cert_leafTestAt_block_2 3616 0 1
cert_leafTestAt_block_2 3616 1 2
cert_leafTestAt_block_2 3616 2 3
cert_leafTestAt_block_2 3616 3 4
cert_leafTestAt_block_2 3616 4 5
cert_leafTestAt_block_2 3616 5 6
cert_leafTestAt_block_2 3616 6 7
cert_leafTestAt_block_2 3616 7 8
cert_leafTestAt_block_2 3616 8 9
cert_leafTestAt_block_2 3616 9 10
cert_leafTestAt_block_2 3616 10 11
cert_leafTestAt_block_2 3616 11 12
cert_leafTestAt_block_2 3616 12 13
cert_leafTestAt_block_2 3616 13 14
cert_leafTestAt_block_2 3616 14 15
cert_leafTestAt_block_2 3616 15 16
cert_leafTestAt_block_2 3616 16 17
cert_leafTestAt_block_2 3616 17 18
cert_leafTestAt_block_2 3616 18 19
cert_leafTestAt_block_2 3616 19 20
cert_leafTestAt_block_2 3616 20 21
cert_leafTestAt_block_2 3616 21 22
cert_leafTestAt_block_2 3616 22 23
cert_leafTestAt_block_2 3616 23 24
cert_leafTestAt_block_2 3616 24 25
cert_leafTestAt_block_2 3616 25 26
cert_leafTestAt_block_2 3616 26 27
cert_leafTestAt_block_2 3616 27 28
cert_leafTestAt_block_2 3616 28 29
cert_leafTestAt_block_2 3616 29 30
cert_leafTestAt_block_2 3616 30 31
cert_leafTestAt_block_2 3616 31 32
theorem leafTestAt3616_complete : Interval leafTestAt3616 0 32 :=
  (interval_append leafTestAt3616 0 16 32
  (interval_append leafTestAt3616 0 8 16
  (interval_append leafTestAt3616 0 4 8
  (interval_append leafTestAt3616 0 2 4
  (interval_append leafTestAt3616 0 1 2
  leafTestAt3616_block_0
  leafTestAt3616_block_1)
  (interval_append leafTestAt3616 2 3 4
  leafTestAt3616_block_2
  leafTestAt3616_block_3))
  (interval_append leafTestAt3616 4 6 8
  (interval_append leafTestAt3616 4 5 6
  leafTestAt3616_block_4
  leafTestAt3616_block_5)
  (interval_append leafTestAt3616 6 7 8
  leafTestAt3616_block_6
  leafTestAt3616_block_7)))
  (interval_append leafTestAt3616 8 12 16
  (interval_append leafTestAt3616 8 10 12
  (interval_append leafTestAt3616 8 9 10
  leafTestAt3616_block_8
  leafTestAt3616_block_9)
  (interval_append leafTestAt3616 10 11 12
  leafTestAt3616_block_10
  leafTestAt3616_block_11))
  (interval_append leafTestAt3616 12 14 16
  (interval_append leafTestAt3616 12 13 14
  leafTestAt3616_block_12
  leafTestAt3616_block_13)
  (interval_append leafTestAt3616 14 15 16
  leafTestAt3616_block_14
  leafTestAt3616_block_15))))
  (interval_append leafTestAt3616 16 24 32
  (interval_append leafTestAt3616 16 20 24
  (interval_append leafTestAt3616 16 18 20
  (interval_append leafTestAt3616 16 17 18
  leafTestAt3616_block_16
  leafTestAt3616_block_17)
  (interval_append leafTestAt3616 18 19 20
  leafTestAt3616_block_18
  leafTestAt3616_block_19))
  (interval_append leafTestAt3616 20 22 24
  (interval_append leafTestAt3616 20 21 22
  leafTestAt3616_block_20
  leafTestAt3616_block_21)
  (interval_append leafTestAt3616 22 23 24
  leafTestAt3616_block_22
  leafTestAt3616_block_23)))
  (interval_append leafTestAt3616 24 28 32
  (interval_append leafTestAt3616 24 26 28
  (interval_append leafTestAt3616 24 25 26
  leafTestAt3616_block_24
  leafTestAt3616_block_25)
  (interval_append leafTestAt3616 26 27 28
  leafTestAt3616_block_26
  leafTestAt3616_block_27))
  (interval_append leafTestAt3616 28 30 32
  (interval_append leafTestAt3616 28 29 30
  leafTestAt3616_block_28
  leafTestAt3616_block_29)
  (interval_append leafTestAt3616 30 31 32
  leafTestAt3616_block_30
  leafTestAt3616_block_31)))))
cert_leafInterval 3616 3648
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
cert_leafTestAt 3648
cert_leafTestAt_block_2 3648 0 1
cert_leafTestAt_block_2 3648 1 2
cert_leafTestAt_block_2 3648 2 3
cert_leafTestAt_block_2 3648 3 4
cert_leafTestAt_block_2 3648 4 5
cert_leafTestAt_block_2 3648 5 6
cert_leafTestAt_block_2 3648 6 7
cert_leafTestAt_block_2 3648 7 8
cert_leafTestAt_block_2 3648 8 9
cert_leafTestAt_block_2 3648 9 10
cert_leafTestAt_block_2 3648 10 11
cert_leafTestAt_block_2 3648 11 12
cert_leafTestAt_block_2 3648 12 13
cert_leafTestAt_block_2 3648 13 14
cert_leafTestAt_block_2 3648 14 15
cert_leafTestAt_block_2 3648 15 16
cert_leafTestAt_block_2 3648 16 17
cert_leafTestAt_block_2 3648 17 18
cert_leafTestAt_block_2 3648 18 19
cert_leafTestAt_block_2 3648 19 20
cert_leafTestAt_block_2 3648 20 21
cert_leafTestAt_block_2 3648 21 22
cert_leafTestAt_block_2 3648 22 23
cert_leafTestAt_block_2 3648 23 24
cert_leafTestAt_block_2 3648 24 25
cert_leafTestAt_block_2 3648 25 26
cert_leafTestAt_block_2 3648 26 27
cert_leafTestAt_block_2 3648 27 28
cert_leafTestAt_block_2 3648 28 29
cert_leafTestAt_block_2 3648 29 30
cert_leafTestAt_block_2 3648 30 31
cert_leafTestAt_block_2 3648 31 32
theorem leafTestAt3648_complete : Interval leafTestAt3648 0 32 :=
  (interval_append leafTestAt3648 0 16 32
  (interval_append leafTestAt3648 0 8 16
  (interval_append leafTestAt3648 0 4 8
  (interval_append leafTestAt3648 0 2 4
  (interval_append leafTestAt3648 0 1 2
  leafTestAt3648_block_0
  leafTestAt3648_block_1)
  (interval_append leafTestAt3648 2 3 4
  leafTestAt3648_block_2
  leafTestAt3648_block_3))
  (interval_append leafTestAt3648 4 6 8
  (interval_append leafTestAt3648 4 5 6
  leafTestAt3648_block_4
  leafTestAt3648_block_5)
  (interval_append leafTestAt3648 6 7 8
  leafTestAt3648_block_6
  leafTestAt3648_block_7)))
  (interval_append leafTestAt3648 8 12 16
  (interval_append leafTestAt3648 8 10 12
  (interval_append leafTestAt3648 8 9 10
  leafTestAt3648_block_8
  leafTestAt3648_block_9)
  (interval_append leafTestAt3648 10 11 12
  leafTestAt3648_block_10
  leafTestAt3648_block_11))
  (interval_append leafTestAt3648 12 14 16
  (interval_append leafTestAt3648 12 13 14
  leafTestAt3648_block_12
  leafTestAt3648_block_13)
  (interval_append leafTestAt3648 14 15 16
  leafTestAt3648_block_14
  leafTestAt3648_block_15))))
  (interval_append leafTestAt3648 16 24 32
  (interval_append leafTestAt3648 16 20 24
  (interval_append leafTestAt3648 16 18 20
  (interval_append leafTestAt3648 16 17 18
  leafTestAt3648_block_16
  leafTestAt3648_block_17)
  (interval_append leafTestAt3648 18 19 20
  leafTestAt3648_block_18
  leafTestAt3648_block_19))
  (interval_append leafTestAt3648 20 22 24
  (interval_append leafTestAt3648 20 21 22
  leafTestAt3648_block_20
  leafTestAt3648_block_21)
  (interval_append leafTestAt3648 22 23 24
  leafTestAt3648_block_22
  leafTestAt3648_block_23)))
  (interval_append leafTestAt3648 24 28 32
  (interval_append leafTestAt3648 24 26 28
  (interval_append leafTestAt3648 24 25 26
  leafTestAt3648_block_24
  leafTestAt3648_block_25)
  (interval_append leafTestAt3648 26 27 28
  leafTestAt3648_block_26
  leafTestAt3648_block_27))
  (interval_append leafTestAt3648 28 30 32
  (interval_append leafTestAt3648 28 29 30
  leafTestAt3648_block_28
  leafTestAt3648_block_29)
  (interval_append leafTestAt3648 30 31 32
  leafTestAt3648_block_30
  leafTestAt3648_block_31)))))
cert_leafInterval 3648 3680
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
cert_leafTestAt 3680
cert_leafTestAt_block_2 3680 0 1
cert_leafTestAt_block_2 3680 1 2
cert_leafTestAt_block_2 3680 2 3
cert_leafTestAt_block_2 3680 3 4
cert_leafTestAt_block_2 3680 4 5
cert_leafTestAt_block_2 3680 5 6
cert_leafTestAt_block_2 3680 6 7
cert_leafTestAt_block_2 3680 7 8
cert_leafTestAt_block_2 3680 8 9
cert_leafTestAt_block_2 3680 9 10
cert_leafTestAt_block_2 3680 10 11
cert_leafTestAt_block_2 3680 11 12
cert_leafTestAt_block_2 3680 12 13
cert_leafTestAt_block_2 3680 13 14
cert_leafTestAt_block_2 3680 14 15
cert_leafTestAt_block_2 3680 15 16
cert_leafTestAt_block_2 3680 16 17
cert_leafTestAt_block_2 3680 17 18
cert_leafTestAt_block_2 3680 18 19
cert_leafTestAt_block_2 3680 19 20
cert_leafTestAt_block_2 3680 20 21
cert_leafTestAt_block_2 3680 21 22
cert_leafTestAt_block_2 3680 22 23
cert_leafTestAt_block_2 3680 23 24
cert_leafTestAt_block_2 3680 24 25
cert_leafTestAt_block_2 3680 25 26
cert_leafTestAt_block_2 3680 26 27
cert_leafTestAt_block_2 3680 27 28
cert_leafTestAt_block_2 3680 28 29
cert_leafTestAt_block_2 3680 29 30
cert_leafTestAt_block_2 3680 30 31
cert_leafTestAt_block_2 3680 31 32
theorem leafTestAt3680_complete : Interval leafTestAt3680 0 32 :=
  (interval_append leafTestAt3680 0 16 32
  (interval_append leafTestAt3680 0 8 16
  (interval_append leafTestAt3680 0 4 8
  (interval_append leafTestAt3680 0 2 4
  (interval_append leafTestAt3680 0 1 2
  leafTestAt3680_block_0
  leafTestAt3680_block_1)
  (interval_append leafTestAt3680 2 3 4
  leafTestAt3680_block_2
  leafTestAt3680_block_3))
  (interval_append leafTestAt3680 4 6 8
  (interval_append leafTestAt3680 4 5 6
  leafTestAt3680_block_4
  leafTestAt3680_block_5)
  (interval_append leafTestAt3680 6 7 8
  leafTestAt3680_block_6
  leafTestAt3680_block_7)))
  (interval_append leafTestAt3680 8 12 16
  (interval_append leafTestAt3680 8 10 12
  (interval_append leafTestAt3680 8 9 10
  leafTestAt3680_block_8
  leafTestAt3680_block_9)
  (interval_append leafTestAt3680 10 11 12
  leafTestAt3680_block_10
  leafTestAt3680_block_11))
  (interval_append leafTestAt3680 12 14 16
  (interval_append leafTestAt3680 12 13 14
  leafTestAt3680_block_12
  leafTestAt3680_block_13)
  (interval_append leafTestAt3680 14 15 16
  leafTestAt3680_block_14
  leafTestAt3680_block_15))))
  (interval_append leafTestAt3680 16 24 32
  (interval_append leafTestAt3680 16 20 24
  (interval_append leafTestAt3680 16 18 20
  (interval_append leafTestAt3680 16 17 18
  leafTestAt3680_block_16
  leafTestAt3680_block_17)
  (interval_append leafTestAt3680 18 19 20
  leafTestAt3680_block_18
  leafTestAt3680_block_19))
  (interval_append leafTestAt3680 20 22 24
  (interval_append leafTestAt3680 20 21 22
  leafTestAt3680_block_20
  leafTestAt3680_block_21)
  (interval_append leafTestAt3680 22 23 24
  leafTestAt3680_block_22
  leafTestAt3680_block_23)))
  (interval_append leafTestAt3680 24 28 32
  (interval_append leafTestAt3680 24 26 28
  (interval_append leafTestAt3680 24 25 26
  leafTestAt3680_block_24
  leafTestAt3680_block_25)
  (interval_append leafTestAt3680 26 27 28
  leafTestAt3680_block_26
  leafTestAt3680_block_27))
  (interval_append leafTestAt3680 28 30 32
  (interval_append leafTestAt3680 28 29 30
  leafTestAt3680_block_28
  leafTestAt3680_block_29)
  (interval_append leafTestAt3680 30 31 32
  leafTestAt3680_block_30
  leafTestAt3680_block_31)))))
cert_leafInterval 3680 3712
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
cert_leafTestAt 3712
cert_leafTestAt_block_2 3712 0 1
cert_leafTestAt_block_2 3712 1 2
cert_leafTestAt_block_2 3712 2 3
cert_leafTestAt_block_2 3712 3 4
cert_leafTestAt_block_2 3712 4 5
cert_leafTestAt_block_2 3712 5 6
cert_leafTestAt_block_2 3712 6 7
cert_leafTestAt_block_2 3712 7 8
cert_leafTestAt_block_2 3712 8 9
cert_leafTestAt_block_2 3712 9 10
cert_leafTestAt_block_2 3712 10 11
cert_leafTestAt_block_2 3712 11 12
cert_leafTestAt_block_2 3712 12 13
cert_leafTestAt_block_2 3712 13 14
cert_leafTestAt_block_2 3712 14 15
cert_leafTestAt_block_2 3712 15 16
cert_leafTestAt_block_2 3712 16 17
cert_leafTestAt_block_2 3712 17 18
cert_leafTestAt_block_2 3712 18 19
cert_leafTestAt_block_2 3712 19 20
cert_leafTestAt_block_2 3712 20 21
cert_leafTestAt_block_2 3712 21 22
cert_leafTestAt_block_2 3712 22 23
cert_leafTestAt_block_2 3712 23 24
cert_leafTestAt_block_2 3712 24 25
cert_leafTestAt_block_2 3712 25 26
cert_leafTestAt_block_2 3712 26 27
cert_leafTestAt_block_2 3712 27 28
cert_leafTestAt_block_2 3712 28 29
cert_leafTestAt_block_2 3712 29 30
cert_leafTestAt_block_2 3712 30 31
cert_leafTestAt_block_2 3712 31 32
theorem leafTestAt3712_complete : Interval leafTestAt3712 0 32 :=
  (interval_append leafTestAt3712 0 16 32
  (interval_append leafTestAt3712 0 8 16
  (interval_append leafTestAt3712 0 4 8
  (interval_append leafTestAt3712 0 2 4
  (interval_append leafTestAt3712 0 1 2
  leafTestAt3712_block_0
  leafTestAt3712_block_1)
  (interval_append leafTestAt3712 2 3 4
  leafTestAt3712_block_2
  leafTestAt3712_block_3))
  (interval_append leafTestAt3712 4 6 8
  (interval_append leafTestAt3712 4 5 6
  leafTestAt3712_block_4
  leafTestAt3712_block_5)
  (interval_append leafTestAt3712 6 7 8
  leafTestAt3712_block_6
  leafTestAt3712_block_7)))
  (interval_append leafTestAt3712 8 12 16
  (interval_append leafTestAt3712 8 10 12
  (interval_append leafTestAt3712 8 9 10
  leafTestAt3712_block_8
  leafTestAt3712_block_9)
  (interval_append leafTestAt3712 10 11 12
  leafTestAt3712_block_10
  leafTestAt3712_block_11))
  (interval_append leafTestAt3712 12 14 16
  (interval_append leafTestAt3712 12 13 14
  leafTestAt3712_block_12
  leafTestAt3712_block_13)
  (interval_append leafTestAt3712 14 15 16
  leafTestAt3712_block_14
  leafTestAt3712_block_15))))
  (interval_append leafTestAt3712 16 24 32
  (interval_append leafTestAt3712 16 20 24
  (interval_append leafTestAt3712 16 18 20
  (interval_append leafTestAt3712 16 17 18
  leafTestAt3712_block_16
  leafTestAt3712_block_17)
  (interval_append leafTestAt3712 18 19 20
  leafTestAt3712_block_18
  leafTestAt3712_block_19))
  (interval_append leafTestAt3712 20 22 24
  (interval_append leafTestAt3712 20 21 22
  leafTestAt3712_block_20
  leafTestAt3712_block_21)
  (interval_append leafTestAt3712 22 23 24
  leafTestAt3712_block_22
  leafTestAt3712_block_23)))
  (interval_append leafTestAt3712 24 28 32
  (interval_append leafTestAt3712 24 26 28
  (interval_append leafTestAt3712 24 25 26
  leafTestAt3712_block_24
  leafTestAt3712_block_25)
  (interval_append leafTestAt3712 26 27 28
  leafTestAt3712_block_26
  leafTestAt3712_block_27))
  (interval_append leafTestAt3712 28 30 32
  (interval_append leafTestAt3712 28 29 30
  leafTestAt3712_block_28
  leafTestAt3712_block_29)
  (interval_append leafTestAt3712 30 31 32
  leafTestAt3712_block_30
  leafTestAt3712_block_31)))))
cert_leafInterval 3712 3744
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
cert_leafTestAt 3744
cert_leafTestAt_block_2 3744 0 1
cert_leafTestAt_block_2 3744 1 2
cert_leafTestAt_block_2 3744 2 3
cert_leafTestAt_block_2 3744 3 4
cert_leafTestAt_block_2 3744 4 5
cert_leafTestAt_block_2 3744 5 6
cert_leafTestAt_block_2 3744 6 7
cert_leafTestAt_block_2 3744 7 8
cert_leafTestAt_block_2 3744 8 9
cert_leafTestAt_block_2 3744 9 10
cert_leafTestAt_block_2 3744 10 11
cert_leafTestAt_block_2 3744 11 12
cert_leafTestAt_block_2 3744 12 13
cert_leafTestAt_block_2 3744 13 14
cert_leafTestAt_block_2 3744 14 15
cert_leafTestAt_block_2 3744 15 16
cert_leafTestAt_block_2 3744 16 17
cert_leafTestAt_block_2 3744 17 18
cert_leafTestAt_block_2 3744 18 19
cert_leafTestAt_block_2 3744 19 20
cert_leafTestAt_block_2 3744 20 21
cert_leafTestAt_block_2 3744 21 22
cert_leafTestAt_block_2 3744 22 23
cert_leafTestAt_block_2 3744 23 24
cert_leafTestAt_block_2 3744 24 25
cert_leafTestAt_block_2 3744 25 26
cert_leafTestAt_block_2 3744 26 27
cert_leafTestAt_block_2 3744 27 28
cert_leafTestAt_block_2 3744 28 29
cert_leafTestAt_block_2 3744 29 30
cert_leafTestAt_block_2 3744 30 31
cert_leafTestAt_block_2 3744 31 32
theorem leafTestAt3744_complete : Interval leafTestAt3744 0 32 :=
  (interval_append leafTestAt3744 0 16 32
  (interval_append leafTestAt3744 0 8 16
  (interval_append leafTestAt3744 0 4 8
  (interval_append leafTestAt3744 0 2 4
  (interval_append leafTestAt3744 0 1 2
  leafTestAt3744_block_0
  leafTestAt3744_block_1)
  (interval_append leafTestAt3744 2 3 4
  leafTestAt3744_block_2
  leafTestAt3744_block_3))
  (interval_append leafTestAt3744 4 6 8
  (interval_append leafTestAt3744 4 5 6
  leafTestAt3744_block_4
  leafTestAt3744_block_5)
  (interval_append leafTestAt3744 6 7 8
  leafTestAt3744_block_6
  leafTestAt3744_block_7)))
  (interval_append leafTestAt3744 8 12 16
  (interval_append leafTestAt3744 8 10 12
  (interval_append leafTestAt3744 8 9 10
  leafTestAt3744_block_8
  leafTestAt3744_block_9)
  (interval_append leafTestAt3744 10 11 12
  leafTestAt3744_block_10
  leafTestAt3744_block_11))
  (interval_append leafTestAt3744 12 14 16
  (interval_append leafTestAt3744 12 13 14
  leafTestAt3744_block_12
  leafTestAt3744_block_13)
  (interval_append leafTestAt3744 14 15 16
  leafTestAt3744_block_14
  leafTestAt3744_block_15))))
  (interval_append leafTestAt3744 16 24 32
  (interval_append leafTestAt3744 16 20 24
  (interval_append leafTestAt3744 16 18 20
  (interval_append leafTestAt3744 16 17 18
  leafTestAt3744_block_16
  leafTestAt3744_block_17)
  (interval_append leafTestAt3744 18 19 20
  leafTestAt3744_block_18
  leafTestAt3744_block_19))
  (interval_append leafTestAt3744 20 22 24
  (interval_append leafTestAt3744 20 21 22
  leafTestAt3744_block_20
  leafTestAt3744_block_21)
  (interval_append leafTestAt3744 22 23 24
  leafTestAt3744_block_22
  leafTestAt3744_block_23)))
  (interval_append leafTestAt3744 24 28 32
  (interval_append leafTestAt3744 24 26 28
  (interval_append leafTestAt3744 24 25 26
  leafTestAt3744_block_24
  leafTestAt3744_block_25)
  (interval_append leafTestAt3744 26 27 28
  leafTestAt3744_block_26
  leafTestAt3744_block_27))
  (interval_append leafTestAt3744 28 30 32
  (interval_append leafTestAt3744 28 29 30
  leafTestAt3744_block_28
  leafTestAt3744_block_29)
  (interval_append leafTestAt3744 30 31 32
  leafTestAt3744_block_30
  leafTestAt3744_block_31)))))
cert_leafInterval 3744 3776
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
cert_leafTestAt 3776
cert_leafTestAt_block_2 3776 0 1
cert_leafTestAt_block_2 3776 1 2
cert_leafTestAt_block_2 3776 2 3
cert_leafTestAt_block_2 3776 3 4
cert_leafTestAt_block_2 3776 4 5
cert_leafTestAt_block_2 3776 5 6
cert_leafTestAt_block_2 3776 6 7
cert_leafTestAt_block_2 3776 7 8
cert_leafTestAt_block_2 3776 8 9
cert_leafTestAt_block_2 3776 9 10
cert_leafTestAt_block_2 3776 10 11
cert_leafTestAt_block_2 3776 11 12
cert_leafTestAt_block_2 3776 12 13
cert_leafTestAt_block_2 3776 13 14
cert_leafTestAt_block_2 3776 14 15
cert_leafTestAt_block_2 3776 15 16
cert_leafTestAt_block_2 3776 16 17
cert_leafTestAt_block_2 3776 17 18
cert_leafTestAt_block_2 3776 18 19
cert_leafTestAt_block_2 3776 19 20
cert_leafTestAt_block_2 3776 20 21
cert_leafTestAt_block_2 3776 21 22
cert_leafTestAt_block_2 3776 22 23
cert_leafTestAt_block_2 3776 23 24
cert_leafTestAt_block_2 3776 24 25
cert_leafTestAt_block_2 3776 25 26
cert_leafTestAt_block_2 3776 26 27
cert_leafTestAt_block_2 3776 27 28
cert_leafTestAt_block_2 3776 28 29
cert_leafTestAt_block_2 3776 29 30
cert_leafTestAt_block_2 3776 30 31
cert_leafTestAt_block_2 3776 31 32
theorem leafTestAt3776_complete : Interval leafTestAt3776 0 32 :=
  (interval_append leafTestAt3776 0 16 32
  (interval_append leafTestAt3776 0 8 16
  (interval_append leafTestAt3776 0 4 8
  (interval_append leafTestAt3776 0 2 4
  (interval_append leafTestAt3776 0 1 2
  leafTestAt3776_block_0
  leafTestAt3776_block_1)
  (interval_append leafTestAt3776 2 3 4
  leafTestAt3776_block_2
  leafTestAt3776_block_3))
  (interval_append leafTestAt3776 4 6 8
  (interval_append leafTestAt3776 4 5 6
  leafTestAt3776_block_4
  leafTestAt3776_block_5)
  (interval_append leafTestAt3776 6 7 8
  leafTestAt3776_block_6
  leafTestAt3776_block_7)))
  (interval_append leafTestAt3776 8 12 16
  (interval_append leafTestAt3776 8 10 12
  (interval_append leafTestAt3776 8 9 10
  leafTestAt3776_block_8
  leafTestAt3776_block_9)
  (interval_append leafTestAt3776 10 11 12
  leafTestAt3776_block_10
  leafTestAt3776_block_11))
  (interval_append leafTestAt3776 12 14 16
  (interval_append leafTestAt3776 12 13 14
  leafTestAt3776_block_12
  leafTestAt3776_block_13)
  (interval_append leafTestAt3776 14 15 16
  leafTestAt3776_block_14
  leafTestAt3776_block_15))))
  (interval_append leafTestAt3776 16 24 32
  (interval_append leafTestAt3776 16 20 24
  (interval_append leafTestAt3776 16 18 20
  (interval_append leafTestAt3776 16 17 18
  leafTestAt3776_block_16
  leafTestAt3776_block_17)
  (interval_append leafTestAt3776 18 19 20
  leafTestAt3776_block_18
  leafTestAt3776_block_19))
  (interval_append leafTestAt3776 20 22 24
  (interval_append leafTestAt3776 20 21 22
  leafTestAt3776_block_20
  leafTestAt3776_block_21)
  (interval_append leafTestAt3776 22 23 24
  leafTestAt3776_block_22
  leafTestAt3776_block_23)))
  (interval_append leafTestAt3776 24 28 32
  (interval_append leafTestAt3776 24 26 28
  (interval_append leafTestAt3776 24 25 26
  leafTestAt3776_block_24
  leafTestAt3776_block_25)
  (interval_append leafTestAt3776 26 27 28
  leafTestAt3776_block_26
  leafTestAt3776_block_27))
  (interval_append leafTestAt3776 28 30 32
  (interval_append leafTestAt3776 28 29 30
  leafTestAt3776_block_28
  leafTestAt3776_block_29)
  (interval_append leafTestAt3776 30 31 32
  leafTestAt3776_block_30
  leafTestAt3776_block_31)))))
cert_leafInterval 3776 3808
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
cert_leafTestAt 3808
cert_leafTestAt_block_2 3808 0 1
cert_leafTestAt_block_2 3808 1 2
cert_leafTestAt_block_2 3808 2 3
cert_leafTestAt_block_2 3808 3 4
cert_leafTestAt_block_2 3808 4 5
cert_leafTestAt_block_2 3808 5 6
cert_leafTestAt_block_2 3808 6 7
cert_leafTestAt_block_2 3808 7 8
cert_leafTestAt_block_2 3808 8 9
cert_leafTestAt_block_2 3808 9 10
cert_leafTestAt_block_2 3808 10 11
cert_leafTestAt_block_2 3808 11 12
cert_leafTestAt_block_2 3808 12 13
cert_leafTestAt_block_2 3808 13 14
cert_leafTestAt_block_2 3808 14 15
cert_leafTestAt_block_2 3808 15 16
cert_leafTestAt_block_2 3808 16 17
cert_leafTestAt_block_2 3808 17 18
cert_leafTestAt_block_2 3808 18 19
cert_leafTestAt_block_2 3808 19 20
cert_leafTestAt_block_2 3808 20 21
cert_leafTestAt_block_2 3808 21 22
cert_leafTestAt_block_2 3808 22 23
cert_leafTestAt_block_2 3808 23 24
cert_leafTestAt_block_2 3808 24 25
cert_leafTestAt_block_2 3808 25 26
cert_leafTestAt_block_2 3808 26 27
cert_leafTestAt_block_2 3808 27 28
cert_leafTestAt_block_2 3808 28 29
cert_leafTestAt_block_2 3808 29 30
cert_leafTestAt_block_2 3808 30 31
cert_leafTestAt_block_2 3808 31 32
theorem leafTestAt3808_complete : Interval leafTestAt3808 0 32 :=
  (interval_append leafTestAt3808 0 16 32
  (interval_append leafTestAt3808 0 8 16
  (interval_append leafTestAt3808 0 4 8
  (interval_append leafTestAt3808 0 2 4
  (interval_append leafTestAt3808 0 1 2
  leafTestAt3808_block_0
  leafTestAt3808_block_1)
  (interval_append leafTestAt3808 2 3 4
  leafTestAt3808_block_2
  leafTestAt3808_block_3))
  (interval_append leafTestAt3808 4 6 8
  (interval_append leafTestAt3808 4 5 6
  leafTestAt3808_block_4
  leafTestAt3808_block_5)
  (interval_append leafTestAt3808 6 7 8
  leafTestAt3808_block_6
  leafTestAt3808_block_7)))
  (interval_append leafTestAt3808 8 12 16
  (interval_append leafTestAt3808 8 10 12
  (interval_append leafTestAt3808 8 9 10
  leafTestAt3808_block_8
  leafTestAt3808_block_9)
  (interval_append leafTestAt3808 10 11 12
  leafTestAt3808_block_10
  leafTestAt3808_block_11))
  (interval_append leafTestAt3808 12 14 16
  (interval_append leafTestAt3808 12 13 14
  leafTestAt3808_block_12
  leafTestAt3808_block_13)
  (interval_append leafTestAt3808 14 15 16
  leafTestAt3808_block_14
  leafTestAt3808_block_15))))
  (interval_append leafTestAt3808 16 24 32
  (interval_append leafTestAt3808 16 20 24
  (interval_append leafTestAt3808 16 18 20
  (interval_append leafTestAt3808 16 17 18
  leafTestAt3808_block_16
  leafTestAt3808_block_17)
  (interval_append leafTestAt3808 18 19 20
  leafTestAt3808_block_18
  leafTestAt3808_block_19))
  (interval_append leafTestAt3808 20 22 24
  (interval_append leafTestAt3808 20 21 22
  leafTestAt3808_block_20
  leafTestAt3808_block_21)
  (interval_append leafTestAt3808 22 23 24
  leafTestAt3808_block_22
  leafTestAt3808_block_23)))
  (interval_append leafTestAt3808 24 28 32
  (interval_append leafTestAt3808 24 26 28
  (interval_append leafTestAt3808 24 25 26
  leafTestAt3808_block_24
  leafTestAt3808_block_25)
  (interval_append leafTestAt3808 26 27 28
  leafTestAt3808_block_26
  leafTestAt3808_block_27))
  (interval_append leafTestAt3808 28 30 32
  (interval_append leafTestAt3808 28 29 30
  leafTestAt3808_block_28
  leafTestAt3808_block_29)
  (interval_append leafTestAt3808 30 31 32
  leafTestAt3808_block_30
  leafTestAt3808_block_31)))))
cert_leafInterval 3808 3840
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
cert_leafTestAt 3840
cert_leafTestAt_block_2 3840 0 1
cert_leafTestAt_block_2 3840 1 2
cert_leafTestAt_block_2 3840 2 3
cert_leafTestAt_block_2 3840 3 4
cert_leafTestAt_block_2 3840 4 5
cert_leafTestAt_block_2 3840 5 6
cert_leafTestAt_block_2 3840 6 7
cert_leafTestAt_block_2 3840 7 8
cert_leafTestAt_block_2 3840 8 9
cert_leafTestAt_block_2 3840 9 10
cert_leafTestAt_block_2 3840 10 11
cert_leafTestAt_block_2 3840 11 12
cert_leafTestAt_block_2 3840 12 13
cert_leafTestAt_block_2 3840 13 14
cert_leafTestAt_block_2 3840 14 15
cert_leafTestAt_block_2 3840 15 16
cert_leafTestAt_block_2 3840 16 17
cert_leafTestAt_block_2 3840 17 18
cert_leafTestAt_block_2 3840 18 19
cert_leafTestAt_block_2 3840 19 20
cert_leafTestAt_block_2 3840 20 21
cert_leafTestAt_block_2 3840 21 22
cert_leafTestAt_block_2 3840 22 23
cert_leafTestAt_block_2 3840 23 24
cert_leafTestAt_block_2 3840 24 25
cert_leafTestAt_block_2 3840 25 26
cert_leafTestAt_block_2 3840 26 27
cert_leafTestAt_block_2 3840 27 28
cert_leafTestAt_block_2 3840 28 29
cert_leafTestAt_block_2 3840 29 30
cert_leafTestAt_block_2 3840 30 31
cert_leafTestAt_block_2 3840 31 32
theorem leafTestAt3840_complete : Interval leafTestAt3840 0 32 :=
  (interval_append leafTestAt3840 0 16 32
  (interval_append leafTestAt3840 0 8 16
  (interval_append leafTestAt3840 0 4 8
  (interval_append leafTestAt3840 0 2 4
  (interval_append leafTestAt3840 0 1 2
  leafTestAt3840_block_0
  leafTestAt3840_block_1)
  (interval_append leafTestAt3840 2 3 4
  leafTestAt3840_block_2
  leafTestAt3840_block_3))
  (interval_append leafTestAt3840 4 6 8
  (interval_append leafTestAt3840 4 5 6
  leafTestAt3840_block_4
  leafTestAt3840_block_5)
  (interval_append leafTestAt3840 6 7 8
  leafTestAt3840_block_6
  leafTestAt3840_block_7)))
  (interval_append leafTestAt3840 8 12 16
  (interval_append leafTestAt3840 8 10 12
  (interval_append leafTestAt3840 8 9 10
  leafTestAt3840_block_8
  leafTestAt3840_block_9)
  (interval_append leafTestAt3840 10 11 12
  leafTestAt3840_block_10
  leafTestAt3840_block_11))
  (interval_append leafTestAt3840 12 14 16
  (interval_append leafTestAt3840 12 13 14
  leafTestAt3840_block_12
  leafTestAt3840_block_13)
  (interval_append leafTestAt3840 14 15 16
  leafTestAt3840_block_14
  leafTestAt3840_block_15))))
  (interval_append leafTestAt3840 16 24 32
  (interval_append leafTestAt3840 16 20 24
  (interval_append leafTestAt3840 16 18 20
  (interval_append leafTestAt3840 16 17 18
  leafTestAt3840_block_16
  leafTestAt3840_block_17)
  (interval_append leafTestAt3840 18 19 20
  leafTestAt3840_block_18
  leafTestAt3840_block_19))
  (interval_append leafTestAt3840 20 22 24
  (interval_append leafTestAt3840 20 21 22
  leafTestAt3840_block_20
  leafTestAt3840_block_21)
  (interval_append leafTestAt3840 22 23 24
  leafTestAt3840_block_22
  leafTestAt3840_block_23)))
  (interval_append leafTestAt3840 24 28 32
  (interval_append leafTestAt3840 24 26 28
  (interval_append leafTestAt3840 24 25 26
  leafTestAt3840_block_24
  leafTestAt3840_block_25)
  (interval_append leafTestAt3840 26 27 28
  leafTestAt3840_block_26
  leafTestAt3840_block_27))
  (interval_append leafTestAt3840 28 30 32
  (interval_append leafTestAt3840 28 29 30
  leafTestAt3840_block_28
  leafTestAt3840_block_29)
  (interval_append leafTestAt3840 30 31 32
  leafTestAt3840_block_30
  leafTestAt3840_block_31)))))
cert_leafInterval 3840 3872
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
cert_leafTestAt 3872
cert_leafTestAt_block_2 3872 0 1
cert_leafTestAt_block_2 3872 1 2
cert_leafTestAt_block_2 3872 2 3
cert_leafTestAt_block_2 3872 3 4
cert_leafTestAt_block_2 3872 4 5
cert_leafTestAt_block_2 3872 5 6
cert_leafTestAt_block_2 3872 6 7
cert_leafTestAt_block_2 3872 7 8
cert_leafTestAt_block_2 3872 8 9
cert_leafTestAt_block_2 3872 9 10
cert_leafTestAt_block_2 3872 10 11
cert_leafTestAt_block_2 3872 11 12
cert_leafTestAt_block_2 3872 12 13
cert_leafTestAt_block_2 3872 13 14
cert_leafTestAt_block_2 3872 14 15
cert_leafTestAt_block_2 3872 15 16
cert_leafTestAt_block_2 3872 16 17
cert_leafTestAt_block_2 3872 17 18
cert_leafTestAt_block_2 3872 18 19
cert_leafTestAt_block_2 3872 19 20
cert_leafTestAt_block_2 3872 20 21
cert_leafTestAt_block_2 3872 21 22
cert_leafTestAt_block_2 3872 22 23
cert_leafTestAt_block_2 3872 23 24
cert_leafTestAt_block_2 3872 24 25
cert_leafTestAt_block_2 3872 25 26
cert_leafTestAt_block_2 3872 26 27
cert_leafTestAt_block_2 3872 27 28
cert_leafTestAt_block_2 3872 28 29
cert_leafTestAt_block_2 3872 29 30
cert_leafTestAt_block_2 3872 30 31
cert_leafTestAt_block_2 3872 31 32
theorem leafTestAt3872_complete : Interval leafTestAt3872 0 32 :=
  (interval_append leafTestAt3872 0 16 32
  (interval_append leafTestAt3872 0 8 16
  (interval_append leafTestAt3872 0 4 8
  (interval_append leafTestAt3872 0 2 4
  (interval_append leafTestAt3872 0 1 2
  leafTestAt3872_block_0
  leafTestAt3872_block_1)
  (interval_append leafTestAt3872 2 3 4
  leafTestAt3872_block_2
  leafTestAt3872_block_3))
  (interval_append leafTestAt3872 4 6 8
  (interval_append leafTestAt3872 4 5 6
  leafTestAt3872_block_4
  leafTestAt3872_block_5)
  (interval_append leafTestAt3872 6 7 8
  leafTestAt3872_block_6
  leafTestAt3872_block_7)))
  (interval_append leafTestAt3872 8 12 16
  (interval_append leafTestAt3872 8 10 12
  (interval_append leafTestAt3872 8 9 10
  leafTestAt3872_block_8
  leafTestAt3872_block_9)
  (interval_append leafTestAt3872 10 11 12
  leafTestAt3872_block_10
  leafTestAt3872_block_11))
  (interval_append leafTestAt3872 12 14 16
  (interval_append leafTestAt3872 12 13 14
  leafTestAt3872_block_12
  leafTestAt3872_block_13)
  (interval_append leafTestAt3872 14 15 16
  leafTestAt3872_block_14
  leafTestAt3872_block_15))))
  (interval_append leafTestAt3872 16 24 32
  (interval_append leafTestAt3872 16 20 24
  (interval_append leafTestAt3872 16 18 20
  (interval_append leafTestAt3872 16 17 18
  leafTestAt3872_block_16
  leafTestAt3872_block_17)
  (interval_append leafTestAt3872 18 19 20
  leafTestAt3872_block_18
  leafTestAt3872_block_19))
  (interval_append leafTestAt3872 20 22 24
  (interval_append leafTestAt3872 20 21 22
  leafTestAt3872_block_20
  leafTestAt3872_block_21)
  (interval_append leafTestAt3872 22 23 24
  leafTestAt3872_block_22
  leafTestAt3872_block_23)))
  (interval_append leafTestAt3872 24 28 32
  (interval_append leafTestAt3872 24 26 28
  (interval_append leafTestAt3872 24 25 26
  leafTestAt3872_block_24
  leafTestAt3872_block_25)
  (interval_append leafTestAt3872 26 27 28
  leafTestAt3872_block_26
  leafTestAt3872_block_27))
  (interval_append leafTestAt3872 28 30 32
  (interval_append leafTestAt3872 28 29 30
  leafTestAt3872_block_28
  leafTestAt3872_block_29)
  (interval_append leafTestAt3872 30 31 32
  leafTestAt3872_block_30
  leafTestAt3872_block_31)))))
cert_leafInterval 3872 3904
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
cert_leafTestAt 3904
cert_leafTestAt_block_2 3904 0 1
cert_leafTestAt_block_2 3904 1 2
cert_leafTestAt_block_2 3904 2 3
cert_leafTestAt_block_2 3904 3 4
cert_leafTestAt_block_2 3904 4 5
cert_leafTestAt_block_2 3904 5 6
cert_leafTestAt_block_2 3904 6 7
cert_leafTestAt_block_2 3904 7 8
cert_leafTestAt_block_2 3904 8 9
cert_leafTestAt_block_2 3904 9 10
cert_leafTestAt_block_2 3904 10 11
cert_leafTestAt_block_2 3904 11 12
cert_leafTestAt_block_2 3904 12 13
cert_leafTestAt_block_2 3904 13 14
cert_leafTestAt_block_2 3904 14 15
cert_leafTestAt_block_2 3904 15 16
cert_leafTestAt_block_2 3904 16 17
cert_leafTestAt_block_2 3904 17 18
cert_leafTestAt_block_2 3904 18 19
cert_leafTestAt_block_2 3904 19 20
cert_leafTestAt_block_2 3904 20 21
cert_leafTestAt_block_2 3904 21 22
cert_leafTestAt_block_2 3904 22 23
cert_leafTestAt_block_2 3904 23 24
cert_leafTestAt_block_2 3904 24 25
cert_leafTestAt_block_2 3904 25 26
cert_leafTestAt_block_2 3904 26 27
cert_leafTestAt_block_2 3904 27 28
cert_leafTestAt_block_2 3904 28 29
cert_leafTestAt_block_2 3904 29 30
cert_leafTestAt_block_2 3904 30 31
cert_leafTestAt_block_2 3904 31 32
theorem leafTestAt3904_complete : Interval leafTestAt3904 0 32 :=
  (interval_append leafTestAt3904 0 16 32
  (interval_append leafTestAt3904 0 8 16
  (interval_append leafTestAt3904 0 4 8
  (interval_append leafTestAt3904 0 2 4
  (interval_append leafTestAt3904 0 1 2
  leafTestAt3904_block_0
  leafTestAt3904_block_1)
  (interval_append leafTestAt3904 2 3 4
  leafTestAt3904_block_2
  leafTestAt3904_block_3))
  (interval_append leafTestAt3904 4 6 8
  (interval_append leafTestAt3904 4 5 6
  leafTestAt3904_block_4
  leafTestAt3904_block_5)
  (interval_append leafTestAt3904 6 7 8
  leafTestAt3904_block_6
  leafTestAt3904_block_7)))
  (interval_append leafTestAt3904 8 12 16
  (interval_append leafTestAt3904 8 10 12
  (interval_append leafTestAt3904 8 9 10
  leafTestAt3904_block_8
  leafTestAt3904_block_9)
  (interval_append leafTestAt3904 10 11 12
  leafTestAt3904_block_10
  leafTestAt3904_block_11))
  (interval_append leafTestAt3904 12 14 16
  (interval_append leafTestAt3904 12 13 14
  leafTestAt3904_block_12
  leafTestAt3904_block_13)
  (interval_append leafTestAt3904 14 15 16
  leafTestAt3904_block_14
  leafTestAt3904_block_15))))
  (interval_append leafTestAt3904 16 24 32
  (interval_append leafTestAt3904 16 20 24
  (interval_append leafTestAt3904 16 18 20
  (interval_append leafTestAt3904 16 17 18
  leafTestAt3904_block_16
  leafTestAt3904_block_17)
  (interval_append leafTestAt3904 18 19 20
  leafTestAt3904_block_18
  leafTestAt3904_block_19))
  (interval_append leafTestAt3904 20 22 24
  (interval_append leafTestAt3904 20 21 22
  leafTestAt3904_block_20
  leafTestAt3904_block_21)
  (interval_append leafTestAt3904 22 23 24
  leafTestAt3904_block_22
  leafTestAt3904_block_23)))
  (interval_append leafTestAt3904 24 28 32
  (interval_append leafTestAt3904 24 26 28
  (interval_append leafTestAt3904 24 25 26
  leafTestAt3904_block_24
  leafTestAt3904_block_25)
  (interval_append leafTestAt3904 26 27 28
  leafTestAt3904_block_26
  leafTestAt3904_block_27))
  (interval_append leafTestAt3904 28 30 32
  (interval_append leafTestAt3904 28 29 30
  leafTestAt3904_block_28
  leafTestAt3904_block_29)
  (interval_append leafTestAt3904 30 31 32
  leafTestAt3904_block_30
  leafTestAt3904_block_31)))))
cert_leafInterval 3904 3936
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
cert_leafTestAt 3936
cert_leafTestAt_block_2 3936 0 1
cert_leafTestAt_block_2 3936 1 2
cert_leafTestAt_block_2 3936 2 3
cert_leafTestAt_block_2 3936 3 4
cert_leafTestAt_block_2 3936 4 5
cert_leafTestAt_block_2 3936 5 6
cert_leafTestAt_block_2 3936 6 7
cert_leafTestAt_block_2 3936 7 8
cert_leafTestAt_block_2 3936 8 9
cert_leafTestAt_block_2 3936 9 10
cert_leafTestAt_block_2 3936 10 11
cert_leafTestAt_block_2 3936 11 12
cert_leafTestAt_block_2 3936 12 13
cert_leafTestAt_block_2 3936 13 14
cert_leafTestAt_block_2 3936 14 15
cert_leafTestAt_block_2 3936 15 16
cert_leafTestAt_block_2 3936 16 17
cert_leafTestAt_block_2 3936 17 18
cert_leafTestAt_block_2 3936 18 19
cert_leafTestAt_block_2 3936 19 20
cert_leafTestAt_block_2 3936 20 21
cert_leafTestAt_block_2 3936 21 22
cert_leafTestAt_block_2 3936 22 23
cert_leafTestAt_block_2 3936 23 24
cert_leafTestAt_block_2 3936 24 25
cert_leafTestAt_block_2 3936 25 26
cert_leafTestAt_block_2 3936 26 27
cert_leafTestAt_block_2 3936 27 28
cert_leafTestAt_block_2 3936 28 29
cert_leafTestAt_block_2 3936 29 30
cert_leafTestAt_block_2 3936 30 31
cert_leafTestAt_block_2 3936 31 32
theorem leafTestAt3936_complete : Interval leafTestAt3936 0 32 :=
  (interval_append leafTestAt3936 0 16 32
  (interval_append leafTestAt3936 0 8 16
  (interval_append leafTestAt3936 0 4 8
  (interval_append leafTestAt3936 0 2 4
  (interval_append leafTestAt3936 0 1 2
  leafTestAt3936_block_0
  leafTestAt3936_block_1)
  (interval_append leafTestAt3936 2 3 4
  leafTestAt3936_block_2
  leafTestAt3936_block_3))
  (interval_append leafTestAt3936 4 6 8
  (interval_append leafTestAt3936 4 5 6
  leafTestAt3936_block_4
  leafTestAt3936_block_5)
  (interval_append leafTestAt3936 6 7 8
  leafTestAt3936_block_6
  leafTestAt3936_block_7)))
  (interval_append leafTestAt3936 8 12 16
  (interval_append leafTestAt3936 8 10 12
  (interval_append leafTestAt3936 8 9 10
  leafTestAt3936_block_8
  leafTestAt3936_block_9)
  (interval_append leafTestAt3936 10 11 12
  leafTestAt3936_block_10
  leafTestAt3936_block_11))
  (interval_append leafTestAt3936 12 14 16
  (interval_append leafTestAt3936 12 13 14
  leafTestAt3936_block_12
  leafTestAt3936_block_13)
  (interval_append leafTestAt3936 14 15 16
  leafTestAt3936_block_14
  leafTestAt3936_block_15))))
  (interval_append leafTestAt3936 16 24 32
  (interval_append leafTestAt3936 16 20 24
  (interval_append leafTestAt3936 16 18 20
  (interval_append leafTestAt3936 16 17 18
  leafTestAt3936_block_16
  leafTestAt3936_block_17)
  (interval_append leafTestAt3936 18 19 20
  leafTestAt3936_block_18
  leafTestAt3936_block_19))
  (interval_append leafTestAt3936 20 22 24
  (interval_append leafTestAt3936 20 21 22
  leafTestAt3936_block_20
  leafTestAt3936_block_21)
  (interval_append leafTestAt3936 22 23 24
  leafTestAt3936_block_22
  leafTestAt3936_block_23)))
  (interval_append leafTestAt3936 24 28 32
  (interval_append leafTestAt3936 24 26 28
  (interval_append leafTestAt3936 24 25 26
  leafTestAt3936_block_24
  leafTestAt3936_block_25)
  (interval_append leafTestAt3936 26 27 28
  leafTestAt3936_block_26
  leafTestAt3936_block_27))
  (interval_append leafTestAt3936 28 30 32
  (interval_append leafTestAt3936 28 29 30
  leafTestAt3936_block_28
  leafTestAt3936_block_29)
  (interval_append leafTestAt3936 30 31 32
  leafTestAt3936_block_30
  leafTestAt3936_block_31)))))
cert_leafInterval 3936 3968
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
cert_leafTestAt 3968
cert_leafTestAt_block_2 3968 0 1
cert_leafTestAt_block_2 3968 1 2
cert_leafTestAt_block_2 3968 2 3
cert_leafTestAt_block_2 3968 3 4
cert_leafTestAt_block_2 3968 4 5
cert_leafTestAt_block_2 3968 5 6
cert_leafTestAt_block_2 3968 6 7
cert_leafTestAt_block_2 3968 7 8
cert_leafTestAt_block_2 3968 8 9
cert_leafTestAt_block_2 3968 9 10
cert_leafTestAt_block_2 3968 10 11
cert_leafTestAt_block_2 3968 11 12
cert_leafTestAt_block_2 3968 12 13
cert_leafTestAt_block_2 3968 13 14
cert_leafTestAt_block_2 3968 14 15
cert_leafTestAt_block_2 3968 15 16
cert_leafTestAt_block_2 3968 16 17
cert_leafTestAt_block_2 3968 17 18
cert_leafTestAt_block_2 3968 18 19
cert_leafTestAt_block_2 3968 19 20
cert_leafTestAt_block_2 3968 20 21
cert_leafTestAt_block_2 3968 21 22
cert_leafTestAt_block_2 3968 22 23
cert_leafTestAt_block_2 3968 23 24
cert_leafTestAt_block_2 3968 24 25
cert_leafTestAt_block_2 3968 25 26
cert_leafTestAt_block_2 3968 26 27
cert_leafTestAt_block_2 3968 27 28
cert_leafTestAt_block_2 3968 28 29
cert_leafTestAt_block_2 3968 29 30
cert_leafTestAt_block_2 3968 30 31
cert_leafTestAt_block_2 3968 31 32
theorem leafTestAt3968_complete : Interval leafTestAt3968 0 32 :=
  (interval_append leafTestAt3968 0 16 32
  (interval_append leafTestAt3968 0 8 16
  (interval_append leafTestAt3968 0 4 8
  (interval_append leafTestAt3968 0 2 4
  (interval_append leafTestAt3968 0 1 2
  leafTestAt3968_block_0
  leafTestAt3968_block_1)
  (interval_append leafTestAt3968 2 3 4
  leafTestAt3968_block_2
  leafTestAt3968_block_3))
  (interval_append leafTestAt3968 4 6 8
  (interval_append leafTestAt3968 4 5 6
  leafTestAt3968_block_4
  leafTestAt3968_block_5)
  (interval_append leafTestAt3968 6 7 8
  leafTestAt3968_block_6
  leafTestAt3968_block_7)))
  (interval_append leafTestAt3968 8 12 16
  (interval_append leafTestAt3968 8 10 12
  (interval_append leafTestAt3968 8 9 10
  leafTestAt3968_block_8
  leafTestAt3968_block_9)
  (interval_append leafTestAt3968 10 11 12
  leafTestAt3968_block_10
  leafTestAt3968_block_11))
  (interval_append leafTestAt3968 12 14 16
  (interval_append leafTestAt3968 12 13 14
  leafTestAt3968_block_12
  leafTestAt3968_block_13)
  (interval_append leafTestAt3968 14 15 16
  leafTestAt3968_block_14
  leafTestAt3968_block_15))))
  (interval_append leafTestAt3968 16 24 32
  (interval_append leafTestAt3968 16 20 24
  (interval_append leafTestAt3968 16 18 20
  (interval_append leafTestAt3968 16 17 18
  leafTestAt3968_block_16
  leafTestAt3968_block_17)
  (interval_append leafTestAt3968 18 19 20
  leafTestAt3968_block_18
  leafTestAt3968_block_19))
  (interval_append leafTestAt3968 20 22 24
  (interval_append leafTestAt3968 20 21 22
  leafTestAt3968_block_20
  leafTestAt3968_block_21)
  (interval_append leafTestAt3968 22 23 24
  leafTestAt3968_block_22
  leafTestAt3968_block_23)))
  (interval_append leafTestAt3968 24 28 32
  (interval_append leafTestAt3968 24 26 28
  (interval_append leafTestAt3968 24 25 26
  leafTestAt3968_block_24
  leafTestAt3968_block_25)
  (interval_append leafTestAt3968 26 27 28
  leafTestAt3968_block_26
  leafTestAt3968_block_27))
  (interval_append leafTestAt3968 28 30 32
  (interval_append leafTestAt3968 28 29 30
  leafTestAt3968_block_28
  leafTestAt3968_block_29)
  (interval_append leafTestAt3968 30 31 32
  leafTestAt3968_block_30
  leafTestAt3968_block_31)))))
cert_leafInterval 3968 4000
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
cert_leafTestAt 4000
cert_leafTestAt_block_2 4000 0 1
cert_leafTestAt_block_2 4000 1 2
cert_leafTestAt_block_2 4000 2 3
cert_leafTestAt_block_2 4000 3 4
cert_leafTestAt_block_2 4000 4 5
cert_leafTestAt_block_2 4000 5 6
cert_leafTestAt_block_2 4000 6 7
cert_leafTestAt_block_2 4000 7 8
cert_leafTestAt_block_2 4000 8 9
cert_leafTestAt_block_2 4000 9 10
cert_leafTestAt_block_2 4000 10 11
cert_leafTestAt_block_2 4000 11 12
cert_leafTestAt_block_2 4000 12 13
cert_leafTestAt_block_2 4000 13 14
cert_leafTestAt_block_2 4000 14 15
cert_leafTestAt_block_2 4000 15 16
cert_leafTestAt_block_2 4000 16 17
cert_leafTestAt_block_2 4000 17 18
cert_leafTestAt_block_2 4000 18 19
cert_leafTestAt_block_2 4000 19 20
cert_leafTestAt_block_2 4000 20 21
cert_leafTestAt_block_2 4000 21 22
cert_leafTestAt_block_2 4000 22 23
cert_leafTestAt_block_2 4000 23 24
cert_leafTestAt_block_2 4000 24 25
cert_leafTestAt_block_2 4000 25 26
cert_leafTestAt_block_2 4000 26 27
cert_leafTestAt_block_2 4000 27 28
cert_leafTestAt_block_2 4000 28 29
cert_leafTestAt_block_2 4000 29 30
cert_leafTestAt_block_2 4000 30 31
cert_leafTestAt_block_2 4000 31 32
theorem leafTestAt4000_complete : Interval leafTestAt4000 0 32 :=
  (interval_append leafTestAt4000 0 16 32
  (interval_append leafTestAt4000 0 8 16
  (interval_append leafTestAt4000 0 4 8
  (interval_append leafTestAt4000 0 2 4
  (interval_append leafTestAt4000 0 1 2
  leafTestAt4000_block_0
  leafTestAt4000_block_1)
  (interval_append leafTestAt4000 2 3 4
  leafTestAt4000_block_2
  leafTestAt4000_block_3))
  (interval_append leafTestAt4000 4 6 8
  (interval_append leafTestAt4000 4 5 6
  leafTestAt4000_block_4
  leafTestAt4000_block_5)
  (interval_append leafTestAt4000 6 7 8
  leafTestAt4000_block_6
  leafTestAt4000_block_7)))
  (interval_append leafTestAt4000 8 12 16
  (interval_append leafTestAt4000 8 10 12
  (interval_append leafTestAt4000 8 9 10
  leafTestAt4000_block_8
  leafTestAt4000_block_9)
  (interval_append leafTestAt4000 10 11 12
  leafTestAt4000_block_10
  leafTestAt4000_block_11))
  (interval_append leafTestAt4000 12 14 16
  (interval_append leafTestAt4000 12 13 14
  leafTestAt4000_block_12
  leafTestAt4000_block_13)
  (interval_append leafTestAt4000 14 15 16
  leafTestAt4000_block_14
  leafTestAt4000_block_15))))
  (interval_append leafTestAt4000 16 24 32
  (interval_append leafTestAt4000 16 20 24
  (interval_append leafTestAt4000 16 18 20
  (interval_append leafTestAt4000 16 17 18
  leafTestAt4000_block_16
  leafTestAt4000_block_17)
  (interval_append leafTestAt4000 18 19 20
  leafTestAt4000_block_18
  leafTestAt4000_block_19))
  (interval_append leafTestAt4000 20 22 24
  (interval_append leafTestAt4000 20 21 22
  leafTestAt4000_block_20
  leafTestAt4000_block_21)
  (interval_append leafTestAt4000 22 23 24
  leafTestAt4000_block_22
  leafTestAt4000_block_23)))
  (interval_append leafTestAt4000 24 28 32
  (interval_append leafTestAt4000 24 26 28
  (interval_append leafTestAt4000 24 25 26
  leafTestAt4000_block_24
  leafTestAt4000_block_25)
  (interval_append leafTestAt4000 26 27 28
  leafTestAt4000_block_26
  leafTestAt4000_block_27))
  (interval_append leafTestAt4000 28 30 32
  (interval_append leafTestAt4000 28 29 30
  leafTestAt4000_block_28
  leafTestAt4000_block_29)
  (interval_append leafTestAt4000 30 31 32
  leafTestAt4000_block_30
  leafTestAt4000_block_31)))))
cert_leafInterval 4000 4032
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
cert_leafTestAt 4032
cert_leafTestAt_block_2 4032 0 1
cert_leafTestAt_block_2 4032 1 2
cert_leafTestAt_block_2 4032 2 3
cert_leafTestAt_block_2 4032 3 4
cert_leafTestAt_block_2 4032 4 5
cert_leafTestAt_block_2 4032 5 6
cert_leafTestAt_block_2 4032 6 7
cert_leafTestAt_block_2 4032 7 8
cert_leafTestAt_block_2 4032 8 9
cert_leafTestAt_block_2 4032 9 10
cert_leafTestAt_block_2 4032 10 11
cert_leafTestAt_block_2 4032 11 12
cert_leafTestAt_block_2 4032 12 13
cert_leafTestAt_block_2 4032 13 14
cert_leafTestAt_block_2 4032 14 15
cert_leafTestAt_block_2 4032 15 16
cert_leafTestAt_block_2 4032 16 17
cert_leafTestAt_block_2 4032 17 18
cert_leafTestAt_block_2 4032 18 19
cert_leafTestAt_block_2 4032 19 20
cert_leafTestAt_block_2 4032 20 21
cert_leafTestAt_block_2 4032 21 22
cert_leafTestAt_block_2 4032 22 23
cert_leafTestAt_block_2 4032 23 24
cert_leafTestAt_block_2 4032 24 25
cert_leafTestAt_block_2 4032 25 26
cert_leafTestAt_block_2 4032 26 27
cert_leafTestAt_block_2 4032 27 28
cert_leafTestAt_block_2 4032 28 29
cert_leafTestAt_block_2 4032 29 30
cert_leafTestAt_block_2 4032 30 31
cert_leafTestAt_block_2 4032 31 32
theorem leafTestAt4032_complete : Interval leafTestAt4032 0 32 :=
  (interval_append leafTestAt4032 0 16 32
  (interval_append leafTestAt4032 0 8 16
  (interval_append leafTestAt4032 0 4 8
  (interval_append leafTestAt4032 0 2 4
  (interval_append leafTestAt4032 0 1 2
  leafTestAt4032_block_0
  leafTestAt4032_block_1)
  (interval_append leafTestAt4032 2 3 4
  leafTestAt4032_block_2
  leafTestAt4032_block_3))
  (interval_append leafTestAt4032 4 6 8
  (interval_append leafTestAt4032 4 5 6
  leafTestAt4032_block_4
  leafTestAt4032_block_5)
  (interval_append leafTestAt4032 6 7 8
  leafTestAt4032_block_6
  leafTestAt4032_block_7)))
  (interval_append leafTestAt4032 8 12 16
  (interval_append leafTestAt4032 8 10 12
  (interval_append leafTestAt4032 8 9 10
  leafTestAt4032_block_8
  leafTestAt4032_block_9)
  (interval_append leafTestAt4032 10 11 12
  leafTestAt4032_block_10
  leafTestAt4032_block_11))
  (interval_append leafTestAt4032 12 14 16
  (interval_append leafTestAt4032 12 13 14
  leafTestAt4032_block_12
  leafTestAt4032_block_13)
  (interval_append leafTestAt4032 14 15 16
  leafTestAt4032_block_14
  leafTestAt4032_block_15))))
  (interval_append leafTestAt4032 16 24 32
  (interval_append leafTestAt4032 16 20 24
  (interval_append leafTestAt4032 16 18 20
  (interval_append leafTestAt4032 16 17 18
  leafTestAt4032_block_16
  leafTestAt4032_block_17)
  (interval_append leafTestAt4032 18 19 20
  leafTestAt4032_block_18
  leafTestAt4032_block_19))
  (interval_append leafTestAt4032 20 22 24
  (interval_append leafTestAt4032 20 21 22
  leafTestAt4032_block_20
  leafTestAt4032_block_21)
  (interval_append leafTestAt4032 22 23 24
  leafTestAt4032_block_22
  leafTestAt4032_block_23)))
  (interval_append leafTestAt4032 24 28 32
  (interval_append leafTestAt4032 24 26 28
  (interval_append leafTestAt4032 24 25 26
  leafTestAt4032_block_24
  leafTestAt4032_block_25)
  (interval_append leafTestAt4032 26 27 28
  leafTestAt4032_block_26
  leafTestAt4032_block_27))
  (interval_append leafTestAt4032 28 30 32
  (interval_append leafTestAt4032 28 29 30
  leafTestAt4032_block_28
  leafTestAt4032_block_29)
  (interval_append leafTestAt4032 30 31 32
  leafTestAt4032_block_30
  leafTestAt4032_block_31)))))
cert_leafInterval 4032 4064
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
cert_leafTestAt 4064
cert_leafTestAt_block_2 4064 0 1
cert_leafTestAt_block_2 4064 1 2
cert_leafTestAt_block_2 4064 2 3
cert_leafTestAt_block_2 4064 3 4
cert_leafTestAt_block_2 4064 4 5
cert_leafTestAt_block_2 4064 5 6
cert_leafTestAt_block_2 4064 6 7
cert_leafTestAt_block_2 4064 7 8
cert_leafTestAt_block_2 4064 8 9
cert_leafTestAt_block_2 4064 9 10
cert_leafTestAt_block_2 4064 10 11
cert_leafTestAt_block_2 4064 11 12
cert_leafTestAt_block_2 4064 12 13
cert_leafTestAt_block_2 4064 13 14
cert_leafTestAt_block_2 4064 14 15
cert_leafTestAt_block_2 4064 15 16
cert_leafTestAt_block_2 4064 16 17
cert_leafTestAt_block_2 4064 17 18
cert_leafTestAt_block_2 4064 18 19
cert_leafTestAt_block_2 4064 19 20
theorem leafTestAt4064_complete : Interval leafTestAt4064 0 20 :=
  (interval_append leafTestAt4064 0 10 20
  (interval_append leafTestAt4064 0 5 10
  (interval_append leafTestAt4064 0 2 5
  (interval_append leafTestAt4064 0 1 2
  leafTestAt4064_block_0
  leafTestAt4064_block_1)
  (interval_append leafTestAt4064 2 3 5
  leafTestAt4064_block_2
  (interval_append leafTestAt4064 3 4 5
  leafTestAt4064_block_3
  leafTestAt4064_block_4)))
  (interval_append leafTestAt4064 5 7 10
  (interval_append leafTestAt4064 5 6 7
  leafTestAt4064_block_5
  leafTestAt4064_block_6)
  (interval_append leafTestAt4064 7 8 10
  leafTestAt4064_block_7
  (interval_append leafTestAt4064 8 9 10
  leafTestAt4064_block_8
  leafTestAt4064_block_9))))
  (interval_append leafTestAt4064 10 15 20
  (interval_append leafTestAt4064 10 12 15
  (interval_append leafTestAt4064 10 11 12
  leafTestAt4064_block_10
  leafTestAt4064_block_11)
  (interval_append leafTestAt4064 12 13 15
  leafTestAt4064_block_12
  (interval_append leafTestAt4064 13 14 15
  leafTestAt4064_block_13
  leafTestAt4064_block_14)))
  (interval_append leafTestAt4064 15 17 20
  (interval_append leafTestAt4064 15 16 17
  leafTestAt4064_block_15
  leafTestAt4064_block_16)
  (interval_append leafTestAt4064 17 18 20
  leafTestAt4064_block_17
  (interval_append leafTestAt4064 18 19 20
  leafTestAt4064_block_18
  leafTestAt4064_block_19)))))
cert_leafInterval 4064 4084
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
