module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0870Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 512
cert_leafTestAt_block_2 512 0 1
cert_leafTestAt_block_2 512 1 2
cert_leafTestAt_block_2 512 2 3
cert_leafTestAt_block_2 512 3 4
cert_leafTestAt_block_2 512 4 5
cert_leafTestAt_block_2 512 5 6
cert_leafTestAt_block_2 512 6 7
cert_leafTestAt_block_2 512 7 8
cert_leafTestAt_block_2 512 8 9
cert_leafTestAt_block_2 512 9 10
cert_leafTestAt_block_2 512 10 11
cert_leafTestAt_block_2 512 11 12
cert_leafTestAt_block_2 512 12 13
cert_leafTestAt_block_2 512 13 14
cert_leafTestAt_block_2 512 14 15
cert_leafTestAt_block_2 512 15 16
cert_leafTestAt_block_2 512 16 17
cert_leafTestAt_block_2 512 17 18
cert_leafTestAt_block_2 512 18 19
cert_leafTestAt_block_2 512 19 20
cert_leafTestAt_block_2 512 20 21
cert_leafTestAt_block_2 512 21 22
cert_leafTestAt_block_2 512 22 23
cert_leafTestAt_block_2 512 23 24
cert_leafTestAt_block_2 512 24 25
cert_leafTestAt_block_2 512 25 26
cert_leafTestAt_block_2 512 26 27
cert_leafTestAt_block_2 512 27 28
cert_leafTestAt_block_2 512 28 29
cert_leafTestAt_block_2 512 29 30
cert_leafTestAt_block_2 512 30 31
cert_leafTestAt_block_2 512 31 32
theorem leafTestAt512_complete : Interval leafTestAt512 0 32 :=
  (interval_append leafTestAt512 0 16 32
  (interval_append leafTestAt512 0 8 16
  (interval_append leafTestAt512 0 4 8
  (interval_append leafTestAt512 0 2 4
  (interval_append leafTestAt512 0 1 2
  leafTestAt512_block_0
  leafTestAt512_block_1)
  (interval_append leafTestAt512 2 3 4
  leafTestAt512_block_2
  leafTestAt512_block_3))
  (interval_append leafTestAt512 4 6 8
  (interval_append leafTestAt512 4 5 6
  leafTestAt512_block_4
  leafTestAt512_block_5)
  (interval_append leafTestAt512 6 7 8
  leafTestAt512_block_6
  leafTestAt512_block_7)))
  (interval_append leafTestAt512 8 12 16
  (interval_append leafTestAt512 8 10 12
  (interval_append leafTestAt512 8 9 10
  leafTestAt512_block_8
  leafTestAt512_block_9)
  (interval_append leafTestAt512 10 11 12
  leafTestAt512_block_10
  leafTestAt512_block_11))
  (interval_append leafTestAt512 12 14 16
  (interval_append leafTestAt512 12 13 14
  leafTestAt512_block_12
  leafTestAt512_block_13)
  (interval_append leafTestAt512 14 15 16
  leafTestAt512_block_14
  leafTestAt512_block_15))))
  (interval_append leafTestAt512 16 24 32
  (interval_append leafTestAt512 16 20 24
  (interval_append leafTestAt512 16 18 20
  (interval_append leafTestAt512 16 17 18
  leafTestAt512_block_16
  leafTestAt512_block_17)
  (interval_append leafTestAt512 18 19 20
  leafTestAt512_block_18
  leafTestAt512_block_19))
  (interval_append leafTestAt512 20 22 24
  (interval_append leafTestAt512 20 21 22
  leafTestAt512_block_20
  leafTestAt512_block_21)
  (interval_append leafTestAt512 22 23 24
  leafTestAt512_block_22
  leafTestAt512_block_23)))
  (interval_append leafTestAt512 24 28 32
  (interval_append leafTestAt512 24 26 28
  (interval_append leafTestAt512 24 25 26
  leafTestAt512_block_24
  leafTestAt512_block_25)
  (interval_append leafTestAt512 26 27 28
  leafTestAt512_block_26
  leafTestAt512_block_27))
  (interval_append leafTestAt512 28 30 32
  (interval_append leafTestAt512 28 29 30
  leafTestAt512_block_28
  leafTestAt512_block_29)
  (interval_append leafTestAt512 30 31 32
  leafTestAt512_block_30
  leafTestAt512_block_31)))))
cert_leafInterval 512 544
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 544
cert_leafTestAt_block_2 544 0 1
cert_leafTestAt_block_2 544 1 2
cert_leafTestAt_block_2 544 2 3
cert_leafTestAt_block_2 544 3 4
cert_leafTestAt_block_2 544 4 5
cert_leafTestAt_block_2 544 5 6
cert_leafTestAt_block_2 544 6 7
cert_leafTestAt_block_2 544 7 8
cert_leafTestAt_block_2 544 8 9
cert_leafTestAt_block_2 544 9 10
cert_leafTestAt_block_2 544 10 11
cert_leafTestAt_block_2 544 11 12
cert_leafTestAt_block_2 544 12 13
cert_leafTestAt_block_2 544 13 14
cert_leafTestAt_block_2 544 14 15
cert_leafTestAt_block_2 544 15 16
cert_leafTestAt_block_2 544 16 17
cert_leafTestAt_block_2 544 17 18
cert_leafTestAt_block_2 544 18 19
cert_leafTestAt_block_2 544 19 20
cert_leafTestAt_block_2 544 20 21
cert_leafTestAt_block_2 544 21 22
cert_leafTestAt_block_2 544 22 23
cert_leafTestAt_block_2 544 23 24
cert_leafTestAt_block_2 544 24 25
cert_leafTestAt_block_2 544 25 26
cert_leafTestAt_block_2 544 26 27
cert_leafTestAt_block_2 544 27 28
cert_leafTestAt_block_2 544 28 29
cert_leafTestAt_block_2 544 29 30
cert_leafTestAt_block_2 544 30 31
cert_leafTestAt_block_2 544 31 32
theorem leafTestAt544_complete : Interval leafTestAt544 0 32 :=
  (interval_append leafTestAt544 0 16 32
  (interval_append leafTestAt544 0 8 16
  (interval_append leafTestAt544 0 4 8
  (interval_append leafTestAt544 0 2 4
  (interval_append leafTestAt544 0 1 2
  leafTestAt544_block_0
  leafTestAt544_block_1)
  (interval_append leafTestAt544 2 3 4
  leafTestAt544_block_2
  leafTestAt544_block_3))
  (interval_append leafTestAt544 4 6 8
  (interval_append leafTestAt544 4 5 6
  leafTestAt544_block_4
  leafTestAt544_block_5)
  (interval_append leafTestAt544 6 7 8
  leafTestAt544_block_6
  leafTestAt544_block_7)))
  (interval_append leafTestAt544 8 12 16
  (interval_append leafTestAt544 8 10 12
  (interval_append leafTestAt544 8 9 10
  leafTestAt544_block_8
  leafTestAt544_block_9)
  (interval_append leafTestAt544 10 11 12
  leafTestAt544_block_10
  leafTestAt544_block_11))
  (interval_append leafTestAt544 12 14 16
  (interval_append leafTestAt544 12 13 14
  leafTestAt544_block_12
  leafTestAt544_block_13)
  (interval_append leafTestAt544 14 15 16
  leafTestAt544_block_14
  leafTestAt544_block_15))))
  (interval_append leafTestAt544 16 24 32
  (interval_append leafTestAt544 16 20 24
  (interval_append leafTestAt544 16 18 20
  (interval_append leafTestAt544 16 17 18
  leafTestAt544_block_16
  leafTestAt544_block_17)
  (interval_append leafTestAt544 18 19 20
  leafTestAt544_block_18
  leafTestAt544_block_19))
  (interval_append leafTestAt544 20 22 24
  (interval_append leafTestAt544 20 21 22
  leafTestAt544_block_20
  leafTestAt544_block_21)
  (interval_append leafTestAt544 22 23 24
  leafTestAt544_block_22
  leafTestAt544_block_23)))
  (interval_append leafTestAt544 24 28 32
  (interval_append leafTestAt544 24 26 28
  (interval_append leafTestAt544 24 25 26
  leafTestAt544_block_24
  leafTestAt544_block_25)
  (interval_append leafTestAt544 26 27 28
  leafTestAt544_block_26
  leafTestAt544_block_27))
  (interval_append leafTestAt544 28 30 32
  (interval_append leafTestAt544 28 29 30
  leafTestAt544_block_28
  leafTestAt544_block_29)
  (interval_append leafTestAt544 30 31 32
  leafTestAt544_block_30
  leafTestAt544_block_31)))))
cert_leafInterval 544 576
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 576
cert_leafTestAt_block_2 576 0 1
cert_leafTestAt_block_2 576 1 2
cert_leafTestAt_block_2 576 2 3
cert_leafTestAt_block_2 576 3 4
cert_leafTestAt_block_2 576 4 5
cert_leafTestAt_block_2 576 5 6
cert_leafTestAt_block_2 576 6 7
cert_leafTestAt_block_2 576 7 8
cert_leafTestAt_block_2 576 8 9
cert_leafTestAt_block_2 576 9 10
cert_leafTestAt_block_2 576 10 11
cert_leafTestAt_block_2 576 11 12
cert_leafTestAt_block_2 576 12 13
cert_leafTestAt_block_2 576 13 14
cert_leafTestAt_block_2 576 14 15
cert_leafTestAt_block_2 576 15 16
cert_leafTestAt_block_2 576 16 17
cert_leafTestAt_block_2 576 17 18
cert_leafTestAt_block_2 576 18 19
cert_leafTestAt_block_2 576 19 20
cert_leafTestAt_block_2 576 20 21
cert_leafTestAt_block_2 576 21 22
cert_leafTestAt_block_2 576 22 23
cert_leafTestAt_block_2 576 23 24
cert_leafTestAt_block_2 576 24 25
cert_leafTestAt_block_2 576 25 26
cert_leafTestAt_block_2 576 26 27
cert_leafTestAt_block_2 576 27 28
cert_leafTestAt_block_2 576 28 29
cert_leafTestAt_block_2 576 29 30
cert_leafTestAt_block_2 576 30 31
cert_leafTestAt_block_2 576 31 32
theorem leafTestAt576_complete : Interval leafTestAt576 0 32 :=
  (interval_append leafTestAt576 0 16 32
  (interval_append leafTestAt576 0 8 16
  (interval_append leafTestAt576 0 4 8
  (interval_append leafTestAt576 0 2 4
  (interval_append leafTestAt576 0 1 2
  leafTestAt576_block_0
  leafTestAt576_block_1)
  (interval_append leafTestAt576 2 3 4
  leafTestAt576_block_2
  leafTestAt576_block_3))
  (interval_append leafTestAt576 4 6 8
  (interval_append leafTestAt576 4 5 6
  leafTestAt576_block_4
  leafTestAt576_block_5)
  (interval_append leafTestAt576 6 7 8
  leafTestAt576_block_6
  leafTestAt576_block_7)))
  (interval_append leafTestAt576 8 12 16
  (interval_append leafTestAt576 8 10 12
  (interval_append leafTestAt576 8 9 10
  leafTestAt576_block_8
  leafTestAt576_block_9)
  (interval_append leafTestAt576 10 11 12
  leafTestAt576_block_10
  leafTestAt576_block_11))
  (interval_append leafTestAt576 12 14 16
  (interval_append leafTestAt576 12 13 14
  leafTestAt576_block_12
  leafTestAt576_block_13)
  (interval_append leafTestAt576 14 15 16
  leafTestAt576_block_14
  leafTestAt576_block_15))))
  (interval_append leafTestAt576 16 24 32
  (interval_append leafTestAt576 16 20 24
  (interval_append leafTestAt576 16 18 20
  (interval_append leafTestAt576 16 17 18
  leafTestAt576_block_16
  leafTestAt576_block_17)
  (interval_append leafTestAt576 18 19 20
  leafTestAt576_block_18
  leafTestAt576_block_19))
  (interval_append leafTestAt576 20 22 24
  (interval_append leafTestAt576 20 21 22
  leafTestAt576_block_20
  leafTestAt576_block_21)
  (interval_append leafTestAt576 22 23 24
  leafTestAt576_block_22
  leafTestAt576_block_23)))
  (interval_append leafTestAt576 24 28 32
  (interval_append leafTestAt576 24 26 28
  (interval_append leafTestAt576 24 25 26
  leafTestAt576_block_24
  leafTestAt576_block_25)
  (interval_append leafTestAt576 26 27 28
  leafTestAt576_block_26
  leafTestAt576_block_27))
  (interval_append leafTestAt576 28 30 32
  (interval_append leafTestAt576 28 29 30
  leafTestAt576_block_28
  leafTestAt576_block_29)
  (interval_append leafTestAt576 30 31 32
  leafTestAt576_block_30
  leafTestAt576_block_31)))))
cert_leafInterval 576 608
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 608
cert_leafTestAt_block_2 608 0 1
cert_leafTestAt_block_2 608 1 2
cert_leafTestAt_block_2 608 2 3
cert_leafTestAt_block_2 608 3 4
cert_leafTestAt_block_2 608 4 5
cert_leafTestAt_block_2 608 5 6
cert_leafTestAt_block_2 608 6 7
cert_leafTestAt_block_2 608 7 8
cert_leafTestAt_block_2 608 8 9
cert_leafTestAt_block_2 608 9 10
cert_leafTestAt_block_2 608 10 11
cert_leafTestAt_block_2 608 11 12
cert_leafTestAt_block_2 608 12 13
cert_leafTestAt_block_2 608 13 14
cert_leafTestAt_block_2 608 14 15
cert_leafTestAt_block_2 608 15 16
cert_leafTestAt_block_2 608 16 17
cert_leafTestAt_block_2 608 17 18
cert_leafTestAt_block_2 608 18 19
cert_leafTestAt_block_2 608 19 20
cert_leafTestAt_block_2 608 20 21
cert_leafTestAt_block_2 608 21 22
cert_leafTestAt_block_2 608 22 23
cert_leafTestAt_block_2 608 23 24
cert_leafTestAt_block_2 608 24 25
cert_leafTestAt_block_2 608 25 26
cert_leafTestAt_block_2 608 26 27
cert_leafTestAt_block_2 608 27 28
cert_leafTestAt_block_2 608 28 29
cert_leafTestAt_block_2 608 29 30
cert_leafTestAt_block_2 608 30 31
cert_leafTestAt_block_2 608 31 32
theorem leafTestAt608_complete : Interval leafTestAt608 0 32 :=
  (interval_append leafTestAt608 0 16 32
  (interval_append leafTestAt608 0 8 16
  (interval_append leafTestAt608 0 4 8
  (interval_append leafTestAt608 0 2 4
  (interval_append leafTestAt608 0 1 2
  leafTestAt608_block_0
  leafTestAt608_block_1)
  (interval_append leafTestAt608 2 3 4
  leafTestAt608_block_2
  leafTestAt608_block_3))
  (interval_append leafTestAt608 4 6 8
  (interval_append leafTestAt608 4 5 6
  leafTestAt608_block_4
  leafTestAt608_block_5)
  (interval_append leafTestAt608 6 7 8
  leafTestAt608_block_6
  leafTestAt608_block_7)))
  (interval_append leafTestAt608 8 12 16
  (interval_append leafTestAt608 8 10 12
  (interval_append leafTestAt608 8 9 10
  leafTestAt608_block_8
  leafTestAt608_block_9)
  (interval_append leafTestAt608 10 11 12
  leafTestAt608_block_10
  leafTestAt608_block_11))
  (interval_append leafTestAt608 12 14 16
  (interval_append leafTestAt608 12 13 14
  leafTestAt608_block_12
  leafTestAt608_block_13)
  (interval_append leafTestAt608 14 15 16
  leafTestAt608_block_14
  leafTestAt608_block_15))))
  (interval_append leafTestAt608 16 24 32
  (interval_append leafTestAt608 16 20 24
  (interval_append leafTestAt608 16 18 20
  (interval_append leafTestAt608 16 17 18
  leafTestAt608_block_16
  leafTestAt608_block_17)
  (interval_append leafTestAt608 18 19 20
  leafTestAt608_block_18
  leafTestAt608_block_19))
  (interval_append leafTestAt608 20 22 24
  (interval_append leafTestAt608 20 21 22
  leafTestAt608_block_20
  leafTestAt608_block_21)
  (interval_append leafTestAt608 22 23 24
  leafTestAt608_block_22
  leafTestAt608_block_23)))
  (interval_append leafTestAt608 24 28 32
  (interval_append leafTestAt608 24 26 28
  (interval_append leafTestAt608 24 25 26
  leafTestAt608_block_24
  leafTestAt608_block_25)
  (interval_append leafTestAt608 26 27 28
  leafTestAt608_block_26
  leafTestAt608_block_27))
  (interval_append leafTestAt608 28 30 32
  (interval_append leafTestAt608 28 29 30
  leafTestAt608_block_28
  leafTestAt608_block_29)
  (interval_append leafTestAt608 30 31 32
  leafTestAt608_block_30
  leafTestAt608_block_31)))))
cert_leafInterval 608 640
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 640
cert_leafTestAt_block_2 640 0 1
cert_leafTestAt_block_2 640 1 2
cert_leafTestAt_block_2 640 2 3
cert_leafTestAt_block_2 640 3 4
cert_leafTestAt_block_2 640 4 5
cert_leafTestAt_block_2 640 5 6
cert_leafTestAt_block_2 640 6 7
cert_leafTestAt_block_2 640 7 8
cert_leafTestAt_block_2 640 8 9
cert_leafTestAt_block_2 640 9 10
cert_leafTestAt_block_2 640 10 11
cert_leafTestAt_block_2 640 11 12
cert_leafTestAt_block_2 640 12 13
cert_leafTestAt_block_2 640 13 14
cert_leafTestAt_block_2 640 14 15
cert_leafTestAt_block_2 640 15 16
cert_leafTestAt_block_2 640 16 17
cert_leafTestAt_block_2 640 17 18
cert_leafTestAt_block_2 640 18 19
cert_leafTestAt_block_2 640 19 20
cert_leafTestAt_block_2 640 20 21
cert_leafTestAt_block_2 640 21 22
cert_leafTestAt_block_2 640 22 23
cert_leafTestAt_block_2 640 23 24
cert_leafTestAt_block_2 640 24 25
cert_leafTestAt_block_2 640 25 26
cert_leafTestAt_block_2 640 26 27
cert_leafTestAt_block_2 640 27 28
cert_leafTestAt_block_2 640 28 29
cert_leafTestAt_block_2 640 29 30
cert_leafTestAt_block_2 640 30 31
cert_leafTestAt_block_2 640 31 32
theorem leafTestAt640_complete : Interval leafTestAt640 0 32 :=
  (interval_append leafTestAt640 0 16 32
  (interval_append leafTestAt640 0 8 16
  (interval_append leafTestAt640 0 4 8
  (interval_append leafTestAt640 0 2 4
  (interval_append leafTestAt640 0 1 2
  leafTestAt640_block_0
  leafTestAt640_block_1)
  (interval_append leafTestAt640 2 3 4
  leafTestAt640_block_2
  leafTestAt640_block_3))
  (interval_append leafTestAt640 4 6 8
  (interval_append leafTestAt640 4 5 6
  leafTestAt640_block_4
  leafTestAt640_block_5)
  (interval_append leafTestAt640 6 7 8
  leafTestAt640_block_6
  leafTestAt640_block_7)))
  (interval_append leafTestAt640 8 12 16
  (interval_append leafTestAt640 8 10 12
  (interval_append leafTestAt640 8 9 10
  leafTestAt640_block_8
  leafTestAt640_block_9)
  (interval_append leafTestAt640 10 11 12
  leafTestAt640_block_10
  leafTestAt640_block_11))
  (interval_append leafTestAt640 12 14 16
  (interval_append leafTestAt640 12 13 14
  leafTestAt640_block_12
  leafTestAt640_block_13)
  (interval_append leafTestAt640 14 15 16
  leafTestAt640_block_14
  leafTestAt640_block_15))))
  (interval_append leafTestAt640 16 24 32
  (interval_append leafTestAt640 16 20 24
  (interval_append leafTestAt640 16 18 20
  (interval_append leafTestAt640 16 17 18
  leafTestAt640_block_16
  leafTestAt640_block_17)
  (interval_append leafTestAt640 18 19 20
  leafTestAt640_block_18
  leafTestAt640_block_19))
  (interval_append leafTestAt640 20 22 24
  (interval_append leafTestAt640 20 21 22
  leafTestAt640_block_20
  leafTestAt640_block_21)
  (interval_append leafTestAt640 22 23 24
  leafTestAt640_block_22
  leafTestAt640_block_23)))
  (interval_append leafTestAt640 24 28 32
  (interval_append leafTestAt640 24 26 28
  (interval_append leafTestAt640 24 25 26
  leafTestAt640_block_24
  leafTestAt640_block_25)
  (interval_append leafTestAt640 26 27 28
  leafTestAt640_block_26
  leafTestAt640_block_27))
  (interval_append leafTestAt640 28 30 32
  (interval_append leafTestAt640 28 29 30
  leafTestAt640_block_28
  leafTestAt640_block_29)
  (interval_append leafTestAt640 30 31 32
  leafTestAt640_block_30
  leafTestAt640_block_31)))))
cert_leafInterval 640 672
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 672
cert_leafTestAt_block_2 672 0 1
cert_leafTestAt_block_2 672 1 2
cert_leafTestAt_block_2 672 2 3
cert_leafTestAt_block_2 672 3 4
cert_leafTestAt_block_2 672 4 5
cert_leafTestAt_block_2 672 5 6
cert_leafTestAt_block_2 672 6 7
cert_leafTestAt_block_2 672 7 8
cert_leafTestAt_block_2 672 8 9
cert_leafTestAt_block_2 672 9 10
cert_leafTestAt_block_2 672 10 11
cert_leafTestAt_block_2 672 11 12
cert_leafTestAt_block_2 672 12 13
cert_leafTestAt_block_2 672 13 14
cert_leafTestAt_block_2 672 14 15
cert_leafTestAt_block_2 672 15 16
cert_leafTestAt_block_2 672 16 17
cert_leafTestAt_block_2 672 17 18
cert_leafTestAt_block_2 672 18 19
cert_leafTestAt_block_2 672 19 20
cert_leafTestAt_block_2 672 20 21
cert_leafTestAt_block_2 672 21 22
cert_leafTestAt_block_2 672 22 23
cert_leafTestAt_block_2 672 23 24
cert_leafTestAt_block_2 672 24 25
cert_leafTestAt_block_2 672 25 26
cert_leafTestAt_block_2 672 26 27
cert_leafTestAt_block_2 672 27 28
cert_leafTestAt_block_2 672 28 29
cert_leafTestAt_block_2 672 29 30
cert_leafTestAt_block_2 672 30 31
cert_leafTestAt_block_2 672 31 32
theorem leafTestAt672_complete : Interval leafTestAt672 0 32 :=
  (interval_append leafTestAt672 0 16 32
  (interval_append leafTestAt672 0 8 16
  (interval_append leafTestAt672 0 4 8
  (interval_append leafTestAt672 0 2 4
  (interval_append leafTestAt672 0 1 2
  leafTestAt672_block_0
  leafTestAt672_block_1)
  (interval_append leafTestAt672 2 3 4
  leafTestAt672_block_2
  leafTestAt672_block_3))
  (interval_append leafTestAt672 4 6 8
  (interval_append leafTestAt672 4 5 6
  leafTestAt672_block_4
  leafTestAt672_block_5)
  (interval_append leafTestAt672 6 7 8
  leafTestAt672_block_6
  leafTestAt672_block_7)))
  (interval_append leafTestAt672 8 12 16
  (interval_append leafTestAt672 8 10 12
  (interval_append leafTestAt672 8 9 10
  leafTestAt672_block_8
  leafTestAt672_block_9)
  (interval_append leafTestAt672 10 11 12
  leafTestAt672_block_10
  leafTestAt672_block_11))
  (interval_append leafTestAt672 12 14 16
  (interval_append leafTestAt672 12 13 14
  leafTestAt672_block_12
  leafTestAt672_block_13)
  (interval_append leafTestAt672 14 15 16
  leafTestAt672_block_14
  leafTestAt672_block_15))))
  (interval_append leafTestAt672 16 24 32
  (interval_append leafTestAt672 16 20 24
  (interval_append leafTestAt672 16 18 20
  (interval_append leafTestAt672 16 17 18
  leafTestAt672_block_16
  leafTestAt672_block_17)
  (interval_append leafTestAt672 18 19 20
  leafTestAt672_block_18
  leafTestAt672_block_19))
  (interval_append leafTestAt672 20 22 24
  (interval_append leafTestAt672 20 21 22
  leafTestAt672_block_20
  leafTestAt672_block_21)
  (interval_append leafTestAt672 22 23 24
  leafTestAt672_block_22
  leafTestAt672_block_23)))
  (interval_append leafTestAt672 24 28 32
  (interval_append leafTestAt672 24 26 28
  (interval_append leafTestAt672 24 25 26
  leafTestAt672_block_24
  leafTestAt672_block_25)
  (interval_append leafTestAt672 26 27 28
  leafTestAt672_block_26
  leafTestAt672_block_27))
  (interval_append leafTestAt672 28 30 32
  (interval_append leafTestAt672 28 29 30
  leafTestAt672_block_28
  leafTestAt672_block_29)
  (interval_append leafTestAt672 30 31 32
  leafTestAt672_block_30
  leafTestAt672_block_31)))))
cert_leafInterval 672 704
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 704
cert_leafTestAt_block_2 704 0 1
cert_leafTestAt_block_2 704 1 2
cert_leafTestAt_block_2 704 2 3
cert_leafTestAt_block_2 704 3 4
cert_leafTestAt_block_2 704 4 5
cert_leafTestAt_block_2 704 5 6
cert_leafTestAt_block_2 704 6 7
cert_leafTestAt_block_2 704 7 8
cert_leafTestAt_block_2 704 8 9
cert_leafTestAt_block_2 704 9 10
cert_leafTestAt_block_2 704 10 11
cert_leafTestAt_block_2 704 11 12
cert_leafTestAt_block_2 704 12 13
cert_leafTestAt_block_2 704 13 14
cert_leafTestAt_block_2 704 14 15
cert_leafTestAt_block_2 704 15 16
cert_leafTestAt_block_2 704 16 17
cert_leafTestAt_block_2 704 17 18
cert_leafTestAt_block_2 704 18 19
cert_leafTestAt_block_2 704 19 20
cert_leafTestAt_block_2 704 20 21
cert_leafTestAt_block_2 704 21 22
cert_leafTestAt_block_2 704 22 23
cert_leafTestAt_block_2 704 23 24
cert_leafTestAt_block_2 704 24 25
cert_leafTestAt_block_2 704 25 26
cert_leafTestAt_block_2 704 26 27
cert_leafTestAt_block_2 704 27 28
cert_leafTestAt_block_2 704 28 29
cert_leafTestAt_block_2 704 29 30
cert_leafTestAt_block_2 704 30 31
cert_leafTestAt_block_2 704 31 32
theorem leafTestAt704_complete : Interval leafTestAt704 0 32 :=
  (interval_append leafTestAt704 0 16 32
  (interval_append leafTestAt704 0 8 16
  (interval_append leafTestAt704 0 4 8
  (interval_append leafTestAt704 0 2 4
  (interval_append leafTestAt704 0 1 2
  leafTestAt704_block_0
  leafTestAt704_block_1)
  (interval_append leafTestAt704 2 3 4
  leafTestAt704_block_2
  leafTestAt704_block_3))
  (interval_append leafTestAt704 4 6 8
  (interval_append leafTestAt704 4 5 6
  leafTestAt704_block_4
  leafTestAt704_block_5)
  (interval_append leafTestAt704 6 7 8
  leafTestAt704_block_6
  leafTestAt704_block_7)))
  (interval_append leafTestAt704 8 12 16
  (interval_append leafTestAt704 8 10 12
  (interval_append leafTestAt704 8 9 10
  leafTestAt704_block_8
  leafTestAt704_block_9)
  (interval_append leafTestAt704 10 11 12
  leafTestAt704_block_10
  leafTestAt704_block_11))
  (interval_append leafTestAt704 12 14 16
  (interval_append leafTestAt704 12 13 14
  leafTestAt704_block_12
  leafTestAt704_block_13)
  (interval_append leafTestAt704 14 15 16
  leafTestAt704_block_14
  leafTestAt704_block_15))))
  (interval_append leafTestAt704 16 24 32
  (interval_append leafTestAt704 16 20 24
  (interval_append leafTestAt704 16 18 20
  (interval_append leafTestAt704 16 17 18
  leafTestAt704_block_16
  leafTestAt704_block_17)
  (interval_append leafTestAt704 18 19 20
  leafTestAt704_block_18
  leafTestAt704_block_19))
  (interval_append leafTestAt704 20 22 24
  (interval_append leafTestAt704 20 21 22
  leafTestAt704_block_20
  leafTestAt704_block_21)
  (interval_append leafTestAt704 22 23 24
  leafTestAt704_block_22
  leafTestAt704_block_23)))
  (interval_append leafTestAt704 24 28 32
  (interval_append leafTestAt704 24 26 28
  (interval_append leafTestAt704 24 25 26
  leafTestAt704_block_24
  leafTestAt704_block_25)
  (interval_append leafTestAt704 26 27 28
  leafTestAt704_block_26
  leafTestAt704_block_27))
  (interval_append leafTestAt704 28 30 32
  (interval_append leafTestAt704 28 29 30
  leafTestAt704_block_28
  leafTestAt704_block_29)
  (interval_append leafTestAt704 30 31 32
  leafTestAt704_block_30
  leafTestAt704_block_31)))))
cert_leafInterval 704 736
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 736
cert_leafTestAt_block_2 736 0 1
cert_leafTestAt_block_2 736 1 2
cert_leafTestAt_block_2 736 2 3
cert_leafTestAt_block_2 736 3 4
cert_leafTestAt_block_2 736 4 5
cert_leafTestAt_block_2 736 5 6
cert_leafTestAt_block_2 736 6 7
cert_leafTestAt_block_2 736 7 8
cert_leafTestAt_block_2 736 8 9
cert_leafTestAt_block_2 736 9 10
cert_leafTestAt_block_2 736 10 11
cert_leafTestAt_block_2 736 11 12
cert_leafTestAt_block_2 736 12 13
cert_leafTestAt_block_2 736 13 14
cert_leafTestAt_block_2 736 14 15
cert_leafTestAt_block_2 736 15 16
cert_leafTestAt_block_2 736 16 17
cert_leafTestAt_block_2 736 17 18
cert_leafTestAt_block_2 736 18 19
cert_leafTestAt_block_2 736 19 20
cert_leafTestAt_block_2 736 20 21
cert_leafTestAt_block_2 736 21 22
cert_leafTestAt_block_2 736 22 23
cert_leafTestAt_block_2 736 23 24
cert_leafTestAt_block_2 736 24 25
cert_leafTestAt_block_2 736 25 26
cert_leafTestAt_block_2 736 26 27
cert_leafTestAt_block_2 736 27 28
cert_leafTestAt_block_2 736 28 29
cert_leafTestAt_block_2 736 29 30
cert_leafTestAt_block_2 736 30 31
cert_leafTestAt_block_2 736 31 32
theorem leafTestAt736_complete : Interval leafTestAt736 0 32 :=
  (interval_append leafTestAt736 0 16 32
  (interval_append leafTestAt736 0 8 16
  (interval_append leafTestAt736 0 4 8
  (interval_append leafTestAt736 0 2 4
  (interval_append leafTestAt736 0 1 2
  leafTestAt736_block_0
  leafTestAt736_block_1)
  (interval_append leafTestAt736 2 3 4
  leafTestAt736_block_2
  leafTestAt736_block_3))
  (interval_append leafTestAt736 4 6 8
  (interval_append leafTestAt736 4 5 6
  leafTestAt736_block_4
  leafTestAt736_block_5)
  (interval_append leafTestAt736 6 7 8
  leafTestAt736_block_6
  leafTestAt736_block_7)))
  (interval_append leafTestAt736 8 12 16
  (interval_append leafTestAt736 8 10 12
  (interval_append leafTestAt736 8 9 10
  leafTestAt736_block_8
  leafTestAt736_block_9)
  (interval_append leafTestAt736 10 11 12
  leafTestAt736_block_10
  leafTestAt736_block_11))
  (interval_append leafTestAt736 12 14 16
  (interval_append leafTestAt736 12 13 14
  leafTestAt736_block_12
  leafTestAt736_block_13)
  (interval_append leafTestAt736 14 15 16
  leafTestAt736_block_14
  leafTestAt736_block_15))))
  (interval_append leafTestAt736 16 24 32
  (interval_append leafTestAt736 16 20 24
  (interval_append leafTestAt736 16 18 20
  (interval_append leafTestAt736 16 17 18
  leafTestAt736_block_16
  leafTestAt736_block_17)
  (interval_append leafTestAt736 18 19 20
  leafTestAt736_block_18
  leafTestAt736_block_19))
  (interval_append leafTestAt736 20 22 24
  (interval_append leafTestAt736 20 21 22
  leafTestAt736_block_20
  leafTestAt736_block_21)
  (interval_append leafTestAt736 22 23 24
  leafTestAt736_block_22
  leafTestAt736_block_23)))
  (interval_append leafTestAt736 24 28 32
  (interval_append leafTestAt736 24 26 28
  (interval_append leafTestAt736 24 25 26
  leafTestAt736_block_24
  leafTestAt736_block_25)
  (interval_append leafTestAt736 26 27 28
  leafTestAt736_block_26
  leafTestAt736_block_27))
  (interval_append leafTestAt736 28 30 32
  (interval_append leafTestAt736 28 29 30
  leafTestAt736_block_28
  leafTestAt736_block_29)
  (interval_append leafTestAt736 30 31 32
  leafTestAt736_block_30
  leafTestAt736_block_31)))))
cert_leafInterval 736 768
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 768
cert_leafTestAt_block_2 768 0 1
cert_leafTestAt_block_2 768 1 2
cert_leafTestAt_block_2 768 2 3
cert_leafTestAt_block_2 768 3 4
cert_leafTestAt_block_2 768 4 5
cert_leafTestAt_block_2 768 5 6
cert_leafTestAt_block_2 768 6 7
cert_leafTestAt_block_2 768 7 8
cert_leafTestAt_block_2 768 8 9
cert_leafTestAt_block_2 768 9 10
cert_leafTestAt_block_2 768 10 11
cert_leafTestAt_block_2 768 11 12
cert_leafTestAt_block_2 768 12 13
cert_leafTestAt_block_2 768 13 14
cert_leafTestAt_block_2 768 14 15
cert_leafTestAt_block_2 768 15 16
cert_leafTestAt_block_2 768 16 17
cert_leafTestAt_block_2 768 17 18
cert_leafTestAt_block_2 768 18 19
cert_leafTestAt_block_2 768 19 20
cert_leafTestAt_block_2 768 20 21
cert_leafTestAt_block_2 768 21 22
cert_leafTestAt_block_2 768 22 23
cert_leafTestAt_block_2 768 23 24
cert_leafTestAt_block_2 768 24 25
cert_leafTestAt_block_2 768 25 26
cert_leafTestAt_block_2 768 26 27
cert_leafTestAt_block_2 768 27 28
cert_leafTestAt_block_2 768 28 29
cert_leafTestAt_block_2 768 29 30
cert_leafTestAt_block_2 768 30 31
cert_leafTestAt_block_2 768 31 32
theorem leafTestAt768_complete : Interval leafTestAt768 0 32 :=
  (interval_append leafTestAt768 0 16 32
  (interval_append leafTestAt768 0 8 16
  (interval_append leafTestAt768 0 4 8
  (interval_append leafTestAt768 0 2 4
  (interval_append leafTestAt768 0 1 2
  leafTestAt768_block_0
  leafTestAt768_block_1)
  (interval_append leafTestAt768 2 3 4
  leafTestAt768_block_2
  leafTestAt768_block_3))
  (interval_append leafTestAt768 4 6 8
  (interval_append leafTestAt768 4 5 6
  leafTestAt768_block_4
  leafTestAt768_block_5)
  (interval_append leafTestAt768 6 7 8
  leafTestAt768_block_6
  leafTestAt768_block_7)))
  (interval_append leafTestAt768 8 12 16
  (interval_append leafTestAt768 8 10 12
  (interval_append leafTestAt768 8 9 10
  leafTestAt768_block_8
  leafTestAt768_block_9)
  (interval_append leafTestAt768 10 11 12
  leafTestAt768_block_10
  leafTestAt768_block_11))
  (interval_append leafTestAt768 12 14 16
  (interval_append leafTestAt768 12 13 14
  leafTestAt768_block_12
  leafTestAt768_block_13)
  (interval_append leafTestAt768 14 15 16
  leafTestAt768_block_14
  leafTestAt768_block_15))))
  (interval_append leafTestAt768 16 24 32
  (interval_append leafTestAt768 16 20 24
  (interval_append leafTestAt768 16 18 20
  (interval_append leafTestAt768 16 17 18
  leafTestAt768_block_16
  leafTestAt768_block_17)
  (interval_append leafTestAt768 18 19 20
  leafTestAt768_block_18
  leafTestAt768_block_19))
  (interval_append leafTestAt768 20 22 24
  (interval_append leafTestAt768 20 21 22
  leafTestAt768_block_20
  leafTestAt768_block_21)
  (interval_append leafTestAt768 22 23 24
  leafTestAt768_block_22
  leafTestAt768_block_23)))
  (interval_append leafTestAt768 24 28 32
  (interval_append leafTestAt768 24 26 28
  (interval_append leafTestAt768 24 25 26
  leafTestAt768_block_24
  leafTestAt768_block_25)
  (interval_append leafTestAt768 26 27 28
  leafTestAt768_block_26
  leafTestAt768_block_27))
  (interval_append leafTestAt768 28 30 32
  (interval_append leafTestAt768 28 29 30
  leafTestAt768_block_28
  leafTestAt768_block_29)
  (interval_append leafTestAt768 30 31 32
  leafTestAt768_block_30
  leafTestAt768_block_31)))))
cert_leafInterval 768 800
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 800
cert_leafTestAt_block_2 800 0 1
cert_leafTestAt_block_2 800 1 2
cert_leafTestAt_block_2 800 2 3
cert_leafTestAt_block_2 800 3 4
cert_leafTestAt_block_2 800 4 5
cert_leafTestAt_block_2 800 5 6
cert_leafTestAt_block_2 800 6 7
cert_leafTestAt_block_2 800 7 8
cert_leafTestAt_block_2 800 8 9
cert_leafTestAt_block_2 800 9 10
cert_leafTestAt_block_2 800 10 11
cert_leafTestAt_block_2 800 11 12
cert_leafTestAt_block_2 800 12 13
cert_leafTestAt_block_2 800 13 14
cert_leafTestAt_block_2 800 14 15
cert_leafTestAt_block_2 800 15 16
cert_leafTestAt_block_2 800 16 17
cert_leafTestAt_block_2 800 17 18
cert_leafTestAt_block_2 800 18 19
cert_leafTestAt_block_2 800 19 20
cert_leafTestAt_block_2 800 20 21
cert_leafTestAt_block_2 800 21 22
cert_leafTestAt_block_2 800 22 23
cert_leafTestAt_block_2 800 23 24
cert_leafTestAt_block_2 800 24 25
cert_leafTestAt_block_2 800 25 26
cert_leafTestAt_block_2 800 26 27
cert_leafTestAt_block_2 800 27 28
cert_leafTestAt_block_2 800 28 29
cert_leafTestAt_block_2 800 29 30
cert_leafTestAt_block_2 800 30 31
cert_leafTestAt_block_2 800 31 32
theorem leafTestAt800_complete : Interval leafTestAt800 0 32 :=
  (interval_append leafTestAt800 0 16 32
  (interval_append leafTestAt800 0 8 16
  (interval_append leafTestAt800 0 4 8
  (interval_append leafTestAt800 0 2 4
  (interval_append leafTestAt800 0 1 2
  leafTestAt800_block_0
  leafTestAt800_block_1)
  (interval_append leafTestAt800 2 3 4
  leafTestAt800_block_2
  leafTestAt800_block_3))
  (interval_append leafTestAt800 4 6 8
  (interval_append leafTestAt800 4 5 6
  leafTestAt800_block_4
  leafTestAt800_block_5)
  (interval_append leafTestAt800 6 7 8
  leafTestAt800_block_6
  leafTestAt800_block_7)))
  (interval_append leafTestAt800 8 12 16
  (interval_append leafTestAt800 8 10 12
  (interval_append leafTestAt800 8 9 10
  leafTestAt800_block_8
  leafTestAt800_block_9)
  (interval_append leafTestAt800 10 11 12
  leafTestAt800_block_10
  leafTestAt800_block_11))
  (interval_append leafTestAt800 12 14 16
  (interval_append leafTestAt800 12 13 14
  leafTestAt800_block_12
  leafTestAt800_block_13)
  (interval_append leafTestAt800 14 15 16
  leafTestAt800_block_14
  leafTestAt800_block_15))))
  (interval_append leafTestAt800 16 24 32
  (interval_append leafTestAt800 16 20 24
  (interval_append leafTestAt800 16 18 20
  (interval_append leafTestAt800 16 17 18
  leafTestAt800_block_16
  leafTestAt800_block_17)
  (interval_append leafTestAt800 18 19 20
  leafTestAt800_block_18
  leafTestAt800_block_19))
  (interval_append leafTestAt800 20 22 24
  (interval_append leafTestAt800 20 21 22
  leafTestAt800_block_20
  leafTestAt800_block_21)
  (interval_append leafTestAt800 22 23 24
  leafTestAt800_block_22
  leafTestAt800_block_23)))
  (interval_append leafTestAt800 24 28 32
  (interval_append leafTestAt800 24 26 28
  (interval_append leafTestAt800 24 25 26
  leafTestAt800_block_24
  leafTestAt800_block_25)
  (interval_append leafTestAt800 26 27 28
  leafTestAt800_block_26
  leafTestAt800_block_27))
  (interval_append leafTestAt800 28 30 32
  (interval_append leafTestAt800 28 29 30
  leafTestAt800_block_28
  leafTestAt800_block_29)
  (interval_append leafTestAt800 30 31 32
  leafTestAt800_block_30
  leafTestAt800_block_31)))))
cert_leafInterval 800 832
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 832
cert_leafTestAt_block_2 832 0 1
cert_leafTestAt_block_2 832 1 2
cert_leafTestAt_block_2 832 2 3
theorem leafTestAt832_complete : Interval leafTestAt832 0 3 :=
  (interval_append leafTestAt832 0 1 3
  leafTestAt832_block_0
  (interval_append leafTestAt832 1 2 3
  leafTestAt832_block_1
  leafTestAt832_block_2))
cert_leafInterval 832 835
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0870
end
end
