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
cert_leafTestAt 2048
cert_leafTestAt_block_2 2048 0 1
cert_leafTestAt_block_2 2048 1 2
cert_leafTestAt_block_2 2048 2 3
cert_leafTestAt_block_2 2048 3 4
cert_leafTestAt_block_2 2048 4 5
cert_leafTestAt_block_2 2048 5 6
cert_leafTestAt_block_2 2048 6 7
cert_leafTestAt_block_2 2048 7 8
cert_leafTestAt_block_2 2048 8 9
cert_leafTestAt_block_2 2048 9 10
cert_leafTestAt_block_2 2048 10 11
cert_leafTestAt_block_2 2048 11 12
cert_leafTestAt_block_2 2048 12 13
cert_leafTestAt_block_2 2048 13 14
cert_leafTestAt_block_2 2048 14 15
cert_leafTestAt_block_2 2048 15 16
cert_leafTestAt_block_2 2048 16 17
cert_leafTestAt_block_2 2048 17 18
cert_leafTestAt_block_2 2048 18 19
cert_leafTestAt_block_2 2048 19 20
cert_leafTestAt_block_2 2048 20 21
cert_leafTestAt_block_2 2048 21 22
cert_leafTestAt_block_2 2048 22 23
cert_leafTestAt_block_2 2048 23 24
cert_leafTestAt_block_2 2048 24 25
cert_leafTestAt_block_2 2048 25 26
cert_leafTestAt_block_2 2048 26 27
cert_leafTestAt_block_2 2048 27 28
cert_leafTestAt_block_2 2048 28 29
cert_leafTestAt_block_2 2048 29 30
cert_leafTestAt_block_2 2048 30 31
cert_leafTestAt_block_2 2048 31 32
theorem leafTestAt2048_complete : Interval leafTestAt2048 0 32 :=
  (interval_append leafTestAt2048 0 16 32
  (interval_append leafTestAt2048 0 8 16
  (interval_append leafTestAt2048 0 4 8
  (interval_append leafTestAt2048 0 2 4
  (interval_append leafTestAt2048 0 1 2
  leafTestAt2048_block_0
  leafTestAt2048_block_1)
  (interval_append leafTestAt2048 2 3 4
  leafTestAt2048_block_2
  leafTestAt2048_block_3))
  (interval_append leafTestAt2048 4 6 8
  (interval_append leafTestAt2048 4 5 6
  leafTestAt2048_block_4
  leafTestAt2048_block_5)
  (interval_append leafTestAt2048 6 7 8
  leafTestAt2048_block_6
  leafTestAt2048_block_7)))
  (interval_append leafTestAt2048 8 12 16
  (interval_append leafTestAt2048 8 10 12
  (interval_append leafTestAt2048 8 9 10
  leafTestAt2048_block_8
  leafTestAt2048_block_9)
  (interval_append leafTestAt2048 10 11 12
  leafTestAt2048_block_10
  leafTestAt2048_block_11))
  (interval_append leafTestAt2048 12 14 16
  (interval_append leafTestAt2048 12 13 14
  leafTestAt2048_block_12
  leafTestAt2048_block_13)
  (interval_append leafTestAt2048 14 15 16
  leafTestAt2048_block_14
  leafTestAt2048_block_15))))
  (interval_append leafTestAt2048 16 24 32
  (interval_append leafTestAt2048 16 20 24
  (interval_append leafTestAt2048 16 18 20
  (interval_append leafTestAt2048 16 17 18
  leafTestAt2048_block_16
  leafTestAt2048_block_17)
  (interval_append leafTestAt2048 18 19 20
  leafTestAt2048_block_18
  leafTestAt2048_block_19))
  (interval_append leafTestAt2048 20 22 24
  (interval_append leafTestAt2048 20 21 22
  leafTestAt2048_block_20
  leafTestAt2048_block_21)
  (interval_append leafTestAt2048 22 23 24
  leafTestAt2048_block_22
  leafTestAt2048_block_23)))
  (interval_append leafTestAt2048 24 28 32
  (interval_append leafTestAt2048 24 26 28
  (interval_append leafTestAt2048 24 25 26
  leafTestAt2048_block_24
  leafTestAt2048_block_25)
  (interval_append leafTestAt2048 26 27 28
  leafTestAt2048_block_26
  leafTestAt2048_block_27))
  (interval_append leafTestAt2048 28 30 32
  (interval_append leafTestAt2048 28 29 30
  leafTestAt2048_block_28
  leafTestAt2048_block_29)
  (interval_append leafTestAt2048 30 31 32
  leafTestAt2048_block_30
  leafTestAt2048_block_31)))))
cert_leafInterval 2048 2080
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
cert_leafTestAt 2080
cert_leafTestAt_block_2 2080 0 1
cert_leafTestAt_block_2 2080 1 2
cert_leafTestAt_block_2 2080 2 3
cert_leafTestAt_block_2 2080 3 4
cert_leafTestAt_block_2 2080 4 5
cert_leafTestAt_block_2 2080 5 6
cert_leafTestAt_block_2 2080 6 7
cert_leafTestAt_block_2 2080 7 8
cert_leafTestAt_block_2 2080 8 9
cert_leafTestAt_block_2 2080 9 10
cert_leafTestAt_block_2 2080 10 11
cert_leafTestAt_block_2 2080 11 12
cert_leafTestAt_block_2 2080 12 13
cert_leafTestAt_block_2 2080 13 14
cert_leafTestAt_block_2 2080 14 15
cert_leafTestAt_block_2 2080 15 16
cert_leafTestAt_block_2 2080 16 17
cert_leafTestAt_block_2 2080 17 18
cert_leafTestAt_block_2 2080 18 19
cert_leafTestAt_block_2 2080 19 20
cert_leafTestAt_block_2 2080 20 21
cert_leafTestAt_block_2 2080 21 22
cert_leafTestAt_block_2 2080 22 23
cert_leafTestAt_block_2 2080 23 24
cert_leafTestAt_block_2 2080 24 25
cert_leafTestAt_block_2 2080 25 26
cert_leafTestAt_block_2 2080 26 27
cert_leafTestAt_block_2 2080 27 28
cert_leafTestAt_block_2 2080 28 29
cert_leafTestAt_block_2 2080 29 30
cert_leafTestAt_block_2 2080 30 31
cert_leafTestAt_block_2 2080 31 32
theorem leafTestAt2080_complete : Interval leafTestAt2080 0 32 :=
  (interval_append leafTestAt2080 0 16 32
  (interval_append leafTestAt2080 0 8 16
  (interval_append leafTestAt2080 0 4 8
  (interval_append leafTestAt2080 0 2 4
  (interval_append leafTestAt2080 0 1 2
  leafTestAt2080_block_0
  leafTestAt2080_block_1)
  (interval_append leafTestAt2080 2 3 4
  leafTestAt2080_block_2
  leafTestAt2080_block_3))
  (interval_append leafTestAt2080 4 6 8
  (interval_append leafTestAt2080 4 5 6
  leafTestAt2080_block_4
  leafTestAt2080_block_5)
  (interval_append leafTestAt2080 6 7 8
  leafTestAt2080_block_6
  leafTestAt2080_block_7)))
  (interval_append leafTestAt2080 8 12 16
  (interval_append leafTestAt2080 8 10 12
  (interval_append leafTestAt2080 8 9 10
  leafTestAt2080_block_8
  leafTestAt2080_block_9)
  (interval_append leafTestAt2080 10 11 12
  leafTestAt2080_block_10
  leafTestAt2080_block_11))
  (interval_append leafTestAt2080 12 14 16
  (interval_append leafTestAt2080 12 13 14
  leafTestAt2080_block_12
  leafTestAt2080_block_13)
  (interval_append leafTestAt2080 14 15 16
  leafTestAt2080_block_14
  leafTestAt2080_block_15))))
  (interval_append leafTestAt2080 16 24 32
  (interval_append leafTestAt2080 16 20 24
  (interval_append leafTestAt2080 16 18 20
  (interval_append leafTestAt2080 16 17 18
  leafTestAt2080_block_16
  leafTestAt2080_block_17)
  (interval_append leafTestAt2080 18 19 20
  leafTestAt2080_block_18
  leafTestAt2080_block_19))
  (interval_append leafTestAt2080 20 22 24
  (interval_append leafTestAt2080 20 21 22
  leafTestAt2080_block_20
  leafTestAt2080_block_21)
  (interval_append leafTestAt2080 22 23 24
  leafTestAt2080_block_22
  leafTestAt2080_block_23)))
  (interval_append leafTestAt2080 24 28 32
  (interval_append leafTestAt2080 24 26 28
  (interval_append leafTestAt2080 24 25 26
  leafTestAt2080_block_24
  leafTestAt2080_block_25)
  (interval_append leafTestAt2080 26 27 28
  leafTestAt2080_block_26
  leafTestAt2080_block_27))
  (interval_append leafTestAt2080 28 30 32
  (interval_append leafTestAt2080 28 29 30
  leafTestAt2080_block_28
  leafTestAt2080_block_29)
  (interval_append leafTestAt2080 30 31 32
  leafTestAt2080_block_30
  leafTestAt2080_block_31)))))
cert_leafInterval 2080 2112
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
cert_leafTestAt 2112
cert_leafTestAt_block_2 2112 0 1
cert_leafTestAt_block_2 2112 1 2
cert_leafTestAt_block_2 2112 2 3
cert_leafTestAt_block_2 2112 3 4
cert_leafTestAt_block_2 2112 4 5
cert_leafTestAt_block_2 2112 5 6
cert_leafTestAt_block_2 2112 6 7
cert_leafTestAt_block_2 2112 7 8
cert_leafTestAt_block_2 2112 8 9
cert_leafTestAt_block_2 2112 9 10
cert_leafTestAt_block_2 2112 10 11
cert_leafTestAt_block_2 2112 11 12
cert_leafTestAt_block_2 2112 12 13
cert_leafTestAt_block_2 2112 13 14
cert_leafTestAt_block_2 2112 14 15
cert_leafTestAt_block_2 2112 15 16
cert_leafTestAt_block_2 2112 16 17
cert_leafTestAt_block_2 2112 17 18
cert_leafTestAt_block_2 2112 18 19
cert_leafTestAt_block_2 2112 19 20
cert_leafTestAt_block_2 2112 20 21
cert_leafTestAt_block_2 2112 21 22
cert_leafTestAt_block_2 2112 22 23
cert_leafTestAt_block_2 2112 23 24
cert_leafTestAt_block_2 2112 24 25
cert_leafTestAt_block_2 2112 25 26
cert_leafTestAt_block_2 2112 26 27
cert_leafTestAt_block_2 2112 27 28
cert_leafTestAt_block_2 2112 28 29
cert_leafTestAt_block_2 2112 29 30
cert_leafTestAt_block_2 2112 30 31
cert_leafTestAt_block_2 2112 31 32
theorem leafTestAt2112_complete : Interval leafTestAt2112 0 32 :=
  (interval_append leafTestAt2112 0 16 32
  (interval_append leafTestAt2112 0 8 16
  (interval_append leafTestAt2112 0 4 8
  (interval_append leafTestAt2112 0 2 4
  (interval_append leafTestAt2112 0 1 2
  leafTestAt2112_block_0
  leafTestAt2112_block_1)
  (interval_append leafTestAt2112 2 3 4
  leafTestAt2112_block_2
  leafTestAt2112_block_3))
  (interval_append leafTestAt2112 4 6 8
  (interval_append leafTestAt2112 4 5 6
  leafTestAt2112_block_4
  leafTestAt2112_block_5)
  (interval_append leafTestAt2112 6 7 8
  leafTestAt2112_block_6
  leafTestAt2112_block_7)))
  (interval_append leafTestAt2112 8 12 16
  (interval_append leafTestAt2112 8 10 12
  (interval_append leafTestAt2112 8 9 10
  leafTestAt2112_block_8
  leafTestAt2112_block_9)
  (interval_append leafTestAt2112 10 11 12
  leafTestAt2112_block_10
  leafTestAt2112_block_11))
  (interval_append leafTestAt2112 12 14 16
  (interval_append leafTestAt2112 12 13 14
  leafTestAt2112_block_12
  leafTestAt2112_block_13)
  (interval_append leafTestAt2112 14 15 16
  leafTestAt2112_block_14
  leafTestAt2112_block_15))))
  (interval_append leafTestAt2112 16 24 32
  (interval_append leafTestAt2112 16 20 24
  (interval_append leafTestAt2112 16 18 20
  (interval_append leafTestAt2112 16 17 18
  leafTestAt2112_block_16
  leafTestAt2112_block_17)
  (interval_append leafTestAt2112 18 19 20
  leafTestAt2112_block_18
  leafTestAt2112_block_19))
  (interval_append leafTestAt2112 20 22 24
  (interval_append leafTestAt2112 20 21 22
  leafTestAt2112_block_20
  leafTestAt2112_block_21)
  (interval_append leafTestAt2112 22 23 24
  leafTestAt2112_block_22
  leafTestAt2112_block_23)))
  (interval_append leafTestAt2112 24 28 32
  (interval_append leafTestAt2112 24 26 28
  (interval_append leafTestAt2112 24 25 26
  leafTestAt2112_block_24
  leafTestAt2112_block_25)
  (interval_append leafTestAt2112 26 27 28
  leafTestAt2112_block_26
  leafTestAt2112_block_27))
  (interval_append leafTestAt2112 28 30 32
  (interval_append leafTestAt2112 28 29 30
  leafTestAt2112_block_28
  leafTestAt2112_block_29)
  (interval_append leafTestAt2112 30 31 32
  leafTestAt2112_block_30
  leafTestAt2112_block_31)))))
cert_leafInterval 2112 2144
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
cert_leafTestAt 2144
cert_leafTestAt_block_2 2144 0 1
cert_leafTestAt_block_2 2144 1 2
cert_leafTestAt_block_2 2144 2 3
cert_leafTestAt_block_2 2144 3 4
cert_leafTestAt_block_2 2144 4 5
cert_leafTestAt_block_2 2144 5 6
cert_leafTestAt_block_2 2144 6 7
cert_leafTestAt_block_2 2144 7 8
cert_leafTestAt_block_2 2144 8 9
cert_leafTestAt_block_2 2144 9 10
cert_leafTestAt_block_2 2144 10 11
cert_leafTestAt_block_2 2144 11 12
cert_leafTestAt_block_2 2144 12 13
cert_leafTestAt_block_2 2144 13 14
cert_leafTestAt_block_2 2144 14 15
cert_leafTestAt_block_2 2144 15 16
cert_leafTestAt_block_2 2144 16 17
cert_leafTestAt_block_2 2144 17 18
cert_leafTestAt_block_2 2144 18 19
cert_leafTestAt_block_2 2144 19 20
cert_leafTestAt_block_2 2144 20 21
cert_leafTestAt_block_2 2144 21 22
cert_leafTestAt_block_2 2144 22 23
cert_leafTestAt_block_2 2144 23 24
cert_leafTestAt_block_2 2144 24 25
cert_leafTestAt_block_2 2144 25 26
cert_leafTestAt_block_2 2144 26 27
cert_leafTestAt_block_2 2144 27 28
cert_leafTestAt_block_2 2144 28 29
cert_leafTestAt_block_2 2144 29 30
cert_leafTestAt_block_2 2144 30 31
cert_leafTestAt_block_2 2144 31 32
theorem leafTestAt2144_complete : Interval leafTestAt2144 0 32 :=
  (interval_append leafTestAt2144 0 16 32
  (interval_append leafTestAt2144 0 8 16
  (interval_append leafTestAt2144 0 4 8
  (interval_append leafTestAt2144 0 2 4
  (interval_append leafTestAt2144 0 1 2
  leafTestAt2144_block_0
  leafTestAt2144_block_1)
  (interval_append leafTestAt2144 2 3 4
  leafTestAt2144_block_2
  leafTestAt2144_block_3))
  (interval_append leafTestAt2144 4 6 8
  (interval_append leafTestAt2144 4 5 6
  leafTestAt2144_block_4
  leafTestAt2144_block_5)
  (interval_append leafTestAt2144 6 7 8
  leafTestAt2144_block_6
  leafTestAt2144_block_7)))
  (interval_append leafTestAt2144 8 12 16
  (interval_append leafTestAt2144 8 10 12
  (interval_append leafTestAt2144 8 9 10
  leafTestAt2144_block_8
  leafTestAt2144_block_9)
  (interval_append leafTestAt2144 10 11 12
  leafTestAt2144_block_10
  leafTestAt2144_block_11))
  (interval_append leafTestAt2144 12 14 16
  (interval_append leafTestAt2144 12 13 14
  leafTestAt2144_block_12
  leafTestAt2144_block_13)
  (interval_append leafTestAt2144 14 15 16
  leafTestAt2144_block_14
  leafTestAt2144_block_15))))
  (interval_append leafTestAt2144 16 24 32
  (interval_append leafTestAt2144 16 20 24
  (interval_append leafTestAt2144 16 18 20
  (interval_append leafTestAt2144 16 17 18
  leafTestAt2144_block_16
  leafTestAt2144_block_17)
  (interval_append leafTestAt2144 18 19 20
  leafTestAt2144_block_18
  leafTestAt2144_block_19))
  (interval_append leafTestAt2144 20 22 24
  (interval_append leafTestAt2144 20 21 22
  leafTestAt2144_block_20
  leafTestAt2144_block_21)
  (interval_append leafTestAt2144 22 23 24
  leafTestAt2144_block_22
  leafTestAt2144_block_23)))
  (interval_append leafTestAt2144 24 28 32
  (interval_append leafTestAt2144 24 26 28
  (interval_append leafTestAt2144 24 25 26
  leafTestAt2144_block_24
  leafTestAt2144_block_25)
  (interval_append leafTestAt2144 26 27 28
  leafTestAt2144_block_26
  leafTestAt2144_block_27))
  (interval_append leafTestAt2144 28 30 32
  (interval_append leafTestAt2144 28 29 30
  leafTestAt2144_block_28
  leafTestAt2144_block_29)
  (interval_append leafTestAt2144 30 31 32
  leafTestAt2144_block_30
  leafTestAt2144_block_31)))))
cert_leafInterval 2144 2176
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
cert_leafTestAt 2176
cert_leafTestAt_block_2 2176 0 1
cert_leafTestAt_block_2 2176 1 2
cert_leafTestAt_block_2 2176 2 3
cert_leafTestAt_block_2 2176 3 4
cert_leafTestAt_block_2 2176 4 5
cert_leafTestAt_block_2 2176 5 6
cert_leafTestAt_block_2 2176 6 7
cert_leafTestAt_block_2 2176 7 8
cert_leafTestAt_block_2 2176 8 9
cert_leafTestAt_block_2 2176 9 10
cert_leafTestAt_block_2 2176 10 11
cert_leafTestAt_block_2 2176 11 12
cert_leafTestAt_block_2 2176 12 13
cert_leafTestAt_block_2 2176 13 14
cert_leafTestAt_block_2 2176 14 15
cert_leafTestAt_block_2 2176 15 16
cert_leafTestAt_block_2 2176 16 17
cert_leafTestAt_block_2 2176 17 18
cert_leafTestAt_block_2 2176 18 19
cert_leafTestAt_block_2 2176 19 20
cert_leafTestAt_block_2 2176 20 21
cert_leafTestAt_block_2 2176 21 22
cert_leafTestAt_block_2 2176 22 23
cert_leafTestAt_block_2 2176 23 24
cert_leafTestAt_block_2 2176 24 25
cert_leafTestAt_block_2 2176 25 26
cert_leafTestAt_block_2 2176 26 27
cert_leafTestAt_block_2 2176 27 28
cert_leafTestAt_block_2 2176 28 29
cert_leafTestAt_block_2 2176 29 30
cert_leafTestAt_block_2 2176 30 31
cert_leafTestAt_block_2 2176 31 32
theorem leafTestAt2176_complete : Interval leafTestAt2176 0 32 :=
  (interval_append leafTestAt2176 0 16 32
  (interval_append leafTestAt2176 0 8 16
  (interval_append leafTestAt2176 0 4 8
  (interval_append leafTestAt2176 0 2 4
  (interval_append leafTestAt2176 0 1 2
  leafTestAt2176_block_0
  leafTestAt2176_block_1)
  (interval_append leafTestAt2176 2 3 4
  leafTestAt2176_block_2
  leafTestAt2176_block_3))
  (interval_append leafTestAt2176 4 6 8
  (interval_append leafTestAt2176 4 5 6
  leafTestAt2176_block_4
  leafTestAt2176_block_5)
  (interval_append leafTestAt2176 6 7 8
  leafTestAt2176_block_6
  leafTestAt2176_block_7)))
  (interval_append leafTestAt2176 8 12 16
  (interval_append leafTestAt2176 8 10 12
  (interval_append leafTestAt2176 8 9 10
  leafTestAt2176_block_8
  leafTestAt2176_block_9)
  (interval_append leafTestAt2176 10 11 12
  leafTestAt2176_block_10
  leafTestAt2176_block_11))
  (interval_append leafTestAt2176 12 14 16
  (interval_append leafTestAt2176 12 13 14
  leafTestAt2176_block_12
  leafTestAt2176_block_13)
  (interval_append leafTestAt2176 14 15 16
  leafTestAt2176_block_14
  leafTestAt2176_block_15))))
  (interval_append leafTestAt2176 16 24 32
  (interval_append leafTestAt2176 16 20 24
  (interval_append leafTestAt2176 16 18 20
  (interval_append leafTestAt2176 16 17 18
  leafTestAt2176_block_16
  leafTestAt2176_block_17)
  (interval_append leafTestAt2176 18 19 20
  leafTestAt2176_block_18
  leafTestAt2176_block_19))
  (interval_append leafTestAt2176 20 22 24
  (interval_append leafTestAt2176 20 21 22
  leafTestAt2176_block_20
  leafTestAt2176_block_21)
  (interval_append leafTestAt2176 22 23 24
  leafTestAt2176_block_22
  leafTestAt2176_block_23)))
  (interval_append leafTestAt2176 24 28 32
  (interval_append leafTestAt2176 24 26 28
  (interval_append leafTestAt2176 24 25 26
  leafTestAt2176_block_24
  leafTestAt2176_block_25)
  (interval_append leafTestAt2176 26 27 28
  leafTestAt2176_block_26
  leafTestAt2176_block_27))
  (interval_append leafTestAt2176 28 30 32
  (interval_append leafTestAt2176 28 29 30
  leafTestAt2176_block_28
  leafTestAt2176_block_29)
  (interval_append leafTestAt2176 30 31 32
  leafTestAt2176_block_30
  leafTestAt2176_block_31)))))
cert_leafInterval 2176 2208
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
cert_leafTestAt 2208
cert_leafTestAt_block_2 2208 0 1
cert_leafTestAt_block_2 2208 1 2
cert_leafTestAt_block_2 2208 2 3
cert_leafTestAt_block_2 2208 3 4
cert_leafTestAt_block_2 2208 4 5
cert_leafTestAt_block_2 2208 5 6
cert_leafTestAt_block_2 2208 6 7
cert_leafTestAt_block_2 2208 7 8
cert_leafTestAt_block_2 2208 8 9
cert_leafTestAt_block_2 2208 9 10
cert_leafTestAt_block_2 2208 10 11
cert_leafTestAt_block_2 2208 11 12
cert_leafTestAt_block_2 2208 12 13
cert_leafTestAt_block_2 2208 13 14
cert_leafTestAt_block_2 2208 14 15
cert_leafTestAt_block_2 2208 15 16
cert_leafTestAt_block_2 2208 16 17
cert_leafTestAt_block_2 2208 17 18
cert_leafTestAt_block_2 2208 18 19
cert_leafTestAt_block_2 2208 19 20
cert_leafTestAt_block_2 2208 20 21
cert_leafTestAt_block_2 2208 21 22
cert_leafTestAt_block_2 2208 22 23
cert_leafTestAt_block_2 2208 23 24
cert_leafTestAt_block_2 2208 24 25
cert_leafTestAt_block_2 2208 25 26
cert_leafTestAt_block_2 2208 26 27
cert_leafTestAt_block_2 2208 27 28
cert_leafTestAt_block_2 2208 28 29
cert_leafTestAt_block_2 2208 29 30
cert_leafTestAt_block_2 2208 30 31
cert_leafTestAt_block_2 2208 31 32
theorem leafTestAt2208_complete : Interval leafTestAt2208 0 32 :=
  (interval_append leafTestAt2208 0 16 32
  (interval_append leafTestAt2208 0 8 16
  (interval_append leafTestAt2208 0 4 8
  (interval_append leafTestAt2208 0 2 4
  (interval_append leafTestAt2208 0 1 2
  leafTestAt2208_block_0
  leafTestAt2208_block_1)
  (interval_append leafTestAt2208 2 3 4
  leafTestAt2208_block_2
  leafTestAt2208_block_3))
  (interval_append leafTestAt2208 4 6 8
  (interval_append leafTestAt2208 4 5 6
  leafTestAt2208_block_4
  leafTestAt2208_block_5)
  (interval_append leafTestAt2208 6 7 8
  leafTestAt2208_block_6
  leafTestAt2208_block_7)))
  (interval_append leafTestAt2208 8 12 16
  (interval_append leafTestAt2208 8 10 12
  (interval_append leafTestAt2208 8 9 10
  leafTestAt2208_block_8
  leafTestAt2208_block_9)
  (interval_append leafTestAt2208 10 11 12
  leafTestAt2208_block_10
  leafTestAt2208_block_11))
  (interval_append leafTestAt2208 12 14 16
  (interval_append leafTestAt2208 12 13 14
  leafTestAt2208_block_12
  leafTestAt2208_block_13)
  (interval_append leafTestAt2208 14 15 16
  leafTestAt2208_block_14
  leafTestAt2208_block_15))))
  (interval_append leafTestAt2208 16 24 32
  (interval_append leafTestAt2208 16 20 24
  (interval_append leafTestAt2208 16 18 20
  (interval_append leafTestAt2208 16 17 18
  leafTestAt2208_block_16
  leafTestAt2208_block_17)
  (interval_append leafTestAt2208 18 19 20
  leafTestAt2208_block_18
  leafTestAt2208_block_19))
  (interval_append leafTestAt2208 20 22 24
  (interval_append leafTestAt2208 20 21 22
  leafTestAt2208_block_20
  leafTestAt2208_block_21)
  (interval_append leafTestAt2208 22 23 24
  leafTestAt2208_block_22
  leafTestAt2208_block_23)))
  (interval_append leafTestAt2208 24 28 32
  (interval_append leafTestAt2208 24 26 28
  (interval_append leafTestAt2208 24 25 26
  leafTestAt2208_block_24
  leafTestAt2208_block_25)
  (interval_append leafTestAt2208 26 27 28
  leafTestAt2208_block_26
  leafTestAt2208_block_27))
  (interval_append leafTestAt2208 28 30 32
  (interval_append leafTestAt2208 28 29 30
  leafTestAt2208_block_28
  leafTestAt2208_block_29)
  (interval_append leafTestAt2208 30 31 32
  leafTestAt2208_block_30
  leafTestAt2208_block_31)))))
cert_leafInterval 2208 2240
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
cert_leafTestAt 2240
cert_leafTestAt_block_2 2240 0 1
cert_leafTestAt_block_2 2240 1 2
cert_leafTestAt_block_2 2240 2 3
cert_leafTestAt_block_2 2240 3 4
cert_leafTestAt_block_2 2240 4 5
cert_leafTestAt_block_2 2240 5 6
cert_leafTestAt_block_2 2240 6 7
cert_leafTestAt_block_2 2240 7 8
cert_leafTestAt_block_2 2240 8 9
cert_leafTestAt_block_2 2240 9 10
cert_leafTestAt_block_2 2240 10 11
cert_leafTestAt_block_2 2240 11 12
cert_leafTestAt_block_2 2240 12 13
cert_leafTestAt_block_2 2240 13 14
cert_leafTestAt_block_2 2240 14 15
cert_leafTestAt_block_2 2240 15 16
cert_leafTestAt_block_2 2240 16 17
cert_leafTestAt_block_2 2240 17 18
cert_leafTestAt_block_2 2240 18 19
cert_leafTestAt_block_2 2240 19 20
cert_leafTestAt_block_2 2240 20 21
cert_leafTestAt_block_2 2240 21 22
cert_leafTestAt_block_2 2240 22 23
cert_leafTestAt_block_2 2240 23 24
cert_leafTestAt_block_2 2240 24 25
cert_leafTestAt_block_2 2240 25 26
cert_leafTestAt_block_2 2240 26 27
cert_leafTestAt_block_2 2240 27 28
cert_leafTestAt_block_2 2240 28 29
cert_leafTestAt_block_2 2240 29 30
cert_leafTestAt_block_2 2240 30 31
cert_leafTestAt_block_2 2240 31 32
theorem leafTestAt2240_complete : Interval leafTestAt2240 0 32 :=
  (interval_append leafTestAt2240 0 16 32
  (interval_append leafTestAt2240 0 8 16
  (interval_append leafTestAt2240 0 4 8
  (interval_append leafTestAt2240 0 2 4
  (interval_append leafTestAt2240 0 1 2
  leafTestAt2240_block_0
  leafTestAt2240_block_1)
  (interval_append leafTestAt2240 2 3 4
  leafTestAt2240_block_2
  leafTestAt2240_block_3))
  (interval_append leafTestAt2240 4 6 8
  (interval_append leafTestAt2240 4 5 6
  leafTestAt2240_block_4
  leafTestAt2240_block_5)
  (interval_append leafTestAt2240 6 7 8
  leafTestAt2240_block_6
  leafTestAt2240_block_7)))
  (interval_append leafTestAt2240 8 12 16
  (interval_append leafTestAt2240 8 10 12
  (interval_append leafTestAt2240 8 9 10
  leafTestAt2240_block_8
  leafTestAt2240_block_9)
  (interval_append leafTestAt2240 10 11 12
  leafTestAt2240_block_10
  leafTestAt2240_block_11))
  (interval_append leafTestAt2240 12 14 16
  (interval_append leafTestAt2240 12 13 14
  leafTestAt2240_block_12
  leafTestAt2240_block_13)
  (interval_append leafTestAt2240 14 15 16
  leafTestAt2240_block_14
  leafTestAt2240_block_15))))
  (interval_append leafTestAt2240 16 24 32
  (interval_append leafTestAt2240 16 20 24
  (interval_append leafTestAt2240 16 18 20
  (interval_append leafTestAt2240 16 17 18
  leafTestAt2240_block_16
  leafTestAt2240_block_17)
  (interval_append leafTestAt2240 18 19 20
  leafTestAt2240_block_18
  leafTestAt2240_block_19))
  (interval_append leafTestAt2240 20 22 24
  (interval_append leafTestAt2240 20 21 22
  leafTestAt2240_block_20
  leafTestAt2240_block_21)
  (interval_append leafTestAt2240 22 23 24
  leafTestAt2240_block_22
  leafTestAt2240_block_23)))
  (interval_append leafTestAt2240 24 28 32
  (interval_append leafTestAt2240 24 26 28
  (interval_append leafTestAt2240 24 25 26
  leafTestAt2240_block_24
  leafTestAt2240_block_25)
  (interval_append leafTestAt2240 26 27 28
  leafTestAt2240_block_26
  leafTestAt2240_block_27))
  (interval_append leafTestAt2240 28 30 32
  (interval_append leafTestAt2240 28 29 30
  leafTestAt2240_block_28
  leafTestAt2240_block_29)
  (interval_append leafTestAt2240 30 31 32
  leafTestAt2240_block_30
  leafTestAt2240_block_31)))))
cert_leafInterval 2240 2272
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
cert_leafTestAt 2272
cert_leafTestAt_block_2 2272 0 1
cert_leafTestAt_block_2 2272 1 2
cert_leafTestAt_block_2 2272 2 3
cert_leafTestAt_block_2 2272 3 4
cert_leafTestAt_block_2 2272 4 5
cert_leafTestAt_block_2 2272 5 6
cert_leafTestAt_block_2 2272 6 7
cert_leafTestAt_block_2 2272 7 8
cert_leafTestAt_block_2 2272 8 9
cert_leafTestAt_block_2 2272 9 10
cert_leafTestAt_block_2 2272 10 11
cert_leafTestAt_block_2 2272 11 12
cert_leafTestAt_block_2 2272 12 13
cert_leafTestAt_block_2 2272 13 14
cert_leafTestAt_block_2 2272 14 15
cert_leafTestAt_block_2 2272 15 16
cert_leafTestAt_block_2 2272 16 17
cert_leafTestAt_block_2 2272 17 18
cert_leafTestAt_block_2 2272 18 19
cert_leafTestAt_block_2 2272 19 20
cert_leafTestAt_block_2 2272 20 21
cert_leafTestAt_block_2 2272 21 22
cert_leafTestAt_block_2 2272 22 23
cert_leafTestAt_block_2 2272 23 24
cert_leafTestAt_block_2 2272 24 25
cert_leafTestAt_block_2 2272 25 26
cert_leafTestAt_block_2 2272 26 27
cert_leafTestAt_block_2 2272 27 28
cert_leafTestAt_block_2 2272 28 29
cert_leafTestAt_block_2 2272 29 30
cert_leafTestAt_block_2 2272 30 31
cert_leafTestAt_block_2 2272 31 32
theorem leafTestAt2272_complete : Interval leafTestAt2272 0 32 :=
  (interval_append leafTestAt2272 0 16 32
  (interval_append leafTestAt2272 0 8 16
  (interval_append leafTestAt2272 0 4 8
  (interval_append leafTestAt2272 0 2 4
  (interval_append leafTestAt2272 0 1 2
  leafTestAt2272_block_0
  leafTestAt2272_block_1)
  (interval_append leafTestAt2272 2 3 4
  leafTestAt2272_block_2
  leafTestAt2272_block_3))
  (interval_append leafTestAt2272 4 6 8
  (interval_append leafTestAt2272 4 5 6
  leafTestAt2272_block_4
  leafTestAt2272_block_5)
  (interval_append leafTestAt2272 6 7 8
  leafTestAt2272_block_6
  leafTestAt2272_block_7)))
  (interval_append leafTestAt2272 8 12 16
  (interval_append leafTestAt2272 8 10 12
  (interval_append leafTestAt2272 8 9 10
  leafTestAt2272_block_8
  leafTestAt2272_block_9)
  (interval_append leafTestAt2272 10 11 12
  leafTestAt2272_block_10
  leafTestAt2272_block_11))
  (interval_append leafTestAt2272 12 14 16
  (interval_append leafTestAt2272 12 13 14
  leafTestAt2272_block_12
  leafTestAt2272_block_13)
  (interval_append leafTestAt2272 14 15 16
  leafTestAt2272_block_14
  leafTestAt2272_block_15))))
  (interval_append leafTestAt2272 16 24 32
  (interval_append leafTestAt2272 16 20 24
  (interval_append leafTestAt2272 16 18 20
  (interval_append leafTestAt2272 16 17 18
  leafTestAt2272_block_16
  leafTestAt2272_block_17)
  (interval_append leafTestAt2272 18 19 20
  leafTestAt2272_block_18
  leafTestAt2272_block_19))
  (interval_append leafTestAt2272 20 22 24
  (interval_append leafTestAt2272 20 21 22
  leafTestAt2272_block_20
  leafTestAt2272_block_21)
  (interval_append leafTestAt2272 22 23 24
  leafTestAt2272_block_22
  leafTestAt2272_block_23)))
  (interval_append leafTestAt2272 24 28 32
  (interval_append leafTestAt2272 24 26 28
  (interval_append leafTestAt2272 24 25 26
  leafTestAt2272_block_24
  leafTestAt2272_block_25)
  (interval_append leafTestAt2272 26 27 28
  leafTestAt2272_block_26
  leafTestAt2272_block_27))
  (interval_append leafTestAt2272 28 30 32
  (interval_append leafTestAt2272 28 29 30
  leafTestAt2272_block_28
  leafTestAt2272_block_29)
  (interval_append leafTestAt2272 30 31 32
  leafTestAt2272_block_30
  leafTestAt2272_block_31)))))
cert_leafInterval 2272 2304
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
cert_leafTestAt 2304
cert_leafTestAt_block_2 2304 0 1
cert_leafTestAt_block_2 2304 1 2
cert_leafTestAt_block_2 2304 2 3
cert_leafTestAt_block_2 2304 3 4
cert_leafTestAt_block_2 2304 4 5
cert_leafTestAt_block_2 2304 5 6
cert_leafTestAt_block_2 2304 6 7
cert_leafTestAt_block_2 2304 7 8
cert_leafTestAt_block_2 2304 8 9
cert_leafTestAt_block_2 2304 9 10
cert_leafTestAt_block_2 2304 10 11
cert_leafTestAt_block_2 2304 11 12
cert_leafTestAt_block_2 2304 12 13
cert_leafTestAt_block_2 2304 13 14
cert_leafTestAt_block_2 2304 14 15
cert_leafTestAt_block_2 2304 15 16
cert_leafTestAt_block_2 2304 16 17
cert_leafTestAt_block_2 2304 17 18
cert_leafTestAt_block_2 2304 18 19
cert_leafTestAt_block_2 2304 19 20
cert_leafTestAt_block_2 2304 20 21
cert_leafTestAt_block_2 2304 21 22
cert_leafTestAt_block_2 2304 22 23
cert_leafTestAt_block_2 2304 23 24
cert_leafTestAt_block_2 2304 24 25
cert_leafTestAt_block_2 2304 25 26
cert_leafTestAt_block_2 2304 26 27
cert_leafTestAt_block_2 2304 27 28
cert_leafTestAt_block_2 2304 28 29
cert_leafTestAt_block_2 2304 29 30
cert_leafTestAt_block_2 2304 30 31
cert_leafTestAt_block_2 2304 31 32
theorem leafTestAt2304_complete : Interval leafTestAt2304 0 32 :=
  (interval_append leafTestAt2304 0 16 32
  (interval_append leafTestAt2304 0 8 16
  (interval_append leafTestAt2304 0 4 8
  (interval_append leafTestAt2304 0 2 4
  (interval_append leafTestAt2304 0 1 2
  leafTestAt2304_block_0
  leafTestAt2304_block_1)
  (interval_append leafTestAt2304 2 3 4
  leafTestAt2304_block_2
  leafTestAt2304_block_3))
  (interval_append leafTestAt2304 4 6 8
  (interval_append leafTestAt2304 4 5 6
  leafTestAt2304_block_4
  leafTestAt2304_block_5)
  (interval_append leafTestAt2304 6 7 8
  leafTestAt2304_block_6
  leafTestAt2304_block_7)))
  (interval_append leafTestAt2304 8 12 16
  (interval_append leafTestAt2304 8 10 12
  (interval_append leafTestAt2304 8 9 10
  leafTestAt2304_block_8
  leafTestAt2304_block_9)
  (interval_append leafTestAt2304 10 11 12
  leafTestAt2304_block_10
  leafTestAt2304_block_11))
  (interval_append leafTestAt2304 12 14 16
  (interval_append leafTestAt2304 12 13 14
  leafTestAt2304_block_12
  leafTestAt2304_block_13)
  (interval_append leafTestAt2304 14 15 16
  leafTestAt2304_block_14
  leafTestAt2304_block_15))))
  (interval_append leafTestAt2304 16 24 32
  (interval_append leafTestAt2304 16 20 24
  (interval_append leafTestAt2304 16 18 20
  (interval_append leafTestAt2304 16 17 18
  leafTestAt2304_block_16
  leafTestAt2304_block_17)
  (interval_append leafTestAt2304 18 19 20
  leafTestAt2304_block_18
  leafTestAt2304_block_19))
  (interval_append leafTestAt2304 20 22 24
  (interval_append leafTestAt2304 20 21 22
  leafTestAt2304_block_20
  leafTestAt2304_block_21)
  (interval_append leafTestAt2304 22 23 24
  leafTestAt2304_block_22
  leafTestAt2304_block_23)))
  (interval_append leafTestAt2304 24 28 32
  (interval_append leafTestAt2304 24 26 28
  (interval_append leafTestAt2304 24 25 26
  leafTestAt2304_block_24
  leafTestAt2304_block_25)
  (interval_append leafTestAt2304 26 27 28
  leafTestAt2304_block_26
  leafTestAt2304_block_27))
  (interval_append leafTestAt2304 28 30 32
  (interval_append leafTestAt2304 28 29 30
  leafTestAt2304_block_28
  leafTestAt2304_block_29)
  (interval_append leafTestAt2304 30 31 32
  leafTestAt2304_block_30
  leafTestAt2304_block_31)))))
cert_leafInterval 2304 2336
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
cert_leafTestAt 2336
cert_leafTestAt_block_2 2336 0 1
cert_leafTestAt_block_2 2336 1 2
cert_leafTestAt_block_2 2336 2 3
cert_leafTestAt_block_2 2336 3 4
cert_leafTestAt_block_2 2336 4 5
cert_leafTestAt_block_2 2336 5 6
cert_leafTestAt_block_2 2336 6 7
cert_leafTestAt_block_2 2336 7 8
cert_leafTestAt_block_2 2336 8 9
cert_leafTestAt_block_2 2336 9 10
cert_leafTestAt_block_2 2336 10 11
cert_leafTestAt_block_2 2336 11 12
cert_leafTestAt_block_2 2336 12 13
cert_leafTestAt_block_2 2336 13 14
cert_leafTestAt_block_2 2336 14 15
cert_leafTestAt_block_2 2336 15 16
cert_leafTestAt_block_2 2336 16 17
cert_leafTestAt_block_2 2336 17 18
cert_leafTestAt_block_2 2336 18 19
cert_leafTestAt_block_2 2336 19 20
cert_leafTestAt_block_2 2336 20 21
cert_leafTestAt_block_2 2336 21 22
cert_leafTestAt_block_2 2336 22 23
cert_leafTestAt_block_2 2336 23 24
cert_leafTestAt_block_2 2336 24 25
cert_leafTestAt_block_2 2336 25 26
cert_leafTestAt_block_2 2336 26 27
cert_leafTestAt_block_2 2336 27 28
cert_leafTestAt_block_2 2336 28 29
cert_leafTestAt_block_2 2336 29 30
cert_leafTestAt_block_2 2336 30 31
cert_leafTestAt_block_2 2336 31 32
theorem leafTestAt2336_complete : Interval leafTestAt2336 0 32 :=
  (interval_append leafTestAt2336 0 16 32
  (interval_append leafTestAt2336 0 8 16
  (interval_append leafTestAt2336 0 4 8
  (interval_append leafTestAt2336 0 2 4
  (interval_append leafTestAt2336 0 1 2
  leafTestAt2336_block_0
  leafTestAt2336_block_1)
  (interval_append leafTestAt2336 2 3 4
  leafTestAt2336_block_2
  leafTestAt2336_block_3))
  (interval_append leafTestAt2336 4 6 8
  (interval_append leafTestAt2336 4 5 6
  leafTestAt2336_block_4
  leafTestAt2336_block_5)
  (interval_append leafTestAt2336 6 7 8
  leafTestAt2336_block_6
  leafTestAt2336_block_7)))
  (interval_append leafTestAt2336 8 12 16
  (interval_append leafTestAt2336 8 10 12
  (interval_append leafTestAt2336 8 9 10
  leafTestAt2336_block_8
  leafTestAt2336_block_9)
  (interval_append leafTestAt2336 10 11 12
  leafTestAt2336_block_10
  leafTestAt2336_block_11))
  (interval_append leafTestAt2336 12 14 16
  (interval_append leafTestAt2336 12 13 14
  leafTestAt2336_block_12
  leafTestAt2336_block_13)
  (interval_append leafTestAt2336 14 15 16
  leafTestAt2336_block_14
  leafTestAt2336_block_15))))
  (interval_append leafTestAt2336 16 24 32
  (interval_append leafTestAt2336 16 20 24
  (interval_append leafTestAt2336 16 18 20
  (interval_append leafTestAt2336 16 17 18
  leafTestAt2336_block_16
  leafTestAt2336_block_17)
  (interval_append leafTestAt2336 18 19 20
  leafTestAt2336_block_18
  leafTestAt2336_block_19))
  (interval_append leafTestAt2336 20 22 24
  (interval_append leafTestAt2336 20 21 22
  leafTestAt2336_block_20
  leafTestAt2336_block_21)
  (interval_append leafTestAt2336 22 23 24
  leafTestAt2336_block_22
  leafTestAt2336_block_23)))
  (interval_append leafTestAt2336 24 28 32
  (interval_append leafTestAt2336 24 26 28
  (interval_append leafTestAt2336 24 25 26
  leafTestAt2336_block_24
  leafTestAt2336_block_25)
  (interval_append leafTestAt2336 26 27 28
  leafTestAt2336_block_26
  leafTestAt2336_block_27))
  (interval_append leafTestAt2336 28 30 32
  (interval_append leafTestAt2336 28 29 30
  leafTestAt2336_block_28
  leafTestAt2336_block_29)
  (interval_append leafTestAt2336 30 31 32
  leafTestAt2336_block_30
  leafTestAt2336_block_31)))))
cert_leafInterval 2336 2368
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
cert_leafTestAt 2368
cert_leafTestAt_block_2 2368 0 1
cert_leafTestAt_block_2 2368 1 2
cert_leafTestAt_block_2 2368 2 3
cert_leafTestAt_block_2 2368 3 4
cert_leafTestAt_block_2 2368 4 5
cert_leafTestAt_block_2 2368 5 6
cert_leafTestAt_block_2 2368 6 7
cert_leafTestAt_block_2 2368 7 8
cert_leafTestAt_block_2 2368 8 9
cert_leafTestAt_block_2 2368 9 10
cert_leafTestAt_block_2 2368 10 11
cert_leafTestAt_block_2 2368 11 12
cert_leafTestAt_block_2 2368 12 13
cert_leafTestAt_block_2 2368 13 14
cert_leafTestAt_block_2 2368 14 15
cert_leafTestAt_block_2 2368 15 16
cert_leafTestAt_block_2 2368 16 17
cert_leafTestAt_block_2 2368 17 18
cert_leafTestAt_block_2 2368 18 19
cert_leafTestAt_block_2 2368 19 20
cert_leafTestAt_block_2 2368 20 21
cert_leafTestAt_block_2 2368 21 22
cert_leafTestAt_block_2 2368 22 23
cert_leafTestAt_block_2 2368 23 24
cert_leafTestAt_block_2 2368 24 25
cert_leafTestAt_block_2 2368 25 26
cert_leafTestAt_block_2 2368 26 27
cert_leafTestAt_block_2 2368 27 28
cert_leafTestAt_block_2 2368 28 29
cert_leafTestAt_block_2 2368 29 30
cert_leafTestAt_block_2 2368 30 31
cert_leafTestAt_block_2 2368 31 32
theorem leafTestAt2368_complete : Interval leafTestAt2368 0 32 :=
  (interval_append leafTestAt2368 0 16 32
  (interval_append leafTestAt2368 0 8 16
  (interval_append leafTestAt2368 0 4 8
  (interval_append leafTestAt2368 0 2 4
  (interval_append leafTestAt2368 0 1 2
  leafTestAt2368_block_0
  leafTestAt2368_block_1)
  (interval_append leafTestAt2368 2 3 4
  leafTestAt2368_block_2
  leafTestAt2368_block_3))
  (interval_append leafTestAt2368 4 6 8
  (interval_append leafTestAt2368 4 5 6
  leafTestAt2368_block_4
  leafTestAt2368_block_5)
  (interval_append leafTestAt2368 6 7 8
  leafTestAt2368_block_6
  leafTestAt2368_block_7)))
  (interval_append leafTestAt2368 8 12 16
  (interval_append leafTestAt2368 8 10 12
  (interval_append leafTestAt2368 8 9 10
  leafTestAt2368_block_8
  leafTestAt2368_block_9)
  (interval_append leafTestAt2368 10 11 12
  leafTestAt2368_block_10
  leafTestAt2368_block_11))
  (interval_append leafTestAt2368 12 14 16
  (interval_append leafTestAt2368 12 13 14
  leafTestAt2368_block_12
  leafTestAt2368_block_13)
  (interval_append leafTestAt2368 14 15 16
  leafTestAt2368_block_14
  leafTestAt2368_block_15))))
  (interval_append leafTestAt2368 16 24 32
  (interval_append leafTestAt2368 16 20 24
  (interval_append leafTestAt2368 16 18 20
  (interval_append leafTestAt2368 16 17 18
  leafTestAt2368_block_16
  leafTestAt2368_block_17)
  (interval_append leafTestAt2368 18 19 20
  leafTestAt2368_block_18
  leafTestAt2368_block_19))
  (interval_append leafTestAt2368 20 22 24
  (interval_append leafTestAt2368 20 21 22
  leafTestAt2368_block_20
  leafTestAt2368_block_21)
  (interval_append leafTestAt2368 22 23 24
  leafTestAt2368_block_22
  leafTestAt2368_block_23)))
  (interval_append leafTestAt2368 24 28 32
  (interval_append leafTestAt2368 24 26 28
  (interval_append leafTestAt2368 24 25 26
  leafTestAt2368_block_24
  leafTestAt2368_block_25)
  (interval_append leafTestAt2368 26 27 28
  leafTestAt2368_block_26
  leafTestAt2368_block_27))
  (interval_append leafTestAt2368 28 30 32
  (interval_append leafTestAt2368 28 29 30
  leafTestAt2368_block_28
  leafTestAt2368_block_29)
  (interval_append leafTestAt2368 30 31 32
  leafTestAt2368_block_30
  leafTestAt2368_block_31)))))
cert_leafInterval 2368 2400
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
cert_leafTestAt 2400
cert_leafTestAt_block_2 2400 0 1
cert_leafTestAt_block_2 2400 1 2
cert_leafTestAt_block_2 2400 2 3
cert_leafTestAt_block_2 2400 3 4
cert_leafTestAt_block_2 2400 4 5
cert_leafTestAt_block_2 2400 5 6
cert_leafTestAt_block_2 2400 6 7
cert_leafTestAt_block_2 2400 7 8
cert_leafTestAt_block_2 2400 8 9
cert_leafTestAt_block_2 2400 9 10
cert_leafTestAt_block_2 2400 10 11
cert_leafTestAt_block_2 2400 11 12
cert_leafTestAt_block_2 2400 12 13
cert_leafTestAt_block_2 2400 13 14
cert_leafTestAt_block_2 2400 14 15
cert_leafTestAt_block_2 2400 15 16
cert_leafTestAt_block_2 2400 16 17
cert_leafTestAt_block_2 2400 17 18
cert_leafTestAt_block_2 2400 18 19
cert_leafTestAt_block_2 2400 19 20
cert_leafTestAt_block_2 2400 20 21
cert_leafTestAt_block_2 2400 21 22
cert_leafTestAt_block_2 2400 22 23
cert_leafTestAt_block_2 2400 23 24
cert_leafTestAt_block_2 2400 24 25
cert_leafTestAt_block_2 2400 25 26
cert_leafTestAt_block_2 2400 26 27
cert_leafTestAt_block_2 2400 27 28
cert_leafTestAt_block_2 2400 28 29
cert_leafTestAt_block_2 2400 29 30
cert_leafTestAt_block_2 2400 30 31
cert_leafTestAt_block_2 2400 31 32
theorem leafTestAt2400_complete : Interval leafTestAt2400 0 32 :=
  (interval_append leafTestAt2400 0 16 32
  (interval_append leafTestAt2400 0 8 16
  (interval_append leafTestAt2400 0 4 8
  (interval_append leafTestAt2400 0 2 4
  (interval_append leafTestAt2400 0 1 2
  leafTestAt2400_block_0
  leafTestAt2400_block_1)
  (interval_append leafTestAt2400 2 3 4
  leafTestAt2400_block_2
  leafTestAt2400_block_3))
  (interval_append leafTestAt2400 4 6 8
  (interval_append leafTestAt2400 4 5 6
  leafTestAt2400_block_4
  leafTestAt2400_block_5)
  (interval_append leafTestAt2400 6 7 8
  leafTestAt2400_block_6
  leafTestAt2400_block_7)))
  (interval_append leafTestAt2400 8 12 16
  (interval_append leafTestAt2400 8 10 12
  (interval_append leafTestAt2400 8 9 10
  leafTestAt2400_block_8
  leafTestAt2400_block_9)
  (interval_append leafTestAt2400 10 11 12
  leafTestAt2400_block_10
  leafTestAt2400_block_11))
  (interval_append leafTestAt2400 12 14 16
  (interval_append leafTestAt2400 12 13 14
  leafTestAt2400_block_12
  leafTestAt2400_block_13)
  (interval_append leafTestAt2400 14 15 16
  leafTestAt2400_block_14
  leafTestAt2400_block_15))))
  (interval_append leafTestAt2400 16 24 32
  (interval_append leafTestAt2400 16 20 24
  (interval_append leafTestAt2400 16 18 20
  (interval_append leafTestAt2400 16 17 18
  leafTestAt2400_block_16
  leafTestAt2400_block_17)
  (interval_append leafTestAt2400 18 19 20
  leafTestAt2400_block_18
  leafTestAt2400_block_19))
  (interval_append leafTestAt2400 20 22 24
  (interval_append leafTestAt2400 20 21 22
  leafTestAt2400_block_20
  leafTestAt2400_block_21)
  (interval_append leafTestAt2400 22 23 24
  leafTestAt2400_block_22
  leafTestAt2400_block_23)))
  (interval_append leafTestAt2400 24 28 32
  (interval_append leafTestAt2400 24 26 28
  (interval_append leafTestAt2400 24 25 26
  leafTestAt2400_block_24
  leafTestAt2400_block_25)
  (interval_append leafTestAt2400 26 27 28
  leafTestAt2400_block_26
  leafTestAt2400_block_27))
  (interval_append leafTestAt2400 28 30 32
  (interval_append leafTestAt2400 28 29 30
  leafTestAt2400_block_28
  leafTestAt2400_block_29)
  (interval_append leafTestAt2400 30 31 32
  leafTestAt2400_block_30
  leafTestAt2400_block_31)))))
cert_leafInterval 2400 2432
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
cert_leafTestAt 2432
cert_leafTestAt_block_2 2432 0 1
cert_leafTestAt_block_2 2432 1 2
cert_leafTestAt_block_2 2432 2 3
cert_leafTestAt_block_2 2432 3 4
cert_leafTestAt_block_2 2432 4 5
cert_leafTestAt_block_2 2432 5 6
cert_leafTestAt_block_2 2432 6 7
cert_leafTestAt_block_2 2432 7 8
cert_leafTestAt_block_2 2432 8 9
cert_leafTestAt_block_2 2432 9 10
cert_leafTestAt_block_2 2432 10 11
cert_leafTestAt_block_2 2432 11 12
cert_leafTestAt_block_2 2432 12 13
cert_leafTestAt_block_2 2432 13 14
cert_leafTestAt_block_2 2432 14 15
cert_leafTestAt_block_2 2432 15 16
cert_leafTestAt_block_2 2432 16 17
cert_leafTestAt_block_2 2432 17 18
cert_leafTestAt_block_2 2432 18 19
cert_leafTestAt_block_2 2432 19 20
cert_leafTestAt_block_2 2432 20 21
cert_leafTestAt_block_2 2432 21 22
cert_leafTestAt_block_2 2432 22 23
cert_leafTestAt_block_2 2432 23 24
cert_leafTestAt_block_2 2432 24 25
cert_leafTestAt_block_2 2432 25 26
cert_leafTestAt_block_2 2432 26 27
cert_leafTestAt_block_2 2432 27 28
cert_leafTestAt_block_2 2432 28 29
cert_leafTestAt_block_2 2432 29 30
cert_leafTestAt_block_2 2432 30 31
cert_leafTestAt_block_2 2432 31 32
theorem leafTestAt2432_complete : Interval leafTestAt2432 0 32 :=
  (interval_append leafTestAt2432 0 16 32
  (interval_append leafTestAt2432 0 8 16
  (interval_append leafTestAt2432 0 4 8
  (interval_append leafTestAt2432 0 2 4
  (interval_append leafTestAt2432 0 1 2
  leafTestAt2432_block_0
  leafTestAt2432_block_1)
  (interval_append leafTestAt2432 2 3 4
  leafTestAt2432_block_2
  leafTestAt2432_block_3))
  (interval_append leafTestAt2432 4 6 8
  (interval_append leafTestAt2432 4 5 6
  leafTestAt2432_block_4
  leafTestAt2432_block_5)
  (interval_append leafTestAt2432 6 7 8
  leafTestAt2432_block_6
  leafTestAt2432_block_7)))
  (interval_append leafTestAt2432 8 12 16
  (interval_append leafTestAt2432 8 10 12
  (interval_append leafTestAt2432 8 9 10
  leafTestAt2432_block_8
  leafTestAt2432_block_9)
  (interval_append leafTestAt2432 10 11 12
  leafTestAt2432_block_10
  leafTestAt2432_block_11))
  (interval_append leafTestAt2432 12 14 16
  (interval_append leafTestAt2432 12 13 14
  leafTestAt2432_block_12
  leafTestAt2432_block_13)
  (interval_append leafTestAt2432 14 15 16
  leafTestAt2432_block_14
  leafTestAt2432_block_15))))
  (interval_append leafTestAt2432 16 24 32
  (interval_append leafTestAt2432 16 20 24
  (interval_append leafTestAt2432 16 18 20
  (interval_append leafTestAt2432 16 17 18
  leafTestAt2432_block_16
  leafTestAt2432_block_17)
  (interval_append leafTestAt2432 18 19 20
  leafTestAt2432_block_18
  leafTestAt2432_block_19))
  (interval_append leafTestAt2432 20 22 24
  (interval_append leafTestAt2432 20 21 22
  leafTestAt2432_block_20
  leafTestAt2432_block_21)
  (interval_append leafTestAt2432 22 23 24
  leafTestAt2432_block_22
  leafTestAt2432_block_23)))
  (interval_append leafTestAt2432 24 28 32
  (interval_append leafTestAt2432 24 26 28
  (interval_append leafTestAt2432 24 25 26
  leafTestAt2432_block_24
  leafTestAt2432_block_25)
  (interval_append leafTestAt2432 26 27 28
  leafTestAt2432_block_26
  leafTestAt2432_block_27))
  (interval_append leafTestAt2432 28 30 32
  (interval_append leafTestAt2432 28 29 30
  leafTestAt2432_block_28
  leafTestAt2432_block_29)
  (interval_append leafTestAt2432 30 31 32
  leafTestAt2432_block_30
  leafTestAt2432_block_31)))))
cert_leafInterval 2432 2464
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
cert_leafTestAt 2464
cert_leafTestAt_block_2 2464 0 1
cert_leafTestAt_block_2 2464 1 2
cert_leafTestAt_block_2 2464 2 3
cert_leafTestAt_block_2 2464 3 4
cert_leafTestAt_block_2 2464 4 5
cert_leafTestAt_block_2 2464 5 6
cert_leafTestAt_block_2 2464 6 7
cert_leafTestAt_block_2 2464 7 8
cert_leafTestAt_block_2 2464 8 9
cert_leafTestAt_block_2 2464 9 10
cert_leafTestAt_block_2 2464 10 11
cert_leafTestAt_block_2 2464 11 12
cert_leafTestAt_block_2 2464 12 13
cert_leafTestAt_block_2 2464 13 14
cert_leafTestAt_block_2 2464 14 15
cert_leafTestAt_block_2 2464 15 16
cert_leafTestAt_block_2 2464 16 17
cert_leafTestAt_block_2 2464 17 18
cert_leafTestAt_block_2 2464 18 19
cert_leafTestAt_block_2 2464 19 20
cert_leafTestAt_block_2 2464 20 21
cert_leafTestAt_block_2 2464 21 22
cert_leafTestAt_block_2 2464 22 23
cert_leafTestAt_block_2 2464 23 24
cert_leafTestAt_block_2 2464 24 25
cert_leafTestAt_block_2 2464 25 26
cert_leafTestAt_block_2 2464 26 27
cert_leafTestAt_block_2 2464 27 28
cert_leafTestAt_block_2 2464 28 29
cert_leafTestAt_block_2 2464 29 30
cert_leafTestAt_block_2 2464 30 31
cert_leafTestAt_block_2 2464 31 32
theorem leafTestAt2464_complete : Interval leafTestAt2464 0 32 :=
  (interval_append leafTestAt2464 0 16 32
  (interval_append leafTestAt2464 0 8 16
  (interval_append leafTestAt2464 0 4 8
  (interval_append leafTestAt2464 0 2 4
  (interval_append leafTestAt2464 0 1 2
  leafTestAt2464_block_0
  leafTestAt2464_block_1)
  (interval_append leafTestAt2464 2 3 4
  leafTestAt2464_block_2
  leafTestAt2464_block_3))
  (interval_append leafTestAt2464 4 6 8
  (interval_append leafTestAt2464 4 5 6
  leafTestAt2464_block_4
  leafTestAt2464_block_5)
  (interval_append leafTestAt2464 6 7 8
  leafTestAt2464_block_6
  leafTestAt2464_block_7)))
  (interval_append leafTestAt2464 8 12 16
  (interval_append leafTestAt2464 8 10 12
  (interval_append leafTestAt2464 8 9 10
  leafTestAt2464_block_8
  leafTestAt2464_block_9)
  (interval_append leafTestAt2464 10 11 12
  leafTestAt2464_block_10
  leafTestAt2464_block_11))
  (interval_append leafTestAt2464 12 14 16
  (interval_append leafTestAt2464 12 13 14
  leafTestAt2464_block_12
  leafTestAt2464_block_13)
  (interval_append leafTestAt2464 14 15 16
  leafTestAt2464_block_14
  leafTestAt2464_block_15))))
  (interval_append leafTestAt2464 16 24 32
  (interval_append leafTestAt2464 16 20 24
  (interval_append leafTestAt2464 16 18 20
  (interval_append leafTestAt2464 16 17 18
  leafTestAt2464_block_16
  leafTestAt2464_block_17)
  (interval_append leafTestAt2464 18 19 20
  leafTestAt2464_block_18
  leafTestAt2464_block_19))
  (interval_append leafTestAt2464 20 22 24
  (interval_append leafTestAt2464 20 21 22
  leafTestAt2464_block_20
  leafTestAt2464_block_21)
  (interval_append leafTestAt2464 22 23 24
  leafTestAt2464_block_22
  leafTestAt2464_block_23)))
  (interval_append leafTestAt2464 24 28 32
  (interval_append leafTestAt2464 24 26 28
  (interval_append leafTestAt2464 24 25 26
  leafTestAt2464_block_24
  leafTestAt2464_block_25)
  (interval_append leafTestAt2464 26 27 28
  leafTestAt2464_block_26
  leafTestAt2464_block_27))
  (interval_append leafTestAt2464 28 30 32
  (interval_append leafTestAt2464 28 29 30
  leafTestAt2464_block_28
  leafTestAt2464_block_29)
  (interval_append leafTestAt2464 30 31 32
  leafTestAt2464_block_30
  leafTestAt2464_block_31)))))
cert_leafInterval 2464 2496
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
cert_leafTestAt 2496
cert_leafTestAt_block_2 2496 0 1
cert_leafTestAt_block_2 2496 1 2
cert_leafTestAt_block_2 2496 2 3
cert_leafTestAt_block_2 2496 3 4
cert_leafTestAt_block_2 2496 4 5
cert_leafTestAt_block_2 2496 5 6
cert_leafTestAt_block_2 2496 6 7
cert_leafTestAt_block_2 2496 7 8
cert_leafTestAt_block_2 2496 8 9
cert_leafTestAt_block_2 2496 9 10
cert_leafTestAt_block_2 2496 10 11
cert_leafTestAt_block_2 2496 11 12
cert_leafTestAt_block_2 2496 12 13
cert_leafTestAt_block_2 2496 13 14
cert_leafTestAt_block_2 2496 14 15
cert_leafTestAt_block_2 2496 15 16
cert_leafTestAt_block_2 2496 16 17
cert_leafTestAt_block_2 2496 17 18
cert_leafTestAt_block_2 2496 18 19
cert_leafTestAt_block_2 2496 19 20
cert_leafTestAt_block_2 2496 20 21
cert_leafTestAt_block_2 2496 21 22
cert_leafTestAt_block_2 2496 22 23
cert_leafTestAt_block_2 2496 23 24
cert_leafTestAt_block_2 2496 24 25
cert_leafTestAt_block_2 2496 25 26
cert_leafTestAt_block_2 2496 26 27
cert_leafTestAt_block_2 2496 27 28
cert_leafTestAt_block_2 2496 28 29
cert_leafTestAt_block_2 2496 29 30
cert_leafTestAt_block_2 2496 30 31
cert_leafTestAt_block_2 2496 31 32
theorem leafTestAt2496_complete : Interval leafTestAt2496 0 32 :=
  (interval_append leafTestAt2496 0 16 32
  (interval_append leafTestAt2496 0 8 16
  (interval_append leafTestAt2496 0 4 8
  (interval_append leafTestAt2496 0 2 4
  (interval_append leafTestAt2496 0 1 2
  leafTestAt2496_block_0
  leafTestAt2496_block_1)
  (interval_append leafTestAt2496 2 3 4
  leafTestAt2496_block_2
  leafTestAt2496_block_3))
  (interval_append leafTestAt2496 4 6 8
  (interval_append leafTestAt2496 4 5 6
  leafTestAt2496_block_4
  leafTestAt2496_block_5)
  (interval_append leafTestAt2496 6 7 8
  leafTestAt2496_block_6
  leafTestAt2496_block_7)))
  (interval_append leafTestAt2496 8 12 16
  (interval_append leafTestAt2496 8 10 12
  (interval_append leafTestAt2496 8 9 10
  leafTestAt2496_block_8
  leafTestAt2496_block_9)
  (interval_append leafTestAt2496 10 11 12
  leafTestAt2496_block_10
  leafTestAt2496_block_11))
  (interval_append leafTestAt2496 12 14 16
  (interval_append leafTestAt2496 12 13 14
  leafTestAt2496_block_12
  leafTestAt2496_block_13)
  (interval_append leafTestAt2496 14 15 16
  leafTestAt2496_block_14
  leafTestAt2496_block_15))))
  (interval_append leafTestAt2496 16 24 32
  (interval_append leafTestAt2496 16 20 24
  (interval_append leafTestAt2496 16 18 20
  (interval_append leafTestAt2496 16 17 18
  leafTestAt2496_block_16
  leafTestAt2496_block_17)
  (interval_append leafTestAt2496 18 19 20
  leafTestAt2496_block_18
  leafTestAt2496_block_19))
  (interval_append leafTestAt2496 20 22 24
  (interval_append leafTestAt2496 20 21 22
  leafTestAt2496_block_20
  leafTestAt2496_block_21)
  (interval_append leafTestAt2496 22 23 24
  leafTestAt2496_block_22
  leafTestAt2496_block_23)))
  (interval_append leafTestAt2496 24 28 32
  (interval_append leafTestAt2496 24 26 28
  (interval_append leafTestAt2496 24 25 26
  leafTestAt2496_block_24
  leafTestAt2496_block_25)
  (interval_append leafTestAt2496 26 27 28
  leafTestAt2496_block_26
  leafTestAt2496_block_27))
  (interval_append leafTestAt2496 28 30 32
  (interval_append leafTestAt2496 28 29 30
  leafTestAt2496_block_28
  leafTestAt2496_block_29)
  (interval_append leafTestAt2496 30 31 32
  leafTestAt2496_block_30
  leafTestAt2496_block_31)))))
cert_leafInterval 2496 2528
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
cert_leafTestAt 2528
cert_leafTestAt_block_2 2528 0 1
cert_leafTestAt_block_2 2528 1 2
cert_leafTestAt_block_2 2528 2 3
cert_leafTestAt_block_2 2528 3 4
cert_leafTestAt_block_2 2528 4 5
cert_leafTestAt_block_2 2528 5 6
cert_leafTestAt_block_2 2528 6 7
cert_leafTestAt_block_2 2528 7 8
cert_leafTestAt_block_2 2528 8 9
cert_leafTestAt_block_2 2528 9 10
cert_leafTestAt_block_2 2528 10 11
cert_leafTestAt_block_2 2528 11 12
cert_leafTestAt_block_2 2528 12 13
cert_leafTestAt_block_2 2528 13 14
cert_leafTestAt_block_2 2528 14 15
cert_leafTestAt_block_2 2528 15 16
cert_leafTestAt_block_2 2528 16 17
cert_leafTestAt_block_2 2528 17 18
cert_leafTestAt_block_2 2528 18 19
cert_leafTestAt_block_2 2528 19 20
cert_leafTestAt_block_2 2528 20 21
cert_leafTestAt_block_2 2528 21 22
cert_leafTestAt_block_2 2528 22 23
cert_leafTestAt_block_2 2528 23 24
cert_leafTestAt_block_2 2528 24 25
cert_leafTestAt_block_2 2528 25 26
cert_leafTestAt_block_2 2528 26 27
cert_leafTestAt_block_2 2528 27 28
cert_leafTestAt_block_2 2528 28 29
cert_leafTestAt_block_2 2528 29 30
cert_leafTestAt_block_2 2528 30 31
cert_leafTestAt_block_2 2528 31 32
theorem leafTestAt2528_complete : Interval leafTestAt2528 0 32 :=
  (interval_append leafTestAt2528 0 16 32
  (interval_append leafTestAt2528 0 8 16
  (interval_append leafTestAt2528 0 4 8
  (interval_append leafTestAt2528 0 2 4
  (interval_append leafTestAt2528 0 1 2
  leafTestAt2528_block_0
  leafTestAt2528_block_1)
  (interval_append leafTestAt2528 2 3 4
  leafTestAt2528_block_2
  leafTestAt2528_block_3))
  (interval_append leafTestAt2528 4 6 8
  (interval_append leafTestAt2528 4 5 6
  leafTestAt2528_block_4
  leafTestAt2528_block_5)
  (interval_append leafTestAt2528 6 7 8
  leafTestAt2528_block_6
  leafTestAt2528_block_7)))
  (interval_append leafTestAt2528 8 12 16
  (interval_append leafTestAt2528 8 10 12
  (interval_append leafTestAt2528 8 9 10
  leafTestAt2528_block_8
  leafTestAt2528_block_9)
  (interval_append leafTestAt2528 10 11 12
  leafTestAt2528_block_10
  leafTestAt2528_block_11))
  (interval_append leafTestAt2528 12 14 16
  (interval_append leafTestAt2528 12 13 14
  leafTestAt2528_block_12
  leafTestAt2528_block_13)
  (interval_append leafTestAt2528 14 15 16
  leafTestAt2528_block_14
  leafTestAt2528_block_15))))
  (interval_append leafTestAt2528 16 24 32
  (interval_append leafTestAt2528 16 20 24
  (interval_append leafTestAt2528 16 18 20
  (interval_append leafTestAt2528 16 17 18
  leafTestAt2528_block_16
  leafTestAt2528_block_17)
  (interval_append leafTestAt2528 18 19 20
  leafTestAt2528_block_18
  leafTestAt2528_block_19))
  (interval_append leafTestAt2528 20 22 24
  (interval_append leafTestAt2528 20 21 22
  leafTestAt2528_block_20
  leafTestAt2528_block_21)
  (interval_append leafTestAt2528 22 23 24
  leafTestAt2528_block_22
  leafTestAt2528_block_23)))
  (interval_append leafTestAt2528 24 28 32
  (interval_append leafTestAt2528 24 26 28
  (interval_append leafTestAt2528 24 25 26
  leafTestAt2528_block_24
  leafTestAt2528_block_25)
  (interval_append leafTestAt2528 26 27 28
  leafTestAt2528_block_26
  leafTestAt2528_block_27))
  (interval_append leafTestAt2528 28 30 32
  (interval_append leafTestAt2528 28 29 30
  leafTestAt2528_block_28
  leafTestAt2528_block_29)
  (interval_append leafTestAt2528 30 31 32
  leafTestAt2528_block_30
  leafTestAt2528_block_31)))))
cert_leafInterval 2528 2560
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end
