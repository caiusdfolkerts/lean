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
cert_leafTestAt 1024
cert_leafTestAt_block_2 1024 0 1
cert_leafTestAt_block_2 1024 1 2
cert_leafTestAt_block_2 1024 2 3
cert_leafTestAt_block_2 1024 3 4
cert_leafTestAt_block_2 1024 4 5
cert_leafTestAt_block_2 1024 5 6
cert_leafTestAt_block_2 1024 6 7
cert_leafTestAt_block_2 1024 7 8
cert_leafTestAt_block_2 1024 8 9
cert_leafTestAt_block_2 1024 9 10
cert_leafTestAt_block_2 1024 10 11
cert_leafTestAt_block_2 1024 11 12
cert_leafTestAt_block_2 1024 12 13
cert_leafTestAt_block_2 1024 13 14
cert_leafTestAt_block_2 1024 14 15
cert_leafTestAt_block_2 1024 15 16
cert_leafTestAt_block_2 1024 16 17
cert_leafTestAt_block_2 1024 17 18
cert_leafTestAt_block_2 1024 18 19
cert_leafTestAt_block_2 1024 19 20
cert_leafTestAt_block_2 1024 20 21
cert_leafTestAt_block_2 1024 21 22
cert_leafTestAt_block_2 1024 22 23
cert_leafTestAt_block_2 1024 23 24
cert_leafTestAt_block_2 1024 24 25
cert_leafTestAt_block_2 1024 25 26
cert_leafTestAt_block_2 1024 26 27
cert_leafTestAt_block_2 1024 27 28
cert_leafTestAt_block_2 1024 28 29
cert_leafTestAt_block_2 1024 29 30
cert_leafTestAt_block_2 1024 30 31
cert_leafTestAt_block_2 1024 31 32
theorem leafTestAt1024_complete : Interval leafTestAt1024 0 32 :=
  (interval_append leafTestAt1024 0 16 32
  (interval_append leafTestAt1024 0 8 16
  (interval_append leafTestAt1024 0 4 8
  (interval_append leafTestAt1024 0 2 4
  (interval_append leafTestAt1024 0 1 2
  leafTestAt1024_block_0
  leafTestAt1024_block_1)
  (interval_append leafTestAt1024 2 3 4
  leafTestAt1024_block_2
  leafTestAt1024_block_3))
  (interval_append leafTestAt1024 4 6 8
  (interval_append leafTestAt1024 4 5 6
  leafTestAt1024_block_4
  leafTestAt1024_block_5)
  (interval_append leafTestAt1024 6 7 8
  leafTestAt1024_block_6
  leafTestAt1024_block_7)))
  (interval_append leafTestAt1024 8 12 16
  (interval_append leafTestAt1024 8 10 12
  (interval_append leafTestAt1024 8 9 10
  leafTestAt1024_block_8
  leafTestAt1024_block_9)
  (interval_append leafTestAt1024 10 11 12
  leafTestAt1024_block_10
  leafTestAt1024_block_11))
  (interval_append leafTestAt1024 12 14 16
  (interval_append leafTestAt1024 12 13 14
  leafTestAt1024_block_12
  leafTestAt1024_block_13)
  (interval_append leafTestAt1024 14 15 16
  leafTestAt1024_block_14
  leafTestAt1024_block_15))))
  (interval_append leafTestAt1024 16 24 32
  (interval_append leafTestAt1024 16 20 24
  (interval_append leafTestAt1024 16 18 20
  (interval_append leafTestAt1024 16 17 18
  leafTestAt1024_block_16
  leafTestAt1024_block_17)
  (interval_append leafTestAt1024 18 19 20
  leafTestAt1024_block_18
  leafTestAt1024_block_19))
  (interval_append leafTestAt1024 20 22 24
  (interval_append leafTestAt1024 20 21 22
  leafTestAt1024_block_20
  leafTestAt1024_block_21)
  (interval_append leafTestAt1024 22 23 24
  leafTestAt1024_block_22
  leafTestAt1024_block_23)))
  (interval_append leafTestAt1024 24 28 32
  (interval_append leafTestAt1024 24 26 28
  (interval_append leafTestAt1024 24 25 26
  leafTestAt1024_block_24
  leafTestAt1024_block_25)
  (interval_append leafTestAt1024 26 27 28
  leafTestAt1024_block_26
  leafTestAt1024_block_27))
  (interval_append leafTestAt1024 28 30 32
  (interval_append leafTestAt1024 28 29 30
  leafTestAt1024_block_28
  leafTestAt1024_block_29)
  (interval_append leafTestAt1024 30 31 32
  leafTestAt1024_block_30
  leafTestAt1024_block_31)))))
cert_leafInterval 1024 1056
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
cert_leafTestAt 1056
cert_leafTestAt_block_2 1056 0 1
cert_leafTestAt_block_2 1056 1 2
cert_leafTestAt_block_2 1056 2 3
cert_leafTestAt_block_2 1056 3 4
cert_leafTestAt_block_2 1056 4 5
cert_leafTestAt_block_2 1056 5 6
cert_leafTestAt_block_2 1056 6 7
cert_leafTestAt_block_2 1056 7 8
cert_leafTestAt_block_2 1056 8 9
cert_leafTestAt_block_2 1056 9 10
cert_leafTestAt_block_2 1056 10 11
cert_leafTestAt_block_2 1056 11 12
cert_leafTestAt_block_2 1056 12 13
cert_leafTestAt_block_2 1056 13 14
cert_leafTestAt_block_2 1056 14 15
cert_leafTestAt_block_2 1056 15 16
cert_leafTestAt_block_2 1056 16 17
cert_leafTestAt_block_2 1056 17 18
cert_leafTestAt_block_2 1056 18 19
cert_leafTestAt_block_2 1056 19 20
cert_leafTestAt_block_2 1056 20 21
cert_leafTestAt_block_2 1056 21 22
cert_leafTestAt_block_2 1056 22 23
cert_leafTestAt_block_2 1056 23 24
cert_leafTestAt_block_2 1056 24 25
cert_leafTestAt_block_2 1056 25 26
cert_leafTestAt_block_2 1056 26 27
cert_leafTestAt_block_2 1056 27 28
cert_leafTestAt_block_2 1056 28 29
cert_leafTestAt_block_2 1056 29 30
cert_leafTestAt_block_2 1056 30 31
cert_leafTestAt_block_2 1056 31 32
theorem leafTestAt1056_complete : Interval leafTestAt1056 0 32 :=
  (interval_append leafTestAt1056 0 16 32
  (interval_append leafTestAt1056 0 8 16
  (interval_append leafTestAt1056 0 4 8
  (interval_append leafTestAt1056 0 2 4
  (interval_append leafTestAt1056 0 1 2
  leafTestAt1056_block_0
  leafTestAt1056_block_1)
  (interval_append leafTestAt1056 2 3 4
  leafTestAt1056_block_2
  leafTestAt1056_block_3))
  (interval_append leafTestAt1056 4 6 8
  (interval_append leafTestAt1056 4 5 6
  leafTestAt1056_block_4
  leafTestAt1056_block_5)
  (interval_append leafTestAt1056 6 7 8
  leafTestAt1056_block_6
  leafTestAt1056_block_7)))
  (interval_append leafTestAt1056 8 12 16
  (interval_append leafTestAt1056 8 10 12
  (interval_append leafTestAt1056 8 9 10
  leafTestAt1056_block_8
  leafTestAt1056_block_9)
  (interval_append leafTestAt1056 10 11 12
  leafTestAt1056_block_10
  leafTestAt1056_block_11))
  (interval_append leafTestAt1056 12 14 16
  (interval_append leafTestAt1056 12 13 14
  leafTestAt1056_block_12
  leafTestAt1056_block_13)
  (interval_append leafTestAt1056 14 15 16
  leafTestAt1056_block_14
  leafTestAt1056_block_15))))
  (interval_append leafTestAt1056 16 24 32
  (interval_append leafTestAt1056 16 20 24
  (interval_append leafTestAt1056 16 18 20
  (interval_append leafTestAt1056 16 17 18
  leafTestAt1056_block_16
  leafTestAt1056_block_17)
  (interval_append leafTestAt1056 18 19 20
  leafTestAt1056_block_18
  leafTestAt1056_block_19))
  (interval_append leafTestAt1056 20 22 24
  (interval_append leafTestAt1056 20 21 22
  leafTestAt1056_block_20
  leafTestAt1056_block_21)
  (interval_append leafTestAt1056 22 23 24
  leafTestAt1056_block_22
  leafTestAt1056_block_23)))
  (interval_append leafTestAt1056 24 28 32
  (interval_append leafTestAt1056 24 26 28
  (interval_append leafTestAt1056 24 25 26
  leafTestAt1056_block_24
  leafTestAt1056_block_25)
  (interval_append leafTestAt1056 26 27 28
  leafTestAt1056_block_26
  leafTestAt1056_block_27))
  (interval_append leafTestAt1056 28 30 32
  (interval_append leafTestAt1056 28 29 30
  leafTestAt1056_block_28
  leafTestAt1056_block_29)
  (interval_append leafTestAt1056 30 31 32
  leafTestAt1056_block_30
  leafTestAt1056_block_31)))))
cert_leafInterval 1056 1088
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
cert_leafTestAt 1088
cert_leafTestAt_block_2 1088 0 1
cert_leafTestAt_block_2 1088 1 2
cert_leafTestAt_block_2 1088 2 3
cert_leafTestAt_block_2 1088 3 4
cert_leafTestAt_block_2 1088 4 5
cert_leafTestAt_block_2 1088 5 6
cert_leafTestAt_block_2 1088 6 7
cert_leafTestAt_block_2 1088 7 8
cert_leafTestAt_block_2 1088 8 9
cert_leafTestAt_block_2 1088 9 10
cert_leafTestAt_block_2 1088 10 11
cert_leafTestAt_block_2 1088 11 12
cert_leafTestAt_block_2 1088 12 13
cert_leafTestAt_block_2 1088 13 14
cert_leafTestAt_block_2 1088 14 15
cert_leafTestAt_block_2 1088 15 16
cert_leafTestAt_block_2 1088 16 17
cert_leafTestAt_block_2 1088 17 18
cert_leafTestAt_block_2 1088 18 19
cert_leafTestAt_block_2 1088 19 20
cert_leafTestAt_block_2 1088 20 21
cert_leafTestAt_block_2 1088 21 22
cert_leafTestAt_block_2 1088 22 23
cert_leafTestAt_block_2 1088 23 24
cert_leafTestAt_block_2 1088 24 25
cert_leafTestAt_block_2 1088 25 26
cert_leafTestAt_block_2 1088 26 27
cert_leafTestAt_block_2 1088 27 28
cert_leafTestAt_block_2 1088 28 29
cert_leafTestAt_block_2 1088 29 30
cert_leafTestAt_block_2 1088 30 31
cert_leafTestAt_block_2 1088 31 32
theorem leafTestAt1088_complete : Interval leafTestAt1088 0 32 :=
  (interval_append leafTestAt1088 0 16 32
  (interval_append leafTestAt1088 0 8 16
  (interval_append leafTestAt1088 0 4 8
  (interval_append leafTestAt1088 0 2 4
  (interval_append leafTestAt1088 0 1 2
  leafTestAt1088_block_0
  leafTestAt1088_block_1)
  (interval_append leafTestAt1088 2 3 4
  leafTestAt1088_block_2
  leafTestAt1088_block_3))
  (interval_append leafTestAt1088 4 6 8
  (interval_append leafTestAt1088 4 5 6
  leafTestAt1088_block_4
  leafTestAt1088_block_5)
  (interval_append leafTestAt1088 6 7 8
  leafTestAt1088_block_6
  leafTestAt1088_block_7)))
  (interval_append leafTestAt1088 8 12 16
  (interval_append leafTestAt1088 8 10 12
  (interval_append leafTestAt1088 8 9 10
  leafTestAt1088_block_8
  leafTestAt1088_block_9)
  (interval_append leafTestAt1088 10 11 12
  leafTestAt1088_block_10
  leafTestAt1088_block_11))
  (interval_append leafTestAt1088 12 14 16
  (interval_append leafTestAt1088 12 13 14
  leafTestAt1088_block_12
  leafTestAt1088_block_13)
  (interval_append leafTestAt1088 14 15 16
  leafTestAt1088_block_14
  leafTestAt1088_block_15))))
  (interval_append leafTestAt1088 16 24 32
  (interval_append leafTestAt1088 16 20 24
  (interval_append leafTestAt1088 16 18 20
  (interval_append leafTestAt1088 16 17 18
  leafTestAt1088_block_16
  leafTestAt1088_block_17)
  (interval_append leafTestAt1088 18 19 20
  leafTestAt1088_block_18
  leafTestAt1088_block_19))
  (interval_append leafTestAt1088 20 22 24
  (interval_append leafTestAt1088 20 21 22
  leafTestAt1088_block_20
  leafTestAt1088_block_21)
  (interval_append leafTestAt1088 22 23 24
  leafTestAt1088_block_22
  leafTestAt1088_block_23)))
  (interval_append leafTestAt1088 24 28 32
  (interval_append leafTestAt1088 24 26 28
  (interval_append leafTestAt1088 24 25 26
  leafTestAt1088_block_24
  leafTestAt1088_block_25)
  (interval_append leafTestAt1088 26 27 28
  leafTestAt1088_block_26
  leafTestAt1088_block_27))
  (interval_append leafTestAt1088 28 30 32
  (interval_append leafTestAt1088 28 29 30
  leafTestAt1088_block_28
  leafTestAt1088_block_29)
  (interval_append leafTestAt1088 30 31 32
  leafTestAt1088_block_30
  leafTestAt1088_block_31)))))
cert_leafInterval 1088 1120
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
cert_leafTestAt 1120
cert_leafTestAt_block_2 1120 0 1
cert_leafTestAt_block_2 1120 1 2
cert_leafTestAt_block_2 1120 2 3
cert_leafTestAt_block_2 1120 3 4
cert_leafTestAt_block_2 1120 4 5
cert_leafTestAt_block_2 1120 5 6
cert_leafTestAt_block_2 1120 6 7
cert_leafTestAt_block_2 1120 7 8
cert_leafTestAt_block_2 1120 8 9
cert_leafTestAt_block_2 1120 9 10
cert_leafTestAt_block_2 1120 10 11
cert_leafTestAt_block_2 1120 11 12
cert_leafTestAt_block_2 1120 12 13
cert_leafTestAt_block_2 1120 13 14
cert_leafTestAt_block_2 1120 14 15
cert_leafTestAt_block_2 1120 15 16
cert_leafTestAt_block_2 1120 16 17
cert_leafTestAt_block_2 1120 17 18
cert_leafTestAt_block_2 1120 18 19
cert_leafTestAt_block_2 1120 19 20
cert_leafTestAt_block_2 1120 20 21
cert_leafTestAt_block_2 1120 21 22
cert_leafTestAt_block_2 1120 22 23
cert_leafTestAt_block_2 1120 23 24
cert_leafTestAt_block_2 1120 24 25
cert_leafTestAt_block_2 1120 25 26
cert_leafTestAt_block_2 1120 26 27
cert_leafTestAt_block_2 1120 27 28
cert_leafTestAt_block_2 1120 28 29
cert_leafTestAt_block_2 1120 29 30
cert_leafTestAt_block_2 1120 30 31
cert_leafTestAt_block_2 1120 31 32
theorem leafTestAt1120_complete : Interval leafTestAt1120 0 32 :=
  (interval_append leafTestAt1120 0 16 32
  (interval_append leafTestAt1120 0 8 16
  (interval_append leafTestAt1120 0 4 8
  (interval_append leafTestAt1120 0 2 4
  (interval_append leafTestAt1120 0 1 2
  leafTestAt1120_block_0
  leafTestAt1120_block_1)
  (interval_append leafTestAt1120 2 3 4
  leafTestAt1120_block_2
  leafTestAt1120_block_3))
  (interval_append leafTestAt1120 4 6 8
  (interval_append leafTestAt1120 4 5 6
  leafTestAt1120_block_4
  leafTestAt1120_block_5)
  (interval_append leafTestAt1120 6 7 8
  leafTestAt1120_block_6
  leafTestAt1120_block_7)))
  (interval_append leafTestAt1120 8 12 16
  (interval_append leafTestAt1120 8 10 12
  (interval_append leafTestAt1120 8 9 10
  leafTestAt1120_block_8
  leafTestAt1120_block_9)
  (interval_append leafTestAt1120 10 11 12
  leafTestAt1120_block_10
  leafTestAt1120_block_11))
  (interval_append leafTestAt1120 12 14 16
  (interval_append leafTestAt1120 12 13 14
  leafTestAt1120_block_12
  leafTestAt1120_block_13)
  (interval_append leafTestAt1120 14 15 16
  leafTestAt1120_block_14
  leafTestAt1120_block_15))))
  (interval_append leafTestAt1120 16 24 32
  (interval_append leafTestAt1120 16 20 24
  (interval_append leafTestAt1120 16 18 20
  (interval_append leafTestAt1120 16 17 18
  leafTestAt1120_block_16
  leafTestAt1120_block_17)
  (interval_append leafTestAt1120 18 19 20
  leafTestAt1120_block_18
  leafTestAt1120_block_19))
  (interval_append leafTestAt1120 20 22 24
  (interval_append leafTestAt1120 20 21 22
  leafTestAt1120_block_20
  leafTestAt1120_block_21)
  (interval_append leafTestAt1120 22 23 24
  leafTestAt1120_block_22
  leafTestAt1120_block_23)))
  (interval_append leafTestAt1120 24 28 32
  (interval_append leafTestAt1120 24 26 28
  (interval_append leafTestAt1120 24 25 26
  leafTestAt1120_block_24
  leafTestAt1120_block_25)
  (interval_append leafTestAt1120 26 27 28
  leafTestAt1120_block_26
  leafTestAt1120_block_27))
  (interval_append leafTestAt1120 28 30 32
  (interval_append leafTestAt1120 28 29 30
  leafTestAt1120_block_28
  leafTestAt1120_block_29)
  (interval_append leafTestAt1120 30 31 32
  leafTestAt1120_block_30
  leafTestAt1120_block_31)))))
cert_leafInterval 1120 1152
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
cert_leafTestAt 1152
cert_leafTestAt_block_2 1152 0 1
cert_leafTestAt_block_2 1152 1 2
cert_leafTestAt_block_2 1152 2 3
cert_leafTestAt_block_2 1152 3 4
cert_leafTestAt_block_2 1152 4 5
cert_leafTestAt_block_2 1152 5 6
cert_leafTestAt_block_2 1152 6 7
cert_leafTestAt_block_2 1152 7 8
cert_leafTestAt_block_2 1152 8 9
cert_leafTestAt_block_2 1152 9 10
cert_leafTestAt_block_2 1152 10 11
cert_leafTestAt_block_2 1152 11 12
cert_leafTestAt_block_2 1152 12 13
cert_leafTestAt_block_2 1152 13 14
cert_leafTestAt_block_2 1152 14 15
cert_leafTestAt_block_2 1152 15 16
cert_leafTestAt_block_2 1152 16 17
cert_leafTestAt_block_2 1152 17 18
cert_leafTestAt_block_2 1152 18 19
cert_leafTestAt_block_2 1152 19 20
cert_leafTestAt_block_2 1152 20 21
cert_leafTestAt_block_2 1152 21 22
cert_leafTestAt_block_2 1152 22 23
cert_leafTestAt_block_2 1152 23 24
cert_leafTestAt_block_2 1152 24 25
cert_leafTestAt_block_2 1152 25 26
cert_leafTestAt_block_2 1152 26 27
cert_leafTestAt_block_2 1152 27 28
cert_leafTestAt_block_2 1152 28 29
cert_leafTestAt_block_2 1152 29 30
cert_leafTestAt_block_2 1152 30 31
cert_leafTestAt_block_2 1152 31 32
theorem leafTestAt1152_complete : Interval leafTestAt1152 0 32 :=
  (interval_append leafTestAt1152 0 16 32
  (interval_append leafTestAt1152 0 8 16
  (interval_append leafTestAt1152 0 4 8
  (interval_append leafTestAt1152 0 2 4
  (interval_append leafTestAt1152 0 1 2
  leafTestAt1152_block_0
  leafTestAt1152_block_1)
  (interval_append leafTestAt1152 2 3 4
  leafTestAt1152_block_2
  leafTestAt1152_block_3))
  (interval_append leafTestAt1152 4 6 8
  (interval_append leafTestAt1152 4 5 6
  leafTestAt1152_block_4
  leafTestAt1152_block_5)
  (interval_append leafTestAt1152 6 7 8
  leafTestAt1152_block_6
  leafTestAt1152_block_7)))
  (interval_append leafTestAt1152 8 12 16
  (interval_append leafTestAt1152 8 10 12
  (interval_append leafTestAt1152 8 9 10
  leafTestAt1152_block_8
  leafTestAt1152_block_9)
  (interval_append leafTestAt1152 10 11 12
  leafTestAt1152_block_10
  leafTestAt1152_block_11))
  (interval_append leafTestAt1152 12 14 16
  (interval_append leafTestAt1152 12 13 14
  leafTestAt1152_block_12
  leafTestAt1152_block_13)
  (interval_append leafTestAt1152 14 15 16
  leafTestAt1152_block_14
  leafTestAt1152_block_15))))
  (interval_append leafTestAt1152 16 24 32
  (interval_append leafTestAt1152 16 20 24
  (interval_append leafTestAt1152 16 18 20
  (interval_append leafTestAt1152 16 17 18
  leafTestAt1152_block_16
  leafTestAt1152_block_17)
  (interval_append leafTestAt1152 18 19 20
  leafTestAt1152_block_18
  leafTestAt1152_block_19))
  (interval_append leafTestAt1152 20 22 24
  (interval_append leafTestAt1152 20 21 22
  leafTestAt1152_block_20
  leafTestAt1152_block_21)
  (interval_append leafTestAt1152 22 23 24
  leafTestAt1152_block_22
  leafTestAt1152_block_23)))
  (interval_append leafTestAt1152 24 28 32
  (interval_append leafTestAt1152 24 26 28
  (interval_append leafTestAt1152 24 25 26
  leafTestAt1152_block_24
  leafTestAt1152_block_25)
  (interval_append leafTestAt1152 26 27 28
  leafTestAt1152_block_26
  leafTestAt1152_block_27))
  (interval_append leafTestAt1152 28 30 32
  (interval_append leafTestAt1152 28 29 30
  leafTestAt1152_block_28
  leafTestAt1152_block_29)
  (interval_append leafTestAt1152 30 31 32
  leafTestAt1152_block_30
  leafTestAt1152_block_31)))))
cert_leafInterval 1152 1184
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
cert_leafTestAt 1184
cert_leafTestAt_block_2 1184 0 1
cert_leafTestAt_block_2 1184 1 2
cert_leafTestAt_block_2 1184 2 3
cert_leafTestAt_block_2 1184 3 4
cert_leafTestAt_block_2 1184 4 5
cert_leafTestAt_block_2 1184 5 6
cert_leafTestAt_block_2 1184 6 7
cert_leafTestAt_block_2 1184 7 8
cert_leafTestAt_block_2 1184 8 9
cert_leafTestAt_block_2 1184 9 10
cert_leafTestAt_block_2 1184 10 11
cert_leafTestAt_block_2 1184 11 12
cert_leafTestAt_block_2 1184 12 13
cert_leafTestAt_block_2 1184 13 14
cert_leafTestAt_block_2 1184 14 15
cert_leafTestAt_block_2 1184 15 16
cert_leafTestAt_block_2 1184 16 17
cert_leafTestAt_block_2 1184 17 18
cert_leafTestAt_block_2 1184 18 19
cert_leafTestAt_block_2 1184 19 20
cert_leafTestAt_block_2 1184 20 21
cert_leafTestAt_block_2 1184 21 22
cert_leafTestAt_block_2 1184 22 23
cert_leafTestAt_block_2 1184 23 24
cert_leafTestAt_block_2 1184 24 25
cert_leafTestAt_block_2 1184 25 26
cert_leafTestAt_block_2 1184 26 27
cert_leafTestAt_block_2 1184 27 28
cert_leafTestAt_block_2 1184 28 29
cert_leafTestAt_block_2 1184 29 30
cert_leafTestAt_block_2 1184 30 31
cert_leafTestAt_block_2 1184 31 32
theorem leafTestAt1184_complete : Interval leafTestAt1184 0 32 :=
  (interval_append leafTestAt1184 0 16 32
  (interval_append leafTestAt1184 0 8 16
  (interval_append leafTestAt1184 0 4 8
  (interval_append leafTestAt1184 0 2 4
  (interval_append leafTestAt1184 0 1 2
  leafTestAt1184_block_0
  leafTestAt1184_block_1)
  (interval_append leafTestAt1184 2 3 4
  leafTestAt1184_block_2
  leafTestAt1184_block_3))
  (interval_append leafTestAt1184 4 6 8
  (interval_append leafTestAt1184 4 5 6
  leafTestAt1184_block_4
  leafTestAt1184_block_5)
  (interval_append leafTestAt1184 6 7 8
  leafTestAt1184_block_6
  leafTestAt1184_block_7)))
  (interval_append leafTestAt1184 8 12 16
  (interval_append leafTestAt1184 8 10 12
  (interval_append leafTestAt1184 8 9 10
  leafTestAt1184_block_8
  leafTestAt1184_block_9)
  (interval_append leafTestAt1184 10 11 12
  leafTestAt1184_block_10
  leafTestAt1184_block_11))
  (interval_append leafTestAt1184 12 14 16
  (interval_append leafTestAt1184 12 13 14
  leafTestAt1184_block_12
  leafTestAt1184_block_13)
  (interval_append leafTestAt1184 14 15 16
  leafTestAt1184_block_14
  leafTestAt1184_block_15))))
  (interval_append leafTestAt1184 16 24 32
  (interval_append leafTestAt1184 16 20 24
  (interval_append leafTestAt1184 16 18 20
  (interval_append leafTestAt1184 16 17 18
  leafTestAt1184_block_16
  leafTestAt1184_block_17)
  (interval_append leafTestAt1184 18 19 20
  leafTestAt1184_block_18
  leafTestAt1184_block_19))
  (interval_append leafTestAt1184 20 22 24
  (interval_append leafTestAt1184 20 21 22
  leafTestAt1184_block_20
  leafTestAt1184_block_21)
  (interval_append leafTestAt1184 22 23 24
  leafTestAt1184_block_22
  leafTestAt1184_block_23)))
  (interval_append leafTestAt1184 24 28 32
  (interval_append leafTestAt1184 24 26 28
  (interval_append leafTestAt1184 24 25 26
  leafTestAt1184_block_24
  leafTestAt1184_block_25)
  (interval_append leafTestAt1184 26 27 28
  leafTestAt1184_block_26
  leafTestAt1184_block_27))
  (interval_append leafTestAt1184 28 30 32
  (interval_append leafTestAt1184 28 29 30
  leafTestAt1184_block_28
  leafTestAt1184_block_29)
  (interval_append leafTestAt1184 30 31 32
  leafTestAt1184_block_30
  leafTestAt1184_block_31)))))
cert_leafInterval 1184 1216
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
cert_leafTestAt 1216
cert_leafTestAt_block_2 1216 0 1
cert_leafTestAt_block_2 1216 1 2
cert_leafTestAt_block_2 1216 2 3
cert_leafTestAt_block_2 1216 3 4
cert_leafTestAt_block_2 1216 4 5
cert_leafTestAt_block_2 1216 5 6
cert_leafTestAt_block_2 1216 6 7
cert_leafTestAt_block_2 1216 7 8
cert_leafTestAt_block_2 1216 8 9
cert_leafTestAt_block_2 1216 9 10
cert_leafTestAt_block_2 1216 10 11
cert_leafTestAt_block_2 1216 11 12
cert_leafTestAt_block_2 1216 12 13
cert_leafTestAt_block_2 1216 13 14
cert_leafTestAt_block_2 1216 14 15
cert_leafTestAt_block_2 1216 15 16
cert_leafTestAt_block_2 1216 16 17
cert_leafTestAt_block_2 1216 17 18
cert_leafTestAt_block_2 1216 18 19
cert_leafTestAt_block_2 1216 19 20
cert_leafTestAt_block_2 1216 20 21
cert_leafTestAt_block_2 1216 21 22
cert_leafTestAt_block_2 1216 22 23
cert_leafTestAt_block_2 1216 23 24
cert_leafTestAt_block_2 1216 24 25
cert_leafTestAt_block_2 1216 25 26
cert_leafTestAt_block_2 1216 26 27
cert_leafTestAt_block_2 1216 27 28
cert_leafTestAt_block_2 1216 28 29
cert_leafTestAt_block_2 1216 29 30
cert_leafTestAt_block_2 1216 30 31
cert_leafTestAt_block_2 1216 31 32
theorem leafTestAt1216_complete : Interval leafTestAt1216 0 32 :=
  (interval_append leafTestAt1216 0 16 32
  (interval_append leafTestAt1216 0 8 16
  (interval_append leafTestAt1216 0 4 8
  (interval_append leafTestAt1216 0 2 4
  (interval_append leafTestAt1216 0 1 2
  leafTestAt1216_block_0
  leafTestAt1216_block_1)
  (interval_append leafTestAt1216 2 3 4
  leafTestAt1216_block_2
  leafTestAt1216_block_3))
  (interval_append leafTestAt1216 4 6 8
  (interval_append leafTestAt1216 4 5 6
  leafTestAt1216_block_4
  leafTestAt1216_block_5)
  (interval_append leafTestAt1216 6 7 8
  leafTestAt1216_block_6
  leafTestAt1216_block_7)))
  (interval_append leafTestAt1216 8 12 16
  (interval_append leafTestAt1216 8 10 12
  (interval_append leafTestAt1216 8 9 10
  leafTestAt1216_block_8
  leafTestAt1216_block_9)
  (interval_append leafTestAt1216 10 11 12
  leafTestAt1216_block_10
  leafTestAt1216_block_11))
  (interval_append leafTestAt1216 12 14 16
  (interval_append leafTestAt1216 12 13 14
  leafTestAt1216_block_12
  leafTestAt1216_block_13)
  (interval_append leafTestAt1216 14 15 16
  leafTestAt1216_block_14
  leafTestAt1216_block_15))))
  (interval_append leafTestAt1216 16 24 32
  (interval_append leafTestAt1216 16 20 24
  (interval_append leafTestAt1216 16 18 20
  (interval_append leafTestAt1216 16 17 18
  leafTestAt1216_block_16
  leafTestAt1216_block_17)
  (interval_append leafTestAt1216 18 19 20
  leafTestAt1216_block_18
  leafTestAt1216_block_19))
  (interval_append leafTestAt1216 20 22 24
  (interval_append leafTestAt1216 20 21 22
  leafTestAt1216_block_20
  leafTestAt1216_block_21)
  (interval_append leafTestAt1216 22 23 24
  leafTestAt1216_block_22
  leafTestAt1216_block_23)))
  (interval_append leafTestAt1216 24 28 32
  (interval_append leafTestAt1216 24 26 28
  (interval_append leafTestAt1216 24 25 26
  leafTestAt1216_block_24
  leafTestAt1216_block_25)
  (interval_append leafTestAt1216 26 27 28
  leafTestAt1216_block_26
  leafTestAt1216_block_27))
  (interval_append leafTestAt1216 28 30 32
  (interval_append leafTestAt1216 28 29 30
  leafTestAt1216_block_28
  leafTestAt1216_block_29)
  (interval_append leafTestAt1216 30 31 32
  leafTestAt1216_block_30
  leafTestAt1216_block_31)))))
cert_leafInterval 1216 1248
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
cert_leafTestAt 1248
cert_leafTestAt_block_2 1248 0 1
cert_leafTestAt_block_2 1248 1 2
cert_leafTestAt_block_2 1248 2 3
cert_leafTestAt_block_2 1248 3 4
cert_leafTestAt_block_2 1248 4 5
cert_leafTestAt_block_2 1248 5 6
cert_leafTestAt_block_2 1248 6 7
cert_leafTestAt_block_2 1248 7 8
cert_leafTestAt_block_2 1248 8 9
cert_leafTestAt_block_2 1248 9 10
cert_leafTestAt_block_2 1248 10 11
cert_leafTestAt_block_2 1248 11 12
cert_leafTestAt_block_2 1248 12 13
cert_leafTestAt_block_2 1248 13 14
cert_leafTestAt_block_2 1248 14 15
cert_leafTestAt_block_2 1248 15 16
cert_leafTestAt_block_2 1248 16 17
cert_leafTestAt_block_2 1248 17 18
cert_leafTestAt_block_2 1248 18 19
cert_leafTestAt_block_2 1248 19 20
cert_leafTestAt_block_2 1248 20 21
cert_leafTestAt_block_2 1248 21 22
cert_leafTestAt_block_2 1248 22 23
cert_leafTestAt_block_2 1248 23 24
cert_leafTestAt_block_2 1248 24 25
cert_leafTestAt_block_2 1248 25 26
cert_leafTestAt_block_2 1248 26 27
cert_leafTestAt_block_2 1248 27 28
cert_leafTestAt_block_2 1248 28 29
cert_leafTestAt_block_2 1248 29 30
cert_leafTestAt_block_2 1248 30 31
cert_leafTestAt_block_2 1248 31 32
theorem leafTestAt1248_complete : Interval leafTestAt1248 0 32 :=
  (interval_append leafTestAt1248 0 16 32
  (interval_append leafTestAt1248 0 8 16
  (interval_append leafTestAt1248 0 4 8
  (interval_append leafTestAt1248 0 2 4
  (interval_append leafTestAt1248 0 1 2
  leafTestAt1248_block_0
  leafTestAt1248_block_1)
  (interval_append leafTestAt1248 2 3 4
  leafTestAt1248_block_2
  leafTestAt1248_block_3))
  (interval_append leafTestAt1248 4 6 8
  (interval_append leafTestAt1248 4 5 6
  leafTestAt1248_block_4
  leafTestAt1248_block_5)
  (interval_append leafTestAt1248 6 7 8
  leafTestAt1248_block_6
  leafTestAt1248_block_7)))
  (interval_append leafTestAt1248 8 12 16
  (interval_append leafTestAt1248 8 10 12
  (interval_append leafTestAt1248 8 9 10
  leafTestAt1248_block_8
  leafTestAt1248_block_9)
  (interval_append leafTestAt1248 10 11 12
  leafTestAt1248_block_10
  leafTestAt1248_block_11))
  (interval_append leafTestAt1248 12 14 16
  (interval_append leafTestAt1248 12 13 14
  leafTestAt1248_block_12
  leafTestAt1248_block_13)
  (interval_append leafTestAt1248 14 15 16
  leafTestAt1248_block_14
  leafTestAt1248_block_15))))
  (interval_append leafTestAt1248 16 24 32
  (interval_append leafTestAt1248 16 20 24
  (interval_append leafTestAt1248 16 18 20
  (interval_append leafTestAt1248 16 17 18
  leafTestAt1248_block_16
  leafTestAt1248_block_17)
  (interval_append leafTestAt1248 18 19 20
  leafTestAt1248_block_18
  leafTestAt1248_block_19))
  (interval_append leafTestAt1248 20 22 24
  (interval_append leafTestAt1248 20 21 22
  leafTestAt1248_block_20
  leafTestAt1248_block_21)
  (interval_append leafTestAt1248 22 23 24
  leafTestAt1248_block_22
  leafTestAt1248_block_23)))
  (interval_append leafTestAt1248 24 28 32
  (interval_append leafTestAt1248 24 26 28
  (interval_append leafTestAt1248 24 25 26
  leafTestAt1248_block_24
  leafTestAt1248_block_25)
  (interval_append leafTestAt1248 26 27 28
  leafTestAt1248_block_26
  leafTestAt1248_block_27))
  (interval_append leafTestAt1248 28 30 32
  (interval_append leafTestAt1248 28 29 30
  leafTestAt1248_block_28
  leafTestAt1248_block_29)
  (interval_append leafTestAt1248 30 31 32
  leafTestAt1248_block_30
  leafTestAt1248_block_31)))))
cert_leafInterval 1248 1280
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
cert_leafTestAt 1280
cert_leafTestAt_block_2 1280 0 1
cert_leafTestAt_block_2 1280 1 2
cert_leafTestAt_block_2 1280 2 3
cert_leafTestAt_block_2 1280 3 4
cert_leafTestAt_block_2 1280 4 5
cert_leafTestAt_block_2 1280 5 6
cert_leafTestAt_block_2 1280 6 7
cert_leafTestAt_block_2 1280 7 8
cert_leafTestAt_block_2 1280 8 9
cert_leafTestAt_block_2 1280 9 10
cert_leafTestAt_block_2 1280 10 11
cert_leafTestAt_block_2 1280 11 12
cert_leafTestAt_block_2 1280 12 13
cert_leafTestAt_block_2 1280 13 14
cert_leafTestAt_block_2 1280 14 15
cert_leafTestAt_block_2 1280 15 16
cert_leafTestAt_block_2 1280 16 17
cert_leafTestAt_block_2 1280 17 18
cert_leafTestAt_block_2 1280 18 19
cert_leafTestAt_block_2 1280 19 20
cert_leafTestAt_block_2 1280 20 21
cert_leafTestAt_block_2 1280 21 22
cert_leafTestAt_block_2 1280 22 23
cert_leafTestAt_block_2 1280 23 24
cert_leafTestAt_block_2 1280 24 25
cert_leafTestAt_block_2 1280 25 26
cert_leafTestAt_block_2 1280 26 27
cert_leafTestAt_block_2 1280 27 28
cert_leafTestAt_block_2 1280 28 29
cert_leafTestAt_block_2 1280 29 30
cert_leafTestAt_block_2 1280 30 31
cert_leafTestAt_block_2 1280 31 32
theorem leafTestAt1280_complete : Interval leafTestAt1280 0 32 :=
  (interval_append leafTestAt1280 0 16 32
  (interval_append leafTestAt1280 0 8 16
  (interval_append leafTestAt1280 0 4 8
  (interval_append leafTestAt1280 0 2 4
  (interval_append leafTestAt1280 0 1 2
  leafTestAt1280_block_0
  leafTestAt1280_block_1)
  (interval_append leafTestAt1280 2 3 4
  leafTestAt1280_block_2
  leafTestAt1280_block_3))
  (interval_append leafTestAt1280 4 6 8
  (interval_append leafTestAt1280 4 5 6
  leafTestAt1280_block_4
  leafTestAt1280_block_5)
  (interval_append leafTestAt1280 6 7 8
  leafTestAt1280_block_6
  leafTestAt1280_block_7)))
  (interval_append leafTestAt1280 8 12 16
  (interval_append leafTestAt1280 8 10 12
  (interval_append leafTestAt1280 8 9 10
  leafTestAt1280_block_8
  leafTestAt1280_block_9)
  (interval_append leafTestAt1280 10 11 12
  leafTestAt1280_block_10
  leafTestAt1280_block_11))
  (interval_append leafTestAt1280 12 14 16
  (interval_append leafTestAt1280 12 13 14
  leafTestAt1280_block_12
  leafTestAt1280_block_13)
  (interval_append leafTestAt1280 14 15 16
  leafTestAt1280_block_14
  leafTestAt1280_block_15))))
  (interval_append leafTestAt1280 16 24 32
  (interval_append leafTestAt1280 16 20 24
  (interval_append leafTestAt1280 16 18 20
  (interval_append leafTestAt1280 16 17 18
  leafTestAt1280_block_16
  leafTestAt1280_block_17)
  (interval_append leafTestAt1280 18 19 20
  leafTestAt1280_block_18
  leafTestAt1280_block_19))
  (interval_append leafTestAt1280 20 22 24
  (interval_append leafTestAt1280 20 21 22
  leafTestAt1280_block_20
  leafTestAt1280_block_21)
  (interval_append leafTestAt1280 22 23 24
  leafTestAt1280_block_22
  leafTestAt1280_block_23)))
  (interval_append leafTestAt1280 24 28 32
  (interval_append leafTestAt1280 24 26 28
  (interval_append leafTestAt1280 24 25 26
  leafTestAt1280_block_24
  leafTestAt1280_block_25)
  (interval_append leafTestAt1280 26 27 28
  leafTestAt1280_block_26
  leafTestAt1280_block_27))
  (interval_append leafTestAt1280 28 30 32
  (interval_append leafTestAt1280 28 29 30
  leafTestAt1280_block_28
  leafTestAt1280_block_29)
  (interval_append leafTestAt1280 30 31 32
  leafTestAt1280_block_30
  leafTestAt1280_block_31)))))
cert_leafInterval 1280 1312
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
cert_leafTestAt 1312
cert_leafTestAt_block_2 1312 0 1
cert_leafTestAt_block_2 1312 1 2
cert_leafTestAt_block_2 1312 2 3
cert_leafTestAt_block_2 1312 3 4
cert_leafTestAt_block_2 1312 4 5
cert_leafTestAt_block_2 1312 5 6
cert_leafTestAt_block_2 1312 6 7
cert_leafTestAt_block_2 1312 7 8
cert_leafTestAt_block_2 1312 8 9
cert_leafTestAt_block_2 1312 9 10
cert_leafTestAt_block_2 1312 10 11
cert_leafTestAt_block_2 1312 11 12
cert_leafTestAt_block_2 1312 12 13
cert_leafTestAt_block_2 1312 13 14
cert_leafTestAt_block_2 1312 14 15
cert_leafTestAt_block_2 1312 15 16
cert_leafTestAt_block_2 1312 16 17
cert_leafTestAt_block_2 1312 17 18
cert_leafTestAt_block_2 1312 18 19
cert_leafTestAt_block_2 1312 19 20
cert_leafTestAt_block_2 1312 20 21
cert_leafTestAt_block_2 1312 21 22
cert_leafTestAt_block_2 1312 22 23
cert_leafTestAt_block_2 1312 23 24
cert_leafTestAt_block_2 1312 24 25
cert_leafTestAt_block_2 1312 25 26
cert_leafTestAt_block_2 1312 26 27
cert_leafTestAt_block_2 1312 27 28
cert_leafTestAt_block_2 1312 28 29
cert_leafTestAt_block_2 1312 29 30
cert_leafTestAt_block_2 1312 30 31
cert_leafTestAt_block_2 1312 31 32
theorem leafTestAt1312_complete : Interval leafTestAt1312 0 32 :=
  (interval_append leafTestAt1312 0 16 32
  (interval_append leafTestAt1312 0 8 16
  (interval_append leafTestAt1312 0 4 8
  (interval_append leafTestAt1312 0 2 4
  (interval_append leafTestAt1312 0 1 2
  leafTestAt1312_block_0
  leafTestAt1312_block_1)
  (interval_append leafTestAt1312 2 3 4
  leafTestAt1312_block_2
  leafTestAt1312_block_3))
  (interval_append leafTestAt1312 4 6 8
  (interval_append leafTestAt1312 4 5 6
  leafTestAt1312_block_4
  leafTestAt1312_block_5)
  (interval_append leafTestAt1312 6 7 8
  leafTestAt1312_block_6
  leafTestAt1312_block_7)))
  (interval_append leafTestAt1312 8 12 16
  (interval_append leafTestAt1312 8 10 12
  (interval_append leafTestAt1312 8 9 10
  leafTestAt1312_block_8
  leafTestAt1312_block_9)
  (interval_append leafTestAt1312 10 11 12
  leafTestAt1312_block_10
  leafTestAt1312_block_11))
  (interval_append leafTestAt1312 12 14 16
  (interval_append leafTestAt1312 12 13 14
  leafTestAt1312_block_12
  leafTestAt1312_block_13)
  (interval_append leafTestAt1312 14 15 16
  leafTestAt1312_block_14
  leafTestAt1312_block_15))))
  (interval_append leafTestAt1312 16 24 32
  (interval_append leafTestAt1312 16 20 24
  (interval_append leafTestAt1312 16 18 20
  (interval_append leafTestAt1312 16 17 18
  leafTestAt1312_block_16
  leafTestAt1312_block_17)
  (interval_append leafTestAt1312 18 19 20
  leafTestAt1312_block_18
  leafTestAt1312_block_19))
  (interval_append leafTestAt1312 20 22 24
  (interval_append leafTestAt1312 20 21 22
  leafTestAt1312_block_20
  leafTestAt1312_block_21)
  (interval_append leafTestAt1312 22 23 24
  leafTestAt1312_block_22
  leafTestAt1312_block_23)))
  (interval_append leafTestAt1312 24 28 32
  (interval_append leafTestAt1312 24 26 28
  (interval_append leafTestAt1312 24 25 26
  leafTestAt1312_block_24
  leafTestAt1312_block_25)
  (interval_append leafTestAt1312 26 27 28
  leafTestAt1312_block_26
  leafTestAt1312_block_27))
  (interval_append leafTestAt1312 28 30 32
  (interval_append leafTestAt1312 28 29 30
  leafTestAt1312_block_28
  leafTestAt1312_block_29)
  (interval_append leafTestAt1312 30 31 32
  leafTestAt1312_block_30
  leafTestAt1312_block_31)))))
cert_leafInterval 1312 1344
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
cert_leafTestAt 1344
cert_leafTestAt_block_2 1344 0 1
cert_leafTestAt_block_2 1344 1 2
cert_leafTestAt_block_2 1344 2 3
cert_leafTestAt_block_2 1344 3 4
cert_leafTestAt_block_2 1344 4 5
cert_leafTestAt_block_2 1344 5 6
cert_leafTestAt_block_2 1344 6 7
cert_leafTestAt_block_2 1344 7 8
cert_leafTestAt_block_2 1344 8 9
cert_leafTestAt_block_2 1344 9 10
cert_leafTestAt_block_2 1344 10 11
cert_leafTestAt_block_2 1344 11 12
cert_leafTestAt_block_2 1344 12 13
cert_leafTestAt_block_2 1344 13 14
cert_leafTestAt_block_2 1344 14 15
cert_leafTestAt_block_2 1344 15 16
cert_leafTestAt_block_2 1344 16 17
cert_leafTestAt_block_2 1344 17 18
cert_leafTestAt_block_2 1344 18 19
cert_leafTestAt_block_2 1344 19 20
cert_leafTestAt_block_2 1344 20 21
cert_leafTestAt_block_2 1344 21 22
cert_leafTestAt_block_2 1344 22 23
cert_leafTestAt_block_2 1344 23 24
cert_leafTestAt_block_2 1344 24 25
cert_leafTestAt_block_2 1344 25 26
cert_leafTestAt_block_2 1344 26 27
cert_leafTestAt_block_2 1344 27 28
cert_leafTestAt_block_2 1344 28 29
cert_leafTestAt_block_2 1344 29 30
cert_leafTestAt_block_2 1344 30 31
cert_leafTestAt_block_2 1344 31 32
theorem leafTestAt1344_complete : Interval leafTestAt1344 0 32 :=
  (interval_append leafTestAt1344 0 16 32
  (interval_append leafTestAt1344 0 8 16
  (interval_append leafTestAt1344 0 4 8
  (interval_append leafTestAt1344 0 2 4
  (interval_append leafTestAt1344 0 1 2
  leafTestAt1344_block_0
  leafTestAt1344_block_1)
  (interval_append leafTestAt1344 2 3 4
  leafTestAt1344_block_2
  leafTestAt1344_block_3))
  (interval_append leafTestAt1344 4 6 8
  (interval_append leafTestAt1344 4 5 6
  leafTestAt1344_block_4
  leafTestAt1344_block_5)
  (interval_append leafTestAt1344 6 7 8
  leafTestAt1344_block_6
  leafTestAt1344_block_7)))
  (interval_append leafTestAt1344 8 12 16
  (interval_append leafTestAt1344 8 10 12
  (interval_append leafTestAt1344 8 9 10
  leafTestAt1344_block_8
  leafTestAt1344_block_9)
  (interval_append leafTestAt1344 10 11 12
  leafTestAt1344_block_10
  leafTestAt1344_block_11))
  (interval_append leafTestAt1344 12 14 16
  (interval_append leafTestAt1344 12 13 14
  leafTestAt1344_block_12
  leafTestAt1344_block_13)
  (interval_append leafTestAt1344 14 15 16
  leafTestAt1344_block_14
  leafTestAt1344_block_15))))
  (interval_append leafTestAt1344 16 24 32
  (interval_append leafTestAt1344 16 20 24
  (interval_append leafTestAt1344 16 18 20
  (interval_append leafTestAt1344 16 17 18
  leafTestAt1344_block_16
  leafTestAt1344_block_17)
  (interval_append leafTestAt1344 18 19 20
  leafTestAt1344_block_18
  leafTestAt1344_block_19))
  (interval_append leafTestAt1344 20 22 24
  (interval_append leafTestAt1344 20 21 22
  leafTestAt1344_block_20
  leafTestAt1344_block_21)
  (interval_append leafTestAt1344 22 23 24
  leafTestAt1344_block_22
  leafTestAt1344_block_23)))
  (interval_append leafTestAt1344 24 28 32
  (interval_append leafTestAt1344 24 26 28
  (interval_append leafTestAt1344 24 25 26
  leafTestAt1344_block_24
  leafTestAt1344_block_25)
  (interval_append leafTestAt1344 26 27 28
  leafTestAt1344_block_26
  leafTestAt1344_block_27))
  (interval_append leafTestAt1344 28 30 32
  (interval_append leafTestAt1344 28 29 30
  leafTestAt1344_block_28
  leafTestAt1344_block_29)
  (interval_append leafTestAt1344 30 31 32
  leafTestAt1344_block_30
  leafTestAt1344_block_31)))))
cert_leafInterval 1344 1376
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
cert_leafTestAt 1376
cert_leafTestAt_block_2 1376 0 1
cert_leafTestAt_block_2 1376 1 2
cert_leafTestAt_block_2 1376 2 3
cert_leafTestAt_block_2 1376 3 4
cert_leafTestAt_block_2 1376 4 5
cert_leafTestAt_block_2 1376 5 6
cert_leafTestAt_block_2 1376 6 7
cert_leafTestAt_block_2 1376 7 8
cert_leafTestAt_block_2 1376 8 9
cert_leafTestAt_block_2 1376 9 10
cert_leafTestAt_block_2 1376 10 11
cert_leafTestAt_block_2 1376 11 12
cert_leafTestAt_block_2 1376 12 13
cert_leafTestAt_block_2 1376 13 14
cert_leafTestAt_block_2 1376 14 15
cert_leafTestAt_block_2 1376 15 16
cert_leafTestAt_block_2 1376 16 17
cert_leafTestAt_block_2 1376 17 18
cert_leafTestAt_block_2 1376 18 19
cert_leafTestAt_block_2 1376 19 20
cert_leafTestAt_block_2 1376 20 21
cert_leafTestAt_block_2 1376 21 22
cert_leafTestAt_block_2 1376 22 23
cert_leafTestAt_block_2 1376 23 24
cert_leafTestAt_block_2 1376 24 25
cert_leafTestAt_block_2 1376 25 26
cert_leafTestAt_block_2 1376 26 27
cert_leafTestAt_block_2 1376 27 28
cert_leafTestAt_block_2 1376 28 29
cert_leafTestAt_block_2 1376 29 30
cert_leafTestAt_block_2 1376 30 31
cert_leafTestAt_block_2 1376 31 32
theorem leafTestAt1376_complete : Interval leafTestAt1376 0 32 :=
  (interval_append leafTestAt1376 0 16 32
  (interval_append leafTestAt1376 0 8 16
  (interval_append leafTestAt1376 0 4 8
  (interval_append leafTestAt1376 0 2 4
  (interval_append leafTestAt1376 0 1 2
  leafTestAt1376_block_0
  leafTestAt1376_block_1)
  (interval_append leafTestAt1376 2 3 4
  leafTestAt1376_block_2
  leafTestAt1376_block_3))
  (interval_append leafTestAt1376 4 6 8
  (interval_append leafTestAt1376 4 5 6
  leafTestAt1376_block_4
  leafTestAt1376_block_5)
  (interval_append leafTestAt1376 6 7 8
  leafTestAt1376_block_6
  leafTestAt1376_block_7)))
  (interval_append leafTestAt1376 8 12 16
  (interval_append leafTestAt1376 8 10 12
  (interval_append leafTestAt1376 8 9 10
  leafTestAt1376_block_8
  leafTestAt1376_block_9)
  (interval_append leafTestAt1376 10 11 12
  leafTestAt1376_block_10
  leafTestAt1376_block_11))
  (interval_append leafTestAt1376 12 14 16
  (interval_append leafTestAt1376 12 13 14
  leafTestAt1376_block_12
  leafTestAt1376_block_13)
  (interval_append leafTestAt1376 14 15 16
  leafTestAt1376_block_14
  leafTestAt1376_block_15))))
  (interval_append leafTestAt1376 16 24 32
  (interval_append leafTestAt1376 16 20 24
  (interval_append leafTestAt1376 16 18 20
  (interval_append leafTestAt1376 16 17 18
  leafTestAt1376_block_16
  leafTestAt1376_block_17)
  (interval_append leafTestAt1376 18 19 20
  leafTestAt1376_block_18
  leafTestAt1376_block_19))
  (interval_append leafTestAt1376 20 22 24
  (interval_append leafTestAt1376 20 21 22
  leafTestAt1376_block_20
  leafTestAt1376_block_21)
  (interval_append leafTestAt1376 22 23 24
  leafTestAt1376_block_22
  leafTestAt1376_block_23)))
  (interval_append leafTestAt1376 24 28 32
  (interval_append leafTestAt1376 24 26 28
  (interval_append leafTestAt1376 24 25 26
  leafTestAt1376_block_24
  leafTestAt1376_block_25)
  (interval_append leafTestAt1376 26 27 28
  leafTestAt1376_block_26
  leafTestAt1376_block_27))
  (interval_append leafTestAt1376 28 30 32
  (interval_append leafTestAt1376 28 29 30
  leafTestAt1376_block_28
  leafTestAt1376_block_29)
  (interval_append leafTestAt1376 30 31 32
  leafTestAt1376_block_30
  leafTestAt1376_block_31)))))
cert_leafInterval 1376 1408
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
cert_leafTestAt 1408
cert_leafTestAt_block_2 1408 0 1
cert_leafTestAt_block_2 1408 1 2
cert_leafTestAt_block_2 1408 2 3
cert_leafTestAt_block_2 1408 3 4
cert_leafTestAt_block_2 1408 4 5
cert_leafTestAt_block_2 1408 5 6
cert_leafTestAt_block_2 1408 6 7
cert_leafTestAt_block_2 1408 7 8
cert_leafTestAt_block_2 1408 8 9
cert_leafTestAt_block_2 1408 9 10
cert_leafTestAt_block_2 1408 10 11
cert_leafTestAt_block_2 1408 11 12
cert_leafTestAt_block_2 1408 12 13
cert_leafTestAt_block_2 1408 13 14
cert_leafTestAt_block_2 1408 14 15
cert_leafTestAt_block_2 1408 15 16
cert_leafTestAt_block_2 1408 16 17
cert_leafTestAt_block_2 1408 17 18
cert_leafTestAt_block_2 1408 18 19
cert_leafTestAt_block_2 1408 19 20
cert_leafTestAt_block_2 1408 20 21
cert_leafTestAt_block_2 1408 21 22
cert_leafTestAt_block_2 1408 22 23
cert_leafTestAt_block_2 1408 23 24
cert_leafTestAt_block_2 1408 24 25
cert_leafTestAt_block_2 1408 25 26
cert_leafTestAt_block_2 1408 26 27
cert_leafTestAt_block_2 1408 27 28
cert_leafTestAt_block_2 1408 28 29
cert_leafTestAt_block_2 1408 29 30
cert_leafTestAt_block_2 1408 30 31
cert_leafTestAt_block_2 1408 31 32
theorem leafTestAt1408_complete : Interval leafTestAt1408 0 32 :=
  (interval_append leafTestAt1408 0 16 32
  (interval_append leafTestAt1408 0 8 16
  (interval_append leafTestAt1408 0 4 8
  (interval_append leafTestAt1408 0 2 4
  (interval_append leafTestAt1408 0 1 2
  leafTestAt1408_block_0
  leafTestAt1408_block_1)
  (interval_append leafTestAt1408 2 3 4
  leafTestAt1408_block_2
  leafTestAt1408_block_3))
  (interval_append leafTestAt1408 4 6 8
  (interval_append leafTestAt1408 4 5 6
  leafTestAt1408_block_4
  leafTestAt1408_block_5)
  (interval_append leafTestAt1408 6 7 8
  leafTestAt1408_block_6
  leafTestAt1408_block_7)))
  (interval_append leafTestAt1408 8 12 16
  (interval_append leafTestAt1408 8 10 12
  (interval_append leafTestAt1408 8 9 10
  leafTestAt1408_block_8
  leafTestAt1408_block_9)
  (interval_append leafTestAt1408 10 11 12
  leafTestAt1408_block_10
  leafTestAt1408_block_11))
  (interval_append leafTestAt1408 12 14 16
  (interval_append leafTestAt1408 12 13 14
  leafTestAt1408_block_12
  leafTestAt1408_block_13)
  (interval_append leafTestAt1408 14 15 16
  leafTestAt1408_block_14
  leafTestAt1408_block_15))))
  (interval_append leafTestAt1408 16 24 32
  (interval_append leafTestAt1408 16 20 24
  (interval_append leafTestAt1408 16 18 20
  (interval_append leafTestAt1408 16 17 18
  leafTestAt1408_block_16
  leafTestAt1408_block_17)
  (interval_append leafTestAt1408 18 19 20
  leafTestAt1408_block_18
  leafTestAt1408_block_19))
  (interval_append leafTestAt1408 20 22 24
  (interval_append leafTestAt1408 20 21 22
  leafTestAt1408_block_20
  leafTestAt1408_block_21)
  (interval_append leafTestAt1408 22 23 24
  leafTestAt1408_block_22
  leafTestAt1408_block_23)))
  (interval_append leafTestAt1408 24 28 32
  (interval_append leafTestAt1408 24 26 28
  (interval_append leafTestAt1408 24 25 26
  leafTestAt1408_block_24
  leafTestAt1408_block_25)
  (interval_append leafTestAt1408 26 27 28
  leafTestAt1408_block_26
  leafTestAt1408_block_27))
  (interval_append leafTestAt1408 28 30 32
  (interval_append leafTestAt1408 28 29 30
  leafTestAt1408_block_28
  leafTestAt1408_block_29)
  (interval_append leafTestAt1408 30 31 32
  leafTestAt1408_block_30
  leafTestAt1408_block_31)))))
cert_leafInterval 1408 1440
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
cert_leafTestAt 1440
cert_leafTestAt_block_2 1440 0 1
cert_leafTestAt_block_2 1440 1 2
cert_leafTestAt_block_2 1440 2 3
cert_leafTestAt_block_2 1440 3 4
cert_leafTestAt_block_2 1440 4 5
cert_leafTestAt_block_2 1440 5 6
cert_leafTestAt_block_2 1440 6 7
cert_leafTestAt_block_2 1440 7 8
cert_leafTestAt_block_2 1440 8 9
cert_leafTestAt_block_2 1440 9 10
cert_leafTestAt_block_2 1440 10 11
cert_leafTestAt_block_2 1440 11 12
cert_leafTestAt_block_2 1440 12 13
cert_leafTestAt_block_2 1440 13 14
cert_leafTestAt_block_2 1440 14 15
cert_leafTestAt_block_2 1440 15 16
cert_leafTestAt_block_2 1440 16 17
cert_leafTestAt_block_2 1440 17 18
cert_leafTestAt_block_2 1440 18 19
cert_leafTestAt_block_2 1440 19 20
cert_leafTestAt_block_2 1440 20 21
cert_leafTestAt_block_2 1440 21 22
cert_leafTestAt_block_2 1440 22 23
cert_leafTestAt_block_2 1440 23 24
cert_leafTestAt_block_2 1440 24 25
cert_leafTestAt_block_2 1440 25 26
cert_leafTestAt_block_2 1440 26 27
cert_leafTestAt_block_2 1440 27 28
cert_leafTestAt_block_2 1440 28 29
cert_leafTestAt_block_2 1440 29 30
cert_leafTestAt_block_2 1440 30 31
cert_leafTestAt_block_2 1440 31 32
theorem leafTestAt1440_complete : Interval leafTestAt1440 0 32 :=
  (interval_append leafTestAt1440 0 16 32
  (interval_append leafTestAt1440 0 8 16
  (interval_append leafTestAt1440 0 4 8
  (interval_append leafTestAt1440 0 2 4
  (interval_append leafTestAt1440 0 1 2
  leafTestAt1440_block_0
  leafTestAt1440_block_1)
  (interval_append leafTestAt1440 2 3 4
  leafTestAt1440_block_2
  leafTestAt1440_block_3))
  (interval_append leafTestAt1440 4 6 8
  (interval_append leafTestAt1440 4 5 6
  leafTestAt1440_block_4
  leafTestAt1440_block_5)
  (interval_append leafTestAt1440 6 7 8
  leafTestAt1440_block_6
  leafTestAt1440_block_7)))
  (interval_append leafTestAt1440 8 12 16
  (interval_append leafTestAt1440 8 10 12
  (interval_append leafTestAt1440 8 9 10
  leafTestAt1440_block_8
  leafTestAt1440_block_9)
  (interval_append leafTestAt1440 10 11 12
  leafTestAt1440_block_10
  leafTestAt1440_block_11))
  (interval_append leafTestAt1440 12 14 16
  (interval_append leafTestAt1440 12 13 14
  leafTestAt1440_block_12
  leafTestAt1440_block_13)
  (interval_append leafTestAt1440 14 15 16
  leafTestAt1440_block_14
  leafTestAt1440_block_15))))
  (interval_append leafTestAt1440 16 24 32
  (interval_append leafTestAt1440 16 20 24
  (interval_append leafTestAt1440 16 18 20
  (interval_append leafTestAt1440 16 17 18
  leafTestAt1440_block_16
  leafTestAt1440_block_17)
  (interval_append leafTestAt1440 18 19 20
  leafTestAt1440_block_18
  leafTestAt1440_block_19))
  (interval_append leafTestAt1440 20 22 24
  (interval_append leafTestAt1440 20 21 22
  leafTestAt1440_block_20
  leafTestAt1440_block_21)
  (interval_append leafTestAt1440 22 23 24
  leafTestAt1440_block_22
  leafTestAt1440_block_23)))
  (interval_append leafTestAt1440 24 28 32
  (interval_append leafTestAt1440 24 26 28
  (interval_append leafTestAt1440 24 25 26
  leafTestAt1440_block_24
  leafTestAt1440_block_25)
  (interval_append leafTestAt1440 26 27 28
  leafTestAt1440_block_26
  leafTestAt1440_block_27))
  (interval_append leafTestAt1440 28 30 32
  (interval_append leafTestAt1440 28 29 30
  leafTestAt1440_block_28
  leafTestAt1440_block_29)
  (interval_append leafTestAt1440 30 31 32
  leafTestAt1440_block_30
  leafTestAt1440_block_31)))))
cert_leafInterval 1440 1472
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
cert_leafTestAt 1472
cert_leafTestAt_block_2 1472 0 1
cert_leafTestAt_block_2 1472 1 2
cert_leafTestAt_block_2 1472 2 3
cert_leafTestAt_block_2 1472 3 4
cert_leafTestAt_block_2 1472 4 5
cert_leafTestAt_block_2 1472 5 6
cert_leafTestAt_block_2 1472 6 7
cert_leafTestAt_block_2 1472 7 8
cert_leafTestAt_block_2 1472 8 9
cert_leafTestAt_block_2 1472 9 10
cert_leafTestAt_block_2 1472 10 11
cert_leafTestAt_block_2 1472 11 12
cert_leafTestAt_block_2 1472 12 13
cert_leafTestAt_block_2 1472 13 14
cert_leafTestAt_block_2 1472 14 15
cert_leafTestAt_block_2 1472 15 16
cert_leafTestAt_block_2 1472 16 17
cert_leafTestAt_block_2 1472 17 18
cert_leafTestAt_block_2 1472 18 19
cert_leafTestAt_block_2 1472 19 20
cert_leafTestAt_block_2 1472 20 21
cert_leafTestAt_block_2 1472 21 22
cert_leafTestAt_block_2 1472 22 23
cert_leafTestAt_block_2 1472 23 24
cert_leafTestAt_block_2 1472 24 25
cert_leafTestAt_block_2 1472 25 26
cert_leafTestAt_block_2 1472 26 27
cert_leafTestAt_block_2 1472 27 28
cert_leafTestAt_block_2 1472 28 29
cert_leafTestAt_block_2 1472 29 30
cert_leafTestAt_block_2 1472 30 31
cert_leafTestAt_block_2 1472 31 32
theorem leafTestAt1472_complete : Interval leafTestAt1472 0 32 :=
  (interval_append leafTestAt1472 0 16 32
  (interval_append leafTestAt1472 0 8 16
  (interval_append leafTestAt1472 0 4 8
  (interval_append leafTestAt1472 0 2 4
  (interval_append leafTestAt1472 0 1 2
  leafTestAt1472_block_0
  leafTestAt1472_block_1)
  (interval_append leafTestAt1472 2 3 4
  leafTestAt1472_block_2
  leafTestAt1472_block_3))
  (interval_append leafTestAt1472 4 6 8
  (interval_append leafTestAt1472 4 5 6
  leafTestAt1472_block_4
  leafTestAt1472_block_5)
  (interval_append leafTestAt1472 6 7 8
  leafTestAt1472_block_6
  leafTestAt1472_block_7)))
  (interval_append leafTestAt1472 8 12 16
  (interval_append leafTestAt1472 8 10 12
  (interval_append leafTestAt1472 8 9 10
  leafTestAt1472_block_8
  leafTestAt1472_block_9)
  (interval_append leafTestAt1472 10 11 12
  leafTestAt1472_block_10
  leafTestAt1472_block_11))
  (interval_append leafTestAt1472 12 14 16
  (interval_append leafTestAt1472 12 13 14
  leafTestAt1472_block_12
  leafTestAt1472_block_13)
  (interval_append leafTestAt1472 14 15 16
  leafTestAt1472_block_14
  leafTestAt1472_block_15))))
  (interval_append leafTestAt1472 16 24 32
  (interval_append leafTestAt1472 16 20 24
  (interval_append leafTestAt1472 16 18 20
  (interval_append leafTestAt1472 16 17 18
  leafTestAt1472_block_16
  leafTestAt1472_block_17)
  (interval_append leafTestAt1472 18 19 20
  leafTestAt1472_block_18
  leafTestAt1472_block_19))
  (interval_append leafTestAt1472 20 22 24
  (interval_append leafTestAt1472 20 21 22
  leafTestAt1472_block_20
  leafTestAt1472_block_21)
  (interval_append leafTestAt1472 22 23 24
  leafTestAt1472_block_22
  leafTestAt1472_block_23)))
  (interval_append leafTestAt1472 24 28 32
  (interval_append leafTestAt1472 24 26 28
  (interval_append leafTestAt1472 24 25 26
  leafTestAt1472_block_24
  leafTestAt1472_block_25)
  (interval_append leafTestAt1472 26 27 28
  leafTestAt1472_block_26
  leafTestAt1472_block_27))
  (interval_append leafTestAt1472 28 30 32
  (interval_append leafTestAt1472 28 29 30
  leafTestAt1472_block_28
  leafTestAt1472_block_29)
  (interval_append leafTestAt1472 30 31 32
  leafTestAt1472_block_30
  leafTestAt1472_block_31)))))
cert_leafInterval 1472 1504
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
cert_leafTestAt 1504
cert_leafTestAt_block_2 1504 0 1
cert_leafTestAt_block_2 1504 1 2
cert_leafTestAt_block_2 1504 2 3
cert_leafTestAt_block_2 1504 3 4
cert_leafTestAt_block_2 1504 4 5
cert_leafTestAt_block_2 1504 5 6
cert_leafTestAt_block_2 1504 6 7
cert_leafTestAt_block_2 1504 7 8
cert_leafTestAt_block_2 1504 8 9
cert_leafTestAt_block_2 1504 9 10
cert_leafTestAt_block_2 1504 10 11
cert_leafTestAt_block_2 1504 11 12
cert_leafTestAt_block_2 1504 12 13
cert_leafTestAt_block_2 1504 13 14
cert_leafTestAt_block_2 1504 14 15
cert_leafTestAt_block_2 1504 15 16
cert_leafTestAt_block_2 1504 16 17
cert_leafTestAt_block_2 1504 17 18
cert_leafTestAt_block_2 1504 18 19
cert_leafTestAt_block_2 1504 19 20
cert_leafTestAt_block_2 1504 20 21
cert_leafTestAt_block_2 1504 21 22
cert_leafTestAt_block_2 1504 22 23
cert_leafTestAt_block_2 1504 23 24
cert_leafTestAt_block_2 1504 24 25
cert_leafTestAt_block_2 1504 25 26
cert_leafTestAt_block_2 1504 26 27
cert_leafTestAt_block_2 1504 27 28
cert_leafTestAt_block_2 1504 28 29
cert_leafTestAt_block_2 1504 29 30
cert_leafTestAt_block_2 1504 30 31
cert_leafTestAt_block_2 1504 31 32
theorem leafTestAt1504_complete : Interval leafTestAt1504 0 32 :=
  (interval_append leafTestAt1504 0 16 32
  (interval_append leafTestAt1504 0 8 16
  (interval_append leafTestAt1504 0 4 8
  (interval_append leafTestAt1504 0 2 4
  (interval_append leafTestAt1504 0 1 2
  leafTestAt1504_block_0
  leafTestAt1504_block_1)
  (interval_append leafTestAt1504 2 3 4
  leafTestAt1504_block_2
  leafTestAt1504_block_3))
  (interval_append leafTestAt1504 4 6 8
  (interval_append leafTestAt1504 4 5 6
  leafTestAt1504_block_4
  leafTestAt1504_block_5)
  (interval_append leafTestAt1504 6 7 8
  leafTestAt1504_block_6
  leafTestAt1504_block_7)))
  (interval_append leafTestAt1504 8 12 16
  (interval_append leafTestAt1504 8 10 12
  (interval_append leafTestAt1504 8 9 10
  leafTestAt1504_block_8
  leafTestAt1504_block_9)
  (interval_append leafTestAt1504 10 11 12
  leafTestAt1504_block_10
  leafTestAt1504_block_11))
  (interval_append leafTestAt1504 12 14 16
  (interval_append leafTestAt1504 12 13 14
  leafTestAt1504_block_12
  leafTestAt1504_block_13)
  (interval_append leafTestAt1504 14 15 16
  leafTestAt1504_block_14
  leafTestAt1504_block_15))))
  (interval_append leafTestAt1504 16 24 32
  (interval_append leafTestAt1504 16 20 24
  (interval_append leafTestAt1504 16 18 20
  (interval_append leafTestAt1504 16 17 18
  leafTestAt1504_block_16
  leafTestAt1504_block_17)
  (interval_append leafTestAt1504 18 19 20
  leafTestAt1504_block_18
  leafTestAt1504_block_19))
  (interval_append leafTestAt1504 20 22 24
  (interval_append leafTestAt1504 20 21 22
  leafTestAt1504_block_20
  leafTestAt1504_block_21)
  (interval_append leafTestAt1504 22 23 24
  leafTestAt1504_block_22
  leafTestAt1504_block_23)))
  (interval_append leafTestAt1504 24 28 32
  (interval_append leafTestAt1504 24 26 28
  (interval_append leafTestAt1504 24 25 26
  leafTestAt1504_block_24
  leafTestAt1504_block_25)
  (interval_append leafTestAt1504 26 27 28
  leafTestAt1504_block_26
  leafTestAt1504_block_27))
  (interval_append leafTestAt1504 28 30 32
  (interval_append leafTestAt1504 28 29 30
  leafTestAt1504_block_28
  leafTestAt1504_block_29)
  (interval_append leafTestAt1504 30 31 32
  leafTestAt1504_block_30
  leafTestAt1504_block_31)))))
cert_leafInterval 1504 1536
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0724
end
end
