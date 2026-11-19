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
cert_leafTestAt 3072
cert_leafTestAt_block_2 3072 0 1
cert_leafTestAt_block_2 3072 1 2
cert_leafTestAt_block_2 3072 2 3
cert_leafTestAt_block_2 3072 3 4
cert_leafTestAt_block_2 3072 4 5
cert_leafTestAt_block_2 3072 5 6
cert_leafTestAt_block_2 3072 6 7
cert_leafTestAt_block_2 3072 7 8
cert_leafTestAt_block_2 3072 8 9
cert_leafTestAt_block_2 3072 9 10
cert_leafTestAt_block_2 3072 10 11
cert_leafTestAt_block_2 3072 11 12
cert_leafTestAt_block_2 3072 12 13
cert_leafTestAt_block_2 3072 13 14
cert_leafTestAt_block_2 3072 14 15
cert_leafTestAt_block_2 3072 15 16
cert_leafTestAt_block_2 3072 16 17
cert_leafTestAt_block_2 3072 17 18
cert_leafTestAt_block_2 3072 18 19
cert_leafTestAt_block_2 3072 19 20
cert_leafTestAt_block_2 3072 20 21
cert_leafTestAt_block_2 3072 21 22
cert_leafTestAt_block_2 3072 22 23
cert_leafTestAt_block_2 3072 23 24
cert_leafTestAt_block_2 3072 24 25
cert_leafTestAt_block_2 3072 25 26
cert_leafTestAt_block_2 3072 26 27
cert_leafTestAt_block_2 3072 27 28
cert_leafTestAt_block_2 3072 28 29
cert_leafTestAt_block_2 3072 29 30
cert_leafTestAt_block_2 3072 30 31
cert_leafTestAt_block_2 3072 31 32
theorem leafTestAt3072_complete : Interval leafTestAt3072 0 32 :=
  (interval_append leafTestAt3072 0 16 32
  (interval_append leafTestAt3072 0 8 16
  (interval_append leafTestAt3072 0 4 8
  (interval_append leafTestAt3072 0 2 4
  (interval_append leafTestAt3072 0 1 2
  leafTestAt3072_block_0
  leafTestAt3072_block_1)
  (interval_append leafTestAt3072 2 3 4
  leafTestAt3072_block_2
  leafTestAt3072_block_3))
  (interval_append leafTestAt3072 4 6 8
  (interval_append leafTestAt3072 4 5 6
  leafTestAt3072_block_4
  leafTestAt3072_block_5)
  (interval_append leafTestAt3072 6 7 8
  leafTestAt3072_block_6
  leafTestAt3072_block_7)))
  (interval_append leafTestAt3072 8 12 16
  (interval_append leafTestAt3072 8 10 12
  (interval_append leafTestAt3072 8 9 10
  leafTestAt3072_block_8
  leafTestAt3072_block_9)
  (interval_append leafTestAt3072 10 11 12
  leafTestAt3072_block_10
  leafTestAt3072_block_11))
  (interval_append leafTestAt3072 12 14 16
  (interval_append leafTestAt3072 12 13 14
  leafTestAt3072_block_12
  leafTestAt3072_block_13)
  (interval_append leafTestAt3072 14 15 16
  leafTestAt3072_block_14
  leafTestAt3072_block_15))))
  (interval_append leafTestAt3072 16 24 32
  (interval_append leafTestAt3072 16 20 24
  (interval_append leafTestAt3072 16 18 20
  (interval_append leafTestAt3072 16 17 18
  leafTestAt3072_block_16
  leafTestAt3072_block_17)
  (interval_append leafTestAt3072 18 19 20
  leafTestAt3072_block_18
  leafTestAt3072_block_19))
  (interval_append leafTestAt3072 20 22 24
  (interval_append leafTestAt3072 20 21 22
  leafTestAt3072_block_20
  leafTestAt3072_block_21)
  (interval_append leafTestAt3072 22 23 24
  leafTestAt3072_block_22
  leafTestAt3072_block_23)))
  (interval_append leafTestAt3072 24 28 32
  (interval_append leafTestAt3072 24 26 28
  (interval_append leafTestAt3072 24 25 26
  leafTestAt3072_block_24
  leafTestAt3072_block_25)
  (interval_append leafTestAt3072 26 27 28
  leafTestAt3072_block_26
  leafTestAt3072_block_27))
  (interval_append leafTestAt3072 28 30 32
  (interval_append leafTestAt3072 28 29 30
  leafTestAt3072_block_28
  leafTestAt3072_block_29)
  (interval_append leafTestAt3072 30 31 32
  leafTestAt3072_block_30
  leafTestAt3072_block_31)))))
cert_leafInterval 3072 3104
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
cert_leafTestAt 3104
cert_leafTestAt_block_2 3104 0 1
cert_leafTestAt_block_2 3104 1 2
cert_leafTestAt_block_2 3104 2 3
cert_leafTestAt_block_2 3104 3 4
cert_leafTestAt_block_2 3104 4 5
cert_leafTestAt_block_2 3104 5 6
cert_leafTestAt_block_2 3104 6 7
cert_leafTestAt_block_2 3104 7 8
cert_leafTestAt_block_2 3104 8 9
cert_leafTestAt_block_2 3104 9 10
cert_leafTestAt_block_2 3104 10 11
cert_leafTestAt_block_2 3104 11 12
cert_leafTestAt_block_2 3104 12 13
cert_leafTestAt_block_2 3104 13 14
cert_leafTestAt_block_2 3104 14 15
cert_leafTestAt_block_2 3104 15 16
cert_leafTestAt_block_2 3104 16 17
cert_leafTestAt_block_2 3104 17 18
cert_leafTestAt_block_2 3104 18 19
cert_leafTestAt_block_2 3104 19 20
cert_leafTestAt_block_2 3104 20 21
cert_leafTestAt_block_2 3104 21 22
cert_leafTestAt_block_2 3104 22 23
cert_leafTestAt_block_2 3104 23 24
cert_leafTestAt_block_2 3104 24 25
cert_leafTestAt_block_2 3104 25 26
cert_leafTestAt_block_2 3104 26 27
cert_leafTestAt_block_2 3104 27 28
cert_leafTestAt_block_2 3104 28 29
cert_leafTestAt_block_2 3104 29 30
cert_leafTestAt_block_2 3104 30 31
cert_leafTestAt_block_2 3104 31 32
theorem leafTestAt3104_complete : Interval leafTestAt3104 0 32 :=
  (interval_append leafTestAt3104 0 16 32
  (interval_append leafTestAt3104 0 8 16
  (interval_append leafTestAt3104 0 4 8
  (interval_append leafTestAt3104 0 2 4
  (interval_append leafTestAt3104 0 1 2
  leafTestAt3104_block_0
  leafTestAt3104_block_1)
  (interval_append leafTestAt3104 2 3 4
  leafTestAt3104_block_2
  leafTestAt3104_block_3))
  (interval_append leafTestAt3104 4 6 8
  (interval_append leafTestAt3104 4 5 6
  leafTestAt3104_block_4
  leafTestAt3104_block_5)
  (interval_append leafTestAt3104 6 7 8
  leafTestAt3104_block_6
  leafTestAt3104_block_7)))
  (interval_append leafTestAt3104 8 12 16
  (interval_append leafTestAt3104 8 10 12
  (interval_append leafTestAt3104 8 9 10
  leafTestAt3104_block_8
  leafTestAt3104_block_9)
  (interval_append leafTestAt3104 10 11 12
  leafTestAt3104_block_10
  leafTestAt3104_block_11))
  (interval_append leafTestAt3104 12 14 16
  (interval_append leafTestAt3104 12 13 14
  leafTestAt3104_block_12
  leafTestAt3104_block_13)
  (interval_append leafTestAt3104 14 15 16
  leafTestAt3104_block_14
  leafTestAt3104_block_15))))
  (interval_append leafTestAt3104 16 24 32
  (interval_append leafTestAt3104 16 20 24
  (interval_append leafTestAt3104 16 18 20
  (interval_append leafTestAt3104 16 17 18
  leafTestAt3104_block_16
  leafTestAt3104_block_17)
  (interval_append leafTestAt3104 18 19 20
  leafTestAt3104_block_18
  leafTestAt3104_block_19))
  (interval_append leafTestAt3104 20 22 24
  (interval_append leafTestAt3104 20 21 22
  leafTestAt3104_block_20
  leafTestAt3104_block_21)
  (interval_append leafTestAt3104 22 23 24
  leafTestAt3104_block_22
  leafTestAt3104_block_23)))
  (interval_append leafTestAt3104 24 28 32
  (interval_append leafTestAt3104 24 26 28
  (interval_append leafTestAt3104 24 25 26
  leafTestAt3104_block_24
  leafTestAt3104_block_25)
  (interval_append leafTestAt3104 26 27 28
  leafTestAt3104_block_26
  leafTestAt3104_block_27))
  (interval_append leafTestAt3104 28 30 32
  (interval_append leafTestAt3104 28 29 30
  leafTestAt3104_block_28
  leafTestAt3104_block_29)
  (interval_append leafTestAt3104 30 31 32
  leafTestAt3104_block_30
  leafTestAt3104_block_31)))))
cert_leafInterval 3104 3136
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
cert_leafTestAt 3136
cert_leafTestAt_block_2 3136 0 1
cert_leafTestAt_block_2 3136 1 2
cert_leafTestAt_block_2 3136 2 3
cert_leafTestAt_block_2 3136 3 4
cert_leafTestAt_block_2 3136 4 5
cert_leafTestAt_block_2 3136 5 6
cert_leafTestAt_block_2 3136 6 7
cert_leafTestAt_block_2 3136 7 8
cert_leafTestAt_block_2 3136 8 9
cert_leafTestAt_block_2 3136 9 10
cert_leafTestAt_block_2 3136 10 11
cert_leafTestAt_block_2 3136 11 12
cert_leafTestAt_block_2 3136 12 13
cert_leafTestAt_block_2 3136 13 14
cert_leafTestAt_block_2 3136 14 15
cert_leafTestAt_block_2 3136 15 16
cert_leafTestAt_block_2 3136 16 17
cert_leafTestAt_block_2 3136 17 18
cert_leafTestAt_block_2 3136 18 19
cert_leafTestAt_block_2 3136 19 20
cert_leafTestAt_block_2 3136 20 21
cert_leafTestAt_block_2 3136 21 22
cert_leafTestAt_block_2 3136 22 23
cert_leafTestAt_block_2 3136 23 24
cert_leafTestAt_block_2 3136 24 25
cert_leafTestAt_block_2 3136 25 26
cert_leafTestAt_block_2 3136 26 27
cert_leafTestAt_block_2 3136 27 28
cert_leafTestAt_block_2 3136 28 29
cert_leafTestAt_block_2 3136 29 30
cert_leafTestAt_block_2 3136 30 31
cert_leafTestAt_block_2 3136 31 32
theorem leafTestAt3136_complete : Interval leafTestAt3136 0 32 :=
  (interval_append leafTestAt3136 0 16 32
  (interval_append leafTestAt3136 0 8 16
  (interval_append leafTestAt3136 0 4 8
  (interval_append leafTestAt3136 0 2 4
  (interval_append leafTestAt3136 0 1 2
  leafTestAt3136_block_0
  leafTestAt3136_block_1)
  (interval_append leafTestAt3136 2 3 4
  leafTestAt3136_block_2
  leafTestAt3136_block_3))
  (interval_append leafTestAt3136 4 6 8
  (interval_append leafTestAt3136 4 5 6
  leafTestAt3136_block_4
  leafTestAt3136_block_5)
  (interval_append leafTestAt3136 6 7 8
  leafTestAt3136_block_6
  leafTestAt3136_block_7)))
  (interval_append leafTestAt3136 8 12 16
  (interval_append leafTestAt3136 8 10 12
  (interval_append leafTestAt3136 8 9 10
  leafTestAt3136_block_8
  leafTestAt3136_block_9)
  (interval_append leafTestAt3136 10 11 12
  leafTestAt3136_block_10
  leafTestAt3136_block_11))
  (interval_append leafTestAt3136 12 14 16
  (interval_append leafTestAt3136 12 13 14
  leafTestAt3136_block_12
  leafTestAt3136_block_13)
  (interval_append leafTestAt3136 14 15 16
  leafTestAt3136_block_14
  leafTestAt3136_block_15))))
  (interval_append leafTestAt3136 16 24 32
  (interval_append leafTestAt3136 16 20 24
  (interval_append leafTestAt3136 16 18 20
  (interval_append leafTestAt3136 16 17 18
  leafTestAt3136_block_16
  leafTestAt3136_block_17)
  (interval_append leafTestAt3136 18 19 20
  leafTestAt3136_block_18
  leafTestAt3136_block_19))
  (interval_append leafTestAt3136 20 22 24
  (interval_append leafTestAt3136 20 21 22
  leafTestAt3136_block_20
  leafTestAt3136_block_21)
  (interval_append leafTestAt3136 22 23 24
  leafTestAt3136_block_22
  leafTestAt3136_block_23)))
  (interval_append leafTestAt3136 24 28 32
  (interval_append leafTestAt3136 24 26 28
  (interval_append leafTestAt3136 24 25 26
  leafTestAt3136_block_24
  leafTestAt3136_block_25)
  (interval_append leafTestAt3136 26 27 28
  leafTestAt3136_block_26
  leafTestAt3136_block_27))
  (interval_append leafTestAt3136 28 30 32
  (interval_append leafTestAt3136 28 29 30
  leafTestAt3136_block_28
  leafTestAt3136_block_29)
  (interval_append leafTestAt3136 30 31 32
  leafTestAt3136_block_30
  leafTestAt3136_block_31)))))
cert_leafInterval 3136 3168
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
cert_leafTestAt 3168
cert_leafTestAt_block_2 3168 0 1
cert_leafTestAt_block_2 3168 1 2
cert_leafTestAt_block_2 3168 2 3
cert_leafTestAt_block_2 3168 3 4
cert_leafTestAt_block_2 3168 4 5
cert_leafTestAt_block_2 3168 5 6
cert_leafTestAt_block_2 3168 6 7
cert_leafTestAt_block_2 3168 7 8
cert_leafTestAt_block_2 3168 8 9
cert_leafTestAt_block_2 3168 9 10
cert_leafTestAt_block_2 3168 10 11
cert_leafTestAt_block_2 3168 11 12
cert_leafTestAt_block_2 3168 12 13
cert_leafTestAt_block_2 3168 13 14
cert_leafTestAt_block_2 3168 14 15
cert_leafTestAt_block_2 3168 15 16
cert_leafTestAt_block_2 3168 16 17
cert_leafTestAt_block_2 3168 17 18
cert_leafTestAt_block_2 3168 18 19
cert_leafTestAt_block_2 3168 19 20
cert_leafTestAt_block_2 3168 20 21
cert_leafTestAt_block_2 3168 21 22
cert_leafTestAt_block_2 3168 22 23
cert_leafTestAt_block_2 3168 23 24
cert_leafTestAt_block_2 3168 24 25
cert_leafTestAt_block_2 3168 25 26
cert_leafTestAt_block_2 3168 26 27
cert_leafTestAt_block_2 3168 27 28
cert_leafTestAt_block_2 3168 28 29
cert_leafTestAt_block_2 3168 29 30
cert_leafTestAt_block_2 3168 30 31
cert_leafTestAt_block_2 3168 31 32
theorem leafTestAt3168_complete : Interval leafTestAt3168 0 32 :=
  (interval_append leafTestAt3168 0 16 32
  (interval_append leafTestAt3168 0 8 16
  (interval_append leafTestAt3168 0 4 8
  (interval_append leafTestAt3168 0 2 4
  (interval_append leafTestAt3168 0 1 2
  leafTestAt3168_block_0
  leafTestAt3168_block_1)
  (interval_append leafTestAt3168 2 3 4
  leafTestAt3168_block_2
  leafTestAt3168_block_3))
  (interval_append leafTestAt3168 4 6 8
  (interval_append leafTestAt3168 4 5 6
  leafTestAt3168_block_4
  leafTestAt3168_block_5)
  (interval_append leafTestAt3168 6 7 8
  leafTestAt3168_block_6
  leafTestAt3168_block_7)))
  (interval_append leafTestAt3168 8 12 16
  (interval_append leafTestAt3168 8 10 12
  (interval_append leafTestAt3168 8 9 10
  leafTestAt3168_block_8
  leafTestAt3168_block_9)
  (interval_append leafTestAt3168 10 11 12
  leafTestAt3168_block_10
  leafTestAt3168_block_11))
  (interval_append leafTestAt3168 12 14 16
  (interval_append leafTestAt3168 12 13 14
  leafTestAt3168_block_12
  leafTestAt3168_block_13)
  (interval_append leafTestAt3168 14 15 16
  leafTestAt3168_block_14
  leafTestAt3168_block_15))))
  (interval_append leafTestAt3168 16 24 32
  (interval_append leafTestAt3168 16 20 24
  (interval_append leafTestAt3168 16 18 20
  (interval_append leafTestAt3168 16 17 18
  leafTestAt3168_block_16
  leafTestAt3168_block_17)
  (interval_append leafTestAt3168 18 19 20
  leafTestAt3168_block_18
  leafTestAt3168_block_19))
  (interval_append leafTestAt3168 20 22 24
  (interval_append leafTestAt3168 20 21 22
  leafTestAt3168_block_20
  leafTestAt3168_block_21)
  (interval_append leafTestAt3168 22 23 24
  leafTestAt3168_block_22
  leafTestAt3168_block_23)))
  (interval_append leafTestAt3168 24 28 32
  (interval_append leafTestAt3168 24 26 28
  (interval_append leafTestAt3168 24 25 26
  leafTestAt3168_block_24
  leafTestAt3168_block_25)
  (interval_append leafTestAt3168 26 27 28
  leafTestAt3168_block_26
  leafTestAt3168_block_27))
  (interval_append leafTestAt3168 28 30 32
  (interval_append leafTestAt3168 28 29 30
  leafTestAt3168_block_28
  leafTestAt3168_block_29)
  (interval_append leafTestAt3168 30 31 32
  leafTestAt3168_block_30
  leafTestAt3168_block_31)))))
cert_leafInterval 3168 3200
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
cert_leafTestAt 3200
cert_leafTestAt_block_2 3200 0 1
cert_leafTestAt_block_2 3200 1 2
cert_leafTestAt_block_2 3200 2 3
cert_leafTestAt_block_2 3200 3 4
cert_leafTestAt_block_2 3200 4 5
cert_leafTestAt_block_2 3200 5 6
cert_leafTestAt_block_2 3200 6 7
cert_leafTestAt_block_2 3200 7 8
cert_leafTestAt_block_2 3200 8 9
cert_leafTestAt_block_2 3200 9 10
cert_leafTestAt_block_2 3200 10 11
cert_leafTestAt_block_2 3200 11 12
cert_leafTestAt_block_2 3200 12 13
cert_leafTestAt_block_2 3200 13 14
cert_leafTestAt_block_2 3200 14 15
cert_leafTestAt_block_2 3200 15 16
cert_leafTestAt_block_2 3200 16 17
cert_leafTestAt_block_2 3200 17 18
cert_leafTestAt_block_2 3200 18 19
cert_leafTestAt_block_2 3200 19 20
cert_leafTestAt_block_2 3200 20 21
cert_leafTestAt_block_2 3200 21 22
cert_leafTestAt_block_2 3200 22 23
cert_leafTestAt_block_2 3200 23 24
cert_leafTestAt_block_2 3200 24 25
cert_leafTestAt_block_2 3200 25 26
cert_leafTestAt_block_2 3200 26 27
cert_leafTestAt_block_2 3200 27 28
cert_leafTestAt_block_2 3200 28 29
cert_leafTestAt_block_2 3200 29 30
cert_leafTestAt_block_2 3200 30 31
cert_leafTestAt_block_2 3200 31 32
theorem leafTestAt3200_complete : Interval leafTestAt3200 0 32 :=
  (interval_append leafTestAt3200 0 16 32
  (interval_append leafTestAt3200 0 8 16
  (interval_append leafTestAt3200 0 4 8
  (interval_append leafTestAt3200 0 2 4
  (interval_append leafTestAt3200 0 1 2
  leafTestAt3200_block_0
  leafTestAt3200_block_1)
  (interval_append leafTestAt3200 2 3 4
  leafTestAt3200_block_2
  leafTestAt3200_block_3))
  (interval_append leafTestAt3200 4 6 8
  (interval_append leafTestAt3200 4 5 6
  leafTestAt3200_block_4
  leafTestAt3200_block_5)
  (interval_append leafTestAt3200 6 7 8
  leafTestAt3200_block_6
  leafTestAt3200_block_7)))
  (interval_append leafTestAt3200 8 12 16
  (interval_append leafTestAt3200 8 10 12
  (interval_append leafTestAt3200 8 9 10
  leafTestAt3200_block_8
  leafTestAt3200_block_9)
  (interval_append leafTestAt3200 10 11 12
  leafTestAt3200_block_10
  leafTestAt3200_block_11))
  (interval_append leafTestAt3200 12 14 16
  (interval_append leafTestAt3200 12 13 14
  leafTestAt3200_block_12
  leafTestAt3200_block_13)
  (interval_append leafTestAt3200 14 15 16
  leafTestAt3200_block_14
  leafTestAt3200_block_15))))
  (interval_append leafTestAt3200 16 24 32
  (interval_append leafTestAt3200 16 20 24
  (interval_append leafTestAt3200 16 18 20
  (interval_append leafTestAt3200 16 17 18
  leafTestAt3200_block_16
  leafTestAt3200_block_17)
  (interval_append leafTestAt3200 18 19 20
  leafTestAt3200_block_18
  leafTestAt3200_block_19))
  (interval_append leafTestAt3200 20 22 24
  (interval_append leafTestAt3200 20 21 22
  leafTestAt3200_block_20
  leafTestAt3200_block_21)
  (interval_append leafTestAt3200 22 23 24
  leafTestAt3200_block_22
  leafTestAt3200_block_23)))
  (interval_append leafTestAt3200 24 28 32
  (interval_append leafTestAt3200 24 26 28
  (interval_append leafTestAt3200 24 25 26
  leafTestAt3200_block_24
  leafTestAt3200_block_25)
  (interval_append leafTestAt3200 26 27 28
  leafTestAt3200_block_26
  leafTestAt3200_block_27))
  (interval_append leafTestAt3200 28 30 32
  (interval_append leafTestAt3200 28 29 30
  leafTestAt3200_block_28
  leafTestAt3200_block_29)
  (interval_append leafTestAt3200 30 31 32
  leafTestAt3200_block_30
  leafTestAt3200_block_31)))))
cert_leafInterval 3200 3232
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
cert_leafTestAt 3232
cert_leafTestAt_block_2 3232 0 1
cert_leafTestAt_block_2 3232 1 2
cert_leafTestAt_block_2 3232 2 3
cert_leafTestAt_block_2 3232 3 4
cert_leafTestAt_block_2 3232 4 5
cert_leafTestAt_block_2 3232 5 6
cert_leafTestAt_block_2 3232 6 7
cert_leafTestAt_block_2 3232 7 8
cert_leafTestAt_block_2 3232 8 9
cert_leafTestAt_block_2 3232 9 10
cert_leafTestAt_block_2 3232 10 11
cert_leafTestAt_block_2 3232 11 12
cert_leafTestAt_block_2 3232 12 13
cert_leafTestAt_block_2 3232 13 14
cert_leafTestAt_block_2 3232 14 15
cert_leafTestAt_block_2 3232 15 16
cert_leafTestAt_block_2 3232 16 17
cert_leafTestAt_block_2 3232 17 18
cert_leafTestAt_block_2 3232 18 19
cert_leafTestAt_block_2 3232 19 20
cert_leafTestAt_block_2 3232 20 21
cert_leafTestAt_block_2 3232 21 22
cert_leafTestAt_block_2 3232 22 23
cert_leafTestAt_block_2 3232 23 24
cert_leafTestAt_block_2 3232 24 25
cert_leafTestAt_block_2 3232 25 26
cert_leafTestAt_block_2 3232 26 27
cert_leafTestAt_block_2 3232 27 28
cert_leafTestAt_block_2 3232 28 29
cert_leafTestAt_block_2 3232 29 30
cert_leafTestAt_block_2 3232 30 31
cert_leafTestAt_block_2 3232 31 32
theorem leafTestAt3232_complete : Interval leafTestAt3232 0 32 :=
  (interval_append leafTestAt3232 0 16 32
  (interval_append leafTestAt3232 0 8 16
  (interval_append leafTestAt3232 0 4 8
  (interval_append leafTestAt3232 0 2 4
  (interval_append leafTestAt3232 0 1 2
  leafTestAt3232_block_0
  leafTestAt3232_block_1)
  (interval_append leafTestAt3232 2 3 4
  leafTestAt3232_block_2
  leafTestAt3232_block_3))
  (interval_append leafTestAt3232 4 6 8
  (interval_append leafTestAt3232 4 5 6
  leafTestAt3232_block_4
  leafTestAt3232_block_5)
  (interval_append leafTestAt3232 6 7 8
  leafTestAt3232_block_6
  leafTestAt3232_block_7)))
  (interval_append leafTestAt3232 8 12 16
  (interval_append leafTestAt3232 8 10 12
  (interval_append leafTestAt3232 8 9 10
  leafTestAt3232_block_8
  leafTestAt3232_block_9)
  (interval_append leafTestAt3232 10 11 12
  leafTestAt3232_block_10
  leafTestAt3232_block_11))
  (interval_append leafTestAt3232 12 14 16
  (interval_append leafTestAt3232 12 13 14
  leafTestAt3232_block_12
  leafTestAt3232_block_13)
  (interval_append leafTestAt3232 14 15 16
  leafTestAt3232_block_14
  leafTestAt3232_block_15))))
  (interval_append leafTestAt3232 16 24 32
  (interval_append leafTestAt3232 16 20 24
  (interval_append leafTestAt3232 16 18 20
  (interval_append leafTestAt3232 16 17 18
  leafTestAt3232_block_16
  leafTestAt3232_block_17)
  (interval_append leafTestAt3232 18 19 20
  leafTestAt3232_block_18
  leafTestAt3232_block_19))
  (interval_append leafTestAt3232 20 22 24
  (interval_append leafTestAt3232 20 21 22
  leafTestAt3232_block_20
  leafTestAt3232_block_21)
  (interval_append leafTestAt3232 22 23 24
  leafTestAt3232_block_22
  leafTestAt3232_block_23)))
  (interval_append leafTestAt3232 24 28 32
  (interval_append leafTestAt3232 24 26 28
  (interval_append leafTestAt3232 24 25 26
  leafTestAt3232_block_24
  leafTestAt3232_block_25)
  (interval_append leafTestAt3232 26 27 28
  leafTestAt3232_block_26
  leafTestAt3232_block_27))
  (interval_append leafTestAt3232 28 30 32
  (interval_append leafTestAt3232 28 29 30
  leafTestAt3232_block_28
  leafTestAt3232_block_29)
  (interval_append leafTestAt3232 30 31 32
  leafTestAt3232_block_30
  leafTestAt3232_block_31)))))
cert_leafInterval 3232 3264
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
cert_leafTestAt 3264
cert_leafTestAt_block_2 3264 0 1
cert_leafTestAt_block_2 3264 1 2
cert_leafTestAt_block_2 3264 2 3
cert_leafTestAt_block_2 3264 3 4
cert_leafTestAt_block_2 3264 4 5
cert_leafTestAt_block_2 3264 5 6
cert_leafTestAt_block_2 3264 6 7
cert_leafTestAt_block_2 3264 7 8
cert_leafTestAt_block_2 3264 8 9
cert_leafTestAt_block_2 3264 9 10
cert_leafTestAt_block_2 3264 10 11
cert_leafTestAt_block_2 3264 11 12
cert_leafTestAt_block_2 3264 12 13
cert_leafTestAt_block_2 3264 13 14
cert_leafTestAt_block_2 3264 14 15
cert_leafTestAt_block_2 3264 15 16
cert_leafTestAt_block_2 3264 16 17
cert_leafTestAt_block_2 3264 17 18
cert_leafTestAt_block_2 3264 18 19
cert_leafTestAt_block_2 3264 19 20
cert_leafTestAt_block_2 3264 20 21
cert_leafTestAt_block_2 3264 21 22
cert_leafTestAt_block_2 3264 22 23
cert_leafTestAt_block_2 3264 23 24
cert_leafTestAt_block_2 3264 24 25
cert_leafTestAt_block_2 3264 25 26
cert_leafTestAt_block_2 3264 26 27
cert_leafTestAt_block_2 3264 27 28
cert_leafTestAt_block_2 3264 28 29
cert_leafTestAt_block_2 3264 29 30
cert_leafTestAt_block_2 3264 30 31
cert_leafTestAt_block_2 3264 31 32
theorem leafTestAt3264_complete : Interval leafTestAt3264 0 32 :=
  (interval_append leafTestAt3264 0 16 32
  (interval_append leafTestAt3264 0 8 16
  (interval_append leafTestAt3264 0 4 8
  (interval_append leafTestAt3264 0 2 4
  (interval_append leafTestAt3264 0 1 2
  leafTestAt3264_block_0
  leafTestAt3264_block_1)
  (interval_append leafTestAt3264 2 3 4
  leafTestAt3264_block_2
  leafTestAt3264_block_3))
  (interval_append leafTestAt3264 4 6 8
  (interval_append leafTestAt3264 4 5 6
  leafTestAt3264_block_4
  leafTestAt3264_block_5)
  (interval_append leafTestAt3264 6 7 8
  leafTestAt3264_block_6
  leafTestAt3264_block_7)))
  (interval_append leafTestAt3264 8 12 16
  (interval_append leafTestAt3264 8 10 12
  (interval_append leafTestAt3264 8 9 10
  leafTestAt3264_block_8
  leafTestAt3264_block_9)
  (interval_append leafTestAt3264 10 11 12
  leafTestAt3264_block_10
  leafTestAt3264_block_11))
  (interval_append leafTestAt3264 12 14 16
  (interval_append leafTestAt3264 12 13 14
  leafTestAt3264_block_12
  leafTestAt3264_block_13)
  (interval_append leafTestAt3264 14 15 16
  leafTestAt3264_block_14
  leafTestAt3264_block_15))))
  (interval_append leafTestAt3264 16 24 32
  (interval_append leafTestAt3264 16 20 24
  (interval_append leafTestAt3264 16 18 20
  (interval_append leafTestAt3264 16 17 18
  leafTestAt3264_block_16
  leafTestAt3264_block_17)
  (interval_append leafTestAt3264 18 19 20
  leafTestAt3264_block_18
  leafTestAt3264_block_19))
  (interval_append leafTestAt3264 20 22 24
  (interval_append leafTestAt3264 20 21 22
  leafTestAt3264_block_20
  leafTestAt3264_block_21)
  (interval_append leafTestAt3264 22 23 24
  leafTestAt3264_block_22
  leafTestAt3264_block_23)))
  (interval_append leafTestAt3264 24 28 32
  (interval_append leafTestAt3264 24 26 28
  (interval_append leafTestAt3264 24 25 26
  leafTestAt3264_block_24
  leafTestAt3264_block_25)
  (interval_append leafTestAt3264 26 27 28
  leafTestAt3264_block_26
  leafTestAt3264_block_27))
  (interval_append leafTestAt3264 28 30 32
  (interval_append leafTestAt3264 28 29 30
  leafTestAt3264_block_28
  leafTestAt3264_block_29)
  (interval_append leafTestAt3264 30 31 32
  leafTestAt3264_block_30
  leafTestAt3264_block_31)))))
cert_leafInterval 3264 3296
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
cert_leafTestAt 3296
cert_leafTestAt_block_2 3296 0 1
cert_leafTestAt_block_2 3296 1 2
cert_leafTestAt_block_2 3296 2 3
cert_leafTestAt_block_2 3296 3 4
cert_leafTestAt_block_2 3296 4 5
cert_leafTestAt_block_2 3296 5 6
cert_leafTestAt_block_2 3296 6 7
cert_leafTestAt_block_2 3296 7 8
cert_leafTestAt_block_2 3296 8 9
cert_leafTestAt_block_2 3296 9 10
cert_leafTestAt_block_2 3296 10 11
cert_leafTestAt_block_2 3296 11 12
cert_leafTestAt_block_2 3296 12 13
cert_leafTestAt_block_2 3296 13 14
cert_leafTestAt_block_2 3296 14 15
cert_leafTestAt_block_2 3296 15 16
cert_leafTestAt_block_2 3296 16 17
cert_leafTestAt_block_2 3296 17 18
cert_leafTestAt_block_2 3296 18 19
cert_leafTestAt_block_2 3296 19 20
cert_leafTestAt_block_2 3296 20 21
cert_leafTestAt_block_2 3296 21 22
cert_leafTestAt_block_2 3296 22 23
cert_leafTestAt_block_2 3296 23 24
cert_leafTestAt_block_2 3296 24 25
cert_leafTestAt_block_2 3296 25 26
cert_leafTestAt_block_2 3296 26 27
cert_leafTestAt_block_2 3296 27 28
cert_leafTestAt_block_2 3296 28 29
cert_leafTestAt_block_2 3296 29 30
cert_leafTestAt_block_2 3296 30 31
cert_leafTestAt_block_2 3296 31 32
theorem leafTestAt3296_complete : Interval leafTestAt3296 0 32 :=
  (interval_append leafTestAt3296 0 16 32
  (interval_append leafTestAt3296 0 8 16
  (interval_append leafTestAt3296 0 4 8
  (interval_append leafTestAt3296 0 2 4
  (interval_append leafTestAt3296 0 1 2
  leafTestAt3296_block_0
  leafTestAt3296_block_1)
  (interval_append leafTestAt3296 2 3 4
  leafTestAt3296_block_2
  leafTestAt3296_block_3))
  (interval_append leafTestAt3296 4 6 8
  (interval_append leafTestAt3296 4 5 6
  leafTestAt3296_block_4
  leafTestAt3296_block_5)
  (interval_append leafTestAt3296 6 7 8
  leafTestAt3296_block_6
  leafTestAt3296_block_7)))
  (interval_append leafTestAt3296 8 12 16
  (interval_append leafTestAt3296 8 10 12
  (interval_append leafTestAt3296 8 9 10
  leafTestAt3296_block_8
  leafTestAt3296_block_9)
  (interval_append leafTestAt3296 10 11 12
  leafTestAt3296_block_10
  leafTestAt3296_block_11))
  (interval_append leafTestAt3296 12 14 16
  (interval_append leafTestAt3296 12 13 14
  leafTestAt3296_block_12
  leafTestAt3296_block_13)
  (interval_append leafTestAt3296 14 15 16
  leafTestAt3296_block_14
  leafTestAt3296_block_15))))
  (interval_append leafTestAt3296 16 24 32
  (interval_append leafTestAt3296 16 20 24
  (interval_append leafTestAt3296 16 18 20
  (interval_append leafTestAt3296 16 17 18
  leafTestAt3296_block_16
  leafTestAt3296_block_17)
  (interval_append leafTestAt3296 18 19 20
  leafTestAt3296_block_18
  leafTestAt3296_block_19))
  (interval_append leafTestAt3296 20 22 24
  (interval_append leafTestAt3296 20 21 22
  leafTestAt3296_block_20
  leafTestAt3296_block_21)
  (interval_append leafTestAt3296 22 23 24
  leafTestAt3296_block_22
  leafTestAt3296_block_23)))
  (interval_append leafTestAt3296 24 28 32
  (interval_append leafTestAt3296 24 26 28
  (interval_append leafTestAt3296 24 25 26
  leafTestAt3296_block_24
  leafTestAt3296_block_25)
  (interval_append leafTestAt3296 26 27 28
  leafTestAt3296_block_26
  leafTestAt3296_block_27))
  (interval_append leafTestAt3296 28 30 32
  (interval_append leafTestAt3296 28 29 30
  leafTestAt3296_block_28
  leafTestAt3296_block_29)
  (interval_append leafTestAt3296 30 31 32
  leafTestAt3296_block_30
  leafTestAt3296_block_31)))))
cert_leafInterval 3296 3328
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
cert_leafTestAt 3328
cert_leafTestAt_block_2 3328 0 1
cert_leafTestAt_block_2 3328 1 2
cert_leafTestAt_block_2 3328 2 3
cert_leafTestAt_block_2 3328 3 4
cert_leafTestAt_block_2 3328 4 5
cert_leafTestAt_block_2 3328 5 6
cert_leafTestAt_block_2 3328 6 7
cert_leafTestAt_block_2 3328 7 8
cert_leafTestAt_block_2 3328 8 9
cert_leafTestAt_block_2 3328 9 10
cert_leafTestAt_block_2 3328 10 11
cert_leafTestAt_block_2 3328 11 12
cert_leafTestAt_block_2 3328 12 13
cert_leafTestAt_block_2 3328 13 14
cert_leafTestAt_block_2 3328 14 15
cert_leafTestAt_block_2 3328 15 16
cert_leafTestAt_block_2 3328 16 17
cert_leafTestAt_block_2 3328 17 18
cert_leafTestAt_block_2 3328 18 19
cert_leafTestAt_block_2 3328 19 20
cert_leafTestAt_block_2 3328 20 21
cert_leafTestAt_block_2 3328 21 22
cert_leafTestAt_block_2 3328 22 23
cert_leafTestAt_block_2 3328 23 24
cert_leafTestAt_block_2 3328 24 25
cert_leafTestAt_block_2 3328 25 26
cert_leafTestAt_block_2 3328 26 27
cert_leafTestAt_block_2 3328 27 28
cert_leafTestAt_block_2 3328 28 29
cert_leafTestAt_block_2 3328 29 30
cert_leafTestAt_block_2 3328 30 31
cert_leafTestAt_block_2 3328 31 32
theorem leafTestAt3328_complete : Interval leafTestAt3328 0 32 :=
  (interval_append leafTestAt3328 0 16 32
  (interval_append leafTestAt3328 0 8 16
  (interval_append leafTestAt3328 0 4 8
  (interval_append leafTestAt3328 0 2 4
  (interval_append leafTestAt3328 0 1 2
  leafTestAt3328_block_0
  leafTestAt3328_block_1)
  (interval_append leafTestAt3328 2 3 4
  leafTestAt3328_block_2
  leafTestAt3328_block_3))
  (interval_append leafTestAt3328 4 6 8
  (interval_append leafTestAt3328 4 5 6
  leafTestAt3328_block_4
  leafTestAt3328_block_5)
  (interval_append leafTestAt3328 6 7 8
  leafTestAt3328_block_6
  leafTestAt3328_block_7)))
  (interval_append leafTestAt3328 8 12 16
  (interval_append leafTestAt3328 8 10 12
  (interval_append leafTestAt3328 8 9 10
  leafTestAt3328_block_8
  leafTestAt3328_block_9)
  (interval_append leafTestAt3328 10 11 12
  leafTestAt3328_block_10
  leafTestAt3328_block_11))
  (interval_append leafTestAt3328 12 14 16
  (interval_append leafTestAt3328 12 13 14
  leafTestAt3328_block_12
  leafTestAt3328_block_13)
  (interval_append leafTestAt3328 14 15 16
  leafTestAt3328_block_14
  leafTestAt3328_block_15))))
  (interval_append leafTestAt3328 16 24 32
  (interval_append leafTestAt3328 16 20 24
  (interval_append leafTestAt3328 16 18 20
  (interval_append leafTestAt3328 16 17 18
  leafTestAt3328_block_16
  leafTestAt3328_block_17)
  (interval_append leafTestAt3328 18 19 20
  leafTestAt3328_block_18
  leafTestAt3328_block_19))
  (interval_append leafTestAt3328 20 22 24
  (interval_append leafTestAt3328 20 21 22
  leafTestAt3328_block_20
  leafTestAt3328_block_21)
  (interval_append leafTestAt3328 22 23 24
  leafTestAt3328_block_22
  leafTestAt3328_block_23)))
  (interval_append leafTestAt3328 24 28 32
  (interval_append leafTestAt3328 24 26 28
  (interval_append leafTestAt3328 24 25 26
  leafTestAt3328_block_24
  leafTestAt3328_block_25)
  (interval_append leafTestAt3328 26 27 28
  leafTestAt3328_block_26
  leafTestAt3328_block_27))
  (interval_append leafTestAt3328 28 30 32
  (interval_append leafTestAt3328 28 29 30
  leafTestAt3328_block_28
  leafTestAt3328_block_29)
  (interval_append leafTestAt3328 30 31 32
  leafTestAt3328_block_30
  leafTestAt3328_block_31)))))
cert_leafInterval 3328 3360
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
cert_leafTestAt 3360
cert_leafTestAt_block_2 3360 0 1
cert_leafTestAt_block_2 3360 1 2
cert_leafTestAt_block_2 3360 2 3
cert_leafTestAt_block_2 3360 3 4
cert_leafTestAt_block_2 3360 4 5
cert_leafTestAt_block_2 3360 5 6
cert_leafTestAt_block_2 3360 6 7
cert_leafTestAt_block_2 3360 7 8
cert_leafTestAt_block_2 3360 8 9
cert_leafTestAt_block_2 3360 9 10
cert_leafTestAt_block_2 3360 10 11
cert_leafTestAt_block_2 3360 11 12
cert_leafTestAt_block_2 3360 12 13
cert_leafTestAt_block_2 3360 13 14
cert_leafTestAt_block_2 3360 14 15
cert_leafTestAt_block_2 3360 15 16
cert_leafTestAt_block_2 3360 16 17
cert_leafTestAt_block_2 3360 17 18
cert_leafTestAt_block_2 3360 18 19
cert_leafTestAt_block_2 3360 19 20
cert_leafTestAt_block_2 3360 20 21
cert_leafTestAt_block_2 3360 21 22
cert_leafTestAt_block_2 3360 22 23
cert_leafTestAt_block_2 3360 23 24
cert_leafTestAt_block_2 3360 24 25
cert_leafTestAt_block_2 3360 25 26
cert_leafTestAt_block_2 3360 26 27
cert_leafTestAt_block_2 3360 27 28
cert_leafTestAt_block_2 3360 28 29
cert_leafTestAt_block_2 3360 29 30
cert_leafTestAt_block_2 3360 30 31
cert_leafTestAt_block_2 3360 31 32
theorem leafTestAt3360_complete : Interval leafTestAt3360 0 32 :=
  (interval_append leafTestAt3360 0 16 32
  (interval_append leafTestAt3360 0 8 16
  (interval_append leafTestAt3360 0 4 8
  (interval_append leafTestAt3360 0 2 4
  (interval_append leafTestAt3360 0 1 2
  leafTestAt3360_block_0
  leafTestAt3360_block_1)
  (interval_append leafTestAt3360 2 3 4
  leafTestAt3360_block_2
  leafTestAt3360_block_3))
  (interval_append leafTestAt3360 4 6 8
  (interval_append leafTestAt3360 4 5 6
  leafTestAt3360_block_4
  leafTestAt3360_block_5)
  (interval_append leafTestAt3360 6 7 8
  leafTestAt3360_block_6
  leafTestAt3360_block_7)))
  (interval_append leafTestAt3360 8 12 16
  (interval_append leafTestAt3360 8 10 12
  (interval_append leafTestAt3360 8 9 10
  leafTestAt3360_block_8
  leafTestAt3360_block_9)
  (interval_append leafTestAt3360 10 11 12
  leafTestAt3360_block_10
  leafTestAt3360_block_11))
  (interval_append leafTestAt3360 12 14 16
  (interval_append leafTestAt3360 12 13 14
  leafTestAt3360_block_12
  leafTestAt3360_block_13)
  (interval_append leafTestAt3360 14 15 16
  leafTestAt3360_block_14
  leafTestAt3360_block_15))))
  (interval_append leafTestAt3360 16 24 32
  (interval_append leafTestAt3360 16 20 24
  (interval_append leafTestAt3360 16 18 20
  (interval_append leafTestAt3360 16 17 18
  leafTestAt3360_block_16
  leafTestAt3360_block_17)
  (interval_append leafTestAt3360 18 19 20
  leafTestAt3360_block_18
  leafTestAt3360_block_19))
  (interval_append leafTestAt3360 20 22 24
  (interval_append leafTestAt3360 20 21 22
  leafTestAt3360_block_20
  leafTestAt3360_block_21)
  (interval_append leafTestAt3360 22 23 24
  leafTestAt3360_block_22
  leafTestAt3360_block_23)))
  (interval_append leafTestAt3360 24 28 32
  (interval_append leafTestAt3360 24 26 28
  (interval_append leafTestAt3360 24 25 26
  leafTestAt3360_block_24
  leafTestAt3360_block_25)
  (interval_append leafTestAt3360 26 27 28
  leafTestAt3360_block_26
  leafTestAt3360_block_27))
  (interval_append leafTestAt3360 28 30 32
  (interval_append leafTestAt3360 28 29 30
  leafTestAt3360_block_28
  leafTestAt3360_block_29)
  (interval_append leafTestAt3360 30 31 32
  leafTestAt3360_block_30
  leafTestAt3360_block_31)))))
cert_leafInterval 3360 3392
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
cert_leafTestAt 3392
cert_leafTestAt_block_2 3392 0 1
cert_leafTestAt_block_2 3392 1 2
cert_leafTestAt_block_2 3392 2 3
cert_leafTestAt_block_2 3392 3 4
cert_leafTestAt_block_2 3392 4 5
cert_leafTestAt_block_2 3392 5 6
cert_leafTestAt_block_2 3392 6 7
cert_leafTestAt_block_2 3392 7 8
cert_leafTestAt_block_2 3392 8 9
cert_leafTestAt_block_2 3392 9 10
cert_leafTestAt_block_2 3392 10 11
cert_leafTestAt_block_2 3392 11 12
cert_leafTestAt_block_2 3392 12 13
cert_leafTestAt_block_2 3392 13 14
cert_leafTestAt_block_2 3392 14 15
cert_leafTestAt_block_2 3392 15 16
cert_leafTestAt_block_2 3392 16 17
cert_leafTestAt_block_2 3392 17 18
cert_leafTestAt_block_2 3392 18 19
cert_leafTestAt_block_2 3392 19 20
cert_leafTestAt_block_2 3392 20 21
cert_leafTestAt_block_2 3392 21 22
cert_leafTestAt_block_2 3392 22 23
cert_leafTestAt_block_2 3392 23 24
cert_leafTestAt_block_2 3392 24 25
cert_leafTestAt_block_2 3392 25 26
cert_leafTestAt_block_2 3392 26 27
cert_leafTestAt_block_2 3392 27 28
cert_leafTestAt_block_2 3392 28 29
cert_leafTestAt_block_2 3392 29 30
cert_leafTestAt_block_2 3392 30 31
cert_leafTestAt_block_2 3392 31 32
theorem leafTestAt3392_complete : Interval leafTestAt3392 0 32 :=
  (interval_append leafTestAt3392 0 16 32
  (interval_append leafTestAt3392 0 8 16
  (interval_append leafTestAt3392 0 4 8
  (interval_append leafTestAt3392 0 2 4
  (interval_append leafTestAt3392 0 1 2
  leafTestAt3392_block_0
  leafTestAt3392_block_1)
  (interval_append leafTestAt3392 2 3 4
  leafTestAt3392_block_2
  leafTestAt3392_block_3))
  (interval_append leafTestAt3392 4 6 8
  (interval_append leafTestAt3392 4 5 6
  leafTestAt3392_block_4
  leafTestAt3392_block_5)
  (interval_append leafTestAt3392 6 7 8
  leafTestAt3392_block_6
  leafTestAt3392_block_7)))
  (interval_append leafTestAt3392 8 12 16
  (interval_append leafTestAt3392 8 10 12
  (interval_append leafTestAt3392 8 9 10
  leafTestAt3392_block_8
  leafTestAt3392_block_9)
  (interval_append leafTestAt3392 10 11 12
  leafTestAt3392_block_10
  leafTestAt3392_block_11))
  (interval_append leafTestAt3392 12 14 16
  (interval_append leafTestAt3392 12 13 14
  leafTestAt3392_block_12
  leafTestAt3392_block_13)
  (interval_append leafTestAt3392 14 15 16
  leafTestAt3392_block_14
  leafTestAt3392_block_15))))
  (interval_append leafTestAt3392 16 24 32
  (interval_append leafTestAt3392 16 20 24
  (interval_append leafTestAt3392 16 18 20
  (interval_append leafTestAt3392 16 17 18
  leafTestAt3392_block_16
  leafTestAt3392_block_17)
  (interval_append leafTestAt3392 18 19 20
  leafTestAt3392_block_18
  leafTestAt3392_block_19))
  (interval_append leafTestAt3392 20 22 24
  (interval_append leafTestAt3392 20 21 22
  leafTestAt3392_block_20
  leafTestAt3392_block_21)
  (interval_append leafTestAt3392 22 23 24
  leafTestAt3392_block_22
  leafTestAt3392_block_23)))
  (interval_append leafTestAt3392 24 28 32
  (interval_append leafTestAt3392 24 26 28
  (interval_append leafTestAt3392 24 25 26
  leafTestAt3392_block_24
  leafTestAt3392_block_25)
  (interval_append leafTestAt3392 26 27 28
  leafTestAt3392_block_26
  leafTestAt3392_block_27))
  (interval_append leafTestAt3392 28 30 32
  (interval_append leafTestAt3392 28 29 30
  leafTestAt3392_block_28
  leafTestAt3392_block_29)
  (interval_append leafTestAt3392 30 31 32
  leafTestAt3392_block_30
  leafTestAt3392_block_31)))))
cert_leafInterval 3392 3424
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
cert_leafTestAt 3424
cert_leafTestAt_block_2 3424 0 1
cert_leafTestAt_block_2 3424 1 2
cert_leafTestAt_block_2 3424 2 3
cert_leafTestAt_block_2 3424 3 4
cert_leafTestAt_block_2 3424 4 5
cert_leafTestAt_block_2 3424 5 6
cert_leafTestAt_block_2 3424 6 7
cert_leafTestAt_block_2 3424 7 8
cert_leafTestAt_block_2 3424 8 9
cert_leafTestAt_block_2 3424 9 10
cert_leafTestAt_block_2 3424 10 11
cert_leafTestAt_block_2 3424 11 12
cert_leafTestAt_block_2 3424 12 13
cert_leafTestAt_block_2 3424 13 14
cert_leafTestAt_block_2 3424 14 15
cert_leafTestAt_block_2 3424 15 16
cert_leafTestAt_block_2 3424 16 17
cert_leafTestAt_block_2 3424 17 18
cert_leafTestAt_block_2 3424 18 19
cert_leafTestAt_block_2 3424 19 20
cert_leafTestAt_block_2 3424 20 21
cert_leafTestAt_block_2 3424 21 22
cert_leafTestAt_block_2 3424 22 23
cert_leafTestAt_block_2 3424 23 24
cert_leafTestAt_block_2 3424 24 25
cert_leafTestAt_block_2 3424 25 26
cert_leafTestAt_block_2 3424 26 27
cert_leafTestAt_block_2 3424 27 28
cert_leafTestAt_block_2 3424 28 29
cert_leafTestAt_block_2 3424 29 30
cert_leafTestAt_block_2 3424 30 31
cert_leafTestAt_block_2 3424 31 32
theorem leafTestAt3424_complete : Interval leafTestAt3424 0 32 :=
  (interval_append leafTestAt3424 0 16 32
  (interval_append leafTestAt3424 0 8 16
  (interval_append leafTestAt3424 0 4 8
  (interval_append leafTestAt3424 0 2 4
  (interval_append leafTestAt3424 0 1 2
  leafTestAt3424_block_0
  leafTestAt3424_block_1)
  (interval_append leafTestAt3424 2 3 4
  leafTestAt3424_block_2
  leafTestAt3424_block_3))
  (interval_append leafTestAt3424 4 6 8
  (interval_append leafTestAt3424 4 5 6
  leafTestAt3424_block_4
  leafTestAt3424_block_5)
  (interval_append leafTestAt3424 6 7 8
  leafTestAt3424_block_6
  leafTestAt3424_block_7)))
  (interval_append leafTestAt3424 8 12 16
  (interval_append leafTestAt3424 8 10 12
  (interval_append leafTestAt3424 8 9 10
  leafTestAt3424_block_8
  leafTestAt3424_block_9)
  (interval_append leafTestAt3424 10 11 12
  leafTestAt3424_block_10
  leafTestAt3424_block_11))
  (interval_append leafTestAt3424 12 14 16
  (interval_append leafTestAt3424 12 13 14
  leafTestAt3424_block_12
  leafTestAt3424_block_13)
  (interval_append leafTestAt3424 14 15 16
  leafTestAt3424_block_14
  leafTestAt3424_block_15))))
  (interval_append leafTestAt3424 16 24 32
  (interval_append leafTestAt3424 16 20 24
  (interval_append leafTestAt3424 16 18 20
  (interval_append leafTestAt3424 16 17 18
  leafTestAt3424_block_16
  leafTestAt3424_block_17)
  (interval_append leafTestAt3424 18 19 20
  leafTestAt3424_block_18
  leafTestAt3424_block_19))
  (interval_append leafTestAt3424 20 22 24
  (interval_append leafTestAt3424 20 21 22
  leafTestAt3424_block_20
  leafTestAt3424_block_21)
  (interval_append leafTestAt3424 22 23 24
  leafTestAt3424_block_22
  leafTestAt3424_block_23)))
  (interval_append leafTestAt3424 24 28 32
  (interval_append leafTestAt3424 24 26 28
  (interval_append leafTestAt3424 24 25 26
  leafTestAt3424_block_24
  leafTestAt3424_block_25)
  (interval_append leafTestAt3424 26 27 28
  leafTestAt3424_block_26
  leafTestAt3424_block_27))
  (interval_append leafTestAt3424 28 30 32
  (interval_append leafTestAt3424 28 29 30
  leafTestAt3424_block_28
  leafTestAt3424_block_29)
  (interval_append leafTestAt3424 30 31 32
  leafTestAt3424_block_30
  leafTestAt3424_block_31)))))
cert_leafInterval 3424 3456
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
cert_leafTestAt 3456
cert_leafTestAt_block_2 3456 0 1
cert_leafTestAt_block_2 3456 1 2
cert_leafTestAt_block_2 3456 2 3
cert_leafTestAt_block_2 3456 3 4
cert_leafTestAt_block_2 3456 4 5
cert_leafTestAt_block_2 3456 5 6
cert_leafTestAt_block_2 3456 6 7
cert_leafTestAt_block_2 3456 7 8
cert_leafTestAt_block_2 3456 8 9
cert_leafTestAt_block_2 3456 9 10
cert_leafTestAt_block_2 3456 10 11
cert_leafTestAt_block_2 3456 11 12
cert_leafTestAt_block_2 3456 12 13
cert_leafTestAt_block_2 3456 13 14
cert_leafTestAt_block_2 3456 14 15
cert_leafTestAt_block_2 3456 15 16
cert_leafTestAt_block_2 3456 16 17
cert_leafTestAt_block_2 3456 17 18
cert_leafTestAt_block_2 3456 18 19
cert_leafTestAt_block_2 3456 19 20
cert_leafTestAt_block_2 3456 20 21
cert_leafTestAt_block_2 3456 21 22
cert_leafTestAt_block_2 3456 22 23
cert_leafTestAt_block_2 3456 23 24
cert_leafTestAt_block_2 3456 24 25
cert_leafTestAt_block_2 3456 25 26
cert_leafTestAt_block_2 3456 26 27
cert_leafTestAt_block_2 3456 27 28
cert_leafTestAt_block_2 3456 28 29
cert_leafTestAt_block_2 3456 29 30
cert_leafTestAt_block_2 3456 30 31
cert_leafTestAt_block_2 3456 31 32
theorem leafTestAt3456_complete : Interval leafTestAt3456 0 32 :=
  (interval_append leafTestAt3456 0 16 32
  (interval_append leafTestAt3456 0 8 16
  (interval_append leafTestAt3456 0 4 8
  (interval_append leafTestAt3456 0 2 4
  (interval_append leafTestAt3456 0 1 2
  leafTestAt3456_block_0
  leafTestAt3456_block_1)
  (interval_append leafTestAt3456 2 3 4
  leafTestAt3456_block_2
  leafTestAt3456_block_3))
  (interval_append leafTestAt3456 4 6 8
  (interval_append leafTestAt3456 4 5 6
  leafTestAt3456_block_4
  leafTestAt3456_block_5)
  (interval_append leafTestAt3456 6 7 8
  leafTestAt3456_block_6
  leafTestAt3456_block_7)))
  (interval_append leafTestAt3456 8 12 16
  (interval_append leafTestAt3456 8 10 12
  (interval_append leafTestAt3456 8 9 10
  leafTestAt3456_block_8
  leafTestAt3456_block_9)
  (interval_append leafTestAt3456 10 11 12
  leafTestAt3456_block_10
  leafTestAt3456_block_11))
  (interval_append leafTestAt3456 12 14 16
  (interval_append leafTestAt3456 12 13 14
  leafTestAt3456_block_12
  leafTestAt3456_block_13)
  (interval_append leafTestAt3456 14 15 16
  leafTestAt3456_block_14
  leafTestAt3456_block_15))))
  (interval_append leafTestAt3456 16 24 32
  (interval_append leafTestAt3456 16 20 24
  (interval_append leafTestAt3456 16 18 20
  (interval_append leafTestAt3456 16 17 18
  leafTestAt3456_block_16
  leafTestAt3456_block_17)
  (interval_append leafTestAt3456 18 19 20
  leafTestAt3456_block_18
  leafTestAt3456_block_19))
  (interval_append leafTestAt3456 20 22 24
  (interval_append leafTestAt3456 20 21 22
  leafTestAt3456_block_20
  leafTestAt3456_block_21)
  (interval_append leafTestAt3456 22 23 24
  leafTestAt3456_block_22
  leafTestAt3456_block_23)))
  (interval_append leafTestAt3456 24 28 32
  (interval_append leafTestAt3456 24 26 28
  (interval_append leafTestAt3456 24 25 26
  leafTestAt3456_block_24
  leafTestAt3456_block_25)
  (interval_append leafTestAt3456 26 27 28
  leafTestAt3456_block_26
  leafTestAt3456_block_27))
  (interval_append leafTestAt3456 28 30 32
  (interval_append leafTestAt3456 28 29 30
  leafTestAt3456_block_28
  leafTestAt3456_block_29)
  (interval_append leafTestAt3456 30 31 32
  leafTestAt3456_block_30
  leafTestAt3456_block_31)))))
cert_leafInterval 3456 3488
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
cert_leafTestAt 3488
cert_leafTestAt_block_2 3488 0 1
cert_leafTestAt_block_2 3488 1 2
cert_leafTestAt_block_2 3488 2 3
cert_leafTestAt_block_2 3488 3 4
cert_leafTestAt_block_2 3488 4 5
cert_leafTestAt_block_2 3488 5 6
cert_leafTestAt_block_2 3488 6 7
cert_leafTestAt_block_2 3488 7 8
cert_leafTestAt_block_2 3488 8 9
cert_leafTestAt_block_2 3488 9 10
cert_leafTestAt_block_2 3488 10 11
cert_leafTestAt_block_2 3488 11 12
cert_leafTestAt_block_2 3488 12 13
cert_leafTestAt_block_2 3488 13 14
cert_leafTestAt_block_2 3488 14 15
cert_leafTestAt_block_2 3488 15 16
cert_leafTestAt_block_2 3488 16 17
cert_leafTestAt_block_2 3488 17 18
cert_leafTestAt_block_2 3488 18 19
cert_leafTestAt_block_2 3488 19 20
cert_leafTestAt_block_2 3488 20 21
cert_leafTestAt_block_2 3488 21 22
cert_leafTestAt_block_2 3488 22 23
cert_leafTestAt_block_2 3488 23 24
cert_leafTestAt_block_2 3488 24 25
cert_leafTestAt_block_2 3488 25 26
cert_leafTestAt_block_2 3488 26 27
cert_leafTestAt_block_2 3488 27 28
cert_leafTestAt_block_2 3488 28 29
cert_leafTestAt_block_2 3488 29 30
cert_leafTestAt_block_2 3488 30 31
cert_leafTestAt_block_2 3488 31 32
theorem leafTestAt3488_complete : Interval leafTestAt3488 0 32 :=
  (interval_append leafTestAt3488 0 16 32
  (interval_append leafTestAt3488 0 8 16
  (interval_append leafTestAt3488 0 4 8
  (interval_append leafTestAt3488 0 2 4
  (interval_append leafTestAt3488 0 1 2
  leafTestAt3488_block_0
  leafTestAt3488_block_1)
  (interval_append leafTestAt3488 2 3 4
  leafTestAt3488_block_2
  leafTestAt3488_block_3))
  (interval_append leafTestAt3488 4 6 8
  (interval_append leafTestAt3488 4 5 6
  leafTestAt3488_block_4
  leafTestAt3488_block_5)
  (interval_append leafTestAt3488 6 7 8
  leafTestAt3488_block_6
  leafTestAt3488_block_7)))
  (interval_append leafTestAt3488 8 12 16
  (interval_append leafTestAt3488 8 10 12
  (interval_append leafTestAt3488 8 9 10
  leafTestAt3488_block_8
  leafTestAt3488_block_9)
  (interval_append leafTestAt3488 10 11 12
  leafTestAt3488_block_10
  leafTestAt3488_block_11))
  (interval_append leafTestAt3488 12 14 16
  (interval_append leafTestAt3488 12 13 14
  leafTestAt3488_block_12
  leafTestAt3488_block_13)
  (interval_append leafTestAt3488 14 15 16
  leafTestAt3488_block_14
  leafTestAt3488_block_15))))
  (interval_append leafTestAt3488 16 24 32
  (interval_append leafTestAt3488 16 20 24
  (interval_append leafTestAt3488 16 18 20
  (interval_append leafTestAt3488 16 17 18
  leafTestAt3488_block_16
  leafTestAt3488_block_17)
  (interval_append leafTestAt3488 18 19 20
  leafTestAt3488_block_18
  leafTestAt3488_block_19))
  (interval_append leafTestAt3488 20 22 24
  (interval_append leafTestAt3488 20 21 22
  leafTestAt3488_block_20
  leafTestAt3488_block_21)
  (interval_append leafTestAt3488 22 23 24
  leafTestAt3488_block_22
  leafTestAt3488_block_23)))
  (interval_append leafTestAt3488 24 28 32
  (interval_append leafTestAt3488 24 26 28
  (interval_append leafTestAt3488 24 25 26
  leafTestAt3488_block_24
  leafTestAt3488_block_25)
  (interval_append leafTestAt3488 26 27 28
  leafTestAt3488_block_26
  leafTestAt3488_block_27))
  (interval_append leafTestAt3488 28 30 32
  (interval_append leafTestAt3488 28 29 30
  leafTestAt3488_block_28
  leafTestAt3488_block_29)
  (interval_append leafTestAt3488 30 31 32
  leafTestAt3488_block_30
  leafTestAt3488_block_31)))))
cert_leafInterval 3488 3520
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
cert_leafTestAt 3520
cert_leafTestAt_block_2 3520 0 1
cert_leafTestAt_block_2 3520 1 2
cert_leafTestAt_block_2 3520 2 3
cert_leafTestAt_block_2 3520 3 4
cert_leafTestAt_block_2 3520 4 5
cert_leafTestAt_block_2 3520 5 6
cert_leafTestAt_block_2 3520 6 7
cert_leafTestAt_block_2 3520 7 8
cert_leafTestAt_block_2 3520 8 9
cert_leafTestAt_block_2 3520 9 10
cert_leafTestAt_block_2 3520 10 11
cert_leafTestAt_block_2 3520 11 12
cert_leafTestAt_block_2 3520 12 13
cert_leafTestAt_block_2 3520 13 14
cert_leafTestAt_block_2 3520 14 15
cert_leafTestAt_block_2 3520 15 16
cert_leafTestAt_block_2 3520 16 17
cert_leafTestAt_block_2 3520 17 18
cert_leafTestAt_block_2 3520 18 19
cert_leafTestAt_block_2 3520 19 20
cert_leafTestAt_block_2 3520 20 21
cert_leafTestAt_block_2 3520 21 22
cert_leafTestAt_block_2 3520 22 23
cert_leafTestAt_block_2 3520 23 24
cert_leafTestAt_block_2 3520 24 25
cert_leafTestAt_block_2 3520 25 26
cert_leafTestAt_block_2 3520 26 27
cert_leafTestAt_block_2 3520 27 28
cert_leafTestAt_block_2 3520 28 29
cert_leafTestAt_block_2 3520 29 30
cert_leafTestAt_block_2 3520 30 31
cert_leafTestAt_block_2 3520 31 32
theorem leafTestAt3520_complete : Interval leafTestAt3520 0 32 :=
  (interval_append leafTestAt3520 0 16 32
  (interval_append leafTestAt3520 0 8 16
  (interval_append leafTestAt3520 0 4 8
  (interval_append leafTestAt3520 0 2 4
  (interval_append leafTestAt3520 0 1 2
  leafTestAt3520_block_0
  leafTestAt3520_block_1)
  (interval_append leafTestAt3520 2 3 4
  leafTestAt3520_block_2
  leafTestAt3520_block_3))
  (interval_append leafTestAt3520 4 6 8
  (interval_append leafTestAt3520 4 5 6
  leafTestAt3520_block_4
  leafTestAt3520_block_5)
  (interval_append leafTestAt3520 6 7 8
  leafTestAt3520_block_6
  leafTestAt3520_block_7)))
  (interval_append leafTestAt3520 8 12 16
  (interval_append leafTestAt3520 8 10 12
  (interval_append leafTestAt3520 8 9 10
  leafTestAt3520_block_8
  leafTestAt3520_block_9)
  (interval_append leafTestAt3520 10 11 12
  leafTestAt3520_block_10
  leafTestAt3520_block_11))
  (interval_append leafTestAt3520 12 14 16
  (interval_append leafTestAt3520 12 13 14
  leafTestAt3520_block_12
  leafTestAt3520_block_13)
  (interval_append leafTestAt3520 14 15 16
  leafTestAt3520_block_14
  leafTestAt3520_block_15))))
  (interval_append leafTestAt3520 16 24 32
  (interval_append leafTestAt3520 16 20 24
  (interval_append leafTestAt3520 16 18 20
  (interval_append leafTestAt3520 16 17 18
  leafTestAt3520_block_16
  leafTestAt3520_block_17)
  (interval_append leafTestAt3520 18 19 20
  leafTestAt3520_block_18
  leafTestAt3520_block_19))
  (interval_append leafTestAt3520 20 22 24
  (interval_append leafTestAt3520 20 21 22
  leafTestAt3520_block_20
  leafTestAt3520_block_21)
  (interval_append leafTestAt3520 22 23 24
  leafTestAt3520_block_22
  leafTestAt3520_block_23)))
  (interval_append leafTestAt3520 24 28 32
  (interval_append leafTestAt3520 24 26 28
  (interval_append leafTestAt3520 24 25 26
  leafTestAt3520_block_24
  leafTestAt3520_block_25)
  (interval_append leafTestAt3520 26 27 28
  leafTestAt3520_block_26
  leafTestAt3520_block_27))
  (interval_append leafTestAt3520 28 30 32
  (interval_append leafTestAt3520 28 29 30
  leafTestAt3520_block_28
  leafTestAt3520_block_29)
  (interval_append leafTestAt3520 30 31 32
  leafTestAt3520_block_30
  leafTestAt3520_block_31)))))
cert_leafInterval 3520 3552
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
cert_leafTestAt 3552
cert_leafTestAt_block_2 3552 0 1
cert_leafTestAt_block_2 3552 1 2
cert_leafTestAt_block_2 3552 2 3
cert_leafTestAt_block_2 3552 3 4
cert_leafTestAt_block_2 3552 4 5
cert_leafTestAt_block_2 3552 5 6
cert_leafTestAt_block_2 3552 6 7
cert_leafTestAt_block_2 3552 7 8
cert_leafTestAt_block_2 3552 8 9
cert_leafTestAt_block_2 3552 9 10
cert_leafTestAt_block_2 3552 10 11
cert_leafTestAt_block_2 3552 11 12
cert_leafTestAt_block_2 3552 12 13
cert_leafTestAt_block_2 3552 13 14
cert_leafTestAt_block_2 3552 14 15
cert_leafTestAt_block_2 3552 15 16
cert_leafTestAt_block_2 3552 16 17
cert_leafTestAt_block_2 3552 17 18
cert_leafTestAt_block_2 3552 18 19
cert_leafTestAt_block_2 3552 19 20
cert_leafTestAt_block_2 3552 20 21
cert_leafTestAt_block_2 3552 21 22
cert_leafTestAt_block_2 3552 22 23
cert_leafTestAt_block_2 3552 23 24
cert_leafTestAt_block_2 3552 24 25
cert_leafTestAt_block_2 3552 25 26
cert_leafTestAt_block_2 3552 26 27
cert_leafTestAt_block_2 3552 27 28
cert_leafTestAt_block_2 3552 28 29
cert_leafTestAt_block_2 3552 29 30
cert_leafTestAt_block_2 3552 30 31
cert_leafTestAt_block_2 3552 31 32
theorem leafTestAt3552_complete : Interval leafTestAt3552 0 32 :=
  (interval_append leafTestAt3552 0 16 32
  (interval_append leafTestAt3552 0 8 16
  (interval_append leafTestAt3552 0 4 8
  (interval_append leafTestAt3552 0 2 4
  (interval_append leafTestAt3552 0 1 2
  leafTestAt3552_block_0
  leafTestAt3552_block_1)
  (interval_append leafTestAt3552 2 3 4
  leafTestAt3552_block_2
  leafTestAt3552_block_3))
  (interval_append leafTestAt3552 4 6 8
  (interval_append leafTestAt3552 4 5 6
  leafTestAt3552_block_4
  leafTestAt3552_block_5)
  (interval_append leafTestAt3552 6 7 8
  leafTestAt3552_block_6
  leafTestAt3552_block_7)))
  (interval_append leafTestAt3552 8 12 16
  (interval_append leafTestAt3552 8 10 12
  (interval_append leafTestAt3552 8 9 10
  leafTestAt3552_block_8
  leafTestAt3552_block_9)
  (interval_append leafTestAt3552 10 11 12
  leafTestAt3552_block_10
  leafTestAt3552_block_11))
  (interval_append leafTestAt3552 12 14 16
  (interval_append leafTestAt3552 12 13 14
  leafTestAt3552_block_12
  leafTestAt3552_block_13)
  (interval_append leafTestAt3552 14 15 16
  leafTestAt3552_block_14
  leafTestAt3552_block_15))))
  (interval_append leafTestAt3552 16 24 32
  (interval_append leafTestAt3552 16 20 24
  (interval_append leafTestAt3552 16 18 20
  (interval_append leafTestAt3552 16 17 18
  leafTestAt3552_block_16
  leafTestAt3552_block_17)
  (interval_append leafTestAt3552 18 19 20
  leafTestAt3552_block_18
  leafTestAt3552_block_19))
  (interval_append leafTestAt3552 20 22 24
  (interval_append leafTestAt3552 20 21 22
  leafTestAt3552_block_20
  leafTestAt3552_block_21)
  (interval_append leafTestAt3552 22 23 24
  leafTestAt3552_block_22
  leafTestAt3552_block_23)))
  (interval_append leafTestAt3552 24 28 32
  (interval_append leafTestAt3552 24 26 28
  (interval_append leafTestAt3552 24 25 26
  leafTestAt3552_block_24
  leafTestAt3552_block_25)
  (interval_append leafTestAt3552 26 27 28
  leafTestAt3552_block_26
  leafTestAt3552_block_27))
  (interval_append leafTestAt3552 28 30 32
  (interval_append leafTestAt3552 28 29 30
  leafTestAt3552_block_28
  leafTestAt3552_block_29)
  (interval_append leafTestAt3552 30 31 32
  leafTestAt3552_block_30
  leafTestAt3552_block_31)))))
cert_leafInterval 3552 3584
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0355
end
end
