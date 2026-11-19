module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0695Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 0
cert_leafTestAt_block_2 0 0 1
cert_leafTestAt_block_2 0 1 2
cert_leafTestAt_block_2 0 2 3
cert_leafTestAt_block_2 0 3 4
cert_leafTestAt_block_2 0 4 5
cert_leafTestAt_block_2 0 5 6
cert_leafTestAt_block_2 0 6 7
cert_leafTestAt_block_2 0 7 8
cert_leafTestAt_block_2 0 8 9
cert_leafTestAt_block_2 0 9 10
cert_leafTestAt_block_2 0 10 11
cert_leafTestAt_block_2 0 11 12
cert_leafTestAt_block_2 0 12 13
cert_leafTestAt_block_2 0 13 14
cert_leafTestAt_block_2 0 14 15
cert_leafTestAt_block_2 0 15 16
cert_leafTestAt_block_2 0 16 17
cert_leafTestAt_block_2 0 17 18
cert_leafTestAt_block_2 0 18 19
cert_leafTestAt_block_2 0 19 20
cert_leafTestAt_block_2 0 20 21
cert_leafTestAt_block_2 0 21 22
cert_leafTestAt_block_2 0 22 23
cert_leafTestAt_block_2 0 23 24
cert_leafTestAt_block_2 0 24 25
cert_leafTestAt_block_2 0 25 26
cert_leafTestAt_block_2 0 26 27
cert_leafTestAt_block_2 0 27 28
cert_leafTestAt_block_2 0 28 29
cert_leafTestAt_block_2 0 29 30
cert_leafTestAt_block_2 0 30 31
cert_leafTestAt_block_2 0 31 32
theorem leafTestAt0_complete : Interval leafTestAt0 0 32 :=
  (interval_append leafTestAt0 0 16 32
  (interval_append leafTestAt0 0 8 16
  (interval_append leafTestAt0 0 4 8
  (interval_append leafTestAt0 0 2 4
  (interval_append leafTestAt0 0 1 2
  leafTestAt0_block_0
  leafTestAt0_block_1)
  (interval_append leafTestAt0 2 3 4
  leafTestAt0_block_2
  leafTestAt0_block_3))
  (interval_append leafTestAt0 4 6 8
  (interval_append leafTestAt0 4 5 6
  leafTestAt0_block_4
  leafTestAt0_block_5)
  (interval_append leafTestAt0 6 7 8
  leafTestAt0_block_6
  leafTestAt0_block_7)))
  (interval_append leafTestAt0 8 12 16
  (interval_append leafTestAt0 8 10 12
  (interval_append leafTestAt0 8 9 10
  leafTestAt0_block_8
  leafTestAt0_block_9)
  (interval_append leafTestAt0 10 11 12
  leafTestAt0_block_10
  leafTestAt0_block_11))
  (interval_append leafTestAt0 12 14 16
  (interval_append leafTestAt0 12 13 14
  leafTestAt0_block_12
  leafTestAt0_block_13)
  (interval_append leafTestAt0 14 15 16
  leafTestAt0_block_14
  leafTestAt0_block_15))))
  (interval_append leafTestAt0 16 24 32
  (interval_append leafTestAt0 16 20 24
  (interval_append leafTestAt0 16 18 20
  (interval_append leafTestAt0 16 17 18
  leafTestAt0_block_16
  leafTestAt0_block_17)
  (interval_append leafTestAt0 18 19 20
  leafTestAt0_block_18
  leafTestAt0_block_19))
  (interval_append leafTestAt0 20 22 24
  (interval_append leafTestAt0 20 21 22
  leafTestAt0_block_20
  leafTestAt0_block_21)
  (interval_append leafTestAt0 22 23 24
  leafTestAt0_block_22
  leafTestAt0_block_23)))
  (interval_append leafTestAt0 24 28 32
  (interval_append leafTestAt0 24 26 28
  (interval_append leafTestAt0 24 25 26
  leafTestAt0_block_24
  leafTestAt0_block_25)
  (interval_append leafTestAt0 26 27 28
  leafTestAt0_block_26
  leafTestAt0_block_27))
  (interval_append leafTestAt0 28 30 32
  (interval_append leafTestAt0 28 29 30
  leafTestAt0_block_28
  leafTestAt0_block_29)
  (interval_append leafTestAt0 30 31 32
  leafTestAt0_block_30
  leafTestAt0_block_31)))))
cert_leafInterval 0 32
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 32
cert_leafTestAt_block_2 32 0 1
cert_leafTestAt_block_2 32 1 2
cert_leafTestAt_block_2 32 2 3
cert_leafTestAt_block_2 32 3 4
cert_leafTestAt_block_2 32 4 5
cert_leafTestAt_block_2 32 5 6
cert_leafTestAt_block_2 32 6 7
cert_leafTestAt_block_2 32 7 8
cert_leafTestAt_block_2 32 8 9
cert_leafTestAt_block_2 32 9 10
cert_leafTestAt_block_2 32 10 11
cert_leafTestAt_block_2 32 11 12
cert_leafTestAt_block_2 32 12 13
cert_leafTestAt_block_2 32 13 14
cert_leafTestAt_block_2 32 14 15
cert_leafTestAt_block_2 32 15 16
cert_leafTestAt_block_2 32 16 17
cert_leafTestAt_block_2 32 17 18
cert_leafTestAt_block_2 32 18 19
cert_leafTestAt_block_2 32 19 20
cert_leafTestAt_block_2 32 20 21
cert_leafTestAt_block_2 32 21 22
cert_leafTestAt_block_2 32 22 23
cert_leafTestAt_block_2 32 23 24
cert_leafTestAt_block_2 32 24 25
cert_leafTestAt_block_2 32 25 26
cert_leafTestAt_block_2 32 26 27
cert_leafTestAt_block_2 32 27 28
cert_leafTestAt_block_2 32 28 29
cert_leafTestAt_block_2 32 29 30
cert_leafTestAt_block_2 32 30 31
cert_leafTestAt_block_2 32 31 32
theorem leafTestAt32_complete : Interval leafTestAt32 0 32 :=
  (interval_append leafTestAt32 0 16 32
  (interval_append leafTestAt32 0 8 16
  (interval_append leafTestAt32 0 4 8
  (interval_append leafTestAt32 0 2 4
  (interval_append leafTestAt32 0 1 2
  leafTestAt32_block_0
  leafTestAt32_block_1)
  (interval_append leafTestAt32 2 3 4
  leafTestAt32_block_2
  leafTestAt32_block_3))
  (interval_append leafTestAt32 4 6 8
  (interval_append leafTestAt32 4 5 6
  leafTestAt32_block_4
  leafTestAt32_block_5)
  (interval_append leafTestAt32 6 7 8
  leafTestAt32_block_6
  leafTestAt32_block_7)))
  (interval_append leafTestAt32 8 12 16
  (interval_append leafTestAt32 8 10 12
  (interval_append leafTestAt32 8 9 10
  leafTestAt32_block_8
  leafTestAt32_block_9)
  (interval_append leafTestAt32 10 11 12
  leafTestAt32_block_10
  leafTestAt32_block_11))
  (interval_append leafTestAt32 12 14 16
  (interval_append leafTestAt32 12 13 14
  leafTestAt32_block_12
  leafTestAt32_block_13)
  (interval_append leafTestAt32 14 15 16
  leafTestAt32_block_14
  leafTestAt32_block_15))))
  (interval_append leafTestAt32 16 24 32
  (interval_append leafTestAt32 16 20 24
  (interval_append leafTestAt32 16 18 20
  (interval_append leafTestAt32 16 17 18
  leafTestAt32_block_16
  leafTestAt32_block_17)
  (interval_append leafTestAt32 18 19 20
  leafTestAt32_block_18
  leafTestAt32_block_19))
  (interval_append leafTestAt32 20 22 24
  (interval_append leafTestAt32 20 21 22
  leafTestAt32_block_20
  leafTestAt32_block_21)
  (interval_append leafTestAt32 22 23 24
  leafTestAt32_block_22
  leafTestAt32_block_23)))
  (interval_append leafTestAt32 24 28 32
  (interval_append leafTestAt32 24 26 28
  (interval_append leafTestAt32 24 25 26
  leafTestAt32_block_24
  leafTestAt32_block_25)
  (interval_append leafTestAt32 26 27 28
  leafTestAt32_block_26
  leafTestAt32_block_27))
  (interval_append leafTestAt32 28 30 32
  (interval_append leafTestAt32 28 29 30
  leafTestAt32_block_28
  leafTestAt32_block_29)
  (interval_append leafTestAt32 30 31 32
  leafTestAt32_block_30
  leafTestAt32_block_31)))))
cert_leafInterval 32 64
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 64
cert_leafTestAt_block_2 64 0 1
cert_leafTestAt_block_2 64 1 2
cert_leafTestAt_block_2 64 2 3
cert_leafTestAt_block_2 64 3 4
cert_leafTestAt_block_2 64 4 5
cert_leafTestAt_block_2 64 5 6
cert_leafTestAt_block_2 64 6 7
cert_leafTestAt_block_2 64 7 8
cert_leafTestAt_block_2 64 8 9
cert_leafTestAt_block_2 64 9 10
cert_leafTestAt_block_2 64 10 11
cert_leafTestAt_block_2 64 11 12
cert_leafTestAt_block_2 64 12 13
cert_leafTestAt_block_2 64 13 14
cert_leafTestAt_block_2 64 14 15
cert_leafTestAt_block_2 64 15 16
cert_leafTestAt_block_2 64 16 17
cert_leafTestAt_block_2 64 17 18
cert_leafTestAt_block_2 64 18 19
cert_leafTestAt_block_2 64 19 20
cert_leafTestAt_block_2 64 20 21
cert_leafTestAt_block_2 64 21 22
cert_leafTestAt_block_2 64 22 23
cert_leafTestAt_block_2 64 23 24
cert_leafTestAt_block_2 64 24 25
cert_leafTestAt_block_2 64 25 26
cert_leafTestAt_block_2 64 26 27
cert_leafTestAt_block_2 64 27 28
cert_leafTestAt_block_2 64 28 29
cert_leafTestAt_block_2 64 29 30
cert_leafTestAt_block_2 64 30 31
cert_leafTestAt_block_2 64 31 32
theorem leafTestAt64_complete : Interval leafTestAt64 0 32 :=
  (interval_append leafTestAt64 0 16 32
  (interval_append leafTestAt64 0 8 16
  (interval_append leafTestAt64 0 4 8
  (interval_append leafTestAt64 0 2 4
  (interval_append leafTestAt64 0 1 2
  leafTestAt64_block_0
  leafTestAt64_block_1)
  (interval_append leafTestAt64 2 3 4
  leafTestAt64_block_2
  leafTestAt64_block_3))
  (interval_append leafTestAt64 4 6 8
  (interval_append leafTestAt64 4 5 6
  leafTestAt64_block_4
  leafTestAt64_block_5)
  (interval_append leafTestAt64 6 7 8
  leafTestAt64_block_6
  leafTestAt64_block_7)))
  (interval_append leafTestAt64 8 12 16
  (interval_append leafTestAt64 8 10 12
  (interval_append leafTestAt64 8 9 10
  leafTestAt64_block_8
  leafTestAt64_block_9)
  (interval_append leafTestAt64 10 11 12
  leafTestAt64_block_10
  leafTestAt64_block_11))
  (interval_append leafTestAt64 12 14 16
  (interval_append leafTestAt64 12 13 14
  leafTestAt64_block_12
  leafTestAt64_block_13)
  (interval_append leafTestAt64 14 15 16
  leafTestAt64_block_14
  leafTestAt64_block_15))))
  (interval_append leafTestAt64 16 24 32
  (interval_append leafTestAt64 16 20 24
  (interval_append leafTestAt64 16 18 20
  (interval_append leafTestAt64 16 17 18
  leafTestAt64_block_16
  leafTestAt64_block_17)
  (interval_append leafTestAt64 18 19 20
  leafTestAt64_block_18
  leafTestAt64_block_19))
  (interval_append leafTestAt64 20 22 24
  (interval_append leafTestAt64 20 21 22
  leafTestAt64_block_20
  leafTestAt64_block_21)
  (interval_append leafTestAt64 22 23 24
  leafTestAt64_block_22
  leafTestAt64_block_23)))
  (interval_append leafTestAt64 24 28 32
  (interval_append leafTestAt64 24 26 28
  (interval_append leafTestAt64 24 25 26
  leafTestAt64_block_24
  leafTestAt64_block_25)
  (interval_append leafTestAt64 26 27 28
  leafTestAt64_block_26
  leafTestAt64_block_27))
  (interval_append leafTestAt64 28 30 32
  (interval_append leafTestAt64 28 29 30
  leafTestAt64_block_28
  leafTestAt64_block_29)
  (interval_append leafTestAt64 30 31 32
  leafTestAt64_block_30
  leafTestAt64_block_31)))))
cert_leafInterval 64 96
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 96
cert_leafTestAt_block_2 96 0 1
cert_leafTestAt_block_2 96 1 2
cert_leafTestAt_block_2 96 2 3
cert_leafTestAt_block_2 96 3 4
cert_leafTestAt_block_2 96 4 5
cert_leafTestAt_block_2 96 5 6
cert_leafTestAt_block_2 96 6 7
cert_leafTestAt_block_2 96 7 8
cert_leafTestAt_block_2 96 8 9
cert_leafTestAt_block_2 96 9 10
cert_leafTestAt_block_2 96 10 11
cert_leafTestAt_block_2 96 11 12
cert_leafTestAt_block_2 96 12 13
cert_leafTestAt_block_2 96 13 14
cert_leafTestAt_block_2 96 14 15
cert_leafTestAt_block_2 96 15 16
cert_leafTestAt_block_2 96 16 17
cert_leafTestAt_block_2 96 17 18
cert_leafTestAt_block_2 96 18 19
cert_leafTestAt_block_2 96 19 20
cert_leafTestAt_block_2 96 20 21
cert_leafTestAt_block_2 96 21 22
cert_leafTestAt_block_2 96 22 23
cert_leafTestAt_block_2 96 23 24
cert_leafTestAt_block_2 96 24 25
cert_leafTestAt_block_2 96 25 26
cert_leafTestAt_block_2 96 26 27
cert_leafTestAt_block_2 96 27 28
cert_leafTestAt_block_2 96 28 29
cert_leafTestAt_block_2 96 29 30
cert_leafTestAt_block_2 96 30 31
cert_leafTestAt_block_2 96 31 32
theorem leafTestAt96_complete : Interval leafTestAt96 0 32 :=
  (interval_append leafTestAt96 0 16 32
  (interval_append leafTestAt96 0 8 16
  (interval_append leafTestAt96 0 4 8
  (interval_append leafTestAt96 0 2 4
  (interval_append leafTestAt96 0 1 2
  leafTestAt96_block_0
  leafTestAt96_block_1)
  (interval_append leafTestAt96 2 3 4
  leafTestAt96_block_2
  leafTestAt96_block_3))
  (interval_append leafTestAt96 4 6 8
  (interval_append leafTestAt96 4 5 6
  leafTestAt96_block_4
  leafTestAt96_block_5)
  (interval_append leafTestAt96 6 7 8
  leafTestAt96_block_6
  leafTestAt96_block_7)))
  (interval_append leafTestAt96 8 12 16
  (interval_append leafTestAt96 8 10 12
  (interval_append leafTestAt96 8 9 10
  leafTestAt96_block_8
  leafTestAt96_block_9)
  (interval_append leafTestAt96 10 11 12
  leafTestAt96_block_10
  leafTestAt96_block_11))
  (interval_append leafTestAt96 12 14 16
  (interval_append leafTestAt96 12 13 14
  leafTestAt96_block_12
  leafTestAt96_block_13)
  (interval_append leafTestAt96 14 15 16
  leafTestAt96_block_14
  leafTestAt96_block_15))))
  (interval_append leafTestAt96 16 24 32
  (interval_append leafTestAt96 16 20 24
  (interval_append leafTestAt96 16 18 20
  (interval_append leafTestAt96 16 17 18
  leafTestAt96_block_16
  leafTestAt96_block_17)
  (interval_append leafTestAt96 18 19 20
  leafTestAt96_block_18
  leafTestAt96_block_19))
  (interval_append leafTestAt96 20 22 24
  (interval_append leafTestAt96 20 21 22
  leafTestAt96_block_20
  leafTestAt96_block_21)
  (interval_append leafTestAt96 22 23 24
  leafTestAt96_block_22
  leafTestAt96_block_23)))
  (interval_append leafTestAt96 24 28 32
  (interval_append leafTestAt96 24 26 28
  (interval_append leafTestAt96 24 25 26
  leafTestAt96_block_24
  leafTestAt96_block_25)
  (interval_append leafTestAt96 26 27 28
  leafTestAt96_block_26
  leafTestAt96_block_27))
  (interval_append leafTestAt96 28 30 32
  (interval_append leafTestAt96 28 29 30
  leafTestAt96_block_28
  leafTestAt96_block_29)
  (interval_append leafTestAt96 30 31 32
  leafTestAt96_block_30
  leafTestAt96_block_31)))))
cert_leafInterval 96 128
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 128
cert_leafTestAt_block_2 128 0 1
cert_leafTestAt_block_2 128 1 2
cert_leafTestAt_block_2 128 2 3
cert_leafTestAt_block_2 128 3 4
cert_leafTestAt_block_2 128 4 5
cert_leafTestAt_block_2 128 5 6
cert_leafTestAt_block_2 128 6 7
cert_leafTestAt_block_2 128 7 8
cert_leafTestAt_block_2 128 8 9
cert_leafTestAt_block_2 128 9 10
theorem leafTestAt128_complete : Interval leafTestAt128 0 10 :=
  (interval_append leafTestAt128 0 5 10
  (interval_append leafTestAt128 0 2 5
  (interval_append leafTestAt128 0 1 2
  leafTestAt128_block_0
  leafTestAt128_block_1)
  (interval_append leafTestAt128 2 3 5
  leafTestAt128_block_2
  (interval_append leafTestAt128 3 4 5
  leafTestAt128_block_3
  leafTestAt128_block_4)))
  (interval_append leafTestAt128 5 7 10
  (interval_append leafTestAt128 5 6 7
  leafTestAt128_block_5
  leafTestAt128_block_6)
  (interval_append leafTestAt128 7 8 10
  leafTestAt128_block_7
  (interval_append leafTestAt128 8 9 10
  leafTestAt128_block_8
  leafTestAt128_block_9))))
cert_leafInterval 128 138
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0695
end
end
