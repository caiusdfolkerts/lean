module
prelude
public meta import LowerSchemas.FiniteRootedSubsumedForest.Part0
public import RootedSubsumedForest0338Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
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
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
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
cert_leafTestAt_block_2 128 10 11
cert_leafTestAt_block_2 128 11 12
cert_leafTestAt_block_2 128 12 13
cert_leafTestAt_block_2 128 13 14
cert_leafTestAt_block_2 128 14 15
cert_leafTestAt_block_2 128 15 16
cert_leafTestAt_block_2 128 16 17
cert_leafTestAt_block_2 128 17 18
cert_leafTestAt_block_2 128 18 19
cert_leafTestAt_block_2 128 19 20
cert_leafTestAt_block_2 128 20 21
cert_leafTestAt_block_2 128 21 22
cert_leafTestAt_block_2 128 22 23
cert_leafTestAt_block_2 128 23 24
cert_leafTestAt_block_2 128 24 25
cert_leafTestAt_block_2 128 25 26
cert_leafTestAt_block_2 128 26 27
cert_leafTestAt_block_2 128 27 28
cert_leafTestAt_block_2 128 28 29
cert_leafTestAt_block_2 128 29 30
cert_leafTestAt_block_2 128 30 31
cert_leafTestAt_block_2 128 31 32
theorem leafTestAt128_complete : Interval leafTestAt128 0 32 :=
  (interval_append leafTestAt128 0 16 32
  (interval_append leafTestAt128 0 8 16
  (interval_append leafTestAt128 0 4 8
  (interval_append leafTestAt128 0 2 4
  (interval_append leafTestAt128 0 1 2
  leafTestAt128_block_0
  leafTestAt128_block_1)
  (interval_append leafTestAt128 2 3 4
  leafTestAt128_block_2
  leafTestAt128_block_3))
  (interval_append leafTestAt128 4 6 8
  (interval_append leafTestAt128 4 5 6
  leafTestAt128_block_4
  leafTestAt128_block_5)
  (interval_append leafTestAt128 6 7 8
  leafTestAt128_block_6
  leafTestAt128_block_7)))
  (interval_append leafTestAt128 8 12 16
  (interval_append leafTestAt128 8 10 12
  (interval_append leafTestAt128 8 9 10
  leafTestAt128_block_8
  leafTestAt128_block_9)
  (interval_append leafTestAt128 10 11 12
  leafTestAt128_block_10
  leafTestAt128_block_11))
  (interval_append leafTestAt128 12 14 16
  (interval_append leafTestAt128 12 13 14
  leafTestAt128_block_12
  leafTestAt128_block_13)
  (interval_append leafTestAt128 14 15 16
  leafTestAt128_block_14
  leafTestAt128_block_15))))
  (interval_append leafTestAt128 16 24 32
  (interval_append leafTestAt128 16 20 24
  (interval_append leafTestAt128 16 18 20
  (interval_append leafTestAt128 16 17 18
  leafTestAt128_block_16
  leafTestAt128_block_17)
  (interval_append leafTestAt128 18 19 20
  leafTestAt128_block_18
  leafTestAt128_block_19))
  (interval_append leafTestAt128 20 22 24
  (interval_append leafTestAt128 20 21 22
  leafTestAt128_block_20
  leafTestAt128_block_21)
  (interval_append leafTestAt128 22 23 24
  leafTestAt128_block_22
  leafTestAt128_block_23)))
  (interval_append leafTestAt128 24 28 32
  (interval_append leafTestAt128 24 26 28
  (interval_append leafTestAt128 24 25 26
  leafTestAt128_block_24
  leafTestAt128_block_25)
  (interval_append leafTestAt128 26 27 28
  leafTestAt128_block_26
  leafTestAt128_block_27))
  (interval_append leafTestAt128 28 30 32
  (interval_append leafTestAt128 28 29 30
  leafTestAt128_block_28
  leafTestAt128_block_29)
  (interval_append leafTestAt128 30 31 32
  leafTestAt128_block_30
  leafTestAt128_block_31)))))
cert_leafInterval 128 160
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 160
cert_leafTestAt_block_2 160 0 1
cert_leafTestAt_block_2 160 1 2
cert_leafTestAt_block_2 160 2 3
cert_leafTestAt_block_2 160 3 4
cert_leafTestAt_block_2 160 4 5
cert_leafTestAt_block_2 160 5 6
cert_leafTestAt_block_2 160 6 7
cert_leafTestAt_block_2 160 7 8
cert_leafTestAt_block_2 160 8 9
cert_leafTestAt_block_2 160 9 10
cert_leafTestAt_block_2 160 10 11
cert_leafTestAt_block_2 160 11 12
cert_leafTestAt_block_2 160 12 13
cert_leafTestAt_block_2 160 13 14
cert_leafTestAt_block_2 160 14 15
cert_leafTestAt_block_2 160 15 16
cert_leafTestAt_block_2 160 16 17
cert_leafTestAt_block_2 160 17 18
cert_leafTestAt_block_2 160 18 19
cert_leafTestAt_block_2 160 19 20
cert_leafTestAt_block_2 160 20 21
cert_leafTestAt_block_2 160 21 22
cert_leafTestAt_block_2 160 22 23
cert_leafTestAt_block_2 160 23 24
cert_leafTestAt_block_2 160 24 25
cert_leafTestAt_block_2 160 25 26
cert_leafTestAt_block_2 160 26 27
cert_leafTestAt_block_2 160 27 28
cert_leafTestAt_block_2 160 28 29
cert_leafTestAt_block_2 160 29 30
cert_leafTestAt_block_2 160 30 31
cert_leafTestAt_block_2 160 31 32
theorem leafTestAt160_complete : Interval leafTestAt160 0 32 :=
  (interval_append leafTestAt160 0 16 32
  (interval_append leafTestAt160 0 8 16
  (interval_append leafTestAt160 0 4 8
  (interval_append leafTestAt160 0 2 4
  (interval_append leafTestAt160 0 1 2
  leafTestAt160_block_0
  leafTestAt160_block_1)
  (interval_append leafTestAt160 2 3 4
  leafTestAt160_block_2
  leafTestAt160_block_3))
  (interval_append leafTestAt160 4 6 8
  (interval_append leafTestAt160 4 5 6
  leafTestAt160_block_4
  leafTestAt160_block_5)
  (interval_append leafTestAt160 6 7 8
  leafTestAt160_block_6
  leafTestAt160_block_7)))
  (interval_append leafTestAt160 8 12 16
  (interval_append leafTestAt160 8 10 12
  (interval_append leafTestAt160 8 9 10
  leafTestAt160_block_8
  leafTestAt160_block_9)
  (interval_append leafTestAt160 10 11 12
  leafTestAt160_block_10
  leafTestAt160_block_11))
  (interval_append leafTestAt160 12 14 16
  (interval_append leafTestAt160 12 13 14
  leafTestAt160_block_12
  leafTestAt160_block_13)
  (interval_append leafTestAt160 14 15 16
  leafTestAt160_block_14
  leafTestAt160_block_15))))
  (interval_append leafTestAt160 16 24 32
  (interval_append leafTestAt160 16 20 24
  (interval_append leafTestAt160 16 18 20
  (interval_append leafTestAt160 16 17 18
  leafTestAt160_block_16
  leafTestAt160_block_17)
  (interval_append leafTestAt160 18 19 20
  leafTestAt160_block_18
  leafTestAt160_block_19))
  (interval_append leafTestAt160 20 22 24
  (interval_append leafTestAt160 20 21 22
  leafTestAt160_block_20
  leafTestAt160_block_21)
  (interval_append leafTestAt160 22 23 24
  leafTestAt160_block_22
  leafTestAt160_block_23)))
  (interval_append leafTestAt160 24 28 32
  (interval_append leafTestAt160 24 26 28
  (interval_append leafTestAt160 24 25 26
  leafTestAt160_block_24
  leafTestAt160_block_25)
  (interval_append leafTestAt160 26 27 28
  leafTestAt160_block_26
  leafTestAt160_block_27))
  (interval_append leafTestAt160 28 30 32
  (interval_append leafTestAt160 28 29 30
  leafTestAt160_block_28
  leafTestAt160_block_29)
  (interval_append leafTestAt160 30 31 32
  leafTestAt160_block_30
  leafTestAt160_block_31)))))
cert_leafInterval 160 192
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 192
cert_leafTestAt_block_2 192 0 1
cert_leafTestAt_block_2 192 1 2
cert_leafTestAt_block_2 192 2 3
cert_leafTestAt_block_2 192 3 4
cert_leafTestAt_block_2 192 4 5
cert_leafTestAt_block_2 192 5 6
cert_leafTestAt_block_2 192 6 7
cert_leafTestAt_block_2 192 7 8
cert_leafTestAt_block_2 192 8 9
cert_leafTestAt_block_2 192 9 10
cert_leafTestAt_block_2 192 10 11
cert_leafTestAt_block_2 192 11 12
cert_leafTestAt_block_2 192 12 13
cert_leafTestAt_block_2 192 13 14
cert_leafTestAt_block_2 192 14 15
cert_leafTestAt_block_2 192 15 16
cert_leafTestAt_block_2 192 16 17
cert_leafTestAt_block_2 192 17 18
cert_leafTestAt_block_2 192 18 19
cert_leafTestAt_block_2 192 19 20
cert_leafTestAt_block_2 192 20 21
cert_leafTestAt_block_2 192 21 22
cert_leafTestAt_block_2 192 22 23
cert_leafTestAt_block_2 192 23 24
cert_leafTestAt_block_2 192 24 25
cert_leafTestAt_block_2 192 25 26
cert_leafTestAt_block_2 192 26 27
cert_leafTestAt_block_2 192 27 28
cert_leafTestAt_block_2 192 28 29
cert_leafTestAt_block_2 192 29 30
cert_leafTestAt_block_2 192 30 31
cert_leafTestAt_block_2 192 31 32
theorem leafTestAt192_complete : Interval leafTestAt192 0 32 :=
  (interval_append leafTestAt192 0 16 32
  (interval_append leafTestAt192 0 8 16
  (interval_append leafTestAt192 0 4 8
  (interval_append leafTestAt192 0 2 4
  (interval_append leafTestAt192 0 1 2
  leafTestAt192_block_0
  leafTestAt192_block_1)
  (interval_append leafTestAt192 2 3 4
  leafTestAt192_block_2
  leafTestAt192_block_3))
  (interval_append leafTestAt192 4 6 8
  (interval_append leafTestAt192 4 5 6
  leafTestAt192_block_4
  leafTestAt192_block_5)
  (interval_append leafTestAt192 6 7 8
  leafTestAt192_block_6
  leafTestAt192_block_7)))
  (interval_append leafTestAt192 8 12 16
  (interval_append leafTestAt192 8 10 12
  (interval_append leafTestAt192 8 9 10
  leafTestAt192_block_8
  leafTestAt192_block_9)
  (interval_append leafTestAt192 10 11 12
  leafTestAt192_block_10
  leafTestAt192_block_11))
  (interval_append leafTestAt192 12 14 16
  (interval_append leafTestAt192 12 13 14
  leafTestAt192_block_12
  leafTestAt192_block_13)
  (interval_append leafTestAt192 14 15 16
  leafTestAt192_block_14
  leafTestAt192_block_15))))
  (interval_append leafTestAt192 16 24 32
  (interval_append leafTestAt192 16 20 24
  (interval_append leafTestAt192 16 18 20
  (interval_append leafTestAt192 16 17 18
  leafTestAt192_block_16
  leafTestAt192_block_17)
  (interval_append leafTestAt192 18 19 20
  leafTestAt192_block_18
  leafTestAt192_block_19))
  (interval_append leafTestAt192 20 22 24
  (interval_append leafTestAt192 20 21 22
  leafTestAt192_block_20
  leafTestAt192_block_21)
  (interval_append leafTestAt192 22 23 24
  leafTestAt192_block_22
  leafTestAt192_block_23)))
  (interval_append leafTestAt192 24 28 32
  (interval_append leafTestAt192 24 26 28
  (interval_append leafTestAt192 24 25 26
  leafTestAt192_block_24
  leafTestAt192_block_25)
  (interval_append leafTestAt192 26 27 28
  leafTestAt192_block_26
  leafTestAt192_block_27))
  (interval_append leafTestAt192 28 30 32
  (interval_append leafTestAt192 28 29 30
  leafTestAt192_block_28
  leafTestAt192_block_29)
  (interval_append leafTestAt192 30 31 32
  leafTestAt192_block_30
  leafTestAt192_block_31)))))
cert_leafInterval 192 224
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 224
cert_leafTestAt_block_2 224 0 1
cert_leafTestAt_block_2 224 1 2
cert_leafTestAt_block_2 224 2 3
cert_leafTestAt_block_2 224 3 4
cert_leafTestAt_block_2 224 4 5
cert_leafTestAt_block_2 224 5 6
cert_leafTestAt_block_2 224 6 7
cert_leafTestAt_block_2 224 7 8
cert_leafTestAt_block_2 224 8 9
cert_leafTestAt_block_2 224 9 10
cert_leafTestAt_block_2 224 10 11
cert_leafTestAt_block_2 224 11 12
cert_leafTestAt_block_2 224 12 13
cert_leafTestAt_block_2 224 13 14
cert_leafTestAt_block_2 224 14 15
cert_leafTestAt_block_2 224 15 16
cert_leafTestAt_block_2 224 16 17
cert_leafTestAt_block_2 224 17 18
cert_leafTestAt_block_2 224 18 19
cert_leafTestAt_block_2 224 19 20
cert_leafTestAt_block_2 224 20 21
cert_leafTestAt_block_2 224 21 22
cert_leafTestAt_block_2 224 22 23
cert_leafTestAt_block_2 224 23 24
cert_leafTestAt_block_2 224 24 25
cert_leafTestAt_block_2 224 25 26
cert_leafTestAt_block_2 224 26 27
cert_leafTestAt_block_2 224 27 28
cert_leafTestAt_block_2 224 28 29
cert_leafTestAt_block_2 224 29 30
cert_leafTestAt_block_2 224 30 31
cert_leafTestAt_block_2 224 31 32
theorem leafTestAt224_complete : Interval leafTestAt224 0 32 :=
  (interval_append leafTestAt224 0 16 32
  (interval_append leafTestAt224 0 8 16
  (interval_append leafTestAt224 0 4 8
  (interval_append leafTestAt224 0 2 4
  (interval_append leafTestAt224 0 1 2
  leafTestAt224_block_0
  leafTestAt224_block_1)
  (interval_append leafTestAt224 2 3 4
  leafTestAt224_block_2
  leafTestAt224_block_3))
  (interval_append leafTestAt224 4 6 8
  (interval_append leafTestAt224 4 5 6
  leafTestAt224_block_4
  leafTestAt224_block_5)
  (interval_append leafTestAt224 6 7 8
  leafTestAt224_block_6
  leafTestAt224_block_7)))
  (interval_append leafTestAt224 8 12 16
  (interval_append leafTestAt224 8 10 12
  (interval_append leafTestAt224 8 9 10
  leafTestAt224_block_8
  leafTestAt224_block_9)
  (interval_append leafTestAt224 10 11 12
  leafTestAt224_block_10
  leafTestAt224_block_11))
  (interval_append leafTestAt224 12 14 16
  (interval_append leafTestAt224 12 13 14
  leafTestAt224_block_12
  leafTestAt224_block_13)
  (interval_append leafTestAt224 14 15 16
  leafTestAt224_block_14
  leafTestAt224_block_15))))
  (interval_append leafTestAt224 16 24 32
  (interval_append leafTestAt224 16 20 24
  (interval_append leafTestAt224 16 18 20
  (interval_append leafTestAt224 16 17 18
  leafTestAt224_block_16
  leafTestAt224_block_17)
  (interval_append leafTestAt224 18 19 20
  leafTestAt224_block_18
  leafTestAt224_block_19))
  (interval_append leafTestAt224 20 22 24
  (interval_append leafTestAt224 20 21 22
  leafTestAt224_block_20
  leafTestAt224_block_21)
  (interval_append leafTestAt224 22 23 24
  leafTestAt224_block_22
  leafTestAt224_block_23)))
  (interval_append leafTestAt224 24 28 32
  (interval_append leafTestAt224 24 26 28
  (interval_append leafTestAt224 24 25 26
  leafTestAt224_block_24
  leafTestAt224_block_25)
  (interval_append leafTestAt224 26 27 28
  leafTestAt224_block_26
  leafTestAt224_block_27))
  (interval_append leafTestAt224 28 30 32
  (interval_append leafTestAt224 28 29 30
  leafTestAt224_block_28
  leafTestAt224_block_29)
  (interval_append leafTestAt224 30 31 32
  leafTestAt224_block_30
  leafTestAt224_block_31)))))
cert_leafInterval 224 256
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 256
cert_leafTestAt_block_2 256 0 1
cert_leafTestAt_block_2 256 1 2
cert_leafTestAt_block_2 256 2 3
cert_leafTestAt_block_2 256 3 4
cert_leafTestAt_block_2 256 4 5
cert_leafTestAt_block_2 256 5 6
cert_leafTestAt_block_2 256 6 7
cert_leafTestAt_block_2 256 7 8
cert_leafTestAt_block_2 256 8 9
cert_leafTestAt_block_2 256 9 10
cert_leafTestAt_block_2 256 10 11
cert_leafTestAt_block_2 256 11 12
cert_leafTestAt_block_2 256 12 13
cert_leafTestAt_block_2 256 13 14
cert_leafTestAt_block_2 256 14 15
cert_leafTestAt_block_2 256 15 16
cert_leafTestAt_block_2 256 16 17
cert_leafTestAt_block_2 256 17 18
cert_leafTestAt_block_2 256 18 19
cert_leafTestAt_block_2 256 19 20
cert_leafTestAt_block_2 256 20 21
cert_leafTestAt_block_2 256 21 22
cert_leafTestAt_block_2 256 22 23
cert_leafTestAt_block_2 256 23 24
cert_leafTestAt_block_2 256 24 25
cert_leafTestAt_block_2 256 25 26
cert_leafTestAt_block_2 256 26 27
cert_leafTestAt_block_2 256 27 28
cert_leafTestAt_block_2 256 28 29
cert_leafTestAt_block_2 256 29 30
cert_leafTestAt_block_2 256 30 31
cert_leafTestAt_block_2 256 31 32
theorem leafTestAt256_complete : Interval leafTestAt256 0 32 :=
  (interval_append leafTestAt256 0 16 32
  (interval_append leafTestAt256 0 8 16
  (interval_append leafTestAt256 0 4 8
  (interval_append leafTestAt256 0 2 4
  (interval_append leafTestAt256 0 1 2
  leafTestAt256_block_0
  leafTestAt256_block_1)
  (interval_append leafTestAt256 2 3 4
  leafTestAt256_block_2
  leafTestAt256_block_3))
  (interval_append leafTestAt256 4 6 8
  (interval_append leafTestAt256 4 5 6
  leafTestAt256_block_4
  leafTestAt256_block_5)
  (interval_append leafTestAt256 6 7 8
  leafTestAt256_block_6
  leafTestAt256_block_7)))
  (interval_append leafTestAt256 8 12 16
  (interval_append leafTestAt256 8 10 12
  (interval_append leafTestAt256 8 9 10
  leafTestAt256_block_8
  leafTestAt256_block_9)
  (interval_append leafTestAt256 10 11 12
  leafTestAt256_block_10
  leafTestAt256_block_11))
  (interval_append leafTestAt256 12 14 16
  (interval_append leafTestAt256 12 13 14
  leafTestAt256_block_12
  leafTestAt256_block_13)
  (interval_append leafTestAt256 14 15 16
  leafTestAt256_block_14
  leafTestAt256_block_15))))
  (interval_append leafTestAt256 16 24 32
  (interval_append leafTestAt256 16 20 24
  (interval_append leafTestAt256 16 18 20
  (interval_append leafTestAt256 16 17 18
  leafTestAt256_block_16
  leafTestAt256_block_17)
  (interval_append leafTestAt256 18 19 20
  leafTestAt256_block_18
  leafTestAt256_block_19))
  (interval_append leafTestAt256 20 22 24
  (interval_append leafTestAt256 20 21 22
  leafTestAt256_block_20
  leafTestAt256_block_21)
  (interval_append leafTestAt256 22 23 24
  leafTestAt256_block_22
  leafTestAt256_block_23)))
  (interval_append leafTestAt256 24 28 32
  (interval_append leafTestAt256 24 26 28
  (interval_append leafTestAt256 24 25 26
  leafTestAt256_block_24
  leafTestAt256_block_25)
  (interval_append leafTestAt256 26 27 28
  leafTestAt256_block_26
  leafTestAt256_block_27))
  (interval_append leafTestAt256 28 30 32
  (interval_append leafTestAt256 28 29 30
  leafTestAt256_block_28
  leafTestAt256_block_29)
  (interval_append leafTestAt256 30 31 32
  leafTestAt256_block_30
  leafTestAt256_block_31)))))
cert_leafInterval 256 288
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 288
cert_leafTestAt_block_2 288 0 1
cert_leafTestAt_block_2 288 1 2
cert_leafTestAt_block_2 288 2 3
cert_leafTestAt_block_2 288 3 4
cert_leafTestAt_block_2 288 4 5
cert_leafTestAt_block_2 288 5 6
cert_leafTestAt_block_2 288 6 7
cert_leafTestAt_block_2 288 7 8
cert_leafTestAt_block_2 288 8 9
cert_leafTestAt_block_2 288 9 10
cert_leafTestAt_block_2 288 10 11
cert_leafTestAt_block_2 288 11 12
cert_leafTestAt_block_2 288 12 13
cert_leafTestAt_block_2 288 13 14
cert_leafTestAt_block_2 288 14 15
cert_leafTestAt_block_2 288 15 16
cert_leafTestAt_block_2 288 16 17
cert_leafTestAt_block_2 288 17 18
cert_leafTestAt_block_2 288 18 19
cert_leafTestAt_block_2 288 19 20
cert_leafTestAt_block_2 288 20 21
cert_leafTestAt_block_2 288 21 22
cert_leafTestAt_block_2 288 22 23
cert_leafTestAt_block_2 288 23 24
cert_leafTestAt_block_2 288 24 25
cert_leafTestAt_block_2 288 25 26
cert_leafTestAt_block_2 288 26 27
cert_leafTestAt_block_2 288 27 28
cert_leafTestAt_block_2 288 28 29
cert_leafTestAt_block_2 288 29 30
cert_leafTestAt_block_2 288 30 31
cert_leafTestAt_block_2 288 31 32
theorem leafTestAt288_complete : Interval leafTestAt288 0 32 :=
  (interval_append leafTestAt288 0 16 32
  (interval_append leafTestAt288 0 8 16
  (interval_append leafTestAt288 0 4 8
  (interval_append leafTestAt288 0 2 4
  (interval_append leafTestAt288 0 1 2
  leafTestAt288_block_0
  leafTestAt288_block_1)
  (interval_append leafTestAt288 2 3 4
  leafTestAt288_block_2
  leafTestAt288_block_3))
  (interval_append leafTestAt288 4 6 8
  (interval_append leafTestAt288 4 5 6
  leafTestAt288_block_4
  leafTestAt288_block_5)
  (interval_append leafTestAt288 6 7 8
  leafTestAt288_block_6
  leafTestAt288_block_7)))
  (interval_append leafTestAt288 8 12 16
  (interval_append leafTestAt288 8 10 12
  (interval_append leafTestAt288 8 9 10
  leafTestAt288_block_8
  leafTestAt288_block_9)
  (interval_append leafTestAt288 10 11 12
  leafTestAt288_block_10
  leafTestAt288_block_11))
  (interval_append leafTestAt288 12 14 16
  (interval_append leafTestAt288 12 13 14
  leafTestAt288_block_12
  leafTestAt288_block_13)
  (interval_append leafTestAt288 14 15 16
  leafTestAt288_block_14
  leafTestAt288_block_15))))
  (interval_append leafTestAt288 16 24 32
  (interval_append leafTestAt288 16 20 24
  (interval_append leafTestAt288 16 18 20
  (interval_append leafTestAt288 16 17 18
  leafTestAt288_block_16
  leafTestAt288_block_17)
  (interval_append leafTestAt288 18 19 20
  leafTestAt288_block_18
  leafTestAt288_block_19))
  (interval_append leafTestAt288 20 22 24
  (interval_append leafTestAt288 20 21 22
  leafTestAt288_block_20
  leafTestAt288_block_21)
  (interval_append leafTestAt288 22 23 24
  leafTestAt288_block_22
  leafTestAt288_block_23)))
  (interval_append leafTestAt288 24 28 32
  (interval_append leafTestAt288 24 26 28
  (interval_append leafTestAt288 24 25 26
  leafTestAt288_block_24
  leafTestAt288_block_25)
  (interval_append leafTestAt288 26 27 28
  leafTestAt288_block_26
  leafTestAt288_block_27))
  (interval_append leafTestAt288 28 30 32
  (interval_append leafTestAt288 28 29 30
  leafTestAt288_block_28
  leafTestAt288_block_29)
  (interval_append leafTestAt288 30 31 32
  leafTestAt288_block_30
  leafTestAt288_block_31)))))
cert_leafInterval 288 320
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 320
cert_leafTestAt_block_2 320 0 1
cert_leafTestAt_block_2 320 1 2
cert_leafTestAt_block_2 320 2 3
cert_leafTestAt_block_2 320 3 4
cert_leafTestAt_block_2 320 4 5
cert_leafTestAt_block_2 320 5 6
cert_leafTestAt_block_2 320 6 7
cert_leafTestAt_block_2 320 7 8
cert_leafTestAt_block_2 320 8 9
cert_leafTestAt_block_2 320 9 10
cert_leafTestAt_block_2 320 10 11
cert_leafTestAt_block_2 320 11 12
cert_leafTestAt_block_2 320 12 13
cert_leafTestAt_block_2 320 13 14
cert_leafTestAt_block_2 320 14 15
cert_leafTestAt_block_2 320 15 16
cert_leafTestAt_block_2 320 16 17
cert_leafTestAt_block_2 320 17 18
cert_leafTestAt_block_2 320 18 19
cert_leafTestAt_block_2 320 19 20
cert_leafTestAt_block_2 320 20 21
cert_leafTestAt_block_2 320 21 22
cert_leafTestAt_block_2 320 22 23
cert_leafTestAt_block_2 320 23 24
cert_leafTestAt_block_2 320 24 25
cert_leafTestAt_block_2 320 25 26
cert_leafTestAt_block_2 320 26 27
cert_leafTestAt_block_2 320 27 28
cert_leafTestAt_block_2 320 28 29
cert_leafTestAt_block_2 320 29 30
cert_leafTestAt_block_2 320 30 31
cert_leafTestAt_block_2 320 31 32
theorem leafTestAt320_complete : Interval leafTestAt320 0 32 :=
  (interval_append leafTestAt320 0 16 32
  (interval_append leafTestAt320 0 8 16
  (interval_append leafTestAt320 0 4 8
  (interval_append leafTestAt320 0 2 4
  (interval_append leafTestAt320 0 1 2
  leafTestAt320_block_0
  leafTestAt320_block_1)
  (interval_append leafTestAt320 2 3 4
  leafTestAt320_block_2
  leafTestAt320_block_3))
  (interval_append leafTestAt320 4 6 8
  (interval_append leafTestAt320 4 5 6
  leafTestAt320_block_4
  leafTestAt320_block_5)
  (interval_append leafTestAt320 6 7 8
  leafTestAt320_block_6
  leafTestAt320_block_7)))
  (interval_append leafTestAt320 8 12 16
  (interval_append leafTestAt320 8 10 12
  (interval_append leafTestAt320 8 9 10
  leafTestAt320_block_8
  leafTestAt320_block_9)
  (interval_append leafTestAt320 10 11 12
  leafTestAt320_block_10
  leafTestAt320_block_11))
  (interval_append leafTestAt320 12 14 16
  (interval_append leafTestAt320 12 13 14
  leafTestAt320_block_12
  leafTestAt320_block_13)
  (interval_append leafTestAt320 14 15 16
  leafTestAt320_block_14
  leafTestAt320_block_15))))
  (interval_append leafTestAt320 16 24 32
  (interval_append leafTestAt320 16 20 24
  (interval_append leafTestAt320 16 18 20
  (interval_append leafTestAt320 16 17 18
  leafTestAt320_block_16
  leafTestAt320_block_17)
  (interval_append leafTestAt320 18 19 20
  leafTestAt320_block_18
  leafTestAt320_block_19))
  (interval_append leafTestAt320 20 22 24
  (interval_append leafTestAt320 20 21 22
  leafTestAt320_block_20
  leafTestAt320_block_21)
  (interval_append leafTestAt320 22 23 24
  leafTestAt320_block_22
  leafTestAt320_block_23)))
  (interval_append leafTestAt320 24 28 32
  (interval_append leafTestAt320 24 26 28
  (interval_append leafTestAt320 24 25 26
  leafTestAt320_block_24
  leafTestAt320_block_25)
  (interval_append leafTestAt320 26 27 28
  leafTestAt320_block_26
  leafTestAt320_block_27))
  (interval_append leafTestAt320 28 30 32
  (interval_append leafTestAt320 28 29 30
  leafTestAt320_block_28
  leafTestAt320_block_29)
  (interval_append leafTestAt320 30 31 32
  leafTestAt320_block_30
  leafTestAt320_block_31)))))
cert_leafInterval 320 352
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
cert_leafTestAt 352
cert_leafTestAt_block_2 352 0 1
cert_leafTestAt_block_2 352 1 2
cert_leafTestAt_block_2 352 2 3
cert_leafTestAt_block_2 352 3 4
cert_leafTestAt_block_2 352 4 5
cert_leafTestAt_block_2 352 5 6
cert_leafTestAt_block_2 352 6 7
cert_leafTestAt_block_2 352 7 8
cert_leafTestAt_block_2 352 8 9
cert_leafTestAt_block_2 352 9 10
cert_leafTestAt_block_2 352 10 11
cert_leafTestAt_block_2 352 11 12
cert_leafTestAt_block_2 352 12 13
cert_leafTestAt_block_2 352 13 14
cert_leafTestAt_block_2 352 14 15
cert_leafTestAt_block_2 352 15 16
cert_leafTestAt_block_2 352 16 17
cert_leafTestAt_block_2 352 17 18
cert_leafTestAt_block_2 352 18 19
cert_leafTestAt_block_2 352 19 20
cert_leafTestAt_block_2 352 20 21
cert_leafTestAt_block_2 352 21 22
cert_leafTestAt_block_2 352 22 23
cert_leafTestAt_block_2 352 23 24
cert_leafTestAt_block_2 352 24 25
cert_leafTestAt_block_2 352 25 26
cert_leafTestAt_block_2 352 26 27
cert_leafTestAt_block_2 352 27 28
cert_leafTestAt_block_2 352 28 29
cert_leafTestAt_block_2 352 29 30
cert_leafTestAt_block_2 352 30 31
theorem leafTestAt352_complete : Interval leafTestAt352 0 31 :=
  (interval_append leafTestAt352 0 15 31
  (interval_append leafTestAt352 0 7 15
  (interval_append leafTestAt352 0 3 7
  (interval_append leafTestAt352 0 1 3
  leafTestAt352_block_0
  (interval_append leafTestAt352 1 2 3
  leafTestAt352_block_1
  leafTestAt352_block_2))
  (interval_append leafTestAt352 3 5 7
  (interval_append leafTestAt352 3 4 5
  leafTestAt352_block_3
  leafTestAt352_block_4)
  (interval_append leafTestAt352 5 6 7
  leafTestAt352_block_5
  leafTestAt352_block_6)))
  (interval_append leafTestAt352 7 11 15
  (interval_append leafTestAt352 7 9 11
  (interval_append leafTestAt352 7 8 9
  leafTestAt352_block_7
  leafTestAt352_block_8)
  (interval_append leafTestAt352 9 10 11
  leafTestAt352_block_9
  leafTestAt352_block_10))
  (interval_append leafTestAt352 11 13 15
  (interval_append leafTestAt352 11 12 13
  leafTestAt352_block_11
  leafTestAt352_block_12)
  (interval_append leafTestAt352 13 14 15
  leafTestAt352_block_13
  leafTestAt352_block_14))))
  (interval_append leafTestAt352 15 23 31
  (interval_append leafTestAt352 15 19 23
  (interval_append leafTestAt352 15 17 19
  (interval_append leafTestAt352 15 16 17
  leafTestAt352_block_15
  leafTestAt352_block_16)
  (interval_append leafTestAt352 17 18 19
  leafTestAt352_block_17
  leafTestAt352_block_18))
  (interval_append leafTestAt352 19 21 23
  (interval_append leafTestAt352 19 20 21
  leafTestAt352_block_19
  leafTestAt352_block_20)
  (interval_append leafTestAt352 21 22 23
  leafTestAt352_block_21
  leafTestAt352_block_22)))
  (interval_append leafTestAt352 23 27 31
  (interval_append leafTestAt352 23 25 27
  (interval_append leafTestAt352 23 24 25
  leafTestAt352_block_23
  leafTestAt352_block_24)
  (interval_append leafTestAt352 25 26 27
  leafTestAt352_block_25
  leafTestAt352_block_26))
  (interval_append leafTestAt352 27 29 31
  (interval_append leafTestAt352 27 28 29
  leafTestAt352_block_27
  leafTestAt352_block_28)
  (interval_append leafTestAt352 29 30 31
  leafTestAt352_block_29
  leafTestAt352_block_30)))))
cert_leafInterval 352 383
end Papers.RationalityTen.RootedForests.RootedSubsumedForest0338
end
end
