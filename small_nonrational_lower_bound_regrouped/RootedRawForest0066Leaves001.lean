module
prelude
public meta import LowerSchemas.FiniteRootedRawForest
public import RootedRawForest0066Data

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0066
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness
def leafTestAt32 (i : Nat) := leafTest (i+32)
cert_leafTestAt_block 32 0 1
cert_leafTestAt_block 32 1 2
cert_leafTestAt_block 32 2 3
cert_leafTestAt_block 32 3 4
cert_leafTestAt_block 32 4 5
cert_leafTestAt_block 32 5 6
cert_leafTestAt_block 32 6 7
cert_leafTestAt_block 32 7 8
cert_leafTestAt_block 32 8 9
cert_leafTestAt_block 32 9 10
cert_leafTestAt_block 32 10 11
cert_leafTestAt_block 32 11 12
cert_leafTestAt_block 32 12 13
cert_leafTestAt_block 32 13 14
cert_leafTestAt_block 32 14 15
cert_leafTestAt_block 32 15 16
cert_leafTestAt_block 32 16 17
cert_leafTestAt_block 32 17 18
cert_leafTestAt_block 32 18 19
cert_leafTestAt_block 32 19 20
cert_leafTestAt_block 32 20 21
cert_leafTestAt_block 32 21 22
cert_leafTestAt_block 32 22 23
cert_leafTestAt_block 32 23 24
cert_leafTestAt_block 32 24 25
cert_leafTestAt_block 32 25 26
cert_leafTestAt_block 32 26 27
cert_leafTestAt_block 32 27 28
cert_leafTestAt_block 32 28 29
cert_leafTestAt_block 32 29 30
cert_leafTestAt_block 32 30 31
cert_leafTestAt_block 32 31 32
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
theorem leafInterval32 : Interval leafTest 32 64 := by
  intro i hlo hhi
  have h := leafTestAt32_complete (i-32) (Nat.zero_le _) (by omega)
  simpa only [leafTestAt32, Nat.sub_add_cancel hlo] using h

end Papers.RationalityTen.RootedForests.RootedRawForest0066
