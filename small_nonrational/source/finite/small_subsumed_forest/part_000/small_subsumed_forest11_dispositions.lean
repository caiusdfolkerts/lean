module
prelude
public import SmallSubsumedForest11Dispositions000
public import SmallSubsumedForest11Dispositions001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 19 39 (interval_append dispositionTest 0 9 19 (interval_append dispositionTest 0 4 9 (interval_append dispositionTest 0 2 4 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 4 disposition_interval_2 disposition_interval_3)) (interval_append dispositionTest 4 6 9 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5) (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)))) (interval_append dispositionTest 9 14 19 (interval_append dispositionTest 9 11 14 (interval_append dispositionTest 9 10 11 disposition_interval_9 disposition_interval_10) (interval_append dispositionTest 11 12 14 disposition_interval_11 (interval_append dispositionTest 12 13 14 disposition_interval_12 disposition_interval_13))) (interval_append dispositionTest 14 16 19 (interval_append dispositionTest 14 15 16 disposition_interval_14 disposition_interval_15) (interval_append dispositionTest 16 17 19 disposition_interval_16 (interval_append dispositionTest 17 18 19 disposition_interval_17 disposition_interval_18))))) (interval_append dispositionTest 19 29 39 (interval_append dispositionTest 19 24 29 (interval_append dispositionTest 19 21 24 (interval_append dispositionTest 19 20 21 disposition_interval_19 disposition_interval_20) (interval_append dispositionTest 21 22 24 disposition_interval_21 (interval_append dispositionTest 22 23 24 disposition_interval_22 disposition_interval_23))) (interval_append dispositionTest 24 26 29 (interval_append dispositionTest 24 25 26 disposition_interval_24 disposition_interval_25) (interval_append dispositionTest 26 27 29 disposition_interval_26 (interval_append dispositionTest 27 28 29 disposition_interval_27 disposition_interval_28)))) (interval_append dispositionTest 29 34 39 (interval_append dispositionTest 29 31 34 (interval_append dispositionTest 29 30 31 disposition_interval_29 disposition_interval_30) (interval_append dispositionTest 31 32 34 disposition_interval_31 (interval_append dispositionTest 32 33 34 disposition_interval_32 disposition_interval_33))) (interval_append dispositionTest 34 36 39 (interval_append dispositionTest 34 35 36 disposition_interval_34 disposition_interval_35) (interval_append dispositionTest 36 37 39 disposition_interval_36 (interval_append dispositionTest 37 38 39 disposition_interval_37 disposition_interval_38))))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map RootedSmallCache.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.SmallRawForests.SmallSubsumedForest11
