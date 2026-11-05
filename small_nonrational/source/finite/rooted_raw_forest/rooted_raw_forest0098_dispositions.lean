module
prelude
public import RootedRawForest0098Dispositions000
public import RootedRawForest0098Dispositions001

@[expose] public section
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Papers.RationalityTen.RootedForests.RootedRawForest0098
open Papers.RationalityTen ConcreteGrowth FiniteChecks
open GrowthDAG SparseGrowthDAG GrowthPruning GrowthRenaming
open GrowthBitsets BatchedGrowthPruning BatchedOrbitGrowth
open RawNatGrowthSoundness RawNatGrowthCompleteness

theorem dispositionTest_complete : Interval dispositionTest 0 leafCount := (interval_append dispositionTest 0 18 36 (interval_append dispositionTest 0 9 18 (interval_append dispositionTest 0 4 9 (interval_append dispositionTest 0 2 4 (interval_append dispositionTest 0 1 2 disposition_interval_0 disposition_interval_1) (interval_append dispositionTest 2 3 4 disposition_interval_2 disposition_interval_3)) (interval_append dispositionTest 4 6 9 (interval_append dispositionTest 4 5 6 disposition_interval_4 disposition_interval_5) (interval_append dispositionTest 6 7 9 disposition_interval_6 (interval_append dispositionTest 7 8 9 disposition_interval_7 disposition_interval_8)))) (interval_append dispositionTest 9 13 18 (interval_append dispositionTest 9 11 13 (interval_append dispositionTest 9 10 11 disposition_interval_9 disposition_interval_10) (interval_append dispositionTest 11 12 13 disposition_interval_11 disposition_interval_12)) (interval_append dispositionTest 13 15 18 (interval_append dispositionTest 13 14 15 disposition_interval_13 disposition_interval_14) (interval_append dispositionTest 15 16 18 disposition_interval_15 (interval_append dispositionTest 16 17 18 disposition_interval_16 disposition_interval_17))))) (interval_append dispositionTest 18 27 36 (interval_append dispositionTest 18 22 27 (interval_append dispositionTest 18 20 22 (interval_append dispositionTest 18 19 20 disposition_interval_18 disposition_interval_19) (interval_append dispositionTest 20 21 22 disposition_interval_20 disposition_interval_21)) (interval_append dispositionTest 22 24 27 (interval_append dispositionTest 22 23 24 disposition_interval_22 disposition_interval_23) (interval_append dispositionTest 24 25 27 disposition_interval_24 (interval_append dispositionTest 25 26 27 disposition_interval_25 disposition_interval_26)))) (interval_append dispositionTest 27 31 36 (interval_append dispositionTest 27 29 31 (interval_append dispositionTest 27 28 29 disposition_interval_27 disposition_interval_28) (interval_append dispositionTest 29 30 31 disposition_interval_29 disposition_interval_30)) (interval_append dispositionTest 31 33 36 (interval_append dispositionTest 31 32 33 disposition_interval_31 disposition_interval_32) (interval_append dispositionTest 33 34 36 disposition_interval_33 (interval_append dispositionTest 34 35 36 disposition_interval_34 disposition_interval_35))))))
theorem disposition_checked (j : Fin leafCount) :
    RawLeafCertificate.check quota ((rawLeaves j.val).map Papers.RationalityTen.RootedCaches.RootedSevenPure064.rawCells)
      (disposition j) = true :=
  dispositionTest_complete j.val (Nat.zero_le _) j.isLt

end Papers.RationalityTen.RootedForests.RootedRawForest0098
